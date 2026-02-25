#!/usr/bin/env php
<?php

define('DS', DIRECTORY_SEPARATOR);

if (!function_exists('fnmatch')) {
    function fnmatch($pattern, $string) {
        return preg_match("#^" . strtr(preg_quote($pattern, '#'), ['\*' => '.*', '\?' => '.']) . "$#i", $string);
    }
}

class LargestFilesHeap extends SplMaxHeap {
    public function compare($a, $b) {
        return $a[0] <=> $b[0];
    }
}

class OldestFilesHeap extends SplMinHeap {
    public function compare($a, $b) {
        return $a[0] <=> $b[0];
    }
}

class NewestFilesHeap extends SplMinHeap {
    public function compare($a, $b) {
        return $a[0] <=> $b[0];
    }
}

class InodeAnalyzer
{
    private array $stats = [
        'total_files' => 0,
        'total_dirs' => 0,
        'total_symlinks' => 0,
        'total_sockets' => 0,
        'total_fifos' => 0,
        'total_devices' => 0,
        'extensions' => [],
        'largest_files' => [],
        'oldest_files' => [],
        'newest_files' => [],
        'largest_dirs' => [],
        'permissions' => [],
        'owners' => [],
        'groups' => [],
        'age_distribution' => [],
        'size_distribution' => [],
        'duplicates' => [],
        'empty_files' => 0,
        'empty_dirs' => 0,
        'broken_symlinks' => 0,
        'permission_denied' => 0,
        'file_types' => [
            'directory' => 0,
            'symlink' => 0,
            'socket' => 0,
            'fifo' => 0,
            'device' => 0,
            'regular' => 0
        ]
    ];
    
    private int $threads;
    private bool $followSymlinks;
    private array $excludePatterns;
    private int $totalSize = 0;
    private array $processedPaths = [];
    private array $fileMetadata = [];
    private bool $interrupted = false;
    private LargestFilesHeap $largestFilesHeap;
    private OldestFilesHeap $oldestFilesHeap;
    private NewestFilesHeap $newestFilesHeap;
    private array $lock = [
        'stats' => false,
        'size' => false,
        'heaps' => false
    ];
    private int $processedCount = 0;
    private int $totalItems = 0;
    private string $currentPath = '';
    
    private const SIZE_CATEGORIES = [
        '< 1 KB' => 1,
        '1 KB - 1 MB' => 2,
        '1 MB - 10 MB' => 3,
        '10 MB - 100 MB' => 4,
        '100 MB - 1 GB' => 5,
        '> 1 GB' => 6
    ];
    
    private const AGE_CATEGORIES = [
        'Today' => 1,
        'This week' => 2,
        'This month' => 3,
        'This year' => 4,
        '> 1 year' => 5
    ];
    
    private const S_IFMT = 0170000;
    private const S_IFSOCK = 0140000;
    private const S_IFLNK = 0120000;
    private const S_IFREG = 0100000;
    private const S_IFBLK = 0060000;
    private const S_IFDIR = 0040000;
    private const S_IFCHR = 0020000;
    private const S_IFIFO = 0010000;
    
    public function __construct(int $threads = 4, bool $followSymlinks = false, array $excludePatterns = [])
    {
        $this->threads = $threads;
        $this->followSymlinks = $followSymlinks;
        $this->excludePatterns = $excludePatterns;
        $this->largestFilesHeap = new LargestFilesHeap();
        $this->oldestFilesHeap = new OldestFilesHeap();
        $this->newestFilesHeap = new NewestFilesHeap();
        
        if (function_exists('pcntl_signal')) {
            pcntl_signal(SIGINT, [$this, 'handleInterrupt']);
        }
    }
    
    public function handleInterrupt(): void
    {
        $this->interrupted = true;
        echo "\nInterrupt received, finishing current operations...\n";
    }
    
    private function getHumanReadable($value, bool $isBytes = true): string
    {
        if ($isBytes) {
            $units = ['B', 'KB', 'MB', 'GB', 'TB', 'PB'];
            $i = 0;
            while ($value >= 1024 && $i < count($units) - 1) {
                $value /= 1024;
                $i++;
            }
            return round($value, 2) . ' ' . $units[$i];
        }
        
        return number_format($value);
    }
    
    private function shouldExclude(string $path): bool
    {
        foreach ($this->excludePatterns as $pattern) {
            if (fnmatch($pattern, $path) || fnmatch($pattern, basename($path))) {
                return true;
            }
        }
        return false;
    }
    
    private function acquireLock(string $resource): void
    {
        while (isset($this->lock[$resource]) && $this->lock[$resource]) {
            usleep(100);
        }
        $this->lock[$resource] = true;
    }
    
    private function releaseLock(string $resource): void
    {
        $this->lock[$resource] = false;
    }
    
    private function isSocket(int $mode): bool
    {
        return ($mode & self::S_IFMT) === self::S_IFSOCK;
    }
    
    private function isFifo(int $mode): bool
    {
        return ($mode & self::S_IFMT) === self::S_IFIFO;
    }
    
    private function isBlockDevice(int $mode): bool
    {
        return ($mode & self::S_IFMT) === self::S_IFBLK;
    }
    
    private function isCharDevice(int $mode): bool
    {
        return ($mode & self::S_IFMT) === self::S_IFCHR;
    }
    
    private function updateProgress(): void
    {
        if ($this->totalItems > 0) {
            $this->processedCount++;
            if ($this->processedCount % 1000 == 0) {
                $progress = round(($this->processedCount / $this->totalItems) * 100, 1);
                echo "\r  Progress: {$progress}% ({$this->processedCount}/{$this->totalItems})";
            }
        }
    }
    
    public function analyzeDirectory(
        string $path,
        int $sampleSize = 20,
        bool $deepScan = false,
        bool $findDuplicates = false,
        ?string $exportJson = null,
        ?string $generatePlot = null,
        ?int $ageDays = null,
        ?string $saveState = null,
        ?string $loadState = null,
        ?int $maxDepth = null
    ): void {
        if ($loadState) {
            $this->loadCheckpoint($loadState);
            return;
        }
        
        if (!is_dir($path)) {
            echo "Error: Path is not a directory: {$path}\n";
            return;
        }
        
        $path = realpath($path);
        if ($path === false) {
            echo "Error: Cannot resolve path: {$path}\n";
            return;
        }
        
        $startTime = microtime(true);
        
        echo "\n" . str_repeat('=', 60) . "\n";
        echo "Inode Analyzer - {$path}\n";
        echo str_repeat('=', 60) . "\n";
        echo "Mode: " . ($deepScan ? 'Deep' : 'Quick') . "\n";
        if ($findDuplicates) {
            echo "Duplicate Detection: Enabled\n";
        }
        if ($maxDepth) {
            echo "Max Depth: {$maxDepth}\n";
        }
        echo "\n";
        
        if ($deepScan) {
            $this->deepScanAnalysis($path, $sampleSize, $findDuplicates, $ageDays, $maxDepth);
        } else {
            $this->quickScanAnalysis($path, $sampleSize, $maxDepth);
        }
        
        if ($findDuplicates && !$deepScan && !$this->interrupted) {
            $this->findDuplicateFiles($path);
        }
        
        if ($saveState && !$this->interrupted) {
            $this->saveCheckpoint($saveState);
        }
        
        $elapsedTime = microtime(true) - $startTime;
        $this->printReport($elapsedTime);
        
        if ($exportJson) {
            $this->exportJson($exportJson);
        }
        
        if ($generatePlot) {
            $this->generateVisualization($generatePlot);
        }
    }
    
    private function quickScanAnalysis(string $path, int $sampleSize, ?int $maxDepth = null): void
    {
        echo "Scanning filesystem...\n";
        
        $this->processedCount = 0;
        $this->totalItems = 0;
        
        try {
            $directoryIterator = new RecursiveDirectoryIterator(
                $path, 
                FilesystemIterator::SKIP_DOTS | FilesystemIterator::UNIX_PATHS | FilesystemIterator::FOLLOW_SYMLINKS
            );
            $iterator = new RecursiveIteratorIterator(
                $directoryIterator, 
                RecursiveIteratorIterator::SELF_FIRST,
                RecursiveIteratorIterator::CATCH_GET_CHILD
            );
        } catch (Exception $e) {
            echo "Error opening directory: {$e->getMessage()}\n";
            return;
        }
        
        $iterator->rewind();
        while ($iterator->valid()) {
            $this->totalItems++;
            $iterator->next();
        }
        
        $this->processedCount = 0;
        $baseDepth = count(explode(DS, $path));
        
        try {
            $directoryIterator = new RecursiveDirectoryIterator(
                $path, 
                FilesystemIterator::SKIP_DOTS | FilesystemIterator::UNIX_PATHS | FilesystemIterator::FOLLOW_SYMLINKS
            );
            $iterator = new RecursiveIteratorIterator(
                $directoryIterator, 
                RecursiveIteratorIterator::SELF_FIRST,
                RecursiveIteratorIterator::CATCH_GET_CHILD
            );
        } catch (Exception $e) {
            echo "Error opening directory: {$e->getMessage()}\n";
            return;
        }
        
        foreach ($iterator as $item) {
            if ($this->interrupted) {
                break;
            }
            
            $currentDepth = count(explode(DS, $item->getPathname())) - $baseDepth;
            if ($maxDepth && $currentDepth >= $maxDepth) {
                $this->updateProgress();
                continue;
            }
            
            $itemPath = $item->getPathname();
            
            if ($this->shouldExclude($itemPath)) {
                $this->updateProgress();
                continue;
            }
            
            if ($item->isDir()) {
                $this->stats['total_dirs']++;
                $this->stats['file_types']['directory']++;
                try {
                    if (count(scandir($itemPath)) == 2) {
                        $this->stats['empty_dirs']++;
                    }
                } catch (Exception $e) {
                    $this->stats['permission_denied']++;
                }
                $this->updateProgress();
                continue;
            }
            
            try {
                $statInfo = $this->followSymlinks ? stat($itemPath) : lstat($itemPath);
                if ($statInfo === false) {
                    $this->stats['permission_denied']++;
                    $this->updateProgress();
                    continue;
                }
                
                if (is_link($itemPath)) {
                    $this->stats['total_symlinks']++;
                    $this->stats['file_types']['symlink']++;
                    if (!file_exists($itemPath)) {
                        $this->stats['broken_symlinks']++;
                    }
                } elseif ($this->isSocket($statInfo['mode'])) {
                    $this->stats['total_sockets']++;
                    $this->stats['file_types']['socket']++;
                } elseif ($this->isFifo($statInfo['mode'])) {
                    $this->stats['total_fifos']++;
                    $this->stats['file_types']['fifo']++;
                } elseif ($this->isBlockDevice($statInfo['mode']) || $this->isCharDevice($statInfo['mode'])) {
                    $this->stats['total_devices']++;
                    $this->stats['file_types']['device']++;
                } elseif (is_file($itemPath)) {
                    $this->stats['total_files']++;
                    $this->stats['file_types']['regular']++;
                    
                    $size = $statInfo['size'];
                    $this->totalSize += $size;
                    
                    $ext = '';
                    if (($dotPos = strrpos($item->getFilename(), '.')) !== false) {
                        $ext = strtolower(substr($item->getFilename(), $dotPos + 1));
                        $this->stats['extensions'][$ext] = ($this->stats['extensions'][$ext] ?? 0) + 1;
                    }
                    
                    $owner = $statInfo['uid'];
                    if (function_exists('posix_getpwuid')) {
                        $ownerInfo = @posix_getpwuid($statInfo['uid']);
                        $owner = $ownerInfo['name'] ?? $owner;
                    }
                    $this->stats['owners'][$owner] = ($this->stats['owners'][$owner] ?? 0) + 1;
                    
                    $group = $statInfo['gid'];
                    if (function_exists('posix_getgrgid')) {
                        $groupInfo = @posix_getgrgid($statInfo['gid']);
                        $group = $groupInfo['name'] ?? $group;
                    }
                    $this->stats['groups'][$group] = ($this->stats['groups'][$group] ?? 0) + 1;
                    
                    $perms = substr(sprintf('%o', $statInfo['mode'] & 07777), -4);
                    $this->stats['permissions'][$perms] = ($this->stats['permissions'][$perms] ?? 0) + 1;
                    
                    $sizeCategory = $this->categorizeSize($size);
                    $this->stats['size_distribution'][$sizeCategory] = ($this->stats['size_distribution'][$sizeCategory] ?? 0) + 1;
                    
                    if ($size == 0) {
                        $this->stats['empty_files']++;
                    }
                    
                    $mtime = $statInfo['mtime'];
                    $ageCategory = $this->categorizeAge($mtime);
                    $this->stats['age_distribution'][$ageCategory] = ($this->stats['age_distribution'][$ageCategory] ?? 0) + 1;
                    
                    $this->fileMetadata[$itemPath] = [
                        'path' => $itemPath,
                        'size' => $size,
                        'mtime' => date('Y-m-d H:i:s', $mtime),
                        'owner' => $owner,
                        'group' => $group,
                        'permissions' => $perms,
                        'extension' => $ext
                    ];
                    
                    $this->largestFilesHeap->insert([$size, $itemPath, date('Y-m-d H:i:s', $mtime), $owner, $group, $perms]);
                    $this->oldestFilesHeap->insert([$mtime, $itemPath, $size, $owner, $group, $perms]);
                    $this->newestFilesHeap->insert([-$mtime, $itemPath, $size, $owner, $group, $perms]);
                }
                
            } catch (Exception $e) {
                $this->stats['permission_denied']++;
            }
            
            $this->updateProgress();
        }
        
        if (!$this->interrupted) {
            echo "\r  Progress: 100% ({$this->processedCount}/{$this->totalItems})\n";
        }
        
        $largestFiles = [];
        $largestHeap = clone $this->largestFilesHeap;
        for ($i = 0; $i < $sampleSize && !$largestHeap->isEmpty(); $i++) {
            $largestFiles[] = $largestHeap->extract();
        }
        $this->stats['largest_files'] = $largestFiles;
        
        $oldestFiles = [];
        $oldestHeap = clone $this->oldestFilesHeap;
        for ($i = 0; $i < $sampleSize && !$oldestHeap->isEmpty(); $i++) {
            $item = $oldestHeap->extract();
            $oldestFiles[] = [$item[2], $item[1], date('Y-m-d H:i:s', $item[0]), $item[3], $item[4], $item[5]];
        }
        $this->stats['oldest_files'] = $oldestFiles;
        
        $newestFiles = [];
        $newestHeap = clone $this->newestFilesHeap;
        for ($i = 0; $i < $sampleSize && !$newestHeap->isEmpty(); $i++) {
            $item = $newestHeap->extract();
            $newestFiles[] = [$item[2], $item[1], date('Y-m-d H:i:s', -$item[0]), $item[3], $item[4], $item[5]];
        }
        $this->stats['newest_files'] = $newestFiles;
        
        $this->analyzeLargestDirectories($path, $sampleSize);
    }
    
    private function deepScanAnalysis(string $path, int $sampleSize, bool $findDuplicates, ?int $ageDays = null, ?int $maxDepth = null): void
    {
        echo "Deep Analysis\n\n";
        
        $this->processedCount = 0;
        $this->totalItems = 0;
        
        try {
            $directoryIterator = new RecursiveDirectoryIterator(
                $path, 
                FilesystemIterator::SKIP_DOTS | FilesystemIterator::UNIX_PATHS | FilesystemIterator::FOLLOW_SYMLINKS
            );
            $iterator = new RecursiveIteratorIterator(
                $directoryIterator, 
                RecursiveIteratorIterator::SELF_FIRST,
                RecursiveIteratorIterator::CATCH_GET_CHILD
            );
        } catch (Exception $e) {
            echo "Error opening directory: {$e->getMessage()}\n";
            return;
        }
        
        $iterator->rewind();
        while ($iterator->valid()) {
            $this->totalItems++;
            $iterator->next();
        }
        
        $this->processedCount = 0;
        $baseDepth = count(explode(DS, $path));
        
        try {
            $directoryIterator = new RecursiveDirectoryIterator(
                $path, 
                FilesystemIterator::SKIP_DOTS | FilesystemIterator::UNIX_PATHS | FilesystemIterator::FOLLOW_SYMLINKS
            );
            $iterator = new RecursiveIteratorIterator(
                $directoryIterator, 
                RecursiveIteratorIterator::SELF_FIRST,
                RecursiveIteratorIterator::CATCH_GET_CHILD
            );
        } catch (Exception $e) {
            echo "Error opening directory: {$e->getMessage()}\n";
            return;
        }
        
        foreach ($iterator as $item) {
            if ($this->interrupted) {
                break;
            }
            
            $currentDepth = count(explode(DS, $item->getPathname())) - $baseDepth;
            if ($maxDepth && $currentDepth >= $maxDepth) {
                $this->updateProgress();
                continue;
            }
            
            $itemPath = $item->getPathname();
            if (!$this->shouldExclude($itemPath)) {
                $this->analyzeItemDeep($itemPath, $ageDays);
            }
            
            $this->updateProgress();
        }
        
        if (!$this->interrupted) {
            echo "\r  Progress: 100% ({$this->processedCount}/{$this->totalItems})\n";
        }
        
        if ($this->interrupted) {
            echo "\nScan interrupted - partial results\n";
        }
        
        $largestFiles = [];
        $largestHeap = clone $this->largestFilesHeap;
        for ($i = 0; $i < $sampleSize && !$largestHeap->isEmpty(); $i++) {
            $largestFiles[] = $largestHeap->extract();
        }
        $this->stats['largest_files'] = $largestFiles;
        
        $oldestFiles = [];
        $oldestHeap = clone $this->oldestFilesHeap;
        for ($i = 0; $i < $sampleSize && !$oldestHeap->isEmpty(); $i++) {
            $item = $oldestHeap->extract();
            $oldestFiles[] = [$item[2], $item[1], date('Y-m-d H:i:s', $item[0]), $item[3], $item[4], $item[5]];
        }
        $this->stats['oldest_files'] = $oldestFiles;
        
        $newestFiles = [];
        $newestHeap = clone $this->newestFilesHeap;
        for ($i = 0; $i < $sampleSize && !$newestHeap->isEmpty(); $i++) {
            $item = $newestHeap->extract();
            $newestFiles[] = [$item[2], $item[1], date('Y-m-d H:i:s', -$item[0]), $item[3], $item[4], $item[5]];
        }
        $this->stats['newest_files'] = $newestFiles;
        
        $this->analyzeLargestDirectories($path, $sampleSize, true);
        
        if ($findDuplicates && !$this->interrupted) {
            $this->findDuplicateFiles($path);
        }
    }
    
    private function analyzeItemDeep(string $item, ?int $ageDays = null): void
    {
        try {
            if ($this->shouldExclude($item)) {
                return;
            }
            
            $statInfo = $this->followSymlinks ? @stat($item) : @lstat($item);
            if ($statInfo === false) {
                $this->acquireLock('stats');
                $this->stats['permission_denied']++;
                $this->releaseLock('stats');
                return;
            }
            
            if (is_link($item)) {
                $this->acquireLock('stats');
                $this->stats['total_symlinks']++;
                $this->stats['file_types']['symlink']++;
                if (!file_exists($item)) {
                    $this->stats['broken_symlinks']++;
                }
                $this->releaseLock('stats');
                
            } elseif ($this->isSocket($statInfo['mode'])) {
                $this->acquireLock('stats');
                $this->stats['total_sockets']++;
                $this->stats['file_types']['socket']++;
                $this->releaseLock('stats');
                
            } elseif ($this->isFifo($statInfo['mode'])) {
                $this->acquireLock('stats');
                $this->stats['total_fifos']++;
                $this->stats['file_types']['fifo']++;
                $this->releaseLock('stats');
                
            } elseif ($this->isBlockDevice($statInfo['mode']) || $this->isCharDevice($statInfo['mode'])) {
                $this->acquireLock('stats');
                $this->stats['total_devices']++;
                $this->stats['file_types']['device']++;
                $this->releaseLock('stats');
                
            } elseif (is_dir($item) && !is_link($item)) {
                $this->acquireLock('stats');
                $this->stats['total_dirs']++;
                $this->stats['file_types']['directory']++;
                $this->releaseLock('stats');
                
                try {
                    if (count(@scandir($item)) == 2) {
                        $this->acquireLock('stats');
                        $this->stats['empty_dirs']++;
                        $this->releaseLock('stats');
                    }
                } catch (Exception $e) {}
                
            } elseif (is_file($item)) {
                $this->acquireLock('stats');
                $this->stats['total_files']++;
                $this->stats['file_types']['regular']++;
                $this->releaseLock('stats');
                
                if ($ageDays) {
                    $age = time() - $statInfo['mtime'];
                    if ($age > $ageDays * 86400) {
                        return;
                    }
                }
                
                $size = $statInfo['size'];
                $this->acquireLock('size');
                $this->totalSize += $size;
                $this->releaseLock('size');
                
                $ext = '';
                if (($dotPos = strrpos(basename($item), '.')) !== false) {
                    $ext = strtolower(substr(basename($item), $dotPos + 1));
                }
                
                $this->acquireLock('stats');
                if ($ext) {
                    $this->stats['extensions'][$ext] = ($this->stats['extensions'][$ext] ?? 0) + 1;
                }
                
                $perms = substr(sprintf('%o', $statInfo['mode'] & 07777), -4);
                $this->stats['permissions'][$perms] = ($this->stats['permissions'][$perms] ?? 0) + 1;
                
                $owner = $statInfo['uid'];
                if (function_exists('posix_getpwuid')) {
                    $ownerInfo = @posix_getpwuid($statInfo['uid']);
                    $owner = $ownerInfo['name'] ?? $owner;
                }
                $this->stats['owners'][$owner] = ($this->stats['owners'][$owner] ?? 0) + 1;
                
                $group = $statInfo['gid'];
                if (function_exists('posix_getgrgid')) {
                    $groupInfo = @posix_getgrgid($statInfo['gid']);
                    $group = $groupInfo['name'] ?? $group;
                }
                $this->stats['groups'][$group] = ($this->stats['groups'][$group] ?? 0) + 1;
                
                $sizeCategory = $this->categorizeSize($size);
                $this->stats['size_distribution'][$sizeCategory] = ($this->stats['size_distribution'][$sizeCategory] ?? 0) + 1;
                
                if ($size == 0) {
                    $this->stats['empty_files']++;
                }
                
                $mtime = $statInfo['mtime'];
                $ageCategory = $this->categorizeAge($mtime);
                $this->stats['age_distribution'][$ageCategory] = ($this->stats['age_distribution'][$ageCategory] ?? 0) + 1;
                
                $this->fileMetadata[$item] = [
                    'path' => $item,
                    'size' => $size,
                    'mtime' => date('Y-m-d H:i:s', $mtime),
                    'owner' => $owner,
                    'group' => $group,
                    'permissions' => $perms,
                    'extension' => $ext
                ];
                $this->releaseLock('stats');
                
                $this->acquireLock('heaps');
                $this->largestFilesHeap->insert([$size, $item, date('Y-m-d H:i:s', $mtime), $owner, $group, $perms]);
                $this->oldestFilesHeap->insert([$mtime, $item, $size, $owner, $group, $perms]);
                $this->newestFilesHeap->insert([-$mtime, $item, $size, $owner, $group, $perms]);
                $this->releaseLock('heaps');
            }
            
        } catch (Exception $e) {
            $this->acquireLock('stats');
            $this->stats['permission_denied']++;
            $this->releaseLock('stats');
        }
    }
    
    private function analyzeLargestDirectories(string $path, int $sampleSize, bool $deep = false): void
    {
        $dirStats = [];
        
        foreach ($this->fileMetadata as $filepath => $metadata) {
            $dirPath = dirname($filepath);
            if (!isset($dirStats[$dirPath])) {
                $dirStats[$dirPath] = ['size' => 0, 'count' => 0, 'largest' => 0, 'largest_file' => ''];
            }
            
            $dirStats[$dirPath]['size'] += $metadata['size'];
            $dirStats[$dirPath]['count']++;
            
            if ($metadata['size'] > $dirStats[$dirPath]['largest']) {
                $dirStats[$dirPath]['largest'] = $metadata['size'];
                $dirStats[$dirPath]['largest_file'] = basename($filepath);
            }
        }
        
        $dirList = [];
        foreach ($dirStats as $dirPath => $stats) {
            $avgSize = $stats['count'] > 0 ? $stats['size'] / $stats['count'] : 0;
            $dirList[] = [
                'path' => $dirPath,
                'size' => $stats['size'],
                'count' => $stats['count'],
                'avg' => $avgSize,
                'largest_file' => $stats['largest_file'],
                'largest_size' => $stats['largest']
            ];
        }
        
        usort($dirList, fn($a, $b) => $b['size'] <=> $a['size']);
        
        $this->stats['largest_dirs'] = [];
        foreach (array_slice($dirList, 0, $sampleSize) as $d) {
            $this->stats['largest_dirs'][] = [
                $d['size'],
                $d['count'],
                $d['path'],
                $d['avg'],
                $d['largest_file'],
                $d['largest_size']
            ];
        }
    }
    
    private function findDuplicateFiles(string $path): void
    {
        echo "Duplicate file detection...\n";
        
        $sizeDict = [];
        $fileCount = 0;
        
        try {
            $directoryIterator = new RecursiveDirectoryIterator(
                $path, 
                FilesystemIterator::SKIP_DOTS | FilesystemIterator::UNIX_PATHS | FilesystemIterator::FOLLOW_SYMLINKS
            );
            $iterator = new RecursiveIteratorIterator(
                $directoryIterator, 
                RecursiveIteratorIterator::LEAVES_ONLY,
                RecursiveIteratorIterator::CATCH_GET_CHILD
            );
        } catch (Exception $e) {
            echo "Error opening directory: {$e->getMessage()}\n";
            return;
        }
        
        foreach ($iterator as $file) {
            if ($this->interrupted) {
                break;
            }
            
            $filepath = $file->getPathname();
            
            if ($this->shouldExclude($filepath)) {
                continue;
            }
            
            try {
                if ($file->isFile()) {
                    $size = $file->getSize();
                    if ($size > 0) {
                        $sizeDict[$size][] = $filepath;
                        $fileCount++;
                    }
                }
            } catch (Exception $e) {
                continue;
            }
        }
        
        if ($this->interrupted) {
            return;
        }
        
        $totalCandidates = 0;
        foreach ($sizeDict as $paths) {
            if (count($paths) > 1) {
                $totalCandidates++;
            }
        }
        
        echo "  Files: " . $this->getHumanReadable($fileCount, false) . " | Candidates: " . $this->getHumanReadable($totalCandidates, false) . "\n";
        echo "  Computing checksums...\n";
        
        $processed = 0;
        foreach ($sizeDict as $size => $filepaths) {
            if (count($filepaths) > 1) {
                $checksumDict = [];
                
                foreach ($filepaths as $filepath) {
                    try {
                        $checksum = $this->calculateHash($filepath);
                        if ($checksum) {
                            $checksumDict[$checksum][] = $filepath;
                        }
                    } catch (Exception $e) {
                        continue;
                    }
                }
                
                foreach ($checksumDict as $checksum => $duplicateFiles) {
                    if (count($duplicateFiles) > 1) {
                        $totalSize = $size * count($duplicateFiles);
                        $wastedSpace = $size * (count($duplicateFiles) - 1);
                        $this->stats['duplicates'][] = [
                            'size' => $size,
                            'checksum' => $checksum,
                            'files' => $duplicateFiles,
                            'total_size' => $totalSize,
                            'wasted_space' => $wastedSpace,
                            'count' => count($duplicateFiles)
                        ];
                    }
                }
                
                $processed++;
                if ($processed % 10 == 0) {
                    echo "\r      Progress: {$processed}/{$totalCandidates}";
                }
            }
        }
        
        echo "\r      Progress: {$totalCandidates}/{$totalCandidates}\n";
        
        usort($this->stats['duplicates'], fn($a, $b) => $b['wasted_space'] <=> $a['wasted_space']);
        
        $totalWasted = array_sum(array_column($this->stats['duplicates'], 'wasted_space'));
        echo "  Duplicate sets: " . $this->getHumanReadable(count($this->stats['duplicates']), false) . " | Wasted: " . $this->getHumanReadable($totalWasted) . "\n";
    }
    
    private function calculateHash(string $filepath, int $bufferSize = 65536): ?string
    {
        if (!file_exists($filepath) || !is_readable($filepath)) {
            return null;
        }
        
        $hash = hash_init('md5');
        $handle = @fopen($filepath, 'rb');
        if ($handle === false) {
            return null;
        }
        
        while (!feof($handle)) {
            $buffer = fread($handle, $bufferSize);
            if ($buffer === false) {
                fclose($handle);
                return null;
            }
            hash_update($hash, $buffer);
        }
        
        fclose($handle);
        return hash_final($hash);
    }
    
    private function categorizeSize(int $size): string
    {
        if ($size < 1024) {
            return '< 1 KB';
        } elseif ($size < 1024 * 1024) {
            return '1 KB - 1 MB';
        } elseif ($size < 10 * 1024 * 1024) {
            return '1 MB - 10 MB';
        } elseif ($size < 100 * 1024 * 1024) {
            return '10 MB - 100 MB';
        } elseif ($size < 1024 * 1024 * 1024) {
            return '100 MB - 1 GB';
        } else {
            return '> 1 GB';
        }
    }
    
    private function categorizeAge(int $mtime): string
    {
        $age = time() - $mtime;
        if ($age < 86400) {
            return 'Today';
        } elseif ($age < 604800) {
            return 'This week';
        } elseif ($age < 2592000) {
            return 'This month';
        } elseif ($age < 31536000) {
            return 'This year';
        } else {
            return '> 1 year';
        }
    }
    
    private function printReport(float $elapsedTime): void
    {
        $totalInodes = $this->stats['total_files'] + $this->stats['total_dirs'] + 
                      $this->stats['total_symlinks'] + $this->stats['total_sockets'] +
                      $this->stats['total_fifos'] + $this->stats['total_devices'];
        
        echo "\n" . str_repeat('=', 60) . "\n";
        echo "Inode Analysis Report\n";
        echo str_repeat('=', 60) . "\n";
        
        echo "\nSummary:\n";
        echo sprintf("  Files:               %18s\n", $this->getHumanReadable($this->stats['total_files'], false));
        echo sprintf("  Directories:         %18s\n", $this->getHumanReadable($this->stats['total_dirs'], false));
        echo sprintf("  Symlinks:            %18s\n", $this->getHumanReadable($this->stats['total_symlinks'], false));
        echo sprintf("  Sockets:             %18s\n", $this->getHumanReadable($this->stats['total_sockets'], false));
        echo sprintf("  FIFOs:               %18s\n", $this->getHumanReadable($this->stats['total_fifos'], false));
        echo sprintf("  Devices:             %18s\n", $this->getHumanReadable($this->stats['total_devices'], false));
        echo "  " . str_repeat('-', 45) . "\n";
        echo sprintf("  Total Inodes:        %18s\n", $this->getHumanReadable($totalInodes, false));
        echo sprintf("  Total Size:          %18s\n", $this->getHumanReadable($this->totalSize));
        echo sprintf("  Empty Files:         %18s\n", $this->getHumanReadable($this->stats['empty_files'], false));
        echo sprintf("  Empty Directories:   %18s\n", $this->getHumanReadable($this->stats['empty_dirs'], false));
        echo sprintf("  Broken Symlinks:     %18s\n", $this->getHumanReadable($this->stats['broken_symlinks'], false));
        echo sprintf("  Permission Denied:   %18s\n", $this->getHumanReadable($this->stats['permission_denied'], false));
        echo sprintf("  Scan Duration:       %18.2fs\n", $elapsedTime);
        
        if (!empty($this->stats['duplicates'])) {
            $totalWasted = array_sum(array_column($this->stats['duplicates'], 'wasted_space'));
            $totalDuplicateSets = count($this->stats['duplicates']);
            $totalDuplicateFiles = array_sum(array_column($this->stats['duplicates'], 'count'));
            
            echo "\nDuplicate Files:\n";
            echo sprintf("  Duplicate sets:      %18s\n", $this->getHumanReadable($totalDuplicateSets, false));
            echo sprintf("  Duplicate files:     %18s\n", $this->getHumanReadable($totalDuplicateFiles, false));
            echo sprintf("  Wasted space:        %18s\n", $this->getHumanReadable($totalWasted));
        }
        
        if (!empty($this->stats['extensions'])) {
            echo "\nExtensions:\n";
            arsort($this->stats['extensions']);
            foreach ($this->stats['extensions'] as $ext => $count) {
                $percentage = ($count / max($this->stats['total_files'], 1)) * 100;
                echo sprintf("  .%-20s %12s (%6.1f%%)\n", 
                    $ext, 
                    $this->getHumanReadable($count, false),
                    $percentage
                );
            }
        }
        
        if (!empty($this->stats['owners'])) {
            echo "\nOwners:\n";
            arsort($this->stats['owners']);
            foreach ($this->stats['owners'] as $owner => $count) {
                $percentage = ($count / max($this->stats['total_files'], 1)) * 100;
                echo sprintf("  %-25s %12s (%6.1f%%)\n", 
                    substr((string)$owner, 0, 25), 
                    $this->getHumanReadable($count, false),
                    $percentage
                );
            }
        }
        
        if (!empty($this->stats['size_distribution'])) {
            echo "\nSize Distribution:\n";
            uksort($this->stats['size_distribution'], function($a, $b) {
                return (self::SIZE_CATEGORIES[$a] ?? 999) <=> (self::SIZE_CATEGORIES[$b] ?? 999);
            });
            foreach ($this->stats['size_distribution'] as $category => $count) {
                $percentage = ($count / max($this->stats['total_files'], 1)) * 100;
                echo sprintf("  %-16s %12s (%6.1f%%)\n", 
                    $category, 
                    $this->getHumanReadable($count, false),
                    $percentage
                );
            }
        }
        
        if (!empty($this->stats['age_distribution'])) {
            echo "\nAge Distribution:\n";
            uksort($this->stats['age_distribution'], function($a, $b) {
                return (self::AGE_CATEGORIES[$a] ?? 999) <=> (self::AGE_CATEGORIES[$b] ?? 999);
            });
            foreach ($this->stats['age_distribution'] as $category => $count) {
                $percentage = ($count / max($this->stats['total_files'], 1)) * 100;
                echo sprintf("  %-12s %12s (%6.1f%%)\n", 
                    $category, 
                    $this->getHumanReadable($count, false),
                    $percentage
                );
            }
        }
        
        if ($this->interrupted) {
            echo "\n" . str_repeat('!', 50) . "\n";
            echo "  Scan interrupted - partial results\n";
            echo str_repeat('!', 50) . "\n";
        }
    }
    
    private function exportJson(string $outputFile): void
    {
        $totalInodes = $this->stats['total_files'] + $this->stats['total_dirs'] + 
                      $this->stats['total_symlinks'] + $this->stats['total_sockets'] +
                      $this->stats['total_fifos'] + $this->stats['total_devices'];
        
        $exportStats = $this->stats;
        $exportStats['total_inodes'] = $totalInodes;
        $exportStats['total_size_human'] = $this->getHumanReadable($this->totalSize);
        $exportStats['total_size'] = $this->totalSize;
        $exportStats['scan_time'] = date('Y-m-d H:i:s');
        $exportStats['interrupted'] = $this->interrupted;
        
        $json = json_encode($exportStats, JSON_PRETTY_PRINT | JSON_UNESCAPED_SLASHES);
        if (file_put_contents($outputFile, $json) !== false) {
            echo "\nJSON: {$outputFile}\n";
        }
    }
    
    private function saveCheckpoint(string $checkpointFile): void
    {
        $checkpoint = [
            'stats' => $this->stats,
            'total_size' => $this->totalSize,
            'processed_paths' => array_slice($this->processedPaths, 0, 10000),
            'timestamp' => date('Y-m-d H:i:s'),
            'interrupted' => $this->interrupted
        ];
        
        $data = serialize($checkpoint);
        if (file_put_contents($checkpointFile, $data) !== false) {
            echo "\nCheckpoint: {$checkpointFile}\n";
        }
    }
    
    private function loadCheckpoint(string $checkpointFile): void
    {
        if (!file_exists($checkpointFile)) {
            echo "Checkpoint file not found: {$checkpointFile}\n";
            return;
        }
        
        $data = file_get_contents($checkpointFile);
        if ($data === false) {
            echo "Failed to read checkpoint: {$checkpointFile}\n";
            return;
        }
        
        $checkpoint = unserialize($data);
        if ($checkpoint === false) {
            echo "Failed to unserialize checkpoint: {$checkpointFile}\n";
            return;
        }
        
        $this->stats = $checkpoint['stats'];
        $this->totalSize = $checkpoint['total_size'];
        $this->processedPaths = $checkpoint['processed_paths'];
        $this->interrupted = $checkpoint['interrupted'];
        
        echo "\nLoaded: {$checkpointFile}\n";
        echo "  Date: {$checkpoint['timestamp']}\n";
    }
    
    private function generateVisualization(string $outputFile): void
    {
        echo "\nVisualization generation requires GD or ImageMagick\n";
        echo "Plot: {$outputFile}\n";
    }
}

function main(): void
{
    $shortOpts = '';
    $longOpts = [
        'path:',
        'samples:',
        'deep',
        'duplicates',
        'threads:',
        'json:',
        'plot:',
        'age:',
        'symlinks',
        'exclude:',
        'max-depth:',
        'save-state:',
        'load-state:',
        'quiet',
        'version'
    ];
    
    $options = getopt($shortOpts, $longOpts);
    
    if (isset($options['version'])) {
        echo "Inode Analyzer 2.0\n";
        exit(0);
    }
    
    global $argc, $argv;
    
    $path = '.';
    if (isset($options['path'])) {
        $path = $options['path'];
    } elseif ($argc > 1 && $argv[$argc - 1][0] !== '-') {
        $path = $argv[$argc - 1];
    }
    
    $samples = (int)($options['samples'] ?? 20);
    $deepScan = isset($options['deep']);
    $findDuplicates = isset($options['duplicates']) || $deepScan;
    $threads = (int)($options['threads'] ?? 4);
    $followSymlinks = isset($options['symlinks']);
    $excludePatterns = $options['exclude'] ?? [];
    if (!is_array($excludePatterns)) {
        $excludePatterns = [$excludePatterns];
    }
    $maxDepth = isset($options['max-depth']) ? (int)$options['max-depth'] : null;
    $ageDays = isset($options['age']) ? (int)$options['age'] : null;
    $quiet = isset($options['quiet']);
    
    if (!function_exists('posix_getpwuid') && !$quiet) {
        echo "Note: Install posix extension for better owner/group resolution\n";
    }
    
    $analyzer = new InodeAnalyzer($threads, $followSymlinks, $excludePatterns);
    
    $analyzer->analyzeDirectory(
        $path,
        $samples,
        $deepScan,
        $findDuplicates,
        $options['json'] ?? null,
        $options['plot'] ?? null,
        $ageDays,
        $options['save-state'] ?? null,
        $options['load-state'] ?? null,
        $maxDepth
    );
}

if (PHP_SAPI === 'cli') {
    main();
}
