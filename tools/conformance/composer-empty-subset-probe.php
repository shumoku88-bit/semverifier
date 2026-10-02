<?php

declare(strict_types=1);

use Composer\Semver\Intervals;
use Composer\Semver\VersionParser;

if ($argc !== 2) {
    fwrite(STDERR, "usage: php composer-empty-subset-probe.php <composer-semver-dir>\n");
    exit(2);
}

$composerDir = $argv[1];
$srcDir = rtrim($composerDir, DIRECTORY_SEPARATOR) . DIRECTORY_SEPARATOR . 'src';

spl_autoload_register(static function (string $class) use ($srcDir): void {
    $prefix = 'Composer\\Semver\\';
    if (!str_starts_with($class, $prefix)) {
        return;
    }

    $relative = substr($class, strlen($prefix));
    $path = $srcDir . DIRECTORY_SEPARATOR . str_replace('\\', DIRECTORY_SEPARATOR, $relative) . '.php';
    if (is_file($path)) {
        require $path;
    }
});

$parser = new VersionParser();

$numericEmpty = $parser->parseConstraints('<0.0.0');
$devEmpty = $parser->parseConstraints('< dev-foo');
$exactZero = $parser->parseConstraints('0.0.0');

$numericIntervals = Intervals::get($numericEmpty);
$devIntervals = Intervals::get($devEmpty);

printf(
    "numeric-empty class=%s string=%s numeric=%d branches=%d exclude=%s self-intersects=%s self-subset=%s subset-exact-zero=%s\n",
    get_class($numericEmpty),
    (string) $numericEmpty,
    count($numericIntervals['numeric']),
    count($numericIntervals['branches']['names']),
    $numericIntervals['branches']['exclude'] ? 'true' : 'false',
    Intervals::haveIntersections($numericEmpty, $numericEmpty) ? 'true' : 'false',
    Intervals::isSubsetOf($numericEmpty, $numericEmpty) ? 'true' : 'false',
    Intervals::isSubsetOf($numericEmpty, $exactZero) ? 'true' : 'false'
);

printf(
    "dev-empty class=%s string=%s numeric=%d branches=%d exclude=%s self-intersects=%s self-subset=%s subset-exact-zero=%s\n",
    get_class($devEmpty),
    (string) $devEmpty,
    count($devIntervals['numeric']),
    count($devIntervals['branches']['names']),
    $devIntervals['branches']['exclude'] ? 'true' : 'false',
    Intervals::haveIntersections($devEmpty, $devEmpty) ? 'true' : 'false',
    Intervals::isSubsetOf($devEmpty, $devEmpty) ? 'true' : 'false',
    Intervals::isSubsetOf($devEmpty, $exactZero) ? 'true' : 'false'
);
