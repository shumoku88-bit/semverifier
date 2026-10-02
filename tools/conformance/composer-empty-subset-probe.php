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

$numericStart = count($numericIntervals['numeric']) > 0
    ? (string) $numericIntervals['numeric'][0]->getStart()
    : 'none';
$numericEnd = count($numericIntervals['numeric']) > 0
    ? (string) $numericIntervals['numeric'][0]->getEnd()
    : 'none';

printf(
    "numeric-empty class=%s string=%s numeric=%d start=%s end=%s branches=%d exclude=%s self-intersects=%s self-subset=%s subset-exact-zero=%s\n",
    get_class($numericEmpty),
    (string) $numericEmpty,
    count($numericIntervals['numeric']),
    $numericStart,
    $numericEnd,
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


$checkpointOK =
    get_class($numericEmpty) === 'Composer\\Semver\\Constraint\\Constraint' &&
    (string) $numericEmpty === '< 0.0.0.0-dev' &&
    count($numericIntervals['numeric']) === 1 &&
    $numericStart === '>= 0.0.0.0-dev' &&
    $numericEnd === '< 0.0.0.0-dev' &&
    Intervals::haveIntersections($numericEmpty, $numericEmpty) === false &&
    Intervals::isSubsetOf($numericEmpty, $numericEmpty) === false &&
    Intervals::isSubsetOf($numericEmpty, $exactZero) === false &&
    count($devIntervals['numeric']) === 0 &&
    Intervals::haveIntersections($devEmpty, $devEmpty) === false &&
    Intervals::isSubsetOf($devEmpty, $devEmpty) === true &&
    Intervals::isSubsetOf($devEmpty, $exactZero) === true;

if (!$checkpointOK) {
    fwrite(STDERR, "Composer empty-subset probe drifted\n");
    exit(1);
}

echo "Composer empty-subset probe matches the pinned observation\n";
