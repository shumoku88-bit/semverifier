<?php

declare(strict_types=1);

use Composer\Semver\Constraint\Constraint;
use Composer\Semver\Intervals;
use Composer\Semver\VersionParser;

if ($argc !== 4) {
    fwrite(STDERR, "usage: php composer-semver-intersection.php <conformance.tsv> <intersection.tsv> <composer-semver-dir>\n");
    exit(2);
}

[$script, $conformancePath, $intersectionPath, $composerDir] = $argv;
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

final class RangeAudit
{
    public string $range;
    public bool $parseOK = true;
    public ?string $parseError = null;
    public int $rows = 0;
    public int $mismatches = 0;
    public int $stableRows = 0;
    public int $stableMismatches = 0;

    public function __construct(string $range)
    {
        $this->range = $range;
    }

    public function stableCompatible(): bool
    {
        return $this->parseOK && $this->stableRows > 0 && $this->stableMismatches === 0;
    }

    public function fullCompatible(): bool
    {
        return $this->parseOK && $this->rows > 0 && $this->mismatches === 0;
    }
}

/** @return iterable<int, array{0:string,1:string,2:string}> */
function tsvRows(string $path): iterable
{
    $fh = fopen($path, 'rb');
    if ($fh === false) {
        throw new RuntimeException("unable to open $path");
    }

    try {
        while (($line = fgets($fh)) !== false) {
            $line = rtrim($line, "\r\n");
            if ($line === '') {
                continue;
            }
            $parts = explode("\t", $line);
            if (count($parts) !== 3) {
                throw new RuntimeException("invalid TSV row: $line");
            }
            yield [$parts[0], $parts[1], $parts[2]];
        }
    } finally {
        fclose($fh);
    }
}

$parser = new VersionParser();

/** @var array<string, RangeAudit> $audits */
$audits = [];
/** @var array<string, object|null> $constraints */
$constraints = [];
/** @var array<string, string> $constraintErrors */
$constraintErrors = [];
/** @var array<string, string> $versionCache */
$versionCache = [];

$corpusRows = 0;
$stableCorpusRows = 0;
$semanticMismatches = 0;
$stableSemanticMismatches = 0;

foreach (tsvRows($conformancePath) as [$rangeText, $versionText, $leanRaw]) {
    $corpusRows++;
    $isStable = !str_contains($versionText, '-');
    if ($isStable) {
        $stableCorpusRows++;
    }

    if (!isset($audits[$rangeText])) {
        $audits[$rangeText] = new RangeAudit($rangeText);
        try {
            $constraints[$rangeText] = $parser->parseConstraints($rangeText);
        } catch (Throwable $e) {
            $constraints[$rangeText] = null;
            $constraintErrors[$rangeText] = $e->getMessage();
            $audits[$rangeText]->parseOK = false;
            $audits[$rangeText]->parseError = $e->getMessage();
        }
    }

    $audit = $audits[$rangeText];
    $audit->rows++;
    if ($isStable) {
        $audit->stableRows++;
    }

    if (!$audit->parseOK) {
        continue;
    }

    try {
        if (!isset($versionCache[$versionText])) {
            $versionCache[$versionText] = $parser->normalize($versionText);
        }
        $provided = new Constraint('==', $versionCache[$versionText]);
        $composerResult = $constraints[$rangeText]->matches($provided);
    } catch (Throwable $e) {
        fwrite(STDERR, sprintf("version evaluation failed: range=%s version=%s error=%s\n", $rangeText, $versionText, $e->getMessage()));
        exit(1);
    }

    $leanResult = $leanRaw === 'true';
    if ($leanRaw !== 'true' && $leanRaw !== 'false') {
        fwrite(STDERR, "invalid Lean result: $leanRaw\n");
        exit(1);
    }

    if ($composerResult !== $leanResult) {
        $audit->mismatches++;
        $semanticMismatches++;
        if ($isStable) {
            $audit->stableMismatches++;
            $stableSemanticMismatches++;
        }
    }
}

ksort($audits);

$stableCompatible = [];
$fullCompatible = [];
foreach ($audits as $rangeText => $audit) {
    if ($audit->stableCompatible()) {
        $stableCompatible[$rangeText] = true;
    }
    if ($audit->fullCompatible()) {
        $fullCompatible[$rangeText] = true;
    }
}

$parseIncompatible = array_filter($audits, static fn (RangeAudit $a): bool => !$a->parseOK);
$stableMismatchRanges = array_filter($audits, static fn (RangeAudit $a): bool => $a->parseOK && $a->stableMismatches > 0);
$fullMismatchRanges = array_filter($audits, static fn (RangeAudit $a): bool => $a->parseOK && $a->mismatches > 0);

echo "corpus rows: $corpusRows\n";
echo "stable corpus rows: $stableCorpusRows\n";
echo "range expressions: " . count($audits) . "\n";
echo "parse-incompatible ranges: " . count($parseIncompatible) . "\n";
echo "semantic mismatches: $semanticMismatches\n";
echo "stable semantic mismatches: $stableSemanticMismatches\n";
echo "ranges with any semantic mismatch: " . count($fullMismatchRanges) . "\n";
echo "ranges with stable semantic mismatch: " . count($stableMismatchRanges) . "\n";
echo "stable-compatible ranges: " . count($stableCompatible) . "\n";
echo "full-corpus-compatible ranges: " . count($fullCompatible) . "\n";

$fingerprint = static function (array $ranges): string {
    $names = array_keys($ranges);
    sort($names, SORT_STRING);
    return hash('sha256', implode("\n", $names));
};

echo "parse-incompatible fingerprint: " . $fingerprint($parseIncompatible) . "\n";
echo "stable-mismatch-range fingerprint: " . $fingerprint($stableMismatchRanges) . "\n";
echo "full-mismatch-range fingerprint: " . $fingerprint($fullMismatchRanges) . "\n";
echo "stable-compatible fingerprint: " . $fingerprint($stableCompatible) . "\n";
echo "full-compatible fingerprint: " . $fingerprint($fullCompatible) . "\n";

foreach ($parseIncompatible as $audit) {
    echo 'parse-incompatible' . "\t" . json_encode($audit->range) . "\t" . $audit->parseError . "\n";
}

$byMismatch = array_values($fullMismatchRanges);
usort($byMismatch, static function (RangeAudit $a, RangeAudit $b): int {
    if ($a->mismatches !== $b->mismatches) {
        return $b->mismatches <=> $a->mismatches;
    }
    return $a->range <=> $b->range;
});
foreach (array_slice($byMismatch, 0, 30) as $audit) {
    echo sprintf(
        "range-mismatches\tall=%d\tstable=%d\trange=%s\n",
        $audit->mismatches,
        $audit->stableMismatches,
        json_encode($audit->range)
    );
}

echo "full-compatible-range-list:";
foreach (array_keys($fullCompatible) as $rangeText) {
    echo "\t" . base64_encode($rangeText);
}
echo "\n";

$intersectionRows = 0;
$comparablePairs = 0;
$intersectionMismatches = 0;
$semverifierOnly = 0;
$composerOnly = 0;
$witnessConfirmedContradictions = 0;
$examples = [];

foreach (tsvRows($intersectionPath) as [$left, $right, $leanRaw]) {
    $intersectionRows++;

    if (!isset($fullCompatible[$left], $fullCompatible[$right])) {
        continue;
    }
    $comparablePairs++;

    $semverifierIntersects = str_starts_with($leanRaw, 'witness=');
    if (!$semverifierIntersects && $leanRaw !== 'disjoint') {
        fwrite(STDERR, "invalid intersection result: $leanRaw\n");
        exit(1);
    }

    /** @var object $leftConstraint */
    $leftConstraint = $constraints[$left];
    /** @var object $rightConstraint */
    $rightConstraint = $constraints[$right];
    $composerIntersects = Intervals::haveIntersections($leftConstraint, $rightConstraint);

    if ($composerIntersects === $semverifierIntersects) {
        continue;
    }

    $intersectionMismatches++;
    $witness = null;
    $witnessAcceptedByComposer = null;

    if ($semverifierIntersects) {
        $semverifierOnly++;
        $witness = substr($leanRaw, strlen('witness='));
        try {
            $normalizedWitness = $parser->normalize($witness);
            $provided = new Constraint('==', $normalizedWitness);
            $witnessAcceptedByComposer =
                $leftConstraint->matches($provided) &&
                $rightConstraint->matches($provided);
        } catch (Throwable $e) {
            $witnessAcceptedByComposer = false;
        }
        if ($witnessAcceptedByComposer) {
            $witnessConfirmedContradictions++;
        }
    } else {
        $composerOnly++;
    }

    if (count($examples) < 40) {
        $examples[] = [
            'left' => $left,
            'right' => $right,
            'semverifier' => $semverifierIntersects,
            'composer' => $composerIntersects,
            'witness' => $witness,
            'witnessAcceptedByComposer' => $witnessAcceptedByComposer,
        ];
    }
}

echo "intersection matrix rows: $intersectionRows\n";
echo "directly comparable full-compatible pairs: $comparablePairs\n";
echo "intersection mismatches: $intersectionMismatches\n";
echo "  Semverifier true / Composer false: $semverifierOnly\n";
echo "  Composer true / Semverifier false: $composerOnly\n";
echo "  witness-confirmed Composer contradictions: $witnessConfirmedContradictions\n";

foreach ($examples as $example) {
    echo "intersection-mismatch\t" . json_encode($example, JSON_UNESCAPED_SLASHES) . "\n";
}

$checkpointOK =
    $corpusRows === 77568 &&
    $stableCorpusRows === 25856 &&
    count($audits) === 202 &&
    count($parseIncompatible) === 60 &&
    $semanticMismatches === 10747 &&
    $stableSemanticMismatches === 280 &&
    count($fullMismatchRanges) === 115 &&
    count($stableMismatchRanges) === 14 &&
    count($stableCompatible) === 128 &&
    count($fullCompatible) === 27 &&
    $fingerprint($parseIncompatible) === 'eee036d58d91eeffb97b2cb741c6eb6a675159a091addd5c23e7c9d8f3604af5' &&
    $fingerprint($stableMismatchRanges) === '88a9e23896b8c4aeeb2efc4120a39ba9daec15303bf179d12c48e99f290318b8' &&
    $fingerprint($fullMismatchRanges) === '649d7d9461b9173541cf69b85f6fcca736ad7a1deb536a25ec5a25bf48567818' &&
    $fingerprint($stableCompatible) === '51d648689b29342443cd908d1031e5b012a26ab8440a4b9dae8723390342a3c4' &&
    $fingerprint($fullCompatible) === 'db380f28b225a2edd0dc9d877310cb914c3d4f45a051d4b7cc65e9a922d3f3df' &&
    $intersectionRows === 40804 &&
    $comparablePairs === 729 &&
    $intersectionMismatches === 0 &&
    $semverifierOnly === 0 &&
    $composerOnly === 0 &&
    $witnessConfirmedContradictions === 0;

if (!$checkpointOK) {
    fwrite(STDERR, "Composer semver audit checkpoint drifted; review the complete output before updating the baseline\n");
    exit(1);
}

echo "Composer semver intersection checkpoint matches the pinned audit\n";
