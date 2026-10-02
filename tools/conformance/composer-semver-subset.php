<?php

declare(strict_types=1);

use Composer\Semver\Constraint\Constraint;
use Composer\Semver\Intervals;
use Composer\Semver\VersionParser;

if ($argc !== 4) {
    fwrite(STDERR, "usage: php composer-semver-subset.php <conformance.tsv> <subset.tsv> <composer-semver-dir>\n");
    exit(2);
}

[$script, $conformancePath, $subsetPath, $composerDir] = $argv;
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
    public int $rows = 0;
    public int $mismatches = 0;

    public function __construct(string $range)
    {
        $this->range = $range;
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
/** @var array<string, string> $versionCache */
$versionCache = [];

$corpusRows = 0;
foreach (tsvRows($conformancePath) as [$rangeText, $versionText, $leanRaw]) {
    $corpusRows++;

    if (!isset($audits[$rangeText])) {
        $audits[$rangeText] = new RangeAudit($rangeText);
        try {
            $constraints[$rangeText] = $parser->parseConstraints($rangeText);
        } catch (Throwable $e) {
            $constraints[$rangeText] = null;
            $audits[$rangeText]->parseOK = false;
        }
    }

    $audit = $audits[$rangeText];
    $audit->rows++;

    if (!$audit->parseOK) {
        continue;
    }

    if (!isset($versionCache[$versionText])) {
        $versionCache[$versionText] = $parser->normalize($versionText);
    }

    $provided = new Constraint('==', $versionCache[$versionText]);
    $composerResult = $constraints[$rangeText]->matches($provided);

    if ($leanRaw !== 'true' && $leanRaw !== 'false') {
        fwrite(STDERR, "invalid Lean result: $leanRaw\n");
        exit(1);
    }

    $leanResult = $leanRaw === 'true';
    if ($composerResult !== $leanResult) {
        $audit->mismatches++;
    }
}

ksort($audits);

$fullCompatible = [];
foreach ($audits as $rangeText => $audit) {
    if ($audit->fullCompatible()) {
        $fullCompatible[$rangeText] = true;
    }
}

$fingerprint = static function (array $ranges): string {
    $names = array_keys($ranges);
    sort($names, SORT_STRING);
    return hash('sha256', implode("\n", $names));
};

echo "corpus rows: $corpusRows\n";
echo "range expressions: " . count($audits) . "\n";
echo "full-corpus-compatible ranges: " . count($fullCompatible) . "\n";
echo "full-compatible fingerprint: " . $fingerprint($fullCompatible) . "\n";

$matrixRows = 0;
$comparablePairs = 0;
$mismatches = 0;
$semverifierSubsetComposerNot = 0;
$semverifierNotComposerSubset = 0;
$witnessConfirmedComposerContradictions = 0;
$examples = [];

foreach (tsvRows($subsetPath) as [$subRaw, $domRaw, $leanRaw]) {
    $matrixRows++;

    if (!isset($fullCompatible[$subRaw], $fullCompatible[$domRaw])) {
        continue;
    }
    $comparablePairs++;

    if ($leanRaw === 'subset') {
        $semverifierSubset = true;
        $witness = null;
    } elseif (str_starts_with($leanRaw, 'counterexample=')) {
        $semverifierSubset = false;
        $witness = substr($leanRaw, strlen('counterexample='));
    } else {
        fwrite(STDERR, "invalid subset result: $leanRaw\n");
        exit(1);
    }

    /** @var object $subConstraint */
    $subConstraint = $constraints[$subRaw];
    /** @var object $domConstraint */
    $domConstraint = $constraints[$domRaw];

    $composerSubset = Intervals::isSubsetOf($subConstraint, $domConstraint);

    if ($composerSubset === $semverifierSubset) {
        continue;
    }

    $mismatches++;

    $witnessAcceptedByComposerSub = null;
    $witnessRejectedByComposerDom = null;
    $directComposerContradiction = null;

    if ($semverifierSubset && !$composerSubset) {
        $semverifierSubsetComposerNot++;
    } else {
        $semverifierNotComposerSubset++;

        try {
            $normalizedWitness = $parser->normalize($witness);
            $provided = new Constraint('==', $normalizedWitness);
            $witnessAcceptedByComposerSub =
                $subConstraint->matches($provided);
            $witnessRejectedByComposerDom =
                !$domConstraint->matches($provided);
            $directComposerContradiction =
                $witnessAcceptedByComposerSub &&
                $witnessRejectedByComposerDom;
        } catch (Throwable $e) {
            $directComposerContradiction = false;
        }

        if ($directComposerContradiction) {
            $witnessConfirmedComposerContradictions++;
        }
    }

    if (count($examples) < 60) {
        $examples[] = [
            'sub' => $subRaw,
            'dom' => $domRaw,
            'semverifierSubset' => $semverifierSubset,
            'composerSubset' => $composerSubset,
            'witness' => $witness,
            'witnessAcceptedByComposerSub' => $witnessAcceptedByComposerSub,
            'witnessRejectedByComposerDom' => $witnessRejectedByComposerDom,
            'directComposerContradiction' => $directComposerContradiction,
        ];
    }
}

echo "subset matrix rows: $matrixRows\n";
echo "directly comparable full-compatible pairs: $comparablePairs\n";
echo "subset mismatches: $mismatches\n";
echo "  Semverifier subset / Composer not-subset: $semverifierSubsetComposerNot\n";
echo "  Semverifier not-subset / Composer subset: $semverifierNotComposerSubset\n";
echo "  witness-confirmed Composer contradictions: $witnessConfirmedComposerContradictions\n";

foreach ($examples as $example) {
    echo "subset-mismatch\t" .
        json_encode($example, JSON_UNESCAPED_SLASHES) .
        "\n";
}
