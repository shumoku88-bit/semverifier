# semverifier

A small Lean 4 project for giving semantic-version precedence and range
questions an explicit, machine-checked meaning.

The project begins deliberately below version ranges. Its first boundary is
SemVer version precedence: given two versions, which one has higher precedence?

## Direction

```text
Version
  -> precedence
  -> Comparator satisfaction
  -> Range (union of comparator sets)
  -> contains
  -> intersects / subset / equivalence
  -> conformance checks against existing implementations
```

The aim is not to invent another package manager or to replace mature SemVer
libraries. The long-term experiment is to build a small verified semantic
oracle that existing implementations can be checked against.

## Range syntax milestone

The first range-syntax semantics milestone is complete.

Canonical strict forms for primitive comparators, conjunction, `||`, partial
and X-ranges, operator-prefixed partials, tilde, `~>`, caret, and strict
hyphen ranges now all lower into the same `Comparator` / `ComparatorSet`
kernel.

At the milestone checkpoint, the deterministic differential corpus contains
202 range expressions × 384 candidate versions = **77,568 judgments**, all
agreeing with node-semver 7.8.5.

This is a semantic milestone, not a claim of drop-in parser compatibility.
Whitespace conveniences, leading-`v` compatibility, `loose`,
`includePrerelease`, and richer range algebra remain separate work.

See [docs/RANGE_SYNTAX_MILESTONE.md](docs/RANGE_SYNTAX_MILESTONE.md) for the
checkpoint boundary.

## First milestone

The first milestone models:

- major, minor, and patch identifiers;
- validated pre-release identifiers;
- complete SemVer 2.0.0 version parsing;
- SemVer precedence;
- examples from the SemVer precedence rules.

Primitive comparator parsing and satisfaction (`< <= > >= =`) are now part of the kernel. Whitespace-separated comparator sets, conjunction, and default pre-release admission are also modeled. Primitive comparator bounds must still be complete SemVer versions.

Range union (`||`) is now modeled as a union of comparator-set intersections.

Full-version caret and tilde syntax are now desugared into the existing
comparator-set kernel. For example:

- `^1.2.3` becomes `>=1.2.3 <2.0.0-0`;
- `~1.2.3` becomes `>=1.2.3 <1.3.0-0`.

Bare partial versions and X-ranges are now desugared into the existing
comparator-set kernel. For example:

- `1` and `1.x` become `>=1.0.0 <2.0.0-0`;
- `1.2` and `1.2.x` become `>=1.2.0 <1.3.0-0`;
- `*` becomes the unconstrained comparator set, which still excludes
  prereleases by default.

Operator-prefixed partial versions and X-ranges use the same frontend and
desugar to primitive comparator boundaries. For example:

- `>1` becomes `>=2.0.0`;
- `>1.2` becomes `>=1.3.0`;
- `>=1.2` becomes `>=1.2.0`;
- `<2.x` becomes `<2.0.0-0`;
- `<=1.2.x` becomes `<1.3.0-0`.

Partial tilde ranges reuse the canonical bare X-range boundaries. For example:

- `~1` and `~1.x` become `>=1.0.0 <2.0.0-0`;
- `~1.2` and `~1.2.x` become `>=1.2.0 <1.3.0-0`;
- `~*` becomes the unconstrained comparator set.

Partial caret ranges preserve the shape of the incomplete tuple before
desugaring. This matters around zero-valued components. For example:

- `^1.2` becomes `>=1.2.0 <2.0.0-0`;
- `^0.2` becomes `>=0.2.0 <0.3.0-0`;
- `^0.0` becomes `>=0.0.0 <0.1.0-0`;
- `^0` becomes `>=0.0.0 <1.0.0-0`;
- `^*` becomes the unconstrained comparator set.

Strict whole-branch hyphen ranges are also desugared into comparator sets. For
example:

- `1.2.3 - 2.3.4` becomes `>=1.2.3 <=2.3.4`;
- `1.2 - 3.4.5` becomes `>=1.2.0 <=3.4.5`;
- `1.2.3 - 3.4` becomes `>=1.2.3 <3.5.0-0`;
- `1 - 2` becomes `>=1.0.0 <3.0.0-0`.

The npm-style `~>` spelling is accepted as an exact alias for `~`, using the
same desugaring path rather than introducing separate semantics.

## Design rule

Keep the semantic kernel smaller than the problem surrounding it.

If a property can be expressed once in the model and derived downstream, do
not duplicate it as defensive convention.

## Differential conformance

The supported subset is checked differentially against node-semver 7.8.5 in CI.
The deterministic corpus currently includes primitive comparators, conjunction,
union, prerelease admission, full-version caret/tilde syntax, bare
partial/X-ranges, operator-prefixed partial/X-ranges, partial tilde ranges,
the `~>` tilde alias, partial caret ranges, and strict hyphen ranges.

A Lean executable generates a deterministic matrix of supported ranges and
versions, evaluates every pair with Semverifier, and a small Node adapter checks
the same judgments with `semver.satisfies`. Any disagreement fails CI.

This harness is intentionally outside the semantic kernel: node-semver is a
reference implementation under test, not a dependency of Semverifier itself.
