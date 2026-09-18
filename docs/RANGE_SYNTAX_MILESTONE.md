# Range Syntax Milestone

Status: closed on 2026-09-18.

This checkpoint marks completion of Semverifier's first range-syntax semantics
milestone. It does not claim drop-in parser compatibility with node-semver, and
it does not mark the whole project complete.

## What is covered

Canonical strict range syntax now lowers into the same small semantic kernel:

- primitive comparators: `< <= > >= =`
- whitespace conjunction
- range union with `||`
- empty / wildcard ranges
- partial versions and X-ranges
- operator-prefixed partial / X-ranges
- tilde ranges, including partial forms
- the `~>` spelling as an exact alias for `~`
- caret ranges, including partial forms
- strict whole-branch hyphen ranges
- default node-semver-style prerelease admission

Advanced forms do not add their own satisfaction relation. They desugar to
primitive `Comparator` / `ComparatorSet` values and reuse the existing range
union semantics.

## Differential checkpoint

The deterministic conformance corpus contains 202 range expressions and 384
candidate versions, for 77,568 range/version judgments.

At this checkpoint all 77,568 judgments agree with node-semver 7.8.5.

node-semver remains a CI reference implementation, not a dependency of the
semantic kernel.

## Why this is a useful boundary

The core range grammar is now represented semantically without needing a new
runtime interpretation for every surface syntax form.

The main chain is:

```text
surface range syntax
        |
        v
desugaring frontends
        |
        v
Comparator / ComparatorSet
        |
        v
Range union
        |
        v
satisfaction
```

This gives later work a stable boundary: new parser conveniences should not
change range meaning, and new algebraic questions can operate on normalized
semantic values rather than syntax.

## Deliberately separate work

The following are not part of this milestone and should not be confused with
missing range semantics:

- parser conveniences such as whitespace between an operator and operand
  (`> 1.2.3`, `~ 1.2`, `^ 1.2`)
- compatibility spellings such as leading `v`
- node-semver `loose` mode
- the `includePrerelease` option
- utility APIs such as minimum/maximum satisfying versions, outside/gtr/ltr,
  simplification, and similar package-level behavior
- richer range algebra such as executable intersection, subset, and equivalence

Those can be studied independently without reopening the syntax semantics
milestone.
