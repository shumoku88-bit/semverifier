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

## First milestone

The first milestone models:

- major, minor, and patch identifiers;
- validated pre-release identifiers;
- complete SemVer 2.0.0 version parsing;
- SemVer precedence;
- examples from the SemVer precedence rules.

Primitive comparator parsing and satisfaction (`< <= > >= =`) are now part of the kernel. Whitespace-separated comparator sets, conjunction, and default pre-release admission are also modeled. Primitive comparator bounds must still be complete SemVer versions.

Range union (`||`) is now modeled as a union of comparator-set intersections.

Advanced syntax such as `^1.2.3`, `~1.2`, wildcards, partial versions, and
hyphen ranges remains intentionally out of scope until the core range algebra
is small and clear.

## Design rule

Keep the semantic kernel smaller than the problem surrounding it.

If a property can be expressed once in the model and derived downstream, do
not duplicate it as defensive convention.
