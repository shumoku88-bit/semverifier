# Masterminds caret-wildcard patch audit

Date: 2026-10-02

## Purpose

Follow up the focused Masterminds/semver caret-wildcard discrepancy reported in
issue #317 without broadening the Semverifier semantic kernel.

The baseline remains Masterminds/semver master at:

- `dd2b995c61c39ddd668b23ac919b04d607be35ab`

Two open repair candidates are compared:

- PR #316 at `8fd2b4b3978ebb17cd8d2015186270cffed1c473`
- PR #319 at `43e5010ceb23aa60e025a32302d54d36949b9cbb`

Both target the same documented `^* --> (any)` behavior, but they place the
wildcard-major fast path at different points inside `constraintCaret`.

## Minimal semantic probe

The probe uses `^*` with three observations:

1. stable `0.0.1`;
2. prerelease `0.0.0-alpha` with the default prerelease policy;
3. the same prerelease after setting `IncludePrerelease = true`.

The expected fingerprints are:

| target | stable | default prerelease | included prerelease |
| --- | --- | --- | --- |
| baseline | false | false | false |
| PR #316 | true | false | false |
| PR #319 | true | false | true |

The stable cell is the original bug from issue #317.

The final cell distinguishes the two patches.

## Why PR #316 still has a boundary hole

PR #316 inserts the wildcard-major return after the existing lower-bound check:

```go
if v.LessThan(c.con) {
    return false, ...
}

if c.dirty && !c.minorDirty && !c.patchDirty {
    return true, nil
}
```

For `^*`, the parsed comparison version is `0.0.0`. Therefore
`0.0.0-alpha` is rejected as lower than `0.0.0` before the wildcard-major
branch is reached, even when `IncludePrerelease` is true.

This is narrower than the PR description's stated opt-in prerelease behavior.

## Why PR #319 reaches the intended boundary

PR #319 places the wildcard-major return after the prerelease admission guard
but before the lower-bound check.

That preserves the default exclusion of prereleases while allowing
`IncludePrerelease = true` to admit `0.0.0-alpha`, which is consistent with
both:

- the source comment that `^*` means `(any)`; and
- the public `IncludePrerelease` option, whose documented purpose is to include
  prereleases in results.

Exact `^0.0.0` remains non-dirty and therefore does not take the wildcard
branch.

## Scope and evidence boundary

This checkpoint is deliberately small.

It does not claim that PR #319 is universally correct for every
Masterminds/semver constraint form. It establishes only that:

- both patches repair the original stable `^*` counterexample;
- PR #316 leaves a concrete option-sensitive boundary case;
- PR #319 handles that boundary case under the library's existing option
  contract.

The existing 77,568-row differential checkpoint remains pinned to the
unmodified upstream baseline. No Semverifier theorem or parser semantics are
changed here.

## Upstream state

As of 2026-10-02:

- issue #317 remains open;
- PR #316 remains open and predates #317;
- PR #319 remains open and explicitly references/fixes #317.

No new upstream comment is made by this checkpoint. The CI evidence should be
reviewed before deciding whether a concise comment on either PR would be useful.
