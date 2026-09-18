import Semverifier

namespace Semverifier.Conformance

private def coreVersions : List String :=
  (List.range 4).flatMap fun major =>
    (List.range 4).flatMap fun minor =>
      (List.range 4).map fun patch =>
        s!"{major}.{minor}.{patch}"

def versions : List String :=
  coreVersions.flatMap fun core =>
    [
      core,
      s!"{core}-alpha",
      s!"{core}-alpha.1",
      s!"{core}-beta.2",
      s!"{core}-rc.0",
      s!"{core}+build.7"
    ]

private def primitiveBounds : List String :=
  [
    "0.0.0",
    "0.0.1",
    "0.1.0",
    "0.2.3",
    "1.0.0",
    "1.2.3",
    "1.2.3-alpha.2",
    "1.9.9",
    "2.0.0",
    "2.5.1",
    "3.0.0"
  ]

private def primitiveRanges : List String :=
  primitiveBounds.flatMap fun bound =>
    [
      bound,
      s!"={bound}",
      s!">{bound}",
      s!">={bound}",
      s!"<{bound}",
      s!"<={bound}"
    ]

private def conjunctionRanges : List String :=
  [
    "",
    ">=0.0.0 <1.0.0",
    ">=0.2.3 <0.3.0",
    ">=1.0.0 <2.0.0",
    ">=1.2.3 <1.3.0",
    ">1.2.3-alpha.2 <2.0.0",
    ">=2.0.0 <3.0.0",
    ">=1.2.3 <=2.5.1"
  ]

private def unionRanges : List String :=
  [
    "1.2.3 || >=2.0.0 <3.0.0",
    "<1.0.0 || >=2.0.0",
    ">1.2.3-alpha.2 || >=3.0.0",
    ">=0.2.3 <0.3.0 || >=1.2.3 <2.0.0",
    ">=1.2.3 || "
  ]

private def caretRanges : List String :=
  [
    "^0.0.0",
    "^0.0.1",
    "^0.0.3",
    "^0.2.3",
    "^1.0.0",
    "^1.2.3",
    "^1.2.3-beta.2",
    "^2.5.1"
  ]

private def partialCaretRanges : List String :=
  [
    "^*",
    "^x",
    "^X",
    "^0",
    "^1",
    "^2",
    "^0.x",
    "^1.x",
    "^1.X",
    "^1.*",
    "^0.0",
    "^0.2",
    "^1.2",
    "^0.0.x",
    "^1.2.x",
    "^2.x.x"
  ]

private def tildeRanges : List String :=
  [
    "~0.0.0",
    "~0.0.1",
    "~0.2.3",
    "~1.0.0",
    "~1.2.3",
    "~1.2.3-beta.2",
    "~2.5.1"
  ]

private def partialTildeRanges : List String :=
  [
    "~*",
    "~x",
    "~X",
    "~0",
    "~1",
    "~2",
    "~0.x",
    "~1.x",
    "~1.X",
    "~1.*",
    "~0.2",
    "~1.2",
    "~1.2.x",
    "~1.2.X",
    "~1.2.*",
    "~2.x.x"
  ]

private def xRanges : List String :=
  [
    "*",
    "x",
    "X",
    "0",
    "1",
    "2",
    "0.x",
    "1.x",
    "1.X",
    "1.*",
    "0.2",
    "1.2",
    "1.2.x",
    "1.2.X",
    "1.2.*",
    "2.x.x"
  ]

private def operatorXRanges : List String :=
  [
    ">0",
    ">1",
    ">1.2",
    ">1.x",
    ">1.2.x",
    ">=0",
    ">=1",
    ">=1.2",
    ">=1.x",
    ">=1.2.x",
    "<1",
    "<1.2",
    "<2.x",
    "<1.2.x",
    "<=0",
    "<=1",
    "<=1.2",
    "<=1.x",
    "<=1.2.x",
    "=1",
    "=1.2.x"
  ]

def ranges : List String :=
  primitiveRanges ++
    conjunctionRanges ++
    unionRanges ++
    caretRanges ++
    partialCaretRanges ++
    tildeRanges ++
    partialTildeRanges ++
    xRanges ++
    operatorXRanges

end Semverifier.Conformance
