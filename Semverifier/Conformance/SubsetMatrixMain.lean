import Semverifier.Conformance.Corpus
import Semverifier.RangeSubset

open Semverifier

namespace Semverifier.Conformance

private def renderPrereleaseIdentifier : PrereleaseIdentifier → String
  | .numeric value => toString value
  | .text value => value.value

private def renderVersion (version : Version) : String :=
  let core := s!"{version.major}.{version.minor}.{version.patch}"
  let prerelease :=
    if version.prerelease.isEmpty then
      ""
    else
      "-" ++ String.intercalate "."
        (version.prerelease.map renderPrereleaseIdentifier)
  let build :=
    if version.build.isEmpty then
      ""
    else
      "+" ++ String.intercalate "." version.build
  core ++ prerelease ++ build

private def parseCorpusRange (raw : String) : IO (String × Range) :=
  match Range.parse? raw with
  | some range => pure (raw, range)
  | none => throw <| IO.userError s!"invalid generated range: {raw}"

def runSubsetMatrix : IO Unit := do
  let parsed ← ranges.mapM parseCorpusRange

  for subEntry in parsed do
    let (subRaw, sub) := subEntry
    for domEntry in parsed do
      let (domRaw, dom) := domEntry
      match Range.findSubsetCounterexample? sub dom with
      | some witness =>
          IO.println
            s!"{subRaw}\t{domRaw}\tcounterexample={renderVersion witness}"
      | none =>
          IO.println s!"{subRaw}\t{domRaw}\tsubset"

end Semverifier.Conformance

def main : IO Unit :=
  Semverifier.Conformance.runSubsetMatrix
