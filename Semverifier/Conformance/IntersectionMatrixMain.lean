import Semverifier.Conformance.Corpus
import Semverifier.RangeIntersection

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

def runIntersectionMatrix : IO Unit := do
  let parsed ← ranges.mapM parseCorpusRange

  for leftEntry in parsed do
    let (leftRaw, left) := leftEntry
    for rightEntry in parsed do
      let (rightRaw, right) := rightEntry
      match Range.findIntersectionWitness? left right with
      | some witness =>
          IO.println s!"{leftRaw}\t{rightRaw}\twitness={renderVersion witness}"
      | none =>
          IO.println s!"{leftRaw}\t{rightRaw}\tdisjoint"

end Semverifier.Conformance

def main : IO Unit :=
  Semverifier.Conformance.runIntersectionMatrix
