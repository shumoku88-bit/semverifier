import Semverifier.Conformance.Corpus
import Semverifier.RangeIntersection

open Semverifier

namespace Semverifier.Conformance

private def renderPrereleaseIdentifier : PrereleaseIdentifier → String
  | .numeric value => toString value
  | .text value => value.value

private def renderPrerelease : List PrereleaseIdentifier → String
  | [] => ""
  | [identifier] => renderPrereleaseIdentifier identifier
  | identifier :: rest =>
      renderPrereleaseIdentifier identifier ++ "." ++ renderPrerelease rest

private def renderVersion (version : Version) : String :=
  let core := s!"{version.major}.{version.minor}.{version.patch}"
  if version.prerelease.isEmpty then
    core
  else
    core ++ "-" ++ renderPrerelease version.prerelease

private def parseCorpusRange (raw : String) : IO (String × Range) :=
  match Range.parse? raw with
  | some range => pure (raw, range)
  | none => throw <| IO.userError s!"invalid generated range: {raw}"

def runIntersectionProbe : IO Unit := do
  let parsed ← ranges.mapM parseCorpusRange
  for leftEntry in parsed do
    let (leftRaw, left) := leftEntry
    for rightEntry in parsed do
      let (rightRaw, right) := rightEntry
      match Range.findIntersectionWitness? left right with
      | some witness =>
          IO.println s!"{leftRaw}\t{rightRaw}\t{renderVersion witness}"
      | none =>
          pure ()

end Semverifier.Conformance

def main : IO Unit :=
  Semverifier.Conformance.runIntersectionProbe
