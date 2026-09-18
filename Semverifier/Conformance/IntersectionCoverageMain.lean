import Semverifier.Conformance.Corpus
import Semverifier.RangeIntersection

open Semverifier

namespace Semverifier.Conformance

private def parseCorpusRange (raw : String) : IO (String × Range) :=
  match Range.parse? raw with
  | some range => pure (raw, range)
  | none => throw <| IO.userError s!"invalid generated range: {raw}"

private def parseCorpusVersion (raw : String) : IO (String × Version) :=
  match Version.parse? raw with
  | some version => pure (raw, version)
  | none => throw <| IO.userError s!"invalid generated version: {raw}"

private def firstOverlapInUniverse?
    (left right : Range) :
    List (String × Version) → Option (String × Version)
  | [] => none
  | entry :: rest =>
      let (_, candidate) := entry
      if Range.overlapsAt left right candidate then
        some entry
      else
        firstOverlapInUniverse? left right rest

def runIntersectionCoverageAudit : IO Unit := do
  let parsedRanges ← ranges.mapM parseCorpusRange
  let parsedVersions ← versions.mapM parseCorpusVersion

  let mut totalPairs := 0
  let mut unresolvedPairs := 0
  let mut uncovered : List (String × String × String) := []

  for leftEntry in parsedRanges do
    let (leftRaw, left) := leftEntry
    for rightEntry in parsedRanges do
      let (rightRaw, right) := rightEntry
      totalPairs := totalPairs + 1

      match Range.findIntersectionWitness? left right with
      | some _ =>
          pure ()
      | none =>
          unresolvedPairs := unresolvedPairs + 1
          match firstOverlapInUniverse? left right parsedVersions with
          | none =>
              pure ()
          | some (candidateRaw, _) =>
              uncovered := (leftRaw, rightRaw, candidateRaw) :: uncovered

  IO.println s!"checked {totalPairs} ordered range pairs"
  IO.println s!"bounded-audited {unresolvedPairs} witness-search none results against {parsedVersions.length} corpus versions"

  if uncovered.isEmpty then
    IO.println "no bounded-universe intersection witness was missed by the boundary candidate search"
  else
    IO.eprintln s!"found {uncovered.length} bounded-universe witness-search false negatives"
    for entry in uncovered.reverse.take 50 do
      let (leftRaw, rightRaw, candidateRaw) := entry
      IO.eprintln s!"{leftRaw}\t{rightRaw}\t{candidateRaw}"
    throw <| IO.userError "intersection boundary candidate coverage audit failed"

end Semverifier.Conformance

def main : IO Unit :=
  Semverifier.Conformance.runIntersectionCoverageAudit
