import Semverifier.Conformance.Corpus
import Semverifier.RangeSubset

open Semverifier

namespace Semverifier.Conformance

private def parseRange (raw : String) : IO Range :=
  match Range.parse? raw with
  | some range => pure range
  | none => throw <| IO.userError s!"invalid generated range: {raw}"

private def parseVersion (raw : String) : IO Version :=
  match Version.parse? raw with
  | some version => pure version
  | none => throw <| IO.userError s!"invalid generated version: {raw}"

private def boundedCounterexample?
    (sub dom : Range)
    (parsedVersions : List Version) : Bool :=
  parsedVersions.any fun candidate =>
    Range.subsetCounterexampleAt sub dom candidate

def runSubsetCoverage : IO Unit := do
  let parsedRanges ← ranges.mapM fun raw => do
    pure (raw, ← parseRange raw)
  let parsedVersions ← versions.mapM parseVersion

  let mut pairs := 0
  let mut boundedFailures := 0
  let mut searchWitnesses := 0
  let mut boundedMisses := 0
  let mut soundnessFailures := 0
  let mut witnessOutsideBoundedCorpus := 0

  for subEntry in parsedRanges do
    let (subRaw, sub) := subEntry
    for domEntry in parsedRanges do
      let (domRaw, dom) := domEntry
      pairs := pairs + 1

      let boundedFailure :=
        boundedCounterexample? sub dom parsedVersions
      if boundedFailure then
        boundedFailures := boundedFailures + 1

      match Range.findSubsetCounterexample? sub dom with
      | none =>
          if boundedFailure then
            boundedMisses := boundedMisses + 1
            IO.println
              s!"bounded-miss\t{subRaw}\t{domRaw}"
      | some witness =>
          searchWitnesses := searchWitnesses + 1
          if !Range.subsetCounterexampleAt sub dom witness then
            soundnessFailures := soundnessFailures + 1
            IO.println
              s!"soundness-failure\t{subRaw}\t{domRaw}"
          if !boundedFailure then
            witnessOutsideBoundedCorpus :=
              witnessOutsideBoundedCorpus + 1

  IO.println s!"range pairs: {pairs}"
  IO.println s!"bounded corpus non-subset pairs: {boundedFailures}"
  IO.println s!"boundary search witnesses: {searchWitnesses}"
  IO.println s!"bounded counterexamples missed by boundary search: {boundedMisses}"
  IO.println s!"soundness failures: {soundnessFailures}"
  IO.println
    s!"boundary witnesses not seen in 384-version corpus: {witnessOutsideBoundedCorpus}"

  if pairs != 40804 ||
      boundedFailures != 29114 ||
      searchWitnesses != 30692 ||
      boundedMisses != 0 ||
      soundnessFailures != 0 ||
      witnessOutsideBoundedCorpus != 1578 then
    throw <| IO.userError
      "subset boundary candidate coverage checkpoint drifted"

end Semverifier.Conformance

def main : IO Unit :=
  Semverifier.Conformance.runSubsetCoverage
