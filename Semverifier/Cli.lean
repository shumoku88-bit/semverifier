import Semverifier.RangeIntersection

open Semverifier

namespace Semverifier.Cli

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

private def usage : String :=
  "usage: semverifier intersect <left-range> <right-range>"

private def runIntersect (leftRaw rightRaw : String) : IO UInt32 :=
  match Range.parse? leftRaw with
  | none => do
      IO.eprintln s!"parse-error\tleft\t{leftRaw}"
      pure 2
  | some left =>
      match Range.parse? rightRaw with
      | none => do
          IO.eprintln s!"parse-error\tright\t{rightRaw}"
          pure 2
      | some right =>
          match Range.findIntersectionWitness? left right with
          | some witness => do
              IO.println s!"witness\t{renderVersion witness}"
              pure 0
          | none => do
              IO.println "disjoint"
              pure 0

def run (args : List String) : IO UInt32 :=
  match args with
  | ["intersect", leftRaw, rightRaw] =>
      runIntersect leftRaw rightRaw
  | _ => do
      IO.eprintln usage
      pure 64

end Semverifier.Cli

def main (args : List String) : IO UInt32 :=
  Semverifier.Cli.run args
