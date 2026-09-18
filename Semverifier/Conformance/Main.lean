import Semverifier.Conformance.Corpus

open Semverifier

namespace Semverifier.Conformance

private def emitCase (rangeRaw versionRaw : String) : IO Unit := do
  match Range.parse? rangeRaw, Version.parse? versionRaw with
  | some range, some version =>
      IO.println s!"{rangeRaw}\t{versionRaw}\t{range.satisfies version}"
  | _, _ =>
      throw <| IO.userError s!"invalid generated conformance case: {rangeRaw} / {versionRaw}"

def run : IO Unit := do
  for rangeRaw in ranges do
    for versionRaw in versions do
      emitCase rangeRaw versionRaw

end Semverifier.Conformance

def main : IO Unit :=
  Semverifier.Conformance.run
