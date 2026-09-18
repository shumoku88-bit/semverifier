import Init.Data.String.Search
import Semverifier.Version

namespace Semverifier

namespace VersionParser

private structure Core where
  major : Nat
  minor : Nat
  patch : Nat

private def parseCore? (raw : String) : Option Core :=
  match raw.split "." |>.toStringList with
  | [majorRaw, minorRaw, patchRaw] => do
      let major ← parseNumericIdentifier? majorRaw
      let minor ← parseNumericIdentifier? minorRaw
      let patch ← parseNumericIdentifier? patchRaw
      some { major, minor, patch }
  | _ => none

private def parsePrerelease? (raw : String) : Option (List PrereleaseIdentifier) :=
  raw.split "." |>.toStringList |>.mapM PrereleaseIdentifier.parse?

private def isValidBuildIdentifier (raw : String) : Bool :=
  let chars := raw.toList
  !chars.isEmpty && chars.all isAllowedIdentifierChar

private def parseBuild? (raw : String) : Option (List String) :=
  raw.split "." |>.toStringList |>.mapM fun identifier =>
    if isValidBuildIdentifier identifier then
      some identifier
    else
      none

private def splitBuild? (raw : String) : Option (String × List String) :=
  match raw.split "+" |>.toStringList with
  | [versionRaw] => some (versionRaw, [])
  | [versionRaw, buildRaw] => do
      let build ← parseBuild? buildRaw
      some (versionRaw, build)
  | _ => none

private def splitPrerelease (raw : String) : String × Option String :=
  match raw.split "-" |>.toStringList with
  | [] => (raw, none)
  | coreRaw :: rest =>
      if rest.isEmpty then
        (coreRaw, none)
      else
        (coreRaw, some (String.intercalate "-" rest))

end VersionParser

namespace Version

/--
Parse one complete SemVer 2.0.0 version.

This parser admits exactly one normal-version core, an optional pre-release
suffix, and optional build metadata. Range syntax is deliberately outside this
boundary.
-/
def parse? (raw : String) : Option Version := do
  let (versionRaw, build) ← VersionParser.splitBuild? raw
  let (coreRaw, prereleaseRaw?) := VersionParser.splitPrerelease versionRaw
  let core ← VersionParser.parseCore? coreRaw
  let prerelease ←
    match prereleaseRaw? with
    | none => some []
    | some prereleaseRaw => VersionParser.parsePrerelease? prereleaseRaw
  some {
    major := core.major
    minor := core.minor
    patch := core.patch
    prerelease
    build
  }

end Version
end Semverifier
