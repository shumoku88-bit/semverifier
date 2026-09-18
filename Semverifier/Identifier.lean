namespace Semverifier

/-- ASCII characters admitted by a SemVer identifier. -/
def isAllowedIdentifierChar (c : Char) : Bool :=
  c.isAlphanum || c == '-'

/--
A non-numeric pre-release identifier.

The constructor is private: callers can inspect the original text but cannot
construct values that bypass `ofString?`.
-/
structure NonNumericIdentifier where
  private mk ::
  value : String
deriving Repr, BEq, DecidableEq

namespace NonNumericIdentifier

/--
Check the SemVer lexical conditions for a non-numeric pre-release identifier:
non-empty, ASCII alphanumeric-or-hyphen only, and containing at least one
non-digit character.
-/
def isValid (value : String) : Bool :=
  let chars := value.toList
  !chars.isEmpty &&
    chars.all isAllowedIdentifierChar &&
    chars.any (fun c => !c.isDigit)

/-- Admit a non-numeric pre-release identifier only when its lexical form is valid. -/
def ofString? (value : String) : Option NonNumericIdentifier :=
  if isValid value then
    some ⟨value⟩
  else
    none

end NonNumericIdentifier

/--
One SemVer pre-release identifier.

Numeric identifiers are stored as naturals, so admitted numeric values have one
canonical meaning independent of their textual spelling. Non-numeric values can
only enter through the validated `NonNumericIdentifier` boundary.
-/
inductive PrereleaseIdentifier where
  | numeric (value : Nat)
  | text (value : NonNumericIdentifier)
deriving Repr, BEq, DecidableEq

private def digitsToNat (chars : List Char) : Nat :=
  chars.foldl
    (fun value c => value * 10 + (c.toNat - '0'.toNat))
    0

/--
Parse a SemVer numeric identifier.

This is shared by major/minor/patch parsing and numeric pre-release identifiers.
The empty string, non-digits, and leading zeroes are rejected.
-/
def parseNumericIdentifier? (raw : String) : Option Nat :=
  let chars := raw.toList
  match chars with
  | [] => none
  | first :: rest =>
      if chars.all Char.isDigit then
        if first == '0' && !rest.isEmpty then
          none
        else
          some (digitsToNat chars)
      else
        none

namespace PrereleaseIdentifier

/--
Parse exactly one SemVer pre-release identifier.

This rejects empty identifiers, non-ASCII identifier characters, and numeric
identifiers with leading zeroes. Dot splitting belongs to the full-version
parser.
-/
def parse? (raw : String) : Option PrereleaseIdentifier :=
  match parseNumericIdentifier? raw with
  | some value => some (.numeric value)
  | none =>
      match NonNumericIdentifier.ofString? raw with
      | some value => some (.text value)
      | none => none

/-- SemVer precedence for one admitted pre-release identifier. -/
def precedence : PrereleaseIdentifier → PrereleaseIdentifier → Ordering
  | .numeric left, .numeric right => compare left right
  | .numeric _, .text _ => .lt
  | .text _, .numeric _ => .gt
  | .text left, .text right => compare left.value right.value

end PrereleaseIdentifier
end Semverifier
