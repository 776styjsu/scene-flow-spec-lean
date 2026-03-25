/-
  SceneFlowSpec.Formula
  The formula AST for SceneFlow temporal properties.
-/
import SceneFlowSpec.Scene

namespace SceneFlowSpec

/-- An atomic predicate is a decidable Boolean test on a single scene snapshot,
    together with a human-readable label. -/
structure AtomicPred where
  label : String
  test  : Scene → Bool
  deriving Inhabited

instance : BEq AtomicPred where
  beq a b := a.label == b.label   -- identity by label

instance : Repr AtomicPred where
  reprPrec a _ := Std.Format.text s!"⟨{a.label}⟩"

/-- SceneFlow property formulas — a finite-trace LTL with bounded operators.

  Constructors mirror the temporal connectives found in SceneFlowLang:
    `X` (next), `U` (until), `R` (release), `F` (eventually),
    `G` (always), and the bounded `$[n][φ]` operator.
-/
inductive SFProp where
  | atom       : AtomicPred → SFProp
  | top        : SFProp
  | bot        : SFProp
  | neg        : SFProp → SFProp
  | conj       : SFProp → SFProp → SFProp
  | disj       : SFProp → SFProp → SFProp
  | impl       : SFProp → SFProp → SFProp
  | next       : SFProp → SFProp
  | until      : SFProp → SFProp → SFProp
  | release    : SFProp → SFProp → SFProp
  | eventually : SFProp → SFProp
  | always     : SFProp → SFProp
  | bounded    : Nat → SFProp → SFProp
  deriving Inhabited

----------------------------------------------------------------------
-- Notation
----------------------------------------------------------------------

namespace SFProp

scoped notation "⊤ₛ" => SFProp.top
scoped notation "⊥ₛ" => SFProp.bot
scoped prefix:90 "¬ₛ"  => SFProp.neg
scoped infixl:65 " ⋀ " => SFProp.conj
scoped infixl:60 " ⋁ " => SFProp.disj
scoped infixr:55 " ⟹ " => SFProp.impl
scoped prefix:90 "◯"   => SFProp.next
scoped infixl:50 " 𝒰 " => SFProp.until
scoped infixl:50 " ℛ " => SFProp.release
scoped prefix:90 "◇"   => SFProp.eventually
scoped prefix:90 "□"   => SFProp.always

end SFProp

----------------------------------------------------------------------
-- Smart constructors
----------------------------------------------------------------------

/-- Build an atomic predicate from a label and test. -/
def mkAtom (label : String) (test : Scene → Bool) : SFProp :=
  .atom ⟨label, test⟩

end SceneFlowSpec
