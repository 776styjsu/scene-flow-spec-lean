/-
  SceneFlowSpec.Semantics
  Finite-trace (weak) semantics for SceneFlow temporal formulas.

  `eval τ i φ` returns `true` iff formula `φ` holds at position `i`
  in the finite trace `τ`.
-/
import SceneFlowSpec.Formula

namespace SceneFlowSpec

open SFProp

----------------------------------------------------------------------
-- § 1.  Non-temporal core
----------------------------------------------------------------------

/-- Evaluate a non-temporal formula layer.  Temporal operators are
    handled by dedicated functions that call back into `evalAt`. -/
def evalAtom (τ : Trace) (i : Nat) (p : AtomicPred) : Bool :=
  if i < τ.length then p.test (τ.getScene i) else false

----------------------------------------------------------------------
-- § 2.  Temporal loops (structural recursion on `fuel : Nat`)
--
--  Each temporal combinator is a standalone function that takes an
--  *already-evaluated* predicate `f : Nat → Bool` (mapping position
--  to a truth value) plus a fuel counter.  This avoids any mutual
--  recursion with `eval`.
----------------------------------------------------------------------

/-- `eventually` loop: is there a `j ∈ [i, i+fuel)` with `f j = true`? -/
def loopEventually (f : Nat → Bool) (i : Nat) : Nat → Bool
  | 0        => false
  | fuel + 1 => f i || loopEventually f (i + 1) fuel

/-- `always` loop: does `f j = true` for every `j ∈ [i, i+fuel)`? -/
def loopAlways (f : Nat → Bool) (i : Nat) : Nat → Bool
  | 0        => true
  | fuel + 1 => f i && loopAlways f (i + 1) fuel

/-- `until` loop: `f₁ U f₂` — is there a `j ∈ [i, i+fuel)` with `f₂ j`,
    and `f₁ k` for all `k ∈ [i, j)`? -/
def loopUntil (f₁ f₂ : Nat → Bool) (i : Nat) : Nat → Bool
  | 0        => false
  | fuel + 1 =>
    if f₂ i then true
    else if f₁ i then loopUntil f₁ f₂ (i + 1) fuel
    else false

/-- `release` loop: `f₁ R f₂` — dual of until. -/
def loopRelease (f₁ f₂ : Nat → Bool) (i : Nat) : Nat → Bool
  | 0        => true   -- vacuously true at end
  | fuel + 1 =>
    if f₁ i && f₂ i then true
    else if f₂ i then loopRelease f₁ f₂ (i + 1) fuel
    else false

/-- bounded loop: `f` holds for n consecutive positions from `i`,
    treating out-of-trace positions as vacuously true. -/
def loopBounded (f : Nat → Bool) (i : Nat) (len : Nat) : Nat → Bool
  | 0     => true
  | n + 1 =>
    if i < len then f i && loopBounded f (i + 1) len n
    else true

----------------------------------------------------------------------
-- § 3.  Main evaluator
----------------------------------------------------------------------

/-- Evaluate a SceneFlow formula at position `i` in finite trace `τ`.
    Structurally recursive on `φ`.
    Temporal operators delegate to loop helpers with
    `fuel = τ.length - i`. -/
def eval (τ : Trace) (i : Nat) : SFProp → Bool
  | .top          => true
  | .bot          => false
  | .atom p       => evalAtom τ i p
  | .neg ψ        => !eval τ i ψ
  | .conj ψ₁ ψ₂  => eval τ i ψ₁ && eval τ i ψ₂
  | .disj ψ₁ ψ₂  => eval τ i ψ₁ || eval τ i ψ₂
  | .impl ψ₁ ψ₂  => !eval τ i ψ₁ || eval τ i ψ₂
  | .next ψ       => eval τ (i + 1) ψ
  | .until ψ₁ ψ₂  =>
      loopUntil (eval τ · ψ₁) (eval τ · ψ₂) i (τ.length - i)
  | .release ψ₁ ψ₂ =>
      loopRelease (eval τ · ψ₁) (eval τ · ψ₂) i (τ.length - i)
  | .eventually ψ =>
      loopEventually (eval τ · ψ) i (τ.length - i)
  | .always ψ =>
      loopAlways (eval τ · ψ) i (τ.length - i)
  | .bounded n ψ =>
      loopBounded (eval τ · ψ) i τ.length n

----------------------------------------------------------------------
-- Trace satisfaction
----------------------------------------------------------------------

/-- A trace `τ` satisfies formula `φ` when `φ` holds at position 0. -/
def satisfies (τ : Trace) (φ : SFProp) : Bool := eval τ 0 φ

/-- Notation: `τ ⊨ φ` means `satisfies τ φ = true`. -/
scoped notation:50 τ " ⊨ " φ => satisfies τ φ = true

/-- Notation: `τ ⊭ φ` means `satisfies τ φ = false`. -/
scoped notation:50 τ " ⊭ " φ => satisfies τ φ = false

----------------------------------------------------------------------
-- § 4.  Simp / unfolding lemmas
----------------------------------------------------------------------

@[simp] theorem eval_top (τ : Trace) (i : Nat) :
    eval τ i ⊤ₛ = true := rfl

@[simp] theorem eval_bot (τ : Trace) (i : Nat) :
    eval τ i ⊥ₛ = false := rfl

@[simp] theorem eval_neg (τ : Trace) (i : Nat) (φ : SFProp) :
    eval τ i (¬ₛ φ) = !eval τ i φ := rfl

@[simp] theorem eval_conj (τ : Trace) (i : Nat) (φ ψ : SFProp) :
    eval τ i (φ ⋀ ψ) = (eval τ i φ && eval τ i ψ) := rfl

@[simp] theorem eval_disj (τ : Trace) (i : Nat) (φ ψ : SFProp) :
    eval τ i (φ ⋁ ψ) = (eval τ i φ || eval τ i ψ) := rfl

@[simp] theorem eval_impl (τ : Trace) (i : Nat) (φ ψ : SFProp) :
    eval τ i (φ ⟹ ψ) = (!eval τ i φ || eval τ i ψ) := rfl

@[simp] theorem eval_next (τ : Trace) (i : Nat) (φ : SFProp) :
    eval τ i (◯ φ) = eval τ (i + 1) φ := rfl

@[simp] theorem eval_eventually_def (τ : Trace) (i : Nat) (φ : SFProp) :
    eval τ i (◇ φ) = loopEventually (eval τ · φ) i (τ.length - i) := rfl

@[simp] theorem eval_always_def (τ : Trace) (i : Nat) (φ : SFProp) :
    eval τ i (□ φ) = loopAlways (eval τ · φ) i (τ.length - i) := rfl

@[simp] theorem eval_bounded_def (τ : Trace) (i : Nat) (n : Nat) (φ : SFProp) :
    eval τ i (.bounded n φ) = loopBounded (eval τ · φ) i τ.length n := rfl

----------------------------------------------------------------------
-- § 5.  Loop unfolding lemmas
----------------------------------------------------------------------

@[simp] theorem loopEventually_zero (f : Nat → Bool) (i : Nat) :
    loopEventually f i 0 = false := rfl

@[simp] theorem loopEventually_succ (f : Nat → Bool) (i fuel : Nat) :
    loopEventually f i (fuel + 1) = (f i || loopEventually f (i + 1) fuel) := rfl

@[simp] theorem loopAlways_zero (f : Nat → Bool) (i : Nat) :
    loopAlways f i 0 = true := rfl

@[simp] theorem loopAlways_succ (f : Nat → Bool) (i fuel : Nat) :
    loopAlways f i (fuel + 1) = (f i && loopAlways f (i + 1) fuel) := rfl

@[simp] theorem loopBounded_zero (f : Nat → Bool) (i len : Nat) :
    loopBounded f i len 0 = true := rfl

end SceneFlowSpec
