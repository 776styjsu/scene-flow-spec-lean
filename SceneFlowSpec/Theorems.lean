/-
  SceneFlowSpec.Theorems
  Mechanized proofs of core metatheoretic properties of the
  finite-trace SceneFlow semantics.
-/
import SceneFlowSpec.Semantics

namespace SceneFlowSpec

open SFProp

----------------------------------------------------------------------
-- § 1. Double negation
----------------------------------------------------------------------

theorem eval_neg_neg (τ : Trace) (i : Nat) (φ : SFProp) :
    eval τ i (¬ₛ(¬ₛ φ)) = eval τ i φ := by
  simp [Bool.not_not]

----------------------------------------------------------------------
-- § 2. Commutativity
----------------------------------------------------------------------

theorem eval_conj_comm (τ : Trace) (i : Nat) (φ ψ : SFProp) :
    eval τ i (φ ⋀ ψ) = eval τ i (ψ ⋀ φ) := by
  simp [Bool.and_comm]

theorem eval_disj_comm (τ : Trace) (i : Nat) (φ ψ : SFProp) :
    eval τ i (φ ⋁ ψ) = eval τ i (ψ ⋁ φ) := by
  simp [Bool.or_comm]

----------------------------------------------------------------------
-- § 3. Implication as disjunction
----------------------------------------------------------------------

theorem eval_impl_as_disj (τ : Trace) (i : Nat) (φ ψ : SFProp) :
    eval τ i (φ ⟹ ψ) = eval τ i (¬ₛ φ ⋁ ψ) := by
  simp

----------------------------------------------------------------------
-- § 4. Empty-trace properties
----------------------------------------------------------------------

theorem eval_atom_empty (p : AtomicPred) :
    eval ([] : Trace) 0 (.atom p) = false := by
  rfl

theorem eval_eventually_empty (φ : SFProp) :
    eval ([] : Trace) 0 (◇ φ) = false := by
  rfl

theorem eval_always_empty (φ : SFProp) :
    eval ([] : Trace) 0 (□ φ) = true := by
  rfl

----------------------------------------------------------------------
-- § 5. Out-of-bounds
----------------------------------------------------------------------

theorem eval_atom_oob (τ : Trace) (i : Nat) (p : AtomicPred) (h : τ.length ≤ i) :
    eval τ i (.atom p) = false := by
  simp [eval, evalAtom]; omega

----------------------------------------------------------------------
-- § 6. Bounded operator properties
----------------------------------------------------------------------

theorem eval_bounded_zero (τ : Trace) (i : Nat) (φ : SFProp) :
    eval τ i (.bounded 0 φ) = true := by
  rfl

----------------------------------------------------------------------
-- § 7. Duality: Always ↔ ¬ Eventually ¬
----------------------------------------------------------------------

/-- Core duality at the loop level. -/
theorem loopAlways_eq_not_loopEventually_neg (f : Nat → Bool) (i fuel : Nat) :
    loopAlways f i fuel = !loopEventually (fun j => !f j) i fuel := by
  induction fuel generalizing i with
  | zero => rfl
  | succ k ih =>
    unfold loopAlways loopEventually
    cases f i <;> simp [ih]

theorem loopEventually_eq_not_loopAlways_neg (f : Nat → Bool) (i fuel : Nat) :
    loopEventually f i fuel = !loopAlways (fun j => !f j) i fuel := by
  induction fuel generalizing i with
  | zero => rfl
  | succ k ih =>
    unfold loopAlways loopEventually
    cases f i <;> simp [ih]

/-- `□ φ = ¬(◇(¬φ))` — The classic duality between always and eventually. -/
theorem always_eq_neg_eventually_neg (τ : Trace) (i : Nat) (φ : SFProp) :
    eval τ i (□ φ) = !eval τ i (◇ (¬ₛ φ)) := by
  simp only [eval_always_def, eval_eventually_def, eval_neg]
  exact loopAlways_eq_not_loopEventually_neg _ _ _

/-- `◇ φ = ¬(□(¬φ))` — The dual direction. -/
theorem eventually_eq_neg_always_neg (τ : Trace) (i : Nat) (φ : SFProp) :
    eval τ i (◇ φ) = !eval τ i (□ (¬ₛ φ)) := by
  simp only [eval_always_def, eval_eventually_def, eval_neg]
  exact loopEventually_eq_not_loopAlways_neg _ _ _

----------------------------------------------------------------------
-- § 8. Always implies Bounded
----------------------------------------------------------------------

/-- If `□φ` holds at position `i`, then `$[n][φ]` also holds. -/
theorem always_implies_bounded (τ : Trace) (i : Nat) (n : Nat) (φ : SFProp)
    (h : eval τ i (□ φ) = true) :
    eval τ i (.bounded n φ) = true := by
  simp only [eval_always_def, eval_bounded_def] at *
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    unfold loopBounded
    by_cases h_bound : i < τ.length
    · have hfuel : ∃ k, τ.length - i = k + 1 := ⟨τ.length - i - 1, by omega⟩
      obtain ⟨k, hk⟩ := hfuel
      rw [hk] at h
      unfold loopAlways at h
      have hfi : eval τ i φ = true := by
        cases heval : eval τ i φ
        · rw [heval] at h; simp only [Bool.false_and] at h; contradiction
        · rfl
      have hrest : loopAlways (fun x => eval τ x φ) (i + 1) k = true := by
        cases heval : eval τ i φ
        · rw [heval] at h; simp only [Bool.false_and] at h; contradiction
        · rw [heval] at h; simp only [Bool.true_and] at h; exact h
      simp only [h_bound, ↓reduceIte, hfi, Bool.true_and]
      apply ih
      have : τ.length - (i + 1) = k := by omega
      rwa [this]
    · rw [if_neg h_bound]

----------------------------------------------------------------------
-- § 9. Unfolding
----------------------------------------------------------------------

/-- Eventually unfolds: `◇φ` at `i` = `φ(i) ∨ ◇φ(i+1)` when in bounds. -/
theorem eval_eventually_unfold (τ : Trace) (i : Nat) (φ : SFProp)
    (h : i < τ.length) :
    eval τ i (◇ φ) = (eval τ i φ || eval τ (i + 1) (◇ φ)) := by
  simp only [eval_eventually_def]
  have heq : τ.length - i = (τ.length - i - 1) + 1 := by omega
  rw [heq, loopEventually_succ]
  have : τ.length - i - 1 = τ.length - (i + 1) := by omega
  rw [this]

/-- Always unfolds: `□φ` at `i` = `φ(i) ∧ □φ(i+1)` when in bounds. -/
theorem eval_always_unfold (τ : Trace) (i : Nat) (φ : SFProp)
    (h : i < τ.length) :
    eval τ i (□ φ) = (eval τ i φ && eval τ (i + 1) (□ φ)) := by
  simp only [eval_always_def]
  have heq : τ.length - i = (τ.length - i - 1) + 1 := by omega
  rw [heq, loopAlways_succ]
  have : τ.length - i - 1 = τ.length - (i + 1) := by omega
  rw [this]

end SceneFlowSpec
