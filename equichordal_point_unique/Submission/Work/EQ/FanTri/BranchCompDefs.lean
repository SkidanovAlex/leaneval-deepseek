import Mathlib
import Submission.Work.EQ.DefsCore

/-!
# Finite compositions of inverse branches

For a finite branch word `w`, `branchComp a w` is the composition
`invBranch a w₀ ∘ invBranch a w₁ ∘ ⋯ ∘ invBranch a w_{n-1}` (read from the head), so that the
stable fan satisfies the "append" identity

`fan a h (w ++ δ) u = branchComp a w (fan a h δ (λ^{|w|} u))`.

This is the bookkeeping behind the reduction of `fan_gap_unif` to the case `ε₀ = []`.
-/

namespace Work.EQ.FanTri

open Work.EQ

noncomputable section

/-- The composition of the inverse branches of the letters of `w`, read from the head:
`branchComp a [] = id`, `branchComp a (c :: w) = invBranch a c ∘ branchComp a w`. -/
def branchComp (a : ℝ) : List Bool → (ℂ × ℂ) → (ℂ × ℂ)
  | [], z => z
  | c :: w, z => invBranch a c (branchComp a w z)

variable (a : ℝ) (h : ℂ → ℂ)

@[simp] lemma branchComp_nil : branchComp a ([] : List Bool) = id := rfl

@[simp] lemma branchComp_apply_nil (z : ℂ × ℂ) : branchComp a ([] : List Bool) z = z := rfl

lemma branchComp_cons (c : Bool) (w : List Bool) (z : ℂ × ℂ) :
    branchComp a (c :: w) z = invBranch a c (branchComp a w z) := rfl

lemma branchComp_cons_apply (c : Bool) (w : List Bool) (z : ℂ × ℂ) :
    branchComp a (c :: w) z = invBranch a c (branchComp a w z) := rfl

/-- **The append identity for the fan.** -/
lemma fan_append_branchComp (w δ : List Bool) (u : ℂ) :
    fan a h (w ++ δ) u = branchComp a w (fan a h δ ((eqLam a : ℂ) ^ w.length * u)) := by
  induction w generalizing u with
  | nil => simp
  | cons c w ih =>
      rw [List.cons_append, fan, ih, branchComp_cons]
      congr 2
      rw [List.length_cons, pow_succ]
      ring_nf

end

end Work.EQ.FanTri
