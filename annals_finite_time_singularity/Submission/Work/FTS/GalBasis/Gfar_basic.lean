import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.FTS.GalBasis.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis

/-!
# The designated far bump `Gfar` is a test function

`Gfar = famRaw 0 0 3 40 80 1 5` is the family element with `p = q = 0` and `n = 3` on the box
`[40/4, 80/4] × [1/4, 5/4] = [10, 20] × [1/4, 5/4]`.  It is the function used to kill the
zero mode `L₁₂(·)(0)` in the adjustment `testFam`.  This file proves the three elementary
facts needed about it: it is `Ccφ` (globally `C^∞`, supported strictly inside a box), it is
everywhere nonnegative (there is no `z^p θ^q` factor), and it vanishes outside its box.

The proofs are direct from the factorization
`Gfar z θ = famZ 3 40 80 z * famTh 3 1 5 θ` (since `z^0 = θ^0 = 1`) together with the
support/plateau lemmas of `Defs.lean` for `famZ`/`famTh`.
-/

/-- The key elementary fact: `Gfar z θ = famZ 3 40 80 z * famTh 3 1 5 θ` — the monomial
factor of `famRaw` is trivial at `p = q = 0`. -/
theorem Gfar_eq_famZ_mul (z θ : ℝ) :
    Gfar z θ = famZ 3 40 80 z * famTh 3 1 5 θ := by
  simp [Gfar, famRaw]

/-- `Gfar` vanishes as soon as one of the four steps of its box is switched off. -/
theorem Gfar_eq_zero {z θ : ℝ}
    (h : 4 * z ≤ 40 ∨ 80 ≤ 4 * z ∨ 4 * θ ≤ 1 ∨ 5 ≤ 4 * θ) : Gfar z θ = 0 := by
  rw [Gfar_eq_famZ_mul]
  rcases h with h | h | h | h
  · rw [famZ_eq_zero (n := 3) (m₁ := 40) (m₂ := 80) (Or.inl (by norm_num1; linarith)),
      zero_mul]
  · rw [famZ_eq_zero (n := 3) (m₁ := 40) (m₂ := 80) (Or.inr (by norm_num1; linarith)),
      zero_mul]
  · rw [famTh_eq_zero (n := 3) (m₃ := 1) (m₄ := 5) (Or.inl (by norm_num1; linarith)),
      mul_zero]
  · rw [famTh_eq_zero (n := 3) (m₃ := 1) (m₄ := 5) (Or.inr (by norm_num1; linarith)),
      mul_zero]

/-- `Gfar` is nowhere negative — it is a product of values of `Real.smoothTransition`, each of
which lies in `[0,1]`, and the monomial weights are absent. -/
theorem Gfar_nonneg (z θ : ℝ) : 0 ≤ Gfar z θ := by
  rw [Gfar_eq_famZ_mul, famZ, famTh]
  exact mul_nonneg (mul_nonneg (stp_nonneg 3 40 z) (ustp_nonneg 3 80 z))
    (mul_nonneg (stp_nonneg 3 1 θ) (ustp_nonneg 3 5 θ))

/-- `Gfar` is a test function: `C^∞` and supported in `[10,20] × [1/4,5/4]`, which is strictly
inside the open box `(9,21) × (1/8, π/2 - 1/8)`. -/
theorem Gfar_ccφ : Ccφ Gfar := by
  refine ⟨9, 21, 1 / 8, by norm_num, by norm_num, by norm_num,
    by linarith [Real.pi_gt_three], ?_, 10, 20, 1 / 4, by norm_num, by norm_num, by norm_num,
    by norm_num, ?_, ?_⟩
  · simpa [Gfar] using contDiff_famRaw 0 0 3 40 80 1 5
  · linarith [Real.pi_gt_three]
  · intro z θ hz
    apply Gfar_eq_zero
    rcases hz with hz | hz
    · rw [Set.mem_Icc, not_and_or, not_le, not_le] at hz
      rcases hz with hz | hz
      · left; linarith
      · right; left; linarith
    · rw [Set.mem_Icc, not_and_or, not_le, not_le] at hz
      rcases hz with hz | hz
      · right; right; left; linarith
      · right; right; right; linarith [Real.pi_gt_three]

theorem Gfar_basic : Ccφ Gfar ∧ (∀ z θ, 0 ≤ Gfar z θ) ∧
    (∀ z θ, (z ≤ 10 ∨ 20 ≤ z ∨ θ ≤ 1 / 4 ∨ 5 / 4 ≤ θ) → Gfar z θ = 0) :=
  ⟨Gfar_ccφ, Gfar_nonneg, by
    intro z θ h
    apply Gfar_eq_zero
    rcases h with h | h | h | h
    · left; linarith
    · right; left; linarith
    · right; right; left; linarith
    · right; right; right; linarith⟩

end Work.FTS.GalBasis
