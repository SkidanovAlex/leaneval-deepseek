import Mathlib
import Submission.Work.ResMath.defs
import Submission.Work.ResMath.resE_defs
import Submission.Work.ResMath.resE_bound
import Submission.Work.ResMath.expGaussBounds
import Submission.Work.ResMath.Nmat_apply
import Submission.Work.ResMath.summable_Nsum
import Submission.Work.ResMath.quad_ineq
import Submission.Work.ResMath.summable_exp_neg_affine_sq

/-!
# Lemma 4.6 of Harvey–van der Hoeven, *Integer multiplication in time* `O(n log n)`

`E = N - I` with `N = C T D` the normalised row-selected resampling matrix of §4.2.  This file
proves the two norm bounds for `E` used in Proposition 4.7(i):

`‖E u‖ ≤ 21/50 · ‖u‖`   and   `‖E u‖ ≤ 2^{-α²(t/s-1)} · ‖u‖`

for the sup norms on `Fin s → ℂ`, from the operator-norm estimate of `resE_bound` and the
elementary exponential bounds of `expGaussBounds`.
-/

namespace Work.ResMath

open HvdH

theorem resE_norm_le (s t α p : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hαp : α ^ 2 < p)
    (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1) :
    (∀ u : Fin s → ℂ, ‖(HvdH.Emat s t α).mulVec u‖ ≤ 21 / 50 * ‖u‖) ∧
    (∀ u : Fin s → ℂ, ‖(HvdH.Emat s t α).mulVec u‖ ≤
      (2 : ℝ) ^ (-((α : ℝ) ^ 2 * ((t : ℝ) / s - 1))) * ‖u‖) := by
  have hs0 : 0 < s := by omega
  have hα0 : 0 < α := by omega
  have hx : 1 ≤ (α : ℝ) ^ 2 * ((t : ℝ) / s - 1) := by
    have h1 : (p : ℝ) / (α : ℝ) ^ 2 ≤ (α : ℝ) ^ 2 * ((t : ℝ) / s - 1) := by
      have h2 := mul_le_mul_of_nonneg_left hθ (sq_nonneg (α : ℝ))
      have h3 : (α : ℝ) ^ 2 * ((p : ℝ) / (α : ℝ) ^ 4) = (p : ℝ) / (α : ℝ) ^ 2 := by
        field_simp
      linarith [h2, h3]
    have hp' : (α : ℝ) ^ 2 < (p : ℝ) := by exact_mod_cast hαp
    have h4 : 1 < (p : ℝ) / (α : ℝ) ^ 2 := by
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < (α : ℝ) ^ 2)]
      simpa using hp'
    linarith
  have hmain : ∀ u : Fin s → ℂ, ‖(HvdH.Emat s t α).mulVec u‖ ≤
      2.000008 * Real.exp (-(Real.pi * ((α : ℝ) ^ 2 * ((t : ℝ) / s - 1)) / 2)) * ‖u‖ :=
    fun u => norm_Emat_mulVec_le s t α hs0 hst hα0 hx u
  constructor
  · intro u
    exact (hmain u).trans (mul_le_mul_of_nonneg_right
      (expGaussBounds ((α : ℝ) ^ 2 * ((t : ℝ) / s - 1)) hx).1 (norm_nonneg u))
  · intro u
    exact (hmain u).trans (mul_le_mul_of_nonneg_right
      (expGaussBounds ((α : ℝ) ^ 2 * ((t : ℝ) / s - 1)) hx).2 (norm_nonneg u))

end Work.ResMath
