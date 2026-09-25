import Mathlib
import Submission.Work.NN.Core.CnPert

/-!
# Coordinate projection of `(A z) w`: bounds at the level of the Newton linearisation

For a field `A : ℂⁿ → (ℂⁿ →L[ℝ] ℂⁿ)` with uniform (`K`-)bounds `h1`–`h5` on a ball of radius `ρ`,
and a vector `w` with `‖w‖ ≤ 1`, the function `z ↦ ((A z) w) j` inherits the same five bounds
(linear growth at `0`, Lipschitz, differentiability, bound on the derivative, Lipschitzness of the
derivative).

The point is that the map `T ↦ (T w) j` is the continuous linear map
`L = (proj j).comp ((apply ℝ (ℂⁿ)) w)`, of operator norm `≤ ‖w‖ ≤ 1`, so `z ↦ ((A z) w) j = L (A z)`
is obtained from `A` by precomposition with a contraction; all five bounds transport, with the
derivative given by `L.comp (fderiv ℝ A z)`.
-/

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Newton

theorem bounds_comp_apply_proj
    {n : ℕ} {A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n}
    {ρ K : ℝ}
    (h1 : ∀ z, ‖z‖ ≤ ρ → ‖A z‖ ≤ K * ‖z‖)
    (h2 : ∀ z w, ‖z‖ ≤ ρ → ‖w‖ ≤ ρ → ‖A z - A w‖ ≤ K * ‖z - w‖)
    (h3 : ∀ z, ‖z‖ ≤ ρ → DifferentiableAt ℝ A z)
    (h4 : ∀ z, ‖z‖ ≤ ρ → ‖fderiv ℝ A z‖ ≤ K)
    (h5 : ∀ z w, ‖z‖ ≤ ρ → ‖w‖ ≤ ρ → ‖fderiv ℝ A z - fderiv ℝ A w‖ ≤ K * ‖z - w‖)
    (w : Work.NN.Core.Cn n) (hw : ‖w‖ ≤ 1) (j : Fin n) :
    (∀ z, ‖z‖ ≤ ρ → ‖(A z w) j‖ ≤ K * ‖z‖) ∧
    (∀ z w', ‖z‖ ≤ ρ → ‖w'‖ ≤ ρ → ‖(A z w) j - (A w' w) j‖ ≤ K * ‖z - w'‖) ∧
    (∀ z, ‖z‖ ≤ ρ → DifferentiableAt ℝ (fun z => (A z w) j) z) ∧
    (∀ z, ‖z‖ ≤ ρ → ‖fderiv ℝ (fun z => (A z w) j) z‖ ≤ K) ∧
    (∀ z w', ‖z‖ ≤ ρ → ‖w'‖ ≤ ρ →
      ‖fderiv ℝ (fun z => (A z w) j) z - fderiv ℝ (fun z => (A z w) j) w'‖ ≤ K * ‖z - w'‖) := by
  -- `L` is the continuous linear map `T ↦ (T w) j`.
  set L : (Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n) →L[ℝ] ℂ :=
    (ContinuousLinearMap.proj j).comp (ContinuousLinearMap.apply ℝ (Work.NN.Core.Cn n) w) with hL
  have hLapply : ∀ T : Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n, L T = (T w) j := by
    intro T; simp [hL, ContinuousLinearMap.apply_apply]
  -- `‖L‖ ≤ ‖w‖ ≤ 1`.
  have hLnorm : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro T
    rw [hLapply]
    calc ‖(T w) j‖ ≤ ‖T w‖ := norm_le_pi_norm _ _
      _ ≤ ‖T‖ * ‖w‖ := T.le_opNorm w
      _ ≤ ‖T‖ * 1 := mul_le_mul_of_nonneg_left hw (norm_nonneg T)
      _ = 1 * ‖T‖ := by ring
  have hg : ∀ z, (A z w) j = L (A z) := fun z => (hLapply (A z)).symm
  have hgfun : (fun z => (A z w) j) = (fun z => L (A z)) := funext hg
  -- The chain rule, with the derivative of `z ↦ L (A z)` equal to `L.comp (fderiv ℝ A z)`.
  have hfd : ∀ z, ‖z‖ ≤ ρ → fderiv ℝ (fun z => (A z w) j) z = L.comp (fderiv ℝ A z) := by
    intro z hz
    rw [hgfun]
    exact ((ContinuousLinearMap.hasFDerivAt L).comp z (h3 z hz).hasFDerivAt).fderiv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rw [hg z]
    calc ‖L (A z)‖ ≤ ‖L‖ * ‖A z‖ := L.le_opNorm _
      _ ≤ 1 * (K * ‖z‖) := mul_le_mul hLnorm (h1 z hz) (norm_nonneg (A z)) zero_le_one
      _ = K * ‖z‖ := one_mul _
  · intro z w' hz hw'
    rw [hg z, hg w', ← map_sub]
    calc ‖L (A z - A w')‖ ≤ ‖L‖ * ‖A z - A w'‖ := L.le_opNorm _
      _ ≤ 1 * (K * ‖z - w'‖) := mul_le_mul hLnorm (h2 z w' hz hw')
          (norm_nonneg (A z - A w')) zero_le_one
      _ = K * ‖z - w'‖ := one_mul _
  · intro z hz
    rw [hgfun]
    exact (ContinuousLinearMap.differentiableAt L).comp z (h3 z hz)
  · intro z hz
    rw [hfd z hz]
    calc ‖L.comp (fderiv ℝ A z)‖ ≤ ‖L‖ * ‖fderiv ℝ A z‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * K := mul_le_mul hLnorm (h4 z hz) (norm_nonneg (fderiv ℝ A z)) zero_le_one
      _ = K := one_mul _
  · intro z w' hz hw'
    rw [hfd z hz, hfd w' hw', ← ContinuousLinearMap.comp_sub]
    calc ‖L.comp (fderiv ℝ A z - fderiv ℝ A w')‖
        ≤ ‖L‖ * ‖fderiv ℝ A z - fderiv ℝ A w'‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * (K * ‖z - w'‖) := mul_le_mul hLnorm (h5 z w' hz hw')
          (norm_nonneg (fderiv ℝ A z - fderiv ℝ A w')) zero_le_one
      _ = K * ‖z - w'‖ := one_mul _

end Work.NN.Newton
