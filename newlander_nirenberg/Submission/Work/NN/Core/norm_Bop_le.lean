import Mathlib
import Submission.Work.NN.Core.DbarCnPertAux

/-!
# Norm bounds for the Beltrami coefficient operators `Bop` and `BopBar`

`Bop A z` and `BopBar A z` are the `ℝ`-linear operators on `Cn n = Fin n → ℂ` whose matrices
are the Beltrami coefficients `β k j z = -(I/2)·(A z e_k)_j` and their conjugates
(see `Work.NN.Core.DbarCnPertAux`).  Since `‖β k j z‖ ≤ ‖A z‖ / 2` (`norm_betaCoef_le`), the
naive row-sum estimate for the operator norm gives

`‖Bop A z‖ ≤ n · ‖A z‖ / 2`,   `‖BopBar A z‖ ≤ n · ‖A z‖ / 2`.

This is the smallness estimate used to invert `1 + BopBar A z` and to control the decoupled
Beltrami coefficient `(1 + BopBar A z)⁻¹ Bop A z`.

The work is done by the auxiliary estimate `opNorm_pi_sum_smulRight_le` on an operator given in
coordinates `v ↦ (k ↦ ∑ j, v j * c k j)`: its operator norm is at most `n` times the bound on
the coefficients.
-/

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Core

/-- **Row-sum norm estimate.**  For coefficients `C k j : ℂ` bounded by `M`, the `ℝ`-linear map
`v ↦ (k ↦ ∑ j, v j * C k j)` on `Cn n = Fin n → ℂ` (with the sup norm on both sides) has
operator norm at most `n * M`: each of the `n` coordinates of the image is a sum of `n` terms
of size at most `‖v‖ * M`. -/
lemma opNorm_pi_sum_smulRight_le {n : ℕ} (C : Fin n → Fin n → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hC : ∀ k j, ‖C k j‖ ≤ M) :
    ‖ContinuousLinearMap.pi (fun k : Fin n => ∑ j : Fin n,
        ContinuousLinearMap.smulRight (ContinuousLinearMap.proj j : Cn n →L[ℝ] ℂ) (C k j))‖
      ≤ (n : ℝ) * M := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have hrow : ∀ k : Fin n,
      ‖(∑ j : Fin n, ContinuousLinearMap.smulRight (ContinuousLinearMap.proj j : Cn n →L[ℝ] ℂ)
          (C k j)) v‖ ≤ (n : ℝ) * M * ‖v‖ := by
    intro k
    have h1 : (∑ j : Fin n, ContinuousLinearMap.smulRight (ContinuousLinearMap.proj j : Cn n →L[ℝ] ℂ)
        (C k j)) v = ∑ j : Fin n, v j • C k j := by
      rw [sum_apply]
      simp [ContinuousLinearMap.smulRight_apply]
    rw [h1]
    calc ‖∑ j : Fin n, v j • C k j‖
        ≤ ∑ j : Fin n, ‖v j • C k j‖ := norm_sum_le _ _
      _ = ∑ j : Fin n, ‖v j‖ * ‖C k j‖ := by simp
      _ ≤ ∑ _j : Fin n, ‖v‖ * M := by
            refine Finset.sum_le_sum fun j _ => ?_
            exact mul_le_mul (norm_le_pi_norm v j) (hC k j) (norm_nonneg _) (norm_nonneg _)
      _ = (n : ℝ) * (‖v‖ * M) := by
            rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      _ = (n : ℝ) * M * ‖v‖ := by ring
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro k
  rw [ContinuousLinearMap.pi_apply]
  exact hrow k

theorem norm_Bop_le {n : ℕ} (A : Cn n → Cn n →L[ℝ] Cn n) (z : Cn n) :
    ‖Bop A z‖ ≤ (n : ℝ) * ‖A z‖ / 2 ∧ ‖BopBar A z‖ ≤ (n : ℝ) * ‖A z‖ / 2 := by
  have hM : (0 : ℝ) ≤ ‖A z‖ / 2 := by positivity
  constructor
  · have h : ‖Bop A z‖ ≤ (n : ℝ) * (‖A z‖ / 2) := by
      change ‖ContinuousLinearMap.pi (fun k : Fin n => ∑ j : Fin n,
        ContinuousLinearMap.smulRight (ContinuousLinearMap.proj j : Cn n →L[ℝ] ℂ)
          (betaCoef A k j z))‖ ≤ (n : ℝ) * (‖A z‖ / 2)
      exact opNorm_pi_sum_smulRight_le _ hM (fun k j => norm_betaCoef_le le_rfl k j)
    calc ‖Bop A z‖ ≤ (n : ℝ) * (‖A z‖ / 2) := h
      _ = (n : ℝ) * ‖A z‖ / 2 := by ring
  · have h : ‖BopBar A z‖ ≤ (n : ℝ) * (‖A z‖ / 2) := by
      change ‖ContinuousLinearMap.pi (fun k : Fin n => ∑ j : Fin n,
        ContinuousLinearMap.smulRight (ContinuousLinearMap.proj j : Cn n →L[ℝ] ℂ)
          (starRingEnd ℂ (betaCoef A k j z)))‖ ≤ (n : ℝ) * (‖A z‖ / 2)
      refine opNorm_pi_sum_smulRight_le _ hM (fun k j => ?_)
      rw [starRingEnd_apply, norm_star]
      exact norm_betaCoef_le le_rfl k j
    calc ‖BopBar A z‖ ≤ (n : ℝ) * (‖A z‖ / 2) := h
      _ = (n : ℝ) * ‖A z‖ / 2 := by ring

end Work.NN.Core
