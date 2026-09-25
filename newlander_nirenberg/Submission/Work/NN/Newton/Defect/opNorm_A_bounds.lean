import Mathlib
import Submission.Work.NN.Newton.DefectDefs
import Submission.Work.NN.Final.holderNormExtract

namespace Work.NN.Newton.Defect

open scoped NNReal ENNReal
open Set

/-- From the `C^{1,α}`-bound `CVBound A α a P` of the columns of a field `A` we extract the two
pointwise consequences: the operator-norm bound `‖A z‖ ≤ a` and the Hölder bound
`‖A x - A y‖ ≤ a ‖x - y‖^α` on `P`.

The hypothesis is a bound `holderNorm 1 α (z ↦ (A z w)_j) P ≤ ofReal a` for every unit vector `w`
and coordinate `j`.  Dropping to `holderNorm 0 α` (`holderNorm_mono_k`) and unpacking it
(`Work.NN.Final.norm_le_of_holderNorm_zero_le`, `..._norm_sub_...`) gives, for each unit `w` and
`j`, the pointwise and Hölder bounds of the column function `z ↦ (A z w)_j`.  The operator norm is
the supremum of the coordinate norms over the unit ball, so scaling `w` back up to an arbitrary
`v` (`A z v = ‖v‖ • A z (‖v‖⁻¹ • v)`) yields the stated operator bounds. -/
theorem opNorm_A_bounds {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    {α a r : ℝ} (hα0 : 0 < α) (ha0 : 0 ≤ a)
    (hA : Work.NN.Newton.CVBound A α a (Work.NN.Newton.polydiscR n r)) :
    (∀ z ∈ Work.NN.Newton.polydiscR n r, ‖A z‖ ≤ a) ∧
    (∀ x ∈ Work.NN.Newton.polydiscR n r, ∀ y ∈ Work.NN.Newton.polydiscR n r,
        ‖A x - A y‖ ≤ a * ‖x - y‖ ^ α) := by
  set P := Work.NN.Newton.polydiscR n r with hP
  -- `C^{0,α}`-bound of each column function `z ↦ (A z w)_j`.
  have h0 : ∀ (w : Work.NN.Core.Cn n) (j : Fin n), ‖w‖ ≤ 1 →
      Work.CR.Flat.holderNorm 0 α (fun z => A z w j) P ≤ ENNReal.ofReal a := by
    intro w j hw
    exact le_trans (Work.CR.Flat.holderNorm_mono_k (Nat.zero_le 1) α _ P) (hA w hw j)
  -- Pointwise bound of a column at a unit vector.
  have hcoord : ∀ (w : Work.NN.Core.Cn n) (j : Fin n), ‖w‖ ≤ 1 → ∀ z ∈ P,
      ‖A z w j‖ ≤ a := by
    intro w j hw z hz
    exact Work.NN.Final.norm_le_of_holderNorm_zero_le ha0 (h0 w j hw) z hz
  -- Hölder bound of a column at a unit vector.
  have hholder : ∀ (w : Work.NN.Core.Cn n) (j : Fin n), ‖w‖ ≤ 1 → ∀ x ∈ P, ∀ y ∈ P,
      ‖A x w j - A y w j‖ ≤ a * ‖x - y‖ ^ α := by
    intro w j hw x hx y hy
    exact Work.NN.Final.norm_sub_le_of_holderNorm_zero_le ha0 (h0 w j hw) x hx y hy
  -- Normalisation bookkeeping for an arbitrary vector `v`.
  have hnormal : ∀ v : Work.NN.Core.Cn n, v ≠ 0 →
      ‖(‖v‖)⁻¹ • v‖ = 1 ∧ ‖v‖ • ((‖v‖)⁻¹ • v) = v := by
    intro v hv
    refine ⟨?_, ?_⟩
    · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg v)), inv_mul_cancel₀]
      exact norm_ne_zero_iff.mpr hv
    · exact smul_inv_smul₀ (ne_of_gt (norm_pos_iff.mpr hv)) v
  constructor
  · intro z hz
    have hcz : ∀ (v : Work.NN.Core.Cn n) (j : Fin n), ‖(A z v) j‖ ≤ a * ‖v‖ := by
      intro v j
      rcases eq_or_ne v 0 with rfl | hv
      · simp
      · obtain ⟨hwnorm, hvdecomp⟩ := hnormal v hv
        have hcw : ‖A z ((‖v‖)⁻¹ • v) j‖ ≤ a := hcoord _ j hwnorm.le z hz
        have hmain : (A z v) j = ‖v‖ • (A z ((‖v‖)⁻¹ • v)) j := by
          conv_lhs => rw [← hvdecomp]
          simp only [map_smul, Pi.smul_apply]
        rw [hmain, norm_smul, Real.norm_of_nonneg (norm_nonneg v)]
        calc ‖v‖ * ‖(A z ((‖v‖)⁻¹ • v)) j‖ ≤ ‖v‖ * a :=
              mul_le_mul_of_nonneg_left hcw (norm_nonneg v)
          _ = a * ‖v‖ := by ring
    rw [ContinuousLinearMap.opNorm_le_iff ha0]
    intro v
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg ha0 (norm_nonneg v))]
    intro j
    exact hcz v j
  · intro x hx y hy
    have hc : 0 ≤ a * ‖x - y‖ ^ α := mul_nonneg ha0 (Real.rpow_nonneg (norm_nonneg _) α)
    have hcz : ∀ (v : Work.NN.Core.Cn n) (j : Fin n),
        ‖((A x - A y) v) j‖ ≤ (a * ‖x - y‖ ^ α) * ‖v‖ := by
      intro v j
      rcases eq_or_ne v 0 with rfl | hv
      · simp
      · obtain ⟨hwnorm, hvdecomp⟩ := hnormal v hv
        have hcw : ‖A x ((‖v‖)⁻¹ • v) j - A y ((‖v‖)⁻¹ • v) j‖ ≤ a * ‖x - y‖ ^ α :=
          hholder _ j hwnorm.le x hx y hy
        have hmain : ((A x - A y) v) j
            = ‖v‖ • ((A x ((‖v‖)⁻¹ • v)) j - (A y ((‖v‖)⁻¹ • v)) j) := by
          conv_lhs => rw [← hvdecomp]
          simp only [sub_apply, map_smul, Pi.sub_apply, Pi.smul_apply, smul_sub]
        rw [hmain, norm_smul, Real.norm_of_nonneg (norm_nonneg v)]
        calc ‖v‖ * ‖(A x ((‖v‖)⁻¹ • v)) j - (A y ((‖v‖)⁻¹ • v)) j‖
              ≤ ‖v‖ * (a * ‖x - y‖ ^ α) := mul_le_mul_of_nonneg_left hcw (norm_nonneg v)
          _ = (a * ‖x - y‖ ^ α) * ‖v‖ := by ring
    rw [ContinuousLinearMap.opNorm_le_iff hc]
    intro v
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg hc (norm_nonneg v))]
    intro j
    exact hcz v j

end Work.NN.Newton.Defect
