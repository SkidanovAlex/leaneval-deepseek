import Mathlib
import Submission.Work.NN.Newton.DefectDefs
import Submission.Work.NN.Newton.Defect.fderiv_lamC_apply
import Submission.Work.NN.Core.holderNorm_fderiv_le_dir

/-!
# The field `z ↦ (DA_z) X` is `C^{0,α}`-small when `A` is `C^{1,α}`-small

`Work.NN.Newton.CVBound A α a P` bounds, for every vector `w` with `‖w‖ ≤ 1` and every coordinate
`j`, the `C^{1,α}(P)`-norm of the component `z ↦ (A z w)_j` by `a`.  The present file derives
from it the `VecHolder`-form of smallness of the *differential* of `A` in a fixed direction `X`
with `‖X‖ ≤ 1`:

  `‖(fderiv ℝ A z) X‖ ≤ a`  and  `‖(fderiv ℝ A z) X - (fderiv ℝ A z') X‖ ≤ a ‖z - z'‖ ^ α`.

The mechanism is `Work.NN.Core.holderNorm_fderiv_le_dir` (the directional derivative of a
`C^{1,α}` function, taken in the fixed direction `X`, is `C^{0,α}` of norm at most `‖X‖` times
the `C^{1,α}`-norm), applied to the components `z ↦ (A z w)_j`: indeed

  `((fderiv ℝ A z) X w) j = fderiv ℝ (fun z' => (A z' w) j) z X`,

so every component of `(fderiv ℝ A z) X` is bounded by `a` in `C^{0,α}(P)`.  Since `ℂⁿ = Fin n → ℂ`
carries the *supremum* norm, coordinatewise bounds assemble into the operator-norm bound on
`(fderiv ℝ A z) X : ℂⁿ →L[ℝ] ℂⁿ`.
-/

noncomputable section

open scoped NNReal ENNReal
open Set

namespace Work.NN.Newton.Defect

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A bound `holderNorm 0 α f Ω ≤ ofReal a` (with `a ≥ 0`) gives the pointwise bound
`‖f z‖ ≤ a` on `Ω`. -/
lemma norm_le_of_holderNorm_zero_le {f : X → ℂ} {Ω : Set X} {α a : ℝ} (ha : 0 ≤ a)
    (h : Work.CR.Flat.holderNorm 0 α f Ω ≤ ENNReal.ofReal a) {z : X} (hz : z ∈ Ω) :
    ‖f z‖ ≤ a := by
  have h1 : ENNReal.ofReal ‖f z‖ ≤ ENNReal.ofReal a :=
    calc ENNReal.ofReal ‖f z‖
        = ENNReal.ofReal ‖iteratedFDerivWithin ℝ 0 f Ω z‖ := by
          rw [norm_iteratedFDerivWithin_zero]
      _ ≤ Work.CR.Flat.iterDerivNorm 0 f Ω := Work.CR.Flat.le_iterDerivNorm 0 f Ω hz
      _ ≤ Work.CR.Flat.holderNorm 0 α f Ω :=
          Work.CR.Flat.iterDerivNorm_le_holderNorm 0 α f Ω le_rfl
      _ ≤ ENNReal.ofReal a := h
  exact (ENNReal.ofReal_le_ofReal_iff ha).mp h1

/-- A bound `holderNorm 0 α f Ω ≤ ofReal a` (with `a ≥ 0`) gives the pointwise Hölder estimate
`‖f z - f z'‖ ≤ a ‖z - z'‖ ^ α` on `Ω`. -/
lemma norm_sub_le_of_holderNorm_zero_le {f : X → ℂ} {Ω : Set X} {α a : ℝ} (ha : 0 ≤ a)
    (h : Work.CR.Flat.holderNorm 0 α f Ω ≤ ENNReal.ofReal a) {z z' : X}
    (hz : z ∈ Ω) (hz' : z' ∈ Ω) :
    ‖f z - f z'‖ ≤ a * ‖z - z'‖ ^ α := by
  rcases eq_or_ne z z' with rfl | hne
  · rw [sub_self, norm_zero]
    exact mul_nonneg ha (Real.rpow_nonneg (norm_nonneg _) α)
  · have heq : ‖iteratedFDerivWithin ℝ 0 f Ω z - iteratedFDerivWithin ℝ 0 f Ω z'‖
        = ‖f z - f z'‖ := by
      have hd := dist_iteratedFDerivWithin_zero (𝕜 := ℝ) f Ω z f Ω z'
      rw [dist_eq_norm, dist_eq_norm] at hd
      exact hd
    have h1 : ENNReal.ofReal (‖f z - f z'‖ / ‖z - z'‖ ^ α) ≤ ENNReal.ofReal a :=
      calc ENNReal.ofReal (‖f z - f z'‖ / ‖z - z'‖ ^ α)
          = ENNReal.ofReal
              (‖iteratedFDerivWithin ℝ 0 f Ω z - iteratedFDerivWithin ℝ 0 f Ω z'‖
                / ‖z - z'‖ ^ α) := by rw [heq]
        _ ≤ Work.CR.Flat.holderSeminorm 0 α f Ω :=
            Work.CR.Flat.le_holderSeminorm 0 α f Ω hz hz' hne
        _ ≤ Work.CR.Flat.holderNorm 0 α f Ω :=
            Work.CR.Flat.holderSeminorm_le_holderNorm 0 α f Ω le_rfl
        _ ≤ ENNReal.ofReal a := h
    have h2 : ‖f z - f z'‖ / ‖z - z'‖ ^ α ≤ a := (ENNReal.ofReal_le_ofReal_iff ha).mp h1
    have hpos : 0 < ‖z - z'‖ ^ α :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) α
    exact (div_le_iff₀ hpos).mp h2

theorem vecHolder_deriv_field {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    {α a r : ℝ} (hα0 : 0 < α) (ha0 : 0 ≤ a)
    (hAc : ContDiffOn ℝ 1 A (Work.NN.Newton.polydiscR n r))
    (hA : Work.NN.Newton.CVBound A α a (Work.NN.Newton.polydiscR n r))
    {X : Work.NN.Core.Cn n} (hX : ‖X‖ ≤ 1) :
    Work.NN.Final.VecHolder (fun z => (fderiv ℝ A z) X) α a (Work.NN.Newton.polydiscR n r) := by
  have hΩo : IsOpen (Work.NN.Newton.polydiscR n r) := Work.NN.Newton.isOpen_polydiscR n r
  have hXnn : (0 : ℝ) ≤ ‖X‖ := norm_nonneg X
  -- ## The `C^{0,α}`-bound on each component `z ↦ ((DA_z) X w)_j`
  have hkey : ∀ (w : Work.NN.Core.Cn n) (j : Fin n), ‖w‖ ≤ 1 →
      Work.CR.Flat.holderNorm 0 α (fun z => ((fderiv ℝ A z) X w) j)
        (Work.NN.Newton.polydiscR n r) ≤ ENNReal.ofReal a := by
    intro w j hw
    have hC1 : ContDiffOn ℝ ((0 + 1 : ℕ) : WithTop ℕ∞) (fun z => (A z w) j)
        (Work.NN.Newton.polydiscR n r) := by
      have h1 : ContDiffOn ℝ ((0 + 1 : ℕ) : WithTop ℕ∞)
          (fun z => (Work.NN.Newton.lamC j) (A z w)) (Work.NN.Newton.polydiscR n r) :=
        ContDiffOn.continuousLinearMap_comp
          ((Work.NN.Newton.lamC j).comp (ContinuousLinearMap.apply ℝ (Work.NN.Core.Cn n) w))
          (by simpa using hAc)
      simpa [Work.NN.Newton.lamC_apply] using h1
    have hb := Work.NN.Core.holderNorm_fderiv_le_dir (α := α) hΩo 0 hC1 X
    have hcongr : ∀ z ∈ Work.NN.Newton.polydiscR n r,
        ((fderiv ℝ A z) X w) j = fderiv ℝ (fun z'' => (A z'' w) j) z X := by
      intro z hz
      have hdiff : DifferentiableAt ℝ A z :=
        (hAc.contDiffAt (hΩo.mem_nhds hz)).differentiableAt (by norm_num)
      have hff : fderiv ℝ (fun z'' => (A z'' w) j) z X = ((fderiv ℝ A z) X w) j := by
        simpa [Work.NN.Newton.lamC_apply] using fderiv_lamC_apply A j w hdiff X
      exact hff.symm
    calc Work.CR.Flat.holderNorm 0 α (fun z => ((fderiv ℝ A z) X w) j)
          (Work.NN.Newton.polydiscR n r)
        = Work.CR.Flat.holderNorm 0 α (fun z => fderiv ℝ (fun z'' => (A z'' w) j) z X)
            (Work.NN.Newton.polydiscR n r) :=
          Work.NN.Core.holderNorm_congr_eqOn hcongr
      _ ≤ ENNReal.ofReal ‖X‖ *
            Work.CR.Flat.holderNorm 1 α (fun z'' => (A z'' w) j)
              (Work.NN.Newton.polydiscR n r) := hb
      _ ≤ ENNReal.ofReal ‖X‖ * ENNReal.ofReal a := mul_le_mul' le_rfl (hA w hw j)
      _ ≤ 1 * ENNReal.ofReal a :=
            mul_le_mul' (by simpa using ENNReal.ofReal_le_ofReal hX) le_rfl
      _ = ENNReal.ofReal a := one_mul _
  -- ## Pointwise corollaries
  have hsup : ∀ (w : Work.NN.Core.Cn n) (j : Fin n), ‖w‖ ≤ 1 →
      ∀ z ∈ Work.NN.Newton.polydiscR n r, ‖((fderiv ℝ A z) X w) j‖ ≤ a :=
    fun w j hw z hz => norm_le_of_holderNorm_zero_le ha0 (hkey w j hw) hz
  have hhol : ∀ (w : Work.NN.Core.Cn n) (j : Fin n), ‖w‖ ≤ 1 →
      ∀ z ∈ Work.NN.Newton.polydiscR n r, ∀ z' ∈ Work.NN.Newton.polydiscR n r,
        ‖((fderiv ℝ A z) X w) j - ((fderiv ℝ A z') X w) j‖ ≤ a * ‖z - z'‖ ^ α :=
    fun w j hw z hz z' hz' => norm_sub_le_of_holderNorm_zero_le ha0 (hkey w j hw) hz hz'
  -- ## Assembly
  have hunit : ∀ u : Work.NN.Core.Cn n, u ≠ 0 → ‖(‖u‖)⁻¹ • u‖ ≤ 1 := by
    intro u hu
    have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg u)]
    exact le_of_eq (inv_mul_cancel₀ (ne_of_gt hpos))
  refine ⟨?_, ?_⟩
  · intro z hz
    rw [ContinuousLinearMap.opNorm_le_iff ha0]
    intro u
    rcases eq_or_ne u 0 with rfl | hu
    · simp
    · have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu
      have h1 : ‖((fderiv ℝ A z) X) ((‖u‖)⁻¹ • u)‖ ≤ a := by
        rw [pi_norm_le_iff_of_nonneg ha0]
        intro j
        exact hsup ((‖u‖)⁻¹ • u) j (hunit u hu) z hz
      have h2 : ((fderiv ℝ A z) X) u
          = ‖u‖ • (((fderiv ℝ A z) X) ((‖u‖)⁻¹ • u)) := by
        conv_lhs => rw [← smul_inv_smul₀ (ne_of_gt hpos) u]
        rw [map_smul]
      calc ‖((fderiv ℝ A z) X) u‖
          = ‖u‖ * ‖((fderiv ℝ A z) X) ((‖u‖)⁻¹ • u)‖ := by
            rw [h2, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg u)]
        _ ≤ ‖u‖ * a := mul_le_mul_of_nonneg_left h1 (norm_nonneg u)
        _ = a * ‖u‖ := by ring
  · intro z hz z' hz'
    have hD : (0 : ℝ) ≤ ‖z - z'‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
    rw [ContinuousLinearMap.opNorm_le_iff (mul_nonneg ha0 hD)]
    intro u
    rcases eq_or_ne u 0 with rfl | hu
    · simp
    · have hpos : 0 < ‖u‖ := norm_pos_iff.mpr hu
      have h1 : ‖((fderiv ℝ A z) X - (fderiv ℝ A z') X) ((‖u‖)⁻¹ • u)‖
          ≤ a * ‖z - z'‖ ^ α := by
        rw [pi_norm_le_iff_of_nonneg (mul_nonneg ha0 hD)]
        intro j
        have hsub : (((fderiv ℝ A z) X - (fderiv ℝ A z') X) ((‖u‖)⁻¹ • u)) j
            = ((fderiv ℝ A z) X ((‖u‖)⁻¹ • u)) j
              - ((fderiv ℝ A z') X ((‖u‖)⁻¹ • u)) j := by
          simp [mul_sub]
        rw [hsub]
        exact hhol ((‖u‖)⁻¹ • u) j (hunit u hu) z hz z' hz'
      have h2 : ((fderiv ℝ A z) X - (fderiv ℝ A z') X) u
          = ‖u‖ • (((fderiv ℝ A z) X - (fderiv ℝ A z') X) ((‖u‖)⁻¹ • u)) := by
        conv_lhs => rw [← smul_inv_smul₀ (ne_of_gt hpos) u]
        rw [map_smul]
      calc ‖((fderiv ℝ A z) X - (fderiv ℝ A z') X) u‖
          = ‖u‖ * ‖((fderiv ℝ A z) X - (fderiv ℝ A z') X) ((‖u‖)⁻¹ • u)‖ := by
            rw [h2, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg u)]
        _ ≤ ‖u‖ * (a * ‖z - z'‖ ^ α) := mul_le_mul_of_nonneg_left h1 (norm_nonneg u)
        _ = (a * ‖z - z'‖ ^ α) * ‖u‖ := by ring

end Work.NN.Newton.Defect
