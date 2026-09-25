import Mathlib
import Submission.Work.NN.Core.fiberBeurling
import Submission.Work.CR.Flat.Cauchy
import Submission.Work.NN.Core.fiberPot
import Submission.Work.NN.Core.fiberPot_eq_cauchyTransform
import Submission.Work.NN.Core.fiberPot_dbarCoord_self
import Submission.Work.CR.Flat.Cauchy.holderNorm_one_disc

noncomputable section

open scoped NNReal ENNReal Topology
open Set MeasureTheory Filter

namespace Work.NN.Core

namespace DCoordFiberPot

/-- The insertion map `t ↦ Function.update y j t` is affine with derivative the `j`-th
standard basis map `ContinuousLinearMap.single`. -/
lemma hasFDerivAt_update_value {n : ℕ} (j : Fin n) (y : Cn n) (w : ℂ) :
    HasFDerivAt (fun t : ℂ => Function.update y j t)
      (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j) w := by
  have hfun : (fun t : ℂ => Function.update y j t)
      = fun t : ℂ => Function.update y j 0
          + (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j) t := by
    funext v
    rw [ContinuousLinearMap.single_apply]
    ext i
    by_cases h : i = j <;> simp [h]
  rw [hfun]
  exact (ContinuousLinearMap.hasFDerivAt
    (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j) (x := w)).const_add
      (Function.update y j 0)

/-- `ContinuousLinearMap.single` evaluated at a point is `Pi.single`. -/
lemma single_apply_eq_pi {n : ℕ} (j : Fin n) (t : ℂ) :
    (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j) t = Pi.single j t :=
  congrFun (ContinuousLinearMap.single_apply ℝ (fun _ : Fin n => ℂ) j) t

/-- The `(1,0)`-derivative of the `j`-th slice is the `j`-th `(1,0)`-derivative of the
function. -/
lemma dzC_slice_eq_dCoord {n : ℕ} (j : Fin n) {g : Cn n → ℂ} {y : Cn n}
    (hg : DifferentiableAt ℝ g y) :
    Work.CR.Flat.dzC (fun t : ℂ => g (Function.update y j t)) (y j)
      = Work.CR.Flat.dCoord j g y := by
  have hg' : DifferentiableAt ℝ g (Function.update y j (y j)) := by
    rwa [Function.update_eq_self]
  have hfd : fderiv ℝ (fun t : ℂ => g (Function.update y j t)) (y j)
      = (fderiv ℝ g y).comp (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j) := by
    have h := (hg'.hasFDerivAt.comp (y j) (hasFDerivAt_update_value j y (y j))).fderiv
    simpa [Function.update_eq_self, Function.comp_def] using h
  unfold Work.CR.Flat.dzC Work.CR.Flat.dCoord
  rw [hfd]
  simp only [ContinuousLinearMap.comp_apply, single_apply_eq_pi]

/-- The coordinatewise insertion map is `C¹`. -/
lemma contDiff_mem_update {n : ℕ} (j : Fin n) (z : Cn n) :
    ContDiff ℝ 1 (fun w : ℂ => Function.update z j w) := by
  have hfun : (fun w : ℂ => Function.update z j w)
      = fun w : ℂ => Function.update z j 0
          + (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j) w := by
    funext v
    rw [ContinuousLinearMap.single_apply]
    ext i
    by_cases h : i = j <;> simp [h]
  rw [hfun]
  exact contDiff_const.add
    (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j : ℂ →L[ℝ] (Cn n)).contDiff

/-- The slice of a `C¹` function in one coordinate is `C¹`. -/
lemma contDiff_fiberSlice {n : ℕ} (j : Fin n) {v : Cn n → ℂ} (hv : ContDiff ℝ 1 v)
    (z : Cn n) : ContDiff ℝ 1 (fiberSlice j v z) :=
  hv.comp (contDiff_mem_update j z)

/-- The slice does not depend on the value of the `j`-th coordinate of the base point. -/
lemma fiberSlice_update {n : ℕ} (j : Fin n) (v : Cn n → ℂ) (z : Cn n) (ζ : ℂ) :
    fiberSlice j v (Function.update z j ζ) = fiberSlice j v z := by
  funext w
  simp only [fiberSlice_apply]
  rw [Function.update_idem]

/-- The fixed-disc potential of `C¹` data is differentiable at every point of the disc
`‖z j‖ < R`.  The proof cuts the data in the fibre variable around `z j`: the piece supported
away from the moving singularity is smooth by differentiation under the integral sign, and the
complementary piece has its singularity shielded by the vanishing of the data. -/
lemma differentiableAt_fiberPot_self {n : ℕ} {R : ℝ} (hR : 0 < R) (j : Fin n) {v : Cn n → ℂ}
    (hv : ContDiff ℝ 1 v) {z : Cn n} (hz : ‖z j‖ < R) :
    DifferentiableAt ℝ (fiberPot R j v) z := by
  set δ : ℝ := (R - ‖z j‖) / 10 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have h3δnn : 0 ≤ 3 * δ := by linarith
  have h36 : 3 * δ < 6 * δ := by linarith
  have hρR : ‖z j‖ + 6 * δ < R := by rw [hδdef]; linarith
  have hρnn : 0 ≤ 6 * δ := by linarith
  have hc_cd : ContDiff ℝ 1 (sharpCut (3 * δ) (6 * δ)) := contDiff_one_of_sharpCut
  have hc_supp : ∀ ζ : ℂ, 6 * δ ≤ ‖ζ‖ → sharpCut (3 * δ) (6 * δ) ζ = 0 :=
    fun ζ hζ => sharpCut_eq_zero h3δnn h36 hζ
  set v₁ : Cn n → ℂ := fun y => v y * sharpCut (3 * δ) (6 * δ) (y j - z j) with hv1
  set v₂ : Cn n → ℂ := fun y => v y * (1 - sharpCut (3 * δ) (6 * δ) (y j - z j)) with hv2
  have hsum : ∀ y : Cn n, v₁ y + v₂ y = v y := by
    intro y; rw [hv1, hv2]; ring
  have hv1_cont : Continuous v₁ := by
    rw [hv1]
    exact hv.continuous.mul (hc_cd.continuous.comp ((continuous_apply j).sub continuous_const))
  have hv2_cont : Continuous v₂ := by
    rw [hv2]
    exact hv.continuous.mul
      (continuous_const.sub (hc_cd.continuous.comp ((continuous_apply j).sub continuous_const)))
  have hv2_cd : ContDiff ℝ 1 v₂ := by
    rw [hv2]
    exact hv.mul (contDiff_const.sub (hc_cd.comp (contDiff_one_apply_sub j z)))
  have hsplit : fiberPot R j v = fun y => fiberPot R j v₁ y + fiberPot R j v₂ y := by
    funext y
    have h := fiberPot_add R j hv1_cont hv2_cont y
    rw [show (fun y => v₁ y + v₂ y) = v from funext hsum] at h
    exact h
  have h1 : DifferentiableAt ℝ (fiberPot R j v₁) z := by
    rw [hv1]
    exact differentiableAt_fiberPot_cut R j hv hc_cd hρnn hc_supp (by linarith)
  have hvan : ∀ y : Cn n, ‖y - z‖ < δ → ∀ w : ℂ, ‖w - y j‖ < δ →
      v₂ (Function.update y j w) = 0 := by
    intro y hy w hw
    simp only [hv2]
    rw [Function.update_self]
    have hc1 : sharpCut (3 * δ) (6 * δ) (w - z j) = 1 := by
      apply sharpCut_eq_one h3δnn h36
      have h1 : ‖w - z j‖ ≤ ‖w - y j‖ + ‖y j - z j‖ := by
        calc ‖w - z j‖ = ‖(w - y j) + (y j - z j)‖ := by ring_nf
          _ ≤ ‖w - y j‖ + ‖y j - z j‖ := norm_add_le _ _
      have h2 : ‖y j - z j‖ ≤ ‖y - z‖ := norm_le_pi_norm (y - z) j
      linarith
    rw [hc1]; ring
  have h2 : DifferentiableAt ℝ (fiberPot R j v₂) z :=
    (fiberPot_dbarCoord_eq_zero R hR j hv2_cd hδpos hvan).1
  rw [hsplit]
  exact h1.add h2

end DCoordFiberPot

/-- The `(1,0)`-derivative of the fixed-disc potential in the fibre direction is the fibrewise Beurling transform: differentiating `fiberPot R j v z = cauchyTransform (2R) (fiberSlice j v z) (z j)` with respect to `z j` (the slice does not depend on `z j`, since `Function.update z j w` does not depend on `z j`) and using `dzC (cauchyTransform ρ f) = beurlingTransform ρ f` (library `dzC_cauchyTransform`, with `ρ = 2R`, support of the slice in `ball 0 R` from `hband`, and `‖z j‖ < R` from `hz`). -/
theorem dCoord_fiberPot_self {n : ℕ} {R : ℝ} (hR : 0 < R) (j : Fin n) {v : Cn n → ℂ}
    (hv : ContDiff ℝ 1 v) (hband : fiberBand R j v) {z : Cn n} (hz : ‖z j‖ < R) :
    Work.CR.Flat.dCoord j (fiberPot R j v) z = fiberBeurling R j v z := by
  have hdiff : DifferentiableAt ℝ (fiberPot R j v) z := DCoordFiberPot.differentiableAt_fiberPot_self hR j hv hz
  have hv0 : ContDiff ℝ 0 v := hv.of_le (by norm_num)
  have hpos : 0 < R - ‖z j‖ := by linarith
  -- along the fibre through `z` the potential is the Cauchy transform of the slice
  have hev : (fun ζ : ℂ => fiberPot R j v (Function.update z j ζ)) =ᶠ[𝓝 (z j)]
      (fun ζ : ℂ => Work.CR.Flat.cauchyTransform (2 * R) (fiberSlice j v z) ζ) := by
    filter_upwards [Metric.ball_mem_nhds (z j) hpos] with ζ hζ
    rw [Metric.mem_ball, dist_eq_norm] at hζ
    have hζR : ‖ζ‖ < R := by
      have h1 : ‖ζ‖ ≤ ‖ζ - z j‖ + ‖z j‖ := by
        have h := norm_add_le (ζ - z j) (z j); simpa using h
      linarith
    rw [fiberPot_eq_cauchyTransform (z := Function.update z j ζ) hR j hv0 hband
      (by rwa [Function.update_self]), DCoordFiberPot.fiberSlice_update j v z ζ, Function.update_self]
  -- `∂_z` does not see the difference along the fibre
  have hdzC : Work.CR.Flat.dzC (fun ζ : ℂ => fiberPot R j v (Function.update z j ζ)) (z j)
      = Work.CR.Flat.dzC
          (fun ζ : ℂ => Work.CR.Flat.cauchyTransform (2 * R) (fiberSlice j v z) ζ) (z j) := by
    unfold Work.CR.Flat.dzC
    rw [hev.fderiv_eq]
  -- the support of the slice in `ball 0 R`
  have hsupp : Work.CR.Flat.SupportedInBall (2 * R / 2) (fiberSlice j v z) := by
    intro w hw
    rw [fiberSlice_apply]
    refine hband _ ?_
    rw [Function.update_self]
    linarith
  have hdzC_cauchy : Work.CR.Flat.dzC
        (fun ζ : ℂ => Work.CR.Flat.cauchyTransform (2 * R) (fiberSlice j v z) ζ) (z j)
      = fiberBeurling R j v z :=
    Work.CR.Flat.Cauchy.dzC_cauchyTransform (ρ := 2 * R) (by linarith)
      (DCoordFiberPot.contDiff_fiberSlice j hv z) hsupp (by linarith)
  calc Work.CR.Flat.dCoord j (fiberPot R j v) z
      = Work.CR.Flat.dzC (fun ζ : ℂ => fiberPot R j v (Function.update z j ζ)) (z j) :=
        (DCoordFiberPot.dzC_slice_eq_dCoord j hdiff).symm
    _ = Work.CR.Flat.dzC
          (fun ζ : ℂ => Work.CR.Flat.cauchyTransform (2 * R) (fiberSlice j v z) ζ) (z j) := hdzC
    _ = fiberBeurling R j v z := hdzC_cauchy

end Work.NN.Core
