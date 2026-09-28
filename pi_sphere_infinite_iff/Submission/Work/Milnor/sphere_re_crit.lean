import Mathlib
import Submission.Work.Milnor.sphere_re_defs

/-!
# The critical points of `Re : S³ → ℝ`

Milnor's Morse function on `M_k = (D⁴ × S³) ∪_f (D⁴ × S³)` restricts on each fibre to (a conjugate
of) the function `z ↦ Re z` on the unit quaternions.  Its critical points on `S³` are exactly
`±1`, which is the content of this file:

`sphere_re_crit : mfderiv 𝓘(ℝ,ℝ³) 𝓘(ℝ,ℝ) (fun z : S³ => (z : ℍ).re) y = 0 ↔ y = ±1`.

The proof computes the manifold derivative through the stereographic chart at `y`
(`chartAt E3 y = stereographic' 3 (-y)`) and Mathlib's explicit formula for the inverse
stereographic projection (`stereographic'_symm_apply`).  Everything reduces to the linear isometry
`chartLin y : E3 →ₗᵢ[ℝ] ℍ` whose image is the orthogonal complement `(ℝ ∙ y)ᗮ ≈ T_y S³`:
the derivative at `0` of the chart expression is `qreCLM ∘ chartLin y`, and that linear map
vanishes exactly when the real-part functional vanishes on `(ℝ ∙ y)ᗮ`, i.e. when `y = ±1`.
-/

open scoped Manifold ContDiff Topology RealInnerProductSpace
open Metric (sphere)
open TopologicalSpace Set

namespace Work.Milnor

noncomputable section

/-! ### The manifold derivative of a function on `S³` through the chart at the point -/

lemma sphere_re_crit_aux_writtenInExtChartAt (y : Submission.Milnor.QS3) (f : Submission.Milnor.QS3 → ℝ) :
    writtenInExtChartAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) y f
      = fun w : E3 => f ((chartAt E3 y).symm w) := by
  ext w
  simp [writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend, chartAt_self_eq]

lemma sphere_re_crit_aux_extChartAt_apply (y : Submission.Milnor.QS3) :
    (extChartAt 𝓘(ℝ, E3) y) y = 0 := by
  have h : ⇑(extChartAt 𝓘(ℝ, E3) y) = ⇑(chartAt E3 y) := by
    ext z; simp [extChartAt, OpenPartialHomeomorph.extend]
  rw [h, show chartAt E3 y = stereographic' 3 (-y) from rfl]
  simp only [stereographic', OpenPartialHomeomorph.trans_apply, stereographic_neg_apply,
    LinearIsometryEquiv.coe_toHomeomorph, Homeomorph.toOpenPartialHomeomorph_apply, map_zero]

lemma sphere_re_crit_aux_range : Set.range (𝓘(ℝ, E3)) = Set.univ := by
  rw [modelWithCornersSelf_coe ℝ E3]
  exact Set.range_id

/-- The manifold derivative of a function `S³ → ℝ` at `y` is the ordinary derivative at `0` of
the same function written in the chart at `y`. -/
lemma sphere_re_crit_aux_mfderiv_eq_fderiv (y : Submission.Milnor.QS3) :
    mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun z : Submission.Milnor.QS3 => (z : Quaternion ℝ).re) y
      = fderiv ℝ (fun w : E3 =>
          (((chartAt E3 y).symm w : Submission.Milnor.QS3) : Quaternion ℝ).re) 0 := by
  have hmd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ)
      (fun z : Submission.Milnor.QS3 => (z : Quaternion ℝ).re) y := by
    have h : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞
        (fun z : Submission.Milnor.QS3 => (z : Quaternion ℝ).re) :=
      (ContinuousLinearMap.contMDiff (n := ∞) (𝕜 := ℝ) qreCLM).comp contMDiff_coe_sphere
    exact h.mdifferentiableAt (by simp)
  rw [hmd.mfderiv]
  rw [sphere_re_crit_aux_writtenInExtChartAt]
  rw [sphere_re_crit_aux_range, fderivWithin_univ]
  rw [sphere_re_crit_aux_extChartAt_apply]
  all_goals first | rfl | (ext v; rfl)

/-! ### The chart expression of the real part -/

/-- The real part of the inverse stereographic chart at `y`, in closed form. -/
lemma sphere_re_crit_aux_chart_symm (y : Submission.Milnor.QS3) (w : E3) :
    (((chartAt E3 y).symm w : Submission.Milnor.QS3) : Quaternion ℝ).re =
      (‖w‖ ^ 2 + 4)⁻¹ *
        (4 * (chartLin y w).re + 4 * (y : Quaternion ℝ).re -
          (y : Quaternion ℝ).re * ‖w‖ ^ 2) := by
  have hneg : (((-y : Submission.Milnor.QS3) : Quaternion ℝ)).re
      = -((y : Quaternion ℝ)).re := by
    rw [show ((-y : Submission.Milnor.QS3) : Quaternion ℝ) = -(y : Quaternion ℝ) from rfl,
      Quaternion.re_neg]
  rw [show chartAt E3 y = stereographic' 3 (-y) from rfl, stereographic'_symm_apply]
  simp only [Quaternion.re_add, Quaternion.re_smul, smul_eq_mul]
  rw [hneg, chartLin_apply]
  unfold chartLinEquiv
  have hn : ‖(↑((OrthonormalBasis.fromOrthogonalSpanSingleton 3
      (ne_zero_of_mem_unit_sphere (-y))).repr.symm w) : Quaternion ℝ)‖ = ‖w‖ := by
    rw [← Submodule.coe_norm]
    exact ((OrthonormalBasis.fromOrthogonalSpanSingleton 3
      (ne_zero_of_mem_unit_sphere (-y))).repr.symm).norm_map w
  rw [hn]
  ring

/-- The derivative of the chart expression of the real part, at the centre of the chart. -/
lemma sphere_re_crit_aux_fderiv (y : Submission.Milnor.QS3)
    (h : (fun w : E3 => (((chartAt E3 y).symm w : Submission.Milnor.QS3) : Quaternion ℝ).re)
          = fun w : E3 =>
              (‖w‖ ^ 2 + 4)⁻¹ * (4 * (chartLin y w).re + 4 * (y : Quaternion ℝ).re
                - (y : Quaternion ℝ).re * ‖w‖ ^ 2)) :
    fderiv ℝ (fun w : E3 =>
        (((chartAt E3 y).symm w : Submission.Milnor.QS3) : Quaternion ℝ).re) 0 =
      qreCLM.comp (chartLin y).toContinuousLinearMap := by
  rw [h]
  set L : E3 →L[ℝ] ℝ := qreCLM.comp (chartLin y).toContinuousLinearMap
  have hL : HasFDerivAt (fun w : E3 => (chartLin y w).re) L 0 := by
    have hf : (⇑L : E3 → ℝ) = fun w => (chartLin y w).re := by
      funext w
      simp [L, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap]
    have h := ContinuousLinearMap.hasFDerivAt L (x := 0)
    rw [hf] at h
    exact h
  have hn : HasFDerivAt (fun w : E3 => ‖w‖ ^ 2) (0 : E3 →L[ℝ] ℝ) (0 : E3) := by
    have h := (hasFDerivAt_id (0 : E3)).norm_sq
    simpa using h
  have hden : HasFDerivAt (fun w : E3 => (‖w‖ ^ 2 + 4)⁻¹) (0 : E3 →L[ℝ] ℝ) (0 : E3) := by
    have h1 : HasFDerivAt (fun w : E3 => ‖w‖ ^ 2 + 4) (0 : E3 →L[ℝ] ℝ) 0 := by
      simpa using hn.const_add (4 : ℝ)
    have h2 : HasFDerivAt (fun t : ℝ => t⁻¹)
        (ContinuousLinearMap.toSpanSingleton ℝ (-((‖(0 : E3)‖ ^ 2 + 4 : ℝ) ^ 2)⁻¹))
        (‖(0 : E3)‖ ^ 2 + 4 : ℝ) :=
      hasFDerivAt_inv (by norm_num : (‖(0 : E3)‖ ^ 2 + 4 : ℝ) ≠ 0)
    have h5 := HasFDerivAt.comp (0 : E3) h2 h1
    rw [ContinuousLinearMap.comp_zero] at h5
    exact h5
  have hnum : HasFDerivAt
      (fun w : E3 => 4 * (chartLin y w).re + 4 * (y : Quaternion ℝ).re
        - (y : Quaternion ℝ).re * ‖w‖ ^ 2) ((4 : ℝ) • L) 0 := by
    have h1 : HasFDerivAt (fun w : E3 => 4 * (chartLin y w).re) ((4 : ℝ) • L) 0 :=
      hL.const_mul 4
    have h2 : HasFDerivAt (fun _ : E3 => 4 * (y : Quaternion ℝ).re) (0 : E3 →L[ℝ] ℝ) 0 :=
      hasFDerivAt_const (4 * (y : Quaternion ℝ).re) 0
    have h3 : HasFDerivAt (fun w : E3 => (y : Quaternion ℝ).re * ‖w‖ ^ 2)
        ((y : Quaternion ℝ).re • (0 : E3 →L[ℝ] ℝ)) 0 := hn.const_mul _
    have h4 := (h1.add h2).sub h3
    have hd : ((4 : ℝ) • L + (0 : E3 →L[ℝ] ℝ)
        - ((y : Quaternion ℝ).re • (0 : E3 →L[ℝ] ℝ))) = (4 : ℝ) • L := by
      simp
    exact h4.congr_fderiv hd
  have hmain : HasFDerivAt (fun w : E3 => (‖w‖ ^ 2 + 4)⁻¹ *
      (4 * (chartLin y w).re + 4 * (y : Quaternion ℝ).re - (y : Quaternion ℝ).re * ‖w‖ ^ 2))
      ((‖(0 : E3)‖ ^ 2 + 4)⁻¹ • ((4 : ℝ) • L)
        + (4 * (y : Quaternion ℝ).re) • (0 : E3 →L[ℝ] ℝ)) 0 := by
    have hm := hden.mul hnum
    have hd : ((‖(0 : E3)‖ ^ 2 + 4)⁻¹ • ((4 : ℝ) • L)
          + (4 * (chartLin y 0).re + 4 * (y : Quaternion ℝ).re
              - (y : Quaternion ℝ).re * ‖(0 : E3)‖ ^ 2) • (0 : E3 →L[ℝ] ℝ))
        = ((‖(0 : E3)‖ ^ 2 + 4)⁻¹ • ((4 : ℝ) • L)
          + (4 * (y : Quaternion ℝ).re) • (0 : E3 →L[ℝ] ℝ)) := by
      simp
    exact hm.congr_fderiv hd
  rw [hmain.fderiv]
  ext v
  simp only [add_apply, smul_apply, smul_eq_mul, zero_apply, mul_zero, add_zero]
  rw [show (‖(0 : E3)‖ ^ 2 + 4 : ℝ)⁻¹ = (4 : ℝ)⁻¹ by norm_num, ← mul_assoc,
    inv_mul_cancel₀ (by norm_num : (4 : ℝ) ≠ 0), one_mul]

/-! ### Vanishing of `qreCLM ∘ chartLin y` -/

lemma sphere_re_crit_aux_clm_zero_iff (y : Submission.Milnor.QS3) :
    qreCLM.comp (chartLin y).toContinuousLinearMap = 0 ↔
      ∀ w : E3, (chartLin y w).re = 0 := by
  constructor
  · intro h w
    have := congrArg (fun L : E3 →L[ℝ] ℝ => L w) h
    simpa using this
  · intro h
    ext w
    simpa using h w

/-- `z ↦ (chartLin y w).re` vanishes identically exactly at the two critical points `±1`. -/
lemma sphere_re_crit_aux_chartLin_re_zero (y : Submission.Milnor.QS3) :
    (∀ w : E3, (chartLin y w).re = 0) ↔
      (y : Quaternion ℝ) = 1 ∨ (y : Quaternion ℝ) = -1 := by
  have hyy : ⟪(y : Quaternion ℝ), (y : Quaternion ℝ)⟫ = 1 := by
    rw [Quaternion.inner_self, Quaternion.normSq_eq_norm_mul_self, Submission.Milnor.norm_coe]
    norm_num
  have hy1 : ⟪(y : Quaternion ℝ), (1 : Quaternion ℝ)⟫ = (y : Quaternion ℝ).re := by
    rw [Quaternion.inner_def, star_one, mul_one]
  constructor
  · intro h
    have hz : (1 - (y : Quaternion ℝ).re • (y : Quaternion ℝ)) ∈
        (ℝ ∙ ((-y : Submission.Milnor.QS3) : Quaternion ℝ))ᗮ := by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      rw [show ((-y : Submission.Milnor.QS3) : Quaternion ℝ) = -(y : Quaternion ℝ) from rfl,
        inner_neg_left, inner_sub_right, inner_smul_right, hy1, hyy]
      ring
    obtain ⟨w, hw⟩ := chartLin_surj y hz
    have h0 : (1 - (y : Quaternion ℝ).re • (y : Quaternion ℝ)).re = 0 := by
      rw [← hw, h w]
    have hred : (1 - (y : Quaternion ℝ).re • (y : Quaternion ℝ)).re
        = 1 - (y : Quaternion ℝ).re * (y : Quaternion ℝ).re := by
      simp [Quaternion.re_sub, Quaternion.re_smul, smul_eq_mul, Quaternion.re_one]
    have hre : (y : Quaternion ℝ).re ^ 2 = 1 := by
      rw [hred] at h0
      nlinarith [h0]
    have hnorm : ‖(y : Quaternion ℝ) - (y : Quaternion ℝ).re • (1 : Quaternion ℝ)‖ ^ 2 = 0 := by
      rw [norm_sub_sq_real, inner_smul_right, hy1, ← real_inner_self_eq_norm_sq, hyy,
        norm_smul, norm_one, mul_one, Real.norm_eq_abs, sq_abs]
      nlinarith [hre]
    have hzero : (y : Quaternion ℝ) - (y : Quaternion ℝ).re • (1 : Quaternion ℝ) = 0 := by
      have h1 : ‖(y : Quaternion ℝ) - (y : Quaternion ℝ).re • (1 : Quaternion ℝ)‖ = 0 :=
        (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hnorm
      exact norm_eq_zero.mp h1
    have hyeq : (y : Quaternion ℝ) = (y : Quaternion ℝ).re • (1 : Quaternion ℝ) :=
      sub_eq_zero.mp hzero
    rcases sq_eq_one_iff.mp hre with hc | hc
    · left; rw [hyeq, hc, one_smul]
    · right; rw [hyeq, hc, neg_smul, one_smul]
  · rintro (hy | hy) w
    · have hmem := chartLin_mem y w
      have h1 : ((-y : Submission.Milnor.QS3) : Quaternion ℝ) = -(1 : Quaternion ℝ) := by
        rw [show ((-y : Submission.Milnor.QS3) : Quaternion ℝ) = -(y : Quaternion ℝ) from rfl, hy]
      rw [h1] at hmem
      have h2 : ⟪chartLin y w, -(1 : Quaternion ℝ)⟫ = 0 :=
        Submodule.mem_orthogonal_singleton_iff_inner_left.mp hmem
      have hq : ⟪chartLin y w, -(1 : Quaternion ℝ)⟫ = -(chartLin y w).re := by
        rw [Quaternion.inner_def, star_neg, star_one, mul_neg, mul_one, Quaternion.re_neg]
      rw [hq] at h2
      linarith
    · have hmem := chartLin_mem y w
      have h1 : ((-y : Submission.Milnor.QS3) : Quaternion ℝ) = (1 : Quaternion ℝ) := by
        rw [show ((-y : Submission.Milnor.QS3) : Quaternion ℝ) = -(y : Quaternion ℝ) from rfl, hy]
        simp
      rw [h1] at hmem
      have h2 : ⟪chartLin y w, (1 : Quaternion ℝ)⟫ = 0 :=
        Submodule.mem_orthogonal_singleton_iff_inner_left.mp hmem
      have hq : ⟪chartLin y w, (1 : Quaternion ℝ)⟫ = (chartLin y w).re := by
        rw [Quaternion.inner_def, star_one, mul_one]
      rw [hq] at h2
      exact h2

/-! ### The main theorem -/

theorem sphere_re_crit (y : Submission.Milnor.QS3) :
    mfderiv (modelWithCornersSelf ℝ E3) (modelWithCornersSelf ℝ ℝ)
        (fun z : Submission.Milnor.QS3 => (z : Quaternion ℝ).re) y = 0 ↔
      (y : Quaternion ℝ) = 1 ∨ (y : Quaternion ℝ) = -1 := by
  have hformula : (fun w : E3 =>
          (((chartAt E3 y).symm w : Submission.Milnor.QS3) : Quaternion ℝ).re)
        = fun w : E3 =>
            (‖w‖ ^ 2 + 4)⁻¹ * (4 * (chartLin y w).re + 4 * (y : Quaternion ℝ).re
              - (y : Quaternion ℝ).re * ‖w‖ ^ 2) :=
    funext (fun w => sphere_re_crit_aux_chart_symm y w)
  rw [sphere_re_crit_aux_mfderiv_eq_fderiv y, sphere_re_crit_aux_fderiv y hformula]
  exact (sphere_re_crit_aux_clm_zero_iff y).trans (sphere_re_crit_aux_chartLin_re_zero y)

end

end Work.Milnor
