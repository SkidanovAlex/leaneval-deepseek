import Mathlib
import Submission.Work.Drive.cappingProjCoords

/-!
# The differential of `z ↦ confProjVecOf u z` kills only the direction `0`

`Work.Drive.confProjVecOf u d = (u · √(1 - ‖d‖²/2), ū · d/√2)` is the sphere lift of a configuration
point of the capping (see `Submission/Work/Drive/cappingProjCoords`).  For `‖u‖ = 1` and
`1 - ‖d‖²/2 > 0` the map `z ↦ confProjVecOf u z` is a smooth immersion: its differential at `d` is
never radial, so the only direction in which the image can move along the line `ℝ · confProjVecOf u d`
is `0`.

The proof is short once the right two derivatives are isolated.

* The image always lies on the unit sphere (`confProjVecOf u ·` has norm `1` as long as the square
  root is real, i.e. `‖·‖ ≤ √2`), so `⟪confProjVecOf u d, d(confProjVecOf u ·)_d w⟫ = 0`; combined
  with `L w = λ • confProjVecOf u d` this forces `λ = 0` because `‖confProjVecOf u d‖ = 1`.
* The *second* complex coordinate `c₂` is linear in `z` (`c₂ (confProjVecOf u z) = ū z/√2`), so the
  chain rule turns `L w = λ • confProjVecOf u d` into `w = λ d`; together with `λ = 0` this gives
  `w = 0`.

Both ingredients are expressed with `HasFDerivAt` chain rules (`HasFDerivAt.norm_sq` for the first,
the continuous linear map `c₂` for the second), so no explicit derivative of the square root is ever
needed — only that the map is differentiable at `d`, which holds because `1 - ‖d‖²/2 ≠ 0`.
-/

namespace Work.Drive

open scoped Topology

noncomputable section

/-- Smoothness of the complex-coordinate embedding `(z, z') ↦ ofComplex z z'`: it is the `ℝ`-linear
identification of `ℂ²` with `ℝ⁴ = Eucl 3`, so composing smooth complex-valued maps with it is
smooth. -/
lemma confProjVecOf_contDiffAt_ofComplex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : E → ℂ} {x : E} {n : WithTop ℕ∞}
    (ha : ContDiffAt ℝ n a x) (hb : ContDiffAt ℝ n b x) :
    ContDiffAt ℝ n (fun w => ofComplex (a w) (b w)) x := by
  rw [contDiffAt_piLp]
  intro i
  fin_cases i
  · simp only [ofComplex, WithLp.ofLp_toLp]
    exact (Complex.reCLM.contDiff.contDiffAt).comp x ha
  · simp only [ofComplex, WithLp.ofLp_toLp]
    exact (Complex.imCLM.contDiff.contDiffAt).comp x ha
  · simp only [ofComplex, WithLp.ofLp_toLp]
    exact (Complex.reCLM.contDiff.contDiffAt).comp x hb
  · simp only [ofComplex, WithLp.ofLp_toLp]
    exact (Complex.imCLM.contDiff.contDiffAt).comp x hb

/-- The second complex coordinate `c₂` as a continuous linear map `Eucl 3 →L[ℝ] ℂ`. -/
def confProjVecOf_c₂CLM : Eucl 3 →L[ℝ] ℂ :=
  (Complex.equivRealProdCLM : ℂ ≃L[ℝ] ℝ × ℝ).symm.toContinuousLinearMap.comp
    ((PiLp.proj 2 (fun _ : Fin 4 => ℝ) (2 : Fin 4)).prod
      (PiLp.proj 2 (fun _ : Fin 4 => ℝ) (3 : Fin 4)))

@[simp] lemma confProjVecOf_c₂CLM_apply (v : Eucl 3) : confProjVecOf_c₂CLM v = c₂ v := by
  show Complex.equivRealProdCLM.symm (v.ofLp 2, v.ofLp 3) = _
  simp only [c₂, Complex.equivRealProdCLM_symm_apply]

/-- `confProjVecOf u z` is a unit vector whenever the square root `√(1 - ‖z‖²/2)` is real, i.e. for
`‖z‖ ≤ √2` (the hypothesis used by `Work.Drive.norm_confProjVecOf` is the special case `‖z‖ ≤ 1`). -/
lemma norm_sq_confProjVecOf_of_nonneg {u : ℂ} (hu : ‖u‖ = 1) {z : ℂ}
    (hz : 0 ≤ 1 - ‖z‖ ^ 2 / 2) : ‖confProjVecOf u z‖ ^ 2 = 1 := by
  have h := norm_sq_c₁_c₂ (confProjVecOf u z)
  rw [c₁_confProjVecOf, c₂_confProjVecOf] at h
  have h1 : ‖u * ((Real.sqrt (1 - ‖z‖ ^ 2 / 2) : ℝ) : ℂ)‖ ^ 2 = 1 - ‖z‖ ^ 2 / 2 := by
    rw [norm_mul, hu, one_mul, Complex.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hz]
  have h3 : ‖star u * z / ((Real.sqrt 2 : ℝ) : ℂ)‖ ^ 2 = ‖z‖ ^ 2 / 2 := by
    rw [norm_div, norm_mul, norm_star, hu, one_mul, div_pow]
    have h2 : ‖((Real.sqrt 2 : ℝ) : ℂ)‖ ^ 2 = 2 := by
      rw [Complex.norm_of_nonneg (Real.sqrt_nonneg 2), Real.sq_sqrt (by norm_num)]
    rw [h2]
  rw [h1, h3] at h
  linarith

theorem confProjVecOf_fderiv_span {u : ℂ} (hu : ‖u‖ = 1) {d : ℂ}
    (hd : 0 < 1 - ‖d‖ ^ 2 / 2) {w : ℂ}
    (hw : fderiv ℝ (fun z : ℂ => Work.Drive.confProjVecOf u z) d w
      ∈ Submodule.span ℝ ({Work.Drive.confProjVecOf u d} : Set (Work.Drive.Eucl 3))) :
    w = 0 := by
  have hd2 : ‖d‖ ^ 2 < 2 := by nlinarith
  set v : Eucl 3 := confProjVecOf u d with hv
  set Lv : ℂ →L[ℝ] Eucl 3 := fderiv ℝ (fun z : ℂ => confProjVecOf u z) d with hLv
  -- differentiability of `z ↦ confProjVecOf u z` at `d`
  have hdiff : DifferentiableAt ℝ (fun z : ℂ => confProjVecOf u z) d := by
    have hnorm2 : ContDiffAt ℝ (1 : WithTop ℕ∞) (fun z : ℂ => ‖z‖ ^ 2) d :=
      (contDiff_norm_sq ℝ (E := ℂ) (n := (1 : WithTop ℕ∞))).contDiffAt
    have hinner : ContDiffAt ℝ (1 : WithTop ℕ∞) (fun z : ℂ => 1 - ‖z‖ ^ 2 / 2) d :=
      contDiffAt_const.sub (hnorm2.div_const 2)
    have hsq : ContDiffAt ℝ (1 : WithTop ℕ∞) (fun z : ℂ => Real.sqrt (1 - ‖z‖ ^ 2 / 2)) d :=
      (Real.contDiffAt_sqrt (ne_of_gt hd)).comp d hinner
    have h1 : ContDiffAt ℝ (1 : WithTop ℕ∞)
        (fun z : ℂ => u * ((Real.sqrt (1 - ‖z‖ ^ 2 / 2) : ℝ) : ℂ)) d :=
      contDiffAt_const.mul ((Complex.ofRealCLM.contDiff.contDiffAt).comp d hsq)
    have h2 : ContDiffAt ℝ (1 : WithTop ℕ∞)
        (fun z : ℂ => star u * z / ((Real.sqrt 2 : ℝ) : ℂ)) d :=
      (contDiffAt_const.mul contDiffAt_id).div_const _
    have hconf : ContDiffAt ℝ (1 : WithTop ℕ∞) (fun z : ℂ => confProjVecOf u z) d := by
      have := confProjVecOf_contDiffAt_ofComplex h1 h2
      simpa only [confProjVecOf] using this
    exact hconf.differentiableAt (by norm_num)
  have hfd : HasFDerivAt (fun z : ℂ => confProjVecOf u z) Lv d := by
    rw [hLv]; exact hdiff.hasFDerivAt
  -- `‖confProjVecOf u ·‖²` is `1` on a neighbourhood of `d`
  have hlt : ∀ᶠ z in 𝓝 d, ‖z‖ ^ 2 < 2 :=
    (isOpen_lt (continuous_norm.pow 2) continuous_const).mem_nhds hd2
  have hconst : (fun z : ℂ => ‖confProjVecOf u z‖ ^ 2) =ᶠ[𝓝 d] (fun _ => (1 : ℝ)) := by
    filter_upwards [hlt] with z hz
    exact norm_sq_confProjVecOf_of_nonneg hu (by linarith)
  have hv1 : ‖v‖ ^ 2 = 1 := by rw [hv]; exact hconst.eq_of_nhds
  have hP0 : fderiv ℝ (fun z : ℂ => ‖confProjVecOf u z‖ ^ 2) d = 0 := by
    rw [hconst.fderiv_eq]; simp
  have hdercomp : fderiv ℝ (fun z : ℂ => ‖confProjVecOf u z‖ ^ 2) d
      = ((2 : ℕ) • innerSL ℝ v) ∘SL Lv := by
    rw [hLv, hv]; exact hfd.norm_sq.fderiv
  -- the differential is tangent to the unit sphere
  have hperp : ∀ y : ℂ, inner ℝ v (Lv y) = 0 := by
    intro y
    have h : (((2 : ℕ) • innerSL ℝ v) ∘SL Lv) y = 0 := by
      rw [← hdercomp, hP0]; simp
    simp only [ContinuousLinearMap.comp_apply, smul_apply] at h
    rw [innerSL_apply_apply, two_nsmul] at h
    linarith
  -- the second coordinate of the differential
  let G : ℂ →L[ℝ] ℂ := ((Real.sqrt 2 : ℝ)⁻¹) • ContinuousLinearMap.mul ℝ ℂ (star u)
  have hG_apply : ∀ z : ℂ, G z = star u * z / ((Real.sqrt 2 : ℝ) : ℂ) := by
    intro z
    change (((Real.sqrt 2 : ℝ)⁻¹) • ContinuousLinearMap.mul ℝ ℂ (star u)) z = _
    rw [smul_apply, show (ContinuousLinearMap.mul ℝ ℂ (star u)) z = star u * z from by simp,
      Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
    ring
  have hc2 : ∀ y : ℂ, c₂ (Lv y) = star u * y / ((Real.sqrt 2 : ℝ) : ℂ) := by
    intro y
    have hcomp : HasFDerivAt (fun z : ℂ => confProjVecOf_c₂CLM (confProjVecOf u z))
        (confProjVecOf_c₂CLM.comp Lv) d :=
      confProjVecOf_c₂CLM.hasFDerivAt.comp d hfd
    have hfun : (fun z : ℂ => confProjVecOf_c₂CLM (confProjVecOf u z))
        = fun z : ℂ => star u * z / ((Real.sqrt 2 : ℝ) : ℂ) := by
      funext z; rw [confProjVecOf_c₂CLM_apply, c₂_confProjVecOf]
    have hcomp' : HasFDerivAt (fun z : ℂ => star u * z / ((Real.sqrt 2 : ℝ) : ℂ))
        (confProjVecOf_c₂CLM.comp Lv) d :=
      hcomp.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hfun.symm)
    have hGder : HasFDerivAt (fun z : ℂ => star u * z / ((Real.sqrt 2 : ℝ) : ℂ)) G d :=
      G.hasFDerivAt.congr_of_eventuallyEq
        (Filter.EventuallyEq.of_eq (funext (fun z => (hG_apply z).symm)))
    have hLG : confProjVecOf_c₂CLM.comp Lv = G := hcomp'.fderiv.symm.trans hGder.fderiv
    have h2 : confProjVecOf_c₂CLM (Lv y) = G y := by
      rw [← ContinuousLinearMap.comp_apply, hLG]
    rw [← confProjVecOf_c₂CLM_apply (Lv y), h2, hG_apply]
  -- the hypothesis gives `Lv w = lam • v`
  rcases Submodule.mem_span_singleton.mp hw with ⟨lam, hlam⟩
  have hc2w : lam • (star u * d / ((Real.sqrt 2 : ℝ) : ℂ))
      = star u * w / ((Real.sqrt 2 : ℝ) : ℂ) := by
    have h1 : c₂ (Lv w) = star u * w / ((Real.sqrt 2 : ℝ) : ℂ) := hc2 w
    rw [← confProjVecOf_c₂CLM_apply, ← hlam, map_smul, confProjVecOf_c₂CLM_apply, hv,
      c₂_confProjVecOf] at h1
    exact h1
  have hsu : star u ≠ 0 := by
    intro h0
    have : ‖u‖ = 0 := by rw [← norm_star, h0, norm_zero]
    rw [hu] at this; norm_num at this
  have hw_eq : w = (lam : ℂ) * d := by
    have hr : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; exact ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    rw [Complex.real_smul] at hc2w
    have h3 : (lam : ℂ) * (star u * d) = star u * w := by
      have h := congrArg (fun z : ℂ => z * ((Real.sqrt 2 : ℝ) : ℂ)) hc2w
      rw [mul_assoc, div_mul_cancel₀ _ hr, div_mul_cancel₀ _ hr] at h
      exact h
    have h2 : star u * w = star u * ((lam : ℂ) * d) := by rw [← h3]; ring
    exact mul_left_cancel₀ hsu h2
  have hlam0 : lam = 0 := by
    have h1 := hperp w
    rw [← hlam] at h1
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq, hv1, mul_one] at h1
    exact h1
  rw [hw_eq, hlam0]; simp

end

end Work.Drive
