import Submission.FUP.DbarConv

open MeasureTheory Metric Filter Function
open scoped ENNReal BigOperators ContDiff

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# The transfer of the weak `∂̄₂`-relation under convolution

If `x ∈ Dom S` with `S x = ζ`, then the convolution `ρ * x` is in `Dom S` with `S (ρ*x) = ρ*ζ`:
the operator `∂̄₂` has constant coefficients, so it commutes with convolution.  The proof uses the
pairing identity `inner_convFun_eq` together with the *covariant translation invariance* of the
formal adjoint `ϑ₂` (`dbarAdjoint2_shiftForm2`).
-/

namespace Submission.FUP

variable {d : ℕ}

/-- The `liftForm`-level form of the covariant translation invariance of `ϑ₂`. -/
lemma liftForm_dbarAdjoint2_shiftForm2 {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 2 φ)
    {Ψ : FormDu d → FormSpace2 d} (hΨ : ∀ i, ContDiff ℝ ∞ (fun z => Ψ z i))
    (y z : FormDu d) :
    liftForm (dbarAdjoint2 φ (toFormFun2 (shiftForm2 φ y Ψ))) z
      = covShift φ y z • liftForm (dbarAdjoint2 φ (toFormFun2 Ψ)) (z + y) := by
  have hfun : dbarAdjoint2 φ (toFormFun2 (shiftForm2 φ y Ψ)) z
      = fun j => covShift φ y z * dbarAdjoint2 φ (toFormFun2 Ψ) (z + y) j :=
    funext fun j => dbarAdjoint2_shiftForm2 hφ hΨ y z j
  dsimp only [liftForm]
  rw [hfun]
  rw [show (fun j => covShift φ y z * dbarAdjoint2 φ (toFormFun2 Ψ) (z + y) j)
      = covShift φ y z • (dbarAdjoint2 φ (toFormFun2 Ψ) (z + y)) from rfl,
    WithLp.toLp_smul]

/-- **Convolution commutes with the weak `∂̄₂`.** -/
theorem dbarWeak2_conv {φ : FormDu d → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {x : H2 φ} {ζ : H3 φ} (hζ : DbarWeak2 φ x ζ)
    {ρ : FormDu d → ℝ} (hρc : Continuous ρ) (hρs : HasCompactSupport ρ)
    (hxloc : LocallyIntegrable (x : FormDu d → FormSpace d) (volume : Measure (FormDu d)))
    (hζloc : LocallyIntegrable (ζ : FormDu d → FormSpace2 d) (volume : Measure (FormDu d)))
    (hxρ : MemLp (convFun ρ (x : FormDu d → FormSpace d)) 2 (wtMeasure φ))
    (hζρ : MemLp (convFun ρ (ζ : FormDu d → FormSpace2 d)) 2 (wtMeasure φ)) :
    DbarWeak2 φ (hxρ.toLp (convFun ρ (x : FormDu d → FormSpace d)))
      (hζρ.toLp (convFun ρ (ζ : FormDu d → FormSpace2 d))) := by
  intro Ψ h1 h2 hΨ hθ
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  -- the `(0,1)`-form `ϑ₂Ψ`
  have hϑc : Continuous (liftForm (dbarAdjoint2 φ (toFormFun2 Ψ))) :=
    continuous_liftForm (continuous_dbarAdjoint2
      (fun i => (contDiff_toFormFun2 h1 i).of_le (WithTop.coe_le_coe.mpr le_top))
      (Complex.ofRealCLM.contDiff.comp hφ1))
  have hϑs : HasCompactSupport (liftForm (dbarAdjoint2 φ (toFormFun2 Ψ))) :=
    hasCompactSupport_liftForm (hasCompactSupport_dbarAdjoint2 (hasCompactSupport_toFormFun2 h2))
  rw [inner_toLp_eq_integral hΨ hζρ, inner_toLp_eq_integral hθ hxρ]
  rw [inner_convFun_eq hφ.continuous h1.continuous h2 hζloc hρc hρs
      (integrable_uncurry_inner_conv hφ.continuous h1.continuous h2 hζloc hρc hρs),
    inner_convFun_eq hφ.continuous hϑc hϑs hxloc hρc hρs
      (integrable_uncurry_inner_conv hφ.continuous hϑc hϑs hxloc hρc hρs)]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  dsimp only
  congr 1
  -- the weak relation tested against the covariantly shifted test form
  have h1y : ContDiff ℝ ∞ (shiftForm2 φ y Ψ) := contDiff_shiftForm2 hφ h1
  have h2y : HasCompactSupport (shiftForm2 φ y Ψ) := hasCompactSupport_shiftForm2 h2
  have hmemy : MemLp (shiftForm2 φ y Ψ) 2 (wtMeasure φ) :=
    memLp_wtMeasure_of_contDiff_hasCompactSupport hφ.continuous h1y h2y
  have hϑy : MemLp (liftForm (dbarAdjoint2 φ (toFormFun2 (shiftForm2 φ y Ψ))))
      2 (wtMeasure φ) :=
    memLp_dbarAdjoint2 hφ1 (fun i => (contDiff_toFormFun2 h1y i).of_le
      (WithTop.coe_le_coe.mpr le_top)) (hasCompactSupport_toFormFun2 h2y)
  have hrel := hζ (shiftForm2 φ y Ψ) h1y h2y hmemy hϑy
  rw [← Lp.toLp_coeFn ζ (Lp.memLp ζ), ← Lp.toLp_coeFn x (Lp.memLp x)] at hrel
  rw [inner_toLp_eq_integral hmemy (Lp.memLp ζ),
    inner_toLp_eq_integral hϑy (Lp.memLp x)] at hrel
  refine hrel.trans ?_
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  dsimp only
  congr 1
  exact liftForm_dbarAdjoint2_shiftForm2 hφ2 (contDiff_toFormFun2 h1) y z


/-! ## Helper calculus lemmas for the `ϑ_φ`-side transfer -/

/-- `∂̄_j` commutes with translation. -/
lemma partialZbar_comp_add (j : Fin d) (g : FormDu d → ℂ) (y z : FormDu d) :
    partialZbar j (fun w => g (w + y)) z = partialZbar j g (z + y) := by
  simp only [partialZbar, fderiv_comp_add_right]

/-- `∂̄_j` of the phase factor. -/
lemma partialZbar_covShift {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 2 φ) {y z : FormDu d}
    (j : Fin d) :
    partialZbar j (fun w => covShift φ y w) z
      = covShift φ y z * (partialZbar j (fun w => ((φ w : ℝ) : ℂ)) z
          - partialZbar j (fun w => ((φ w : ℝ) : ℂ)) (z + y)) := by
  have hΦ : (fun w : FormDu d => ((φ w : ℝ) : ℂ)) = toC (fun w => φ w) := rfl
  have hL : star (partialZbar j (fun w => covShift φ y w) z)
      = covShift φ y z * (partialZ j (fun w => ((φ w : ℝ) : ℂ)) z
          - partialZ j (fun w => ((φ w : ℝ) : ℂ)) (z + y)) := by
    rw [star_partialZbar j (fun w => covShift φ y w) z,
      show (fun w => star (covShift φ y w)) = fun w => covShift φ y w from
        funext fun w => star_covShift φ y w,
      partialZ_covShift hφ (y := y) (z := z) j]
  have hconj : ∀ v : FormDu d, star (partialZbar j (fun w => ((φ w : ℝ) : ℂ)) v)
      = partialZ j (fun w => ((φ w : ℝ) : ℂ)) v := by
    intro v
    have h := star_partialZbar j (fun w => ((φ w : ℝ) : ℂ)) v
    rw [show (fun w => star (((φ w : ℝ) : ℂ))) = fun w => ((φ w : ℝ) : ℂ) from
      funext fun w => by rw [Complex.star_def, Complex.conj_ofReal]] at h
    exact h
  have hR : star (covShift φ y z * (partialZbar j (fun w => ((φ w : ℝ) : ℂ)) z
        - partialZbar j (fun w => ((φ w : ℝ) : ℂ)) (z + y)))
      = covShift φ y z * (partialZ j (fun w => ((φ w : ℝ) : ℂ)) z
          - partialZ j (fun w => ((φ w : ℝ) : ℂ)) (z + y)) := by
    rw [star_mul, star_sub, star_covShift, hconj z, hconj (z + y)]
    ring
  apply star_injective
  rw [hL, hR]

/-- The Leibniz rule together with the covariant shift: the `∂̄_j` of
`w ↦ covShift φ y w * f (w + y)`. -/
lemma partialZbar_covShift_mul {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 2 φ)
    {f : FormDu d → ℂ} (hf : ∀ w, DifferentiableAt ℝ f w) (y z : FormDu d) (j : Fin d) :
    partialZbar j (fun w => covShift φ y w * f (w + y)) z
      = covShift φ y z * (partialZbar j f (z + y)
          + f (z + y) * partialZbar j (fun w => ((φ w : ℝ) : ℂ)) z
          - f (z + y) * partialZbar j (fun w => ((φ w : ℝ) : ℂ)) (z + y)) := by
  have hcd : DifferentiableAt ℝ (fun w : FormDu d => covShift φ y w) z := by
    have hc : ContDiff ℝ 2 fun v : FormDu d => covShift φ y v := by
      unfold covShift
      exact Complex.contDiff_exp.comp
        ((Complex.ofRealCLM.contDiff.comp hφ).sub
          ((Complex.ofRealCLM.contDiff.comp hφ).comp (contDiff_id.add contDiff_const)))
    exact hc.differentiable (by norm_num) z
  have hfd : DifferentiableAt ℝ (fun w : FormDu d => f (w + y)) z :=
    (hf (z + y)).comp z (differentiableAt_id.add (differentiableAt_const y))
  rw [partialZbar_mul hcd hfd j, partialZbar_covShift hφ (y := y) (z := z) j,
    partialZbar_comp_add j f y z]
  ring

/-! ## The covariant shift of test functions and the defect form -/

section ConvShift

/-- The covariantly shifted test function `ψ_y(w) = e^{φ(w) - φ(w+y)} f(w+y)`. -/
noncomputable def shiftFun (φ : FormDu d → ℝ) (y : FormDu d) (f : FormDu d → ℂ) :
    FormDu d → ℂ :=
  fun w => covShift φ y w * f (w + y)

@[simp] lemma shiftFun_apply (φ : FormDu d → ℝ) (y : FormDu d) (f : FormDu d → ℂ)
    (w : FormDu d) : shiftFun φ y f w = covShift φ y w * f (w + y) := rfl

lemma hasCompactSupport_comp_add {f : FormDu d → ℂ} (hf : HasCompactSupport f) (y : FormDu d) :
    HasCompactSupport (fun w : FormDu d => f (w + y)) := by
  have h1 := hf.comp_homeomorph (Homeomorph.addRight y)
  simpa only [Function.comp_def, Homeomorph.coe_addRight] using h1

lemma hasCompactSupport_shiftFun {φ : FormDu d → ℝ} {y : FormDu d} {f : FormDu d → ℂ}
    (hf : HasCompactSupport f) : HasCompactSupport (shiftFun φ y f) := by
  have h : HasCompactSupport (fun w => f (w + y)) := hasCompactSupport_comp_add hf y
  exact h.mul_left

lemma contDiff_covShift {φ : FormDu d → ℝ} {n : WithTop ℕ∞} (hφ : ContDiff ℝ n φ)
    (y : FormDu d) : ContDiff ℝ n (fun w => covShift φ y w) := by
  unfold covShift
  refine Complex.contDiff_exp.comp ?_
  exact (Complex.ofRealCLM.contDiff.comp hφ).sub
    ((Complex.ofRealCLM.contDiff.comp hφ).comp (contDiff_id.add contDiff_const))

lemma continuous_covShift {φ : FormDu d → ℝ} (hφ : Continuous φ) (y : FormDu d) :
    Continuous (fun w => covShift φ y w) := by
  unfold covShift
  exact Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp hφ).sub
      ((Complex.continuous_ofReal.comp hφ).comp (continuous_id.add continuous_const)))

lemma contDiff_shiftFun {φ : FormDu d → ℝ} {n : WithTop ℕ∞} (hφ : ContDiff ℝ n φ)
    {f : FormDu d → ℂ} (hf : ContDiff ℝ n f) (y : FormDu d) :
    ContDiff ℝ n (shiftFun φ y f) :=
  (contDiff_covShift hφ y).mul (hf.comp (contDiff_id.add contDiff_const))

lemma continuous_shiftFun {φ : FormDu d → ℝ} (hφ : Continuous φ) {f : FormDu d → ℂ}
    (hf : Continuous f) (y : FormDu d) : Continuous (shiftFun φ y f) :=
  (continuous_covShift hφ y).mul (hf.comp (continuous_id.add continuous_const))

/-- Conjugation of `∂̄_j` of a real function: `conj (∂̄_jΦ) = ∂_jΦ`. -/
lemma star_partialZbar_toC (φ : FormDu d → ℝ) (j : Fin d) (z : FormDu d) :
    star (partialZbar j (toC φ) z) = partialZ j (toC φ) z := by
  have h := star_partialZbar j (toC φ) z
  rw [show (fun w => star (toC φ w)) = toC φ from funext fun w => by
    simp only [toC_apply, Complex.star_def, Complex.conj_ofReal]] at h
  exact h

lemma partialZbar_shiftFun {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 2 φ) {f : FormDu d → ℂ}
    (hf : ContDiff ℝ ∞ f) (y w : FormDu d) (j : Fin d) :
    partialZbar j (shiftFun φ y f) w
      = covShift φ y w * (partialZbar j f (w + y) + f (w + y) * partialZbar j (toC φ) w
          - f (w + y) * partialZbar j (toC φ) (w + y)) :=
  partialZbar_covShift_mul hφ (fun v => hf.differentiable (by norm_num) v) y w j

/-- The defect `(0,1)`-form of the covariant shift. -/
noncomputable def shiftDefectForm (φ : FormDu d → ℝ) (y : FormDu d) (f : FormDu d → ℂ) :
    FormDu d → FormSpace d :=
  liftForm (fun w j => covShift φ y w
    * (f (w + y) * (partialZbar j (toC φ) w - partialZbar j (toC φ) (w + y))))

@[simp] lemma shiftDefectForm_apply (φ : FormDu d → ℝ) (y w : FormDu d) (f : FormDu d → ℂ)
    (j : Fin d) : shiftDefectForm φ y f w j = covShift φ y w
      * (f (w + y) * (partialZbar j (toC φ) w - partialZbar j (toC φ) (w + y))) := rfl

lemma dbarFormFun_shiftFun {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 2 φ) {f : FormDu d → ℂ}
    (hf : ContDiff ℝ ∞ f) (y w : FormDu d) :
    dbarFormFun (shiftFun φ y f) w
      = covShift φ y w • dbarFormFun f (w + y) + shiftDefectForm φ y f w := by
  have hfun : (fun j => partialZbar j (shiftFun φ y f) w)
      = fun j => covShift φ y w * (partialZbar j f (w + y) + f (w + y) * partialZbar j (toC φ) w
          - f (w + y) * partialZbar j (toC φ) (w + y)) :=
    funext fun j => partialZbar_shiftFun hφ hf y w j
  have hsplit : (fun j => covShift φ y w * (partialZbar j f (w + y)
        + f (w + y) * partialZbar j (toC φ) w
        - f (w + y) * partialZbar j (toC φ) (w + y)))
      = covShift φ y w • (fun j => partialZbar j f (w + y))
        + fun j => covShift φ y w
            * (f (w + y) * (partialZbar j (toC φ) w - partialZbar j (toC φ) (w + y))) := by
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [show dbarFormFun (shiftFun φ y f) w
      = WithLp.toLp 2 (fun j => partialZbar j (shiftFun φ y f) w) from rfl,
    hfun, hsplit, WithLp.toLp_add, WithLp.toLp_smul]
  rfl

lemma continuous_partialZbar_toC {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 2 φ) (j : Fin d) :
    Continuous (partialZbar j (toC φ)) :=
  continuous_partialZbar (contDiff_toC (hφ.of_le (by norm_num))) j

lemma continuous_shiftDefectForm {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 2 φ) {f : FormDu d → ℂ}
    (hf : ContDiff ℝ ∞ f) (y : FormDu d) : Continuous (shiftDefectForm φ y f) := by
  have hcov : Continuous (fun w : FormDu d => covShift φ y w) := continuous_covShift hφ.continuous y
  have hff : Continuous (fun w : FormDu d => f (w + y)) :=
    hf.continuous.comp (continuous_id.add continuous_const)
  have hcont : ∀ j : Fin d, Continuous (fun w : FormDu d => covShift φ y w
      * (f (w + y) * (partialZbar j (toC φ) w - partialZbar j (toC φ) (w + y)))) := fun j =>
    hcov.mul (hff.mul (((continuous_partialZbar_toC hφ j)).sub
      ((continuous_partialZbar_toC hφ j).comp (continuous_id.add continuous_const))))
  rw [show shiftDefectForm φ y f = liftForm (fun w j => covShift φ y w
      * (f (w + y) * (partialZbar j (toC φ) w - partialZbar j (toC φ) (w + y)))) from rfl]
  exact continuous_liftForm (continuous_pi hcont)

lemma hasCompactSupport_shiftDefectForm {φ : FormDu d → ℝ} {y : FormDu d} {f : FormDu d → ℂ}
    (hf : HasCompactSupport f) : HasCompactSupport (shiftDefectForm φ y f) := by
  have h : HasCompactSupport (fun w : FormDu d => f (w + y)) := hasCompactSupport_comp_add hf y
  refine h.mono' fun w hw => ?_
  have h1 : f (w + y) ≠ 0 := by
    intro h0
    exact hw (PiLp.ext fun j => by simp [shiftDefectForm_apply, h0])
  exact subset_tsupport _ h1

/-- The real-smul / complex-multiplication bridge on `ℂ`. -/
lemma real_smul_eq_mul' (r : ℝ) (z : ℂ) : r • z = (r : ℂ) * z := Complex.real_smul

lemma ofReal_exp_neg_mul_covShift (φ : FormDu d → ℝ) (y w : FormDu d) :
    (((Real.exp (-(φ w)) : ℝ)) : ℂ) * covShift φ y w
      = (((Real.exp (-(φ (w + y))) : ℝ)) : ℂ) := by
  rw [covShift_apply, Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add]
  rw [show ((-(φ w) : ℝ) : ℂ) + (((φ w : ℝ) : ℂ) - ((φ (w + y) : ℝ) : ℂ))
      = ((-(φ (w + y)) : ℝ) : ℂ) by push_cast; ring]

/-- The pointwise splitting of the pairing of `∂̄ψ_y` against `X`. -/
lemma inner_shiftDefectForm (φ : FormDu d → ℝ) (y w : FormDu d) (f : FormDu d → ℂ)
    (X : FormDu d → FormSpace d) :
    inner ℂ (shiftDefectForm φ y f w) (X w)
      = (covShift φ y w * star (f (w + y)))
        * (∑ j : Fin d, star (partialZbar j (toC φ) w - partialZbar j (toC φ) (w + y))
            * X w j) := by
  rw [PiLp.inner_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [shiftDefectForm_apply, RCLike.inner_apply, starRingEnd_apply,
    star_mul, star_sub, star_covShift]
  ring

end ConvShift

/-! ## The defect of the `ϑ_φ`-side convolution -/

/-- The `(0,1)`-form defect measuring the failure of the ordinary convolution to commute with
`ϑ_φ` (whose coefficients `∂_jφ` are not constant):

  `dbarAdjDefect φ ρ X u = ∫ y, ρ y • ∑_j (∂_jφ(u-y) - ∂_jφ(u)) X_j (u-y) dy`.

Then `ϑ_φ (ρ * X) = ρ * (ϑ_φ X) - V_ρ`, i.e. `dbarAdjWeak φ (ρ*X) (ρ*z - V_ρ)` whenever
`dbarAdjWeak φ X z`. -/
noncomputable def dbarAdjDefectFun (φ : FormDu d → ℝ) (X : FormDu d → FormSpace d)
    (u y : FormDu d) : ℂ :=
  ∑ j : Fin d,
    (partialZ j (fun w => ((φ w : ℝ) : ℂ)) (u - y) - partialZ j (fun w => ((φ w : ℝ) : ℂ)) u)
      * X (u - y) j

noncomputable def dbarAdjDefect (φ : FormDu d → ℝ) (ρ : FormDu d → ℝ)
    (X : FormDu d → FormSpace d) : FormDu d → ℂ :=
  fun u => ∫ y, ρ y • dbarAdjDefectFun φ X u y

/-- The pointwise integrand of the defect identity for the `ϑ_φ`-side convolution. -/
noncomputable def defectPair (φ : FormDu d → ℝ) (f : FormDu d → ℂ) (ρ : FormDu d → ℝ)
    (X : FormDu d → FormSpace d) : FormDu d → FormDu d → ℂ :=
  fun u y => ((Real.exp (-(φ u)) : ℝ) : ℂ)
    * (star (f u) * (((ρ y : ℝ) : ℂ) * (∑ j : Fin d,
        (partialZ j (toC φ) (u - y) - partialZ j (toC φ) u) * (X (u - y) j))))

lemma integrable_defectPair {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 2 φ) {f : FormDu d → ℂ} (hfc : Continuous f)
    (hfs : HasCompactSupport f) {ρ : FormDu d → ℝ} (hρc : Continuous ρ)
    (hρs : HasCompactSupport ρ) {X : FormDu d → FormSpace d}
    (hX : LocallyIntegrable X (volume : Measure (FormDu d))) :
    Integrable (Function.uncurry (defectPair (d := d) φ f ρ X))
      ((volume : Measure (FormDu d)).prod (volume : Measure (FormDu d))) := by
  classical
  obtain ⟨Cf, hCf⟩ := hfs.exists_bound_of_continuousOn hfc.continuousOn
  obtain ⟨Cρ, hCρ⟩ := hρs.exists_bound_of_continuousOn hρc.continuousOn
  obtain ⟨CE, hCE⟩ := hfs.exists_bound_of_continuousOn
    (Real.continuous_exp.comp hφ.continuous.neg).continuousOn
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hΦ1 : ContDiff ℝ 1 (toC φ) := contDiff_toC hφ1
  have hcontZ : ∀ j : Fin d, Continuous (partialZ j (toC φ)) := fun j =>
    continuous_partialZ hΦ1 j
  have hcontΨ : Continuous (fun p : FormDu d × FormDu d =>
      ∑ j : Fin d, ‖partialZ j (toC φ) (p.1 - p.2) - partialZ j (toC φ) p.1‖) :=
    continuous_finsetSum (Finset.univ : Finset (Fin d)) fun j _ =>
      ((hcontZ j).comp (continuous_fst.sub continuous_snd)).sub
        ((hcontZ j).comp continuous_fst) |>.norm
  obtain ⟨CΨ, hCΨ⟩ := (hfs.isCompact.prod hρs.isCompact).exists_bound_of_continuousOn
    hcontΨ.continuousOn
  have hbase := Commons.MeasureTheory.integrable_indicator_prod_norm_sub (d := d)
    (E := FormSpace d) hX hfs.isCompact hρs.isCompact
  have hg := hbase.const_mul (CE * Cf * Cρ * CΨ)
  refine hg.mono' ?_ ?_
  · -- a.e. strong measurability
    have h1 : AEStronglyMeasurable
        (fun p : FormDu d × FormDu d => ((Real.exp (-(φ p.1)) : ℝ) : ℂ))
        ((volume : Measure (FormDu d)).prod (volume : Measure (FormDu d))) :=
      ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp hφ.continuous.neg)).comp
        continuous_fst).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun p : FormDu d × FormDu d => star (f p.1))
        ((volume : Measure (FormDu d)).prod (volume : Measure (FormDu d))) :=
      (hfc.star.comp continuous_fst).aestronglyMeasurable
    have h3 : AEStronglyMeasurable (fun p : FormDu d × FormDu d => ((ρ p.2 : ℝ) : ℂ))
        ((volume : Measure (FormDu d)).prod (volume : Measure (FormDu d))) :=
      ((Complex.continuous_ofReal.comp (hρc.comp continuous_snd))).aestronglyMeasurable
    have hq : Measure.QuasiMeasurePreserving (fun p : FormDu d × FormDu d => p.1 - p.2)
        ((volume : Measure (FormDu d)).prod (volume : Measure (FormDu d)))
        (volume : Measure (FormDu d)) :=
      ⟨measurable_fst.sub measurable_snd,
        Commons.Analysis.Convolution.map_sub_prod_absolutelyContinuous (E := FormDu d)⟩
    have hXc : AEStronglyMeasurable (fun p : FormDu d × FormDu d => X (p.1 - p.2))
        ((volume : Measure (FormDu d)).prod (volume : Measure (FormDu d))) :=
      hX.aestronglyMeasurable.comp_quasiMeasurePreserving hq
    have h4 : AEStronglyMeasurable
        (fun p : FormDu d × FormDu d => ∑ j : Fin d,
          (partialZ j (toC φ) (p.1 - p.2) - partialZ j (toC φ) p.1) * (X (p.1 - p.2) j))
        ((volume : Measure (FormDu d)).prod (volume : Measure (FormDu d))) := by
      have hsum : AEStronglyMeasurable
          (∑ j : Fin d, fun p : FormDu d × FormDu d =>
            (partialZ j (toC φ) (p.1 - p.2) - partialZ j (toC φ) p.1) * (X (p.1 - p.2) j))
          ((volume : Measure (FormDu d)).prod (volume : Measure (FormDu d))) :=
        Finset.aestronglyMeasurable_sum (Finset.univ : Finset (Fin d)) (fun j _ => by
          refine AEStronglyMeasurable.mul ?_ ?_
          · exact (((hcontZ j).comp (continuous_fst.sub continuous_snd)).sub
              ((hcontZ j).comp continuous_fst)).aestronglyMeasurable
          · have hX2 : AEMeasurable (fun p : FormDu d × FormDu d => X (p.1 - p.2))
                ((volume : Measure (FormDu d)).prod (volume : Measure (FormDu d))) :=
              hXc.aemeasurable
            exact (AEMeasurable.comp_aemeasurable
              (g := fun x : FormSpace d => x j) (by fun_prop) hX2).aestronglyMeasurable)
      refine hsum.congr ?_
      filter_upwards with p
      exact Finset.sum_apply p Finset.univ _
    exact h1.mul (h2.mul (h3.mul h4))
  · -- pointwise bound
    filter_upwards with p
    rcases p with ⟨u, y⟩
    simp only [Function.uncurry_apply_pair]
    by_cases hu : u ∈ tsupport f
    · by_cases hy : y ∈ tsupport ρ
      · rw [Set.indicator_of_mem (Set.mk_mem_prod hu hy)]
        have he : Real.exp (-(φ u)) ≤ CE := by
          have h := hCE u hu
          rwa [Function.comp_apply, Real.norm_of_nonneg (Real.exp_nonneg _)] at h
        have hf : ‖f u‖ ≤ Cf := hCf u hu
        have hρ : |ρ y| ≤ Cρ := hCρ y hy
        have hΨ : ∑ j : Fin d, ‖partialZ j (toC φ) (u - y) - partialZ j (toC φ) u‖ ≤ CΨ := by
          have h := hCΨ (u, y) (Set.mk_mem_prod hu hy)
          rwa [Real.norm_of_nonneg (Finset.sum_nonneg fun j _ => norm_nonneg _)] at h
        have hXj : ∀ j : Fin d, ‖X (u - y) j‖ ≤ ‖X (u - y)‖ := fun j => PiLp.norm_apply_le _ j
        have hsum : ‖∑ j : Fin d,
            (partialZ j (toC φ) (u - y) - partialZ j (toC φ) u) * (X (u - y) j)‖
            ≤ CΨ * ‖X (u - y)‖ := by
          refine (norm_sum_le _ _).trans ?_
          calc ∑ j : Fin d, ‖(partialZ j (toC φ) (u - y) - partialZ j (toC φ) u) * (X (u - y) j)‖
              ≤ ∑ j : Fin d,
                  ‖partialZ j (toC φ) (u - y) - partialZ j (toC φ) u‖ * ‖X (u - y)‖ := by
                refine Finset.sum_le_sum fun j _ => ?_
                rw [norm_mul]
                exact mul_le_mul_of_nonneg_left (hXj j) (norm_nonneg _)
            _ = (∑ j : Fin d, ‖partialZ j (toC φ) (u - y) - partialZ j (toC φ) u‖)
                  * ‖X (u - y)‖ := (Finset.sum_mul _ _ _).symm
            _ ≤ CΨ * ‖X (u - y)‖ := mul_le_mul_of_nonneg_right hΨ (norm_nonneg _)
        have henorm : ‖(((Real.exp (-(φ u)) : ℝ)) : ℂ)‖ = Real.exp (-(φ u)) := by
          rw [Complex.norm_def, Complex.normSq_ofReal, ← pow_two, Real.sqrt_sq_eq_abs,
            abs_of_nonneg (Real.exp_nonneg _)]
        have hρnorm : ‖(((ρ y : ℝ)) : ℂ)‖ = |ρ y| := by
          rw [Complex.norm_def, Complex.normSq_ofReal, ← pow_two, Real.sqrt_sq_eq_abs]
        have hnorm : ‖defectPair φ f ρ X u y‖
            = Real.exp (-(φ u)) * (‖f u‖ * (|ρ y| * ‖∑ j : Fin d,
                (partialZ j (toC φ) (u - y) - partialZ j (toC φ) u) * (X (u - y) j)‖)) := by
          simp only [defectPair, norm_mul, norm_star, henorm, hρnorm]
        rw [hnorm]
        have h1 : |ρ y| * ‖∑ j : Fin d,
              (partialZ j (toC φ) (u - y) - partialZ j (toC φ) u) * (X (u - y) j)‖
            ≤ Cρ * (CΨ * ‖X (u - y)‖) :=
          mul_le_mul hρ hsum (norm_nonneg _) (le_trans (abs_nonneg _) hρ)
        have h2 : ‖f u‖ * (|ρ y| * ‖∑ j : Fin d,
              (partialZ j (toC φ) (u - y) - partialZ j (toC φ) u) * (X (u - y) j)‖)
            ≤ Cf * (Cρ * (CΨ * ‖X (u - y)‖)) :=
          mul_le_mul hf h1 (mul_nonneg (abs_nonneg _) (norm_nonneg _))
            (le_trans (norm_nonneg _) hf)
        have h3 : Real.exp (-(φ u)) * (‖f u‖ * (|ρ y| * ‖∑ j : Fin d,
              (partialZ j (toC φ) (u - y) - partialZ j (toC φ) u) * (X (u - y) j)‖))
            ≤ CE * (Cf * (Cρ * (CΨ * ‖X (u - y)‖))) :=
          mul_le_mul he h2 (mul_nonneg (norm_nonneg _) (mul_nonneg (abs_nonneg _) (norm_nonneg _)))
            (le_trans (Real.exp_nonneg _) he)
        calc Real.exp (-(φ u)) * (‖f u‖ * (|ρ y| * ‖∑ j : Fin d,
              (partialZ j (toC φ) (u - y) - partialZ j (toC φ) u) * (X (u - y) j)‖))
            ≤ CE * (Cf * (Cρ * (CΨ * ‖X (u - y)‖))) := h3
          _ = CE * Cf * Cρ * CΨ * ‖X (u - y)‖ := by ring
      · have h : ((tsupport f ×ˢ tsupport ρ).indicator
            (fun p : FormDu d × FormDu d => ‖X (p.1 - p.2)‖)) (u, y) = 0 :=
          Set.indicator_of_notMem (fun hh => hy hh.2) _
        rw [h, mul_zero]
        have hρ0 : ρ y = 0 := image_eq_zero_of_notMem_tsupport hy
        simp [defectPair, hρ0]
    · have h : ((tsupport f ×ˢ tsupport ρ).indicator
          (fun p : FormDu d × FormDu d => ‖X (p.1 - p.2)‖)) (u, y) = 0 :=
        Set.indicator_of_notMem (fun hh => hu hh.1) _
      rw [h, mul_zero]
      have hf0 : f u = 0 := image_eq_zero_of_notMem_tsupport hu
      simp [defectPair, hf0]


theorem integral_defectPair_eq {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 2 φ)
    {f : FormDu d → ℂ} (hfc : Continuous f) (hfs : HasCompactSupport f)
    {ρ : FormDu d → ℝ} (hρc : Continuous ρ) (hρs : HasCompactSupport ρ)
    {X : FormDu d → FormSpace d} (hX : LocallyIntegrable X (volume : Measure (FormDu d))) :
    (∫ y, ρ y • (∫ w, inner ℂ (shiftDefectForm φ y f w) (X w) ∂(wtMeasure φ))
        ∂(volume : Measure (FormDu d)))
      = ∫ u, star (f u) * dbarAdjDefect φ ρ X u ∂(wtMeasure φ) := by
  have hInt := integrable_defectPair (d := d) hφ hfc hfs hρc hρs hX
  have hL : (∫ y, ρ y • (∫ w, inner ℂ (shiftDefectForm φ y f w) (X w) ∂(wtMeasure φ))
        ∂(volume : Measure (FormDu d)))
      = ∫ y, ∫ w, defectPair φ f ρ X (w + y) y ∂volume ∂volume := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only
    rw [← integral_smul (ρ y) (fun w => inner ℂ (shiftDefectForm φ y f w) (X w)),
      integral_wtMeasure hφ.continuous]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    dsimp only
    rw [inner_shiftDefectForm]
    simp only [real_smul_eq_mul']
    have h2 : (((Real.exp (-(φ w)) : ℝ)) : ℂ)
        * ((covShift φ y w * star (f (w + y)))
          * (∑ j : Fin d, star (partialZbar j (toC φ) w - partialZbar j (toC φ) (w + y))
              * X w j))
        = (((Real.exp (-(φ (w + y))) : ℝ)) : ℂ)
          * (star (f (w + y))
            * (∑ j : Fin d, star (partialZbar j (toC φ) w - partialZbar j (toC φ) (w + y))
                * X w j)) := by
      rw [mul_assoc (covShift φ y w), ← mul_assoc (((Real.exp (-(φ w)) : ℝ)) : ℂ),
        ofReal_exp_neg_mul_covShift φ y w]
    calc (((Real.exp (-(φ w)) : ℝ)) : ℂ)
          * (((ρ y : ℝ) : ℂ) * ((covShift φ y w * star (f (w + y)))
            * (∑ j : Fin d, star (partialZbar j (toC φ) w - partialZbar j (toC φ) (w + y))
                * X w j)))
        = ((ρ y : ℝ) : ℂ) * ((((Real.exp (-(φ w)) : ℝ)) : ℂ)
            * ((covShift φ y w * star (f (w + y)))
              * (∑ j : Fin d, star (partialZbar j (toC φ) w - partialZbar j (toC φ) (w + y))
                  * X w j))) := by ring
      _ = ((ρ y : ℝ) : ℂ) * ((((Real.exp (-(φ (w + y))) : ℝ)) : ℂ)
            * (star (f (w + y))
              * (∑ j : Fin d, star (partialZbar j (toC φ) w - partialZbar j (toC φ) (w + y))
                  * X w j))) := by rw [h2]
      _ = defectPair φ f ρ X (w + y) y := by
            simp only [defectPair, dbarAdjDefectFun, add_sub_cancel_right, star_sub,
              star_partialZbar_toC]
            ring
  have hR : (∫ u, star (f u) * dbarAdjDefect φ ρ X u ∂(wtMeasure φ))
      = ∫ u, ∫ y, defectPair φ f ρ X u y ∂volume ∂volume := by
    rw [integral_wtMeasure hφ.continuous]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp only
    rw [real_smul_eq_mul', dbarAdjDefect]
    have hA : star (f u) * (∫ y, ρ y • dbarAdjDefectFun φ X u y
          ∂(volume : Measure (FormDu d)))
        = ∫ y, star (f u) * (ρ y • dbarAdjDefectFun φ X u y)
          ∂(volume : Measure (FormDu d)) := by
      rw [show star (f u) * (∫ y, ρ y • dbarAdjDefectFun φ X u y
            ∂(volume : Measure (FormDu d)))
          = star (f u) • (∫ y, ρ y • dbarAdjDefectFun φ X u y
              ∂(volume : Measure (FormDu d))) from (smul_eq_mul (star (f u)) _).symm,
        ← integral_smul (μ := (volume : Measure (FormDu d))) (star (f u))]
      exact integral_congr_ae (Eventually.of_forall fun y => smul_eq_mul _ _)
    have hB : ((((Real.exp (-(φ u)) : ℝ)) : ℂ))
        * (∫ y, star (f u) * (ρ y • dbarAdjDefectFun φ X u y)
          ∂(volume : Measure (FormDu d)))
        = ∫ y, ((((Real.exp (-(φ u)) : ℝ)) : ℂ))
            * (star (f u) * (ρ y • dbarAdjDefectFun φ X u y))
          ∂(volume : Measure (FormDu d)) := by
      rw [show ((((Real.exp (-(φ u)) : ℝ)) : ℂ))
            * (∫ y, star (f u) * (ρ y • dbarAdjDefectFun φ X u y)
              ∂(volume : Measure (FormDu d)))
          = ((((Real.exp (-(φ u)) : ℝ)) : ℂ)) • (∫ y, star (f u)
              * (ρ y • dbarAdjDefectFun φ X u y)
              ∂(volume : Measure (FormDu d))) from
            (smul_eq_mul ((((Real.exp (-(φ u)) : ℝ)) : ℂ)) _).symm,
        ← integral_smul (μ := (volume : Measure (FormDu d)))
          (((Real.exp (-(φ u)) : ℝ)) : ℂ)]
      exact integral_congr_ae (Eventually.of_forall fun y => smul_eq_mul _ _)
    rw [hA, hB]
    exact integral_congr_ae (Eventually.of_forall fun y => by
      dsimp only
      rw [real_smul_eq_mul']
      rfl)
  have hswap := integral_integral_swap hInt
  have hsub : (∫ y, ∫ u, defectPair φ f ρ X u y ∂volume ∂volume)
      = ∫ y, ∫ w, defectPair φ f ρ X (w + y) y ∂volume ∂volume := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only
    exact (integral_add_right_eq_self (fun u => defectPair φ f ρ X u y) y).symm
  calc (∫ y, ρ y • (∫ w, inner ℂ (shiftDefectForm φ y f w) (X w) ∂(wtMeasure φ))
          ∂(volume : Measure (FormDu d)))
      = ∫ y, ∫ w, defectPair φ f ρ X (w + y) y ∂volume ∂volume := hL
    _ = ∫ y, ∫ u, defectPair φ f ρ X u y ∂volume ∂volume := hsub.symm
    _ = ∫ u, ∫ y, defectPair φ f ρ X u y ∂volume ∂volume := hswap.symm
    _ = ∫ u, star (f u) * dbarAdjDefect φ ρ X u ∂(wtMeasure φ) := hR.symm


/-! ## The `(0,1)`-side pairing integrands and the `ϑ_φ`-transfer -/

section Transfer

/-- The uncurried integrand of the `S`-part of the `ϑ_φ`-side convolution. -/
noncomputable def convPairS (φ : FormDu d → ℝ) (f : FormDu d → ℂ) (ρ : FormDu d → ℝ)
    (X : FormDu d → FormSpace d) : FormDu d × FormDu d → ℂ :=
  fun p => ((ρ p.1 : ℝ) : ℂ) * (((Real.exp (-(φ p.2)) : ℝ) : ℂ)
    * inner ℂ (shiftForm φ p.1 (dbarFormFun f) p.2) (X p.2))

/-- The uncurried integrand of the `D`-part of the `ϑ_φ`-side convolution. -/
noncomputable def convPairD (φ : FormDu d → ℝ) (f : FormDu d → ℂ) (ρ : FormDu d → ℝ)
    (X : FormDu d → FormSpace d) : FormDu d × FormDu d → ℂ :=
  fun p => ((ρ p.1 : ℝ) : ℂ) * (((Real.exp (-(φ p.2)) : ℝ) : ℂ)
    * inner ℂ (shiftDefectForm φ p.1 f p.2) (X p.2))

lemma star_inner_eq_inner_swap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (a b : E) : star (inner ℂ a b) = inner ℂ b a := inner_conj_symm b a

/-- A compact set is contained in a closed ball. -/
lemma exists_subset_closedBall_of_isCompact {K : Set (FormDu d)} (hK : IsCompact K) :
    ∃ R : ℝ, K ⊆ Metric.closedBall (0 : FormDu d) R := by
  rcases Set.eq_empty_or_nonempty K with h | ⟨x₀, hx₀⟩
  · exact ⟨0, by rw [h]; exact Set.empty_subset _⟩
  · obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp hK.isBounded
    refine ⟨C + dist x₀ 0, fun u hu => ?_⟩
    rw [Metric.mem_closedBall]
    calc dist u 0 ≤ dist u x₀ + dist x₀ 0 := dist_triangle _ _ _
      _ ≤ C + dist x₀ 0 := by linarith [hC hu hx₀]

/-- `Integrable` of the second-coordinate majorant cut off to a product of compacts. -/
lemma integrable_indicator_prod_norm_snd {K L : Set (FormDu d)} (hK : IsCompact K)
    (hL : IsCompact L) {X : FormDu d → FormSpace d} (hX : LocallyIntegrable X volume) :
    Integrable ((K ×ˢ L).indicator (fun q : FormDu d × FormDu d => ‖X q.2‖))
      ((volume : Measure (FormDu d)).prod (volume : Measure (FormDu d))) := by
  have h1 : Integrable (K.indicator (fun _ : FormDu d => (1 : ℝ))) volume := by
    rw [integrable_indicator_iff hK.isClosed.measurableSet]
    exact integrableOn_const (by simpa using hK.measure_lt_top.ne) (by simp)
  have h2 : Integrable (L.indicator (fun w => ‖X w‖)) volume := by
    rw [integrable_indicator_iff hL.isClosed.measurableSet]
    exact (hX.integrableOn_isCompact hL).norm
  refine (h1.mul_prod h2).congr (Filter.Eventually.of_forall fun p => ?_)
  obtain ⟨y, w⟩ := p
  dsimp only
  by_cases hp : (y, w) ∈ K ×ˢ L
  · obtain ⟨hy, hw⟩ := Set.mem_prod.mp hp
    simp only [Set.indicator_of_mem hp, Set.indicator_of_mem hy, Set.indicator_of_mem hw,
      one_mul]
  · have hzero : (K.indicator (fun _ : FormDu d => (1 : ℝ))) y
        * (L.indicator (fun w => ‖X w‖)) w = 0 := by
      by_cases hy : y ∈ K
      · have hw : w ∉ L := fun hw => hp (Set.mk_mem_prod hy hw)
        rw [Set.indicator_of_notMem hw, mul_zero]
      · rw [Set.indicator_of_notMem hy, zero_mul]
    rw [hzero, Set.indicator_of_notMem hp]

lemma norm_covShift (φ : FormDu d → ℝ) (y w : FormDu d) :
    ‖covShift φ y w‖ = Real.exp (φ w - φ (w + y)) := by
  rw [covShift_apply, Complex.norm_exp]
  simp

lemma continuous_toLp_formSpace {α : Type*} [TopologicalSpace α] {u : α → (Fin d → ℂ)}
    (hu : Continuous u) : Continuous (fun a => WithLp.toLp 2 (u a)) :=
  (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin d => ℂ)).comp hu

/-- Bound for the pairing of the shifted `∂̄f` against `X`. -/
lemma norm_inner_shiftForm_le (φ : FormDu d → ℝ) (f : FormDu d → ℂ)
    (X : FormDu d → FormSpace d) (y w : FormDu d) :
    ‖inner ℂ (shiftForm φ y (dbarFormFun f) w) (X w)‖
      ≤ (Real.exp (φ w - φ (w + y)) * ‖dbarFormFun f (w + y)‖)
        * ∑ j : Fin d, ‖X w j‖ := by
  rw [PiLp.inner_apply]
  calc ‖∑ j : Fin d, inner ℂ (shiftForm φ y (dbarFormFun f) w j) ((X w) j)‖
      ≤ ∑ j : Fin d, ‖inner ℂ (shiftForm φ y (dbarFormFun f) w j) ((X w) j)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ j : Fin d, ‖shiftForm φ y (dbarFormFun f) w j‖ * ‖(X w) j‖ :=
        Finset.sum_le_sum fun j _ => norm_inner_le_norm _ _
    _ = ∑ j : Fin d, (Real.exp (φ w - φ (w + y)) * ‖dbarFormFun f (w + y) j‖)
          * ‖(X w) j‖ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [show shiftForm φ y (dbarFormFun f) w j = covShift φ y w * dbarFormFun f (w + y) j
          from rfl, norm_mul, norm_covShift]
    _ ≤ ∑ j : Fin d, (Real.exp (φ w - φ (w + y)) * ‖dbarFormFun f (w + y)‖)
          * ‖(X w) j‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le _ j) (Real.exp_nonneg _)
    _ = (Real.exp (φ w - φ (w + y)) * ‖dbarFormFun f (w + y)‖)
          * ∑ j : Fin d, ‖X w j‖ := (Finset.mul_sum _ _ _).symm

/-- Bound for the pairing of the defect form against `X`. -/
lemma norm_inner_shiftDefectForm_le (φ : FormDu d → ℝ) (f : FormDu d → ℂ)
    (X : FormDu d → FormSpace d) (y w : FormDu d) {CΦ : ℝ}
    (hCΦ : ∀ j : Fin d,
      ‖partialZbar j (toC φ) w - partialZbar j (toC φ) (w + y)‖ ≤ CΦ) :
    ‖inner ℂ (shiftDefectForm φ y f w) (X w)‖
      ≤ (Real.exp (φ w - φ (w + y)) * ‖f (w + y)‖ * CΦ)
        * ∑ j : Fin d, ‖X w j‖ := by
  rw [PiLp.inner_apply]
  calc ‖∑ j : Fin d, inner ℂ (shiftDefectForm φ y f w j) ((X w) j)‖
      ≤ ∑ j : Fin d, ‖inner ℂ (shiftDefectForm φ y f w j) ((X w) j)‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin d, ‖shiftDefectForm φ y f w j‖ * ‖(X w) j‖ :=
        Finset.sum_le_sum fun j _ => norm_inner_le_norm _ _
    _ = ∑ j : Fin d, (Real.exp (φ w - φ (w + y)) * ‖f (w + y)‖
          * ‖partialZbar j (toC φ) w - partialZbar j (toC φ) (w + y)‖) * ‖(X w) j‖ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [shiftDefectForm_apply, norm_mul, norm_mul, norm_covShift]
        ring
    _ ≤ ∑ j : Fin d, (Real.exp (φ w - φ (w + y)) * ‖f (w + y)‖ * CΦ) * ‖(X w) j‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left (hCΦ j) (mul_nonneg (Real.exp_nonneg _) (norm_nonneg _))
    _ = (Real.exp (φ w - φ (w + y)) * ‖f (w + y)‖ * CΦ) * ∑ j : Fin d, ‖X w j‖ :=
        (Finset.mul_sum _ _ _).symm

/-- Bound for the sum of the components of a form by `d` times the norm. -/
lemma sum_norm_apply_le (d : ℕ) {x : FormSpace d} : ∑ j : Fin d, ‖x j‖ ≤ (d : ℝ) * ‖x‖ := by
  calc ∑ j : Fin d, ‖x j‖ ≤ ∑ _j : Fin d, ‖x‖ := Finset.sum_le_sum fun j _ => PiLp.norm_apply_le x j
    _ = (d : ℝ) * ‖x‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma continuous_convPairS {φ : FormDu d → ℝ} (hφ : Continuous φ) {f : FormDu d → ℂ}
    (hf : ContDiff ℝ ∞ f) {ρ : FormDu d → ℝ} (hρc : Continuous ρ)
    {X : FormDu d → FormSpace d} (hX : AEStronglyMeasurable X volume) :
    AEStronglyMeasurable (convPairS φ f ρ X)
      ((volume : Measure (FormDu d)).prod (volume : Measure (FormDu d))) := by
  have hcov : Continuous (fun p : FormDu d × FormDu d => covShift φ p.1 p.2) := by
    unfold covShift
    refine Complex.continuous_exp.comp ?_
    exact ((Complex.continuous_ofReal.comp (hφ.comp continuous_snd)).sub
      (Complex.continuous_ofReal.comp (hφ.comp (continuous_snd.add continuous_fst))))
  have hψ : Continuous (fun p : FormDu d × FormDu d => dbarFormFun f (p.2 + p.1)) :=
    (contDiff_dbarFormFun hf).continuous.comp (continuous_snd.add continuous_fst)
  have h1 : AEStronglyMeasurable (fun p : FormDu d × FormDu d => ((ρ p.1 : ℝ) : ℂ))
      ((volume : Measure (FormDu d)).prod (volume : Measure (FormDu d))) :=
    ((Complex.continuous_ofReal.comp (hρc.comp continuous_fst))).aestronglyMeasurable
  have h2 : AEStronglyMeasurable
      (fun p : FormDu d × FormDu d => ((Real.exp (-(φ p.2)) : ℝ) : ℂ))
      ((volume : Measure (FormDu d)).prod (volume : Measure (FormDu d))) :=
    ((Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (hφ.neg.comp continuous_snd)))).aestronglyMeasurable
  have h3 : AEStronglyMeasurable (fun p : FormDu d × FormDu d =>
      inner ℂ (shiftForm φ p.1 (dbarFormFun f) p.2) (X p.2))
      ((volume : Measure (FormDu d)).prod (volume : Measure (FormDu d))) :=
    ((hcov.smul hψ).aestronglyMeasurable).inner
      (hX.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  exact h1.mul (h2.mul h3)

lemma continuous_convPairD {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 2 φ) {f : FormDu d → ℂ}
    (hf : ContDiff ℝ ∞ f) {ρ : FormDu d → ℝ} (hρc : Continuous ρ)
    {X : FormDu d → FormSpace d} (hX : AEStronglyMeasurable X volume) :
    AEStronglyMeasurable (convPairD φ f ρ X)
      ((volume : Measure (FormDu d)).prod (volume : Measure (FormDu d))) := by
  have hcov : Continuous (fun p : FormDu d × FormDu d => covShift φ p.1 p.2) := by
    unfold covShift
    refine Complex.continuous_exp.comp ?_
    exact ((Complex.continuous_ofReal.comp (hφ.continuous.comp continuous_snd)).sub
      (Complex.continuous_ofReal.comp (hφ.continuous.comp (continuous_snd.add continuous_fst))))
  have hff : Continuous (fun p : FormDu d × FormDu d => f (p.2 + p.1)) :=
    hf.continuous.comp (continuous_snd.add continuous_fst)
  have hc1 : ∀ j : Fin d, Continuous (fun p : FormDu d × FormDu d => partialZbar j (toC φ) p.2) :=
    fun j => (continuous_partialZbar_toC hφ j).comp continuous_snd
  have hc2 : ∀ j : Fin d, Continuous (fun p : FormDu d × FormDu d =>
      partialZbar j (toC φ) (p.2 + p.1)) :=
    fun j => (continuous_partialZbar_toC hφ j).comp (continuous_snd.add continuous_fst)
  have hψD : Continuous (fun q : FormDu d × FormDu d => fun j : Fin d => covShift φ q.1 q.2
      * (f (q.2 + q.1) * (partialZbar j (toC φ) q.2 - partialZbar j (toC φ) (q.2 + q.1)))) :=
    continuous_pi fun j => hcov.mul (hff.mul ((hc1 j).sub (hc2 j)))
  have hD : Continuous (fun q : FormDu d × FormDu d => shiftDefectForm φ q.1 f q.2) := by
    rw [show (fun q : FormDu d × FormDu d => shiftDefectForm φ q.1 f q.2)
        = fun q => WithLp.toLp 2 (fun j : Fin d => covShift φ q.1 q.2
            * (f (q.2 + q.1) * (partialZbar j (toC φ) q.2 - partialZbar j (toC φ) (q.2 + q.1))))
        from rfl]
    exact continuous_toLp_formSpace hψD
  have h1 : AEStronglyMeasurable (fun p : FormDu d × FormDu d => ((ρ p.1 : ℝ) : ℂ))
      ((volume : Measure (FormDu d)).prod (volume : Measure (FormDu d))) :=
    ((Complex.continuous_ofReal.comp (hρc.comp continuous_fst))).aestronglyMeasurable
  have h2 : AEStronglyMeasurable
      (fun p : FormDu d × FormDu d => ((Real.exp (-(φ p.2)) : ℝ) : ℂ))
      ((volume : Measure (FormDu d)).prod (volume : Measure (FormDu d))) :=
    ((Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (hφ.continuous.neg.comp continuous_snd)))).aestronglyMeasurable
  have h3 : AEStronglyMeasurable (fun p : FormDu d × FormDu d =>
      inner ℂ (shiftDefectForm φ p.1 f p.2) (X p.2))
      ((volume : Measure (FormDu d)).prod (volume : Measure (FormDu d))) :=
    hD.aestronglyMeasurable.inner
      (hX.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  exact h1.mul (h2.mul h3)

lemma shiftDefectForm_eq_zero_of_eq_zero {φ : FormDu d → ℝ} {f : FormDu d → ℂ}
    {y w : FormDu d} (h : f (w + y) = 0) : shiftDefectForm φ y f w = 0 := by
  refine PiLp.ext fun j => ?_
  simp [shiftDefectForm_apply, h]

lemma integrable_convPairS {φ : FormDu d → ℝ} (hφ : ContDiff ℝ ∞ φ) {f : FormDu d → ℂ}
    (hf : ContDiff ℝ ∞ f) (hfs : HasCompactSupport f) {ρ : FormDu d → ℝ}
    (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) {X : FormDu d → FormSpace d}
    (hX : LocallyIntegrable X volume) :
    Integrable (convPairS φ f ρ X)
      ((volume : Measure (FormDu d)).prod (volume : Measure (FormDu d))) := by
  classical
  obtain ⟨R, hR⟩ := exists_subset_closedBall_of_isCompact
    (hasCompactSupport_dbarFormFun hfs).isCompact
  obtain ⟨R', hR'⟩ := exists_subset_closedBall_of_isCompact hρs.isCompact
  obtain ⟨CG, hCG⟩ := (hasCompactSupport_dbarFormFun hfs).exists_bound_of_continuousOn
      ((Real.continuous_exp.comp hφ.continuous.neg).mul
        (contDiff_dbarFormFun hf).continuous.norm).continuousOn
  obtain ⟨Cρ, hCρ⟩ := hρs.exists_bound_of_continuousOn hρc.continuousOn
  have hbase := integrable_indicator_prod_norm_snd (isCompact_closedBall (0 : FormDu d) R')
      (isCompact_closedBall (0 : FormDu d) (R + R')) hX
  have hg := hbase.const_mul ((max Cρ 0) * (max CG 0) * (d : ℝ))
  refine hg.mono' (continuous_convPairS hφ.continuous hf hρc hX.aestronglyMeasurable) ?_
  filter_upwards with p
  obtain ⟨y, w⟩ := p
  have hnonneg : (0 : ℝ) ≤ (max Cρ 0) * (max CG 0) * (d : ℝ)
      * ((Metric.closedBall (0 : FormDu d) R'
          ×ˢ Metric.closedBall (0 : FormDu d) (R + R')).indicator
        (fun q : FormDu d × FormDu d => ‖X q.2‖)) (y, w) :=
    mul_nonneg (mul_nonneg (mul_nonneg (le_max_right _ _) (le_max_right _ _))
      (Nat.cast_nonneg d)) (Set.indicator_nonneg (fun _ _ => norm_nonneg _) _)
  by_cases hy : y ∈ tsupport ρ
  · by_cases hwy : w + y ∈ tsupport (dbarFormFun f)
    · have hym : y ∈ Metric.closedBall (0 : FormDu d) R' := hR' hy
      have hwm : w ∈ Metric.closedBall (0 : FormDu d) (R + R') := by
        rw [Metric.mem_closedBall]
        have h1 : ‖w + y‖ ≤ R := by
          have h := hR hwy
          rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
          exact h
        have h2 : ‖y‖ ≤ R' := by
          have h := hR' hy
          rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
          exact h
        calc dist w 0 = ‖w‖ := by rw [dist_eq_norm, sub_zero]
          _ = ‖(w + y) - y‖ := by rw [add_sub_cancel_right]
          _ ≤ ‖w + y‖ + ‖y‖ := norm_sub_le _ _
          _ ≤ R + R' := add_le_add h1 h2
      rw [Set.indicator_of_mem (Set.mk_mem_prod hym hwm)]
      have hρb : |ρ y| ≤ max Cρ 0 := by
        have h : |ρ y| ≤ Cρ := by simpa only [Real.norm_eq_abs] using hCρ y hy
        exact h.trans (le_max_left _ _)
      have hCGb : Real.exp (-(φ (w + y))) * ‖dbarFormFun f (w + y)‖ ≤ max CG 0 := by
        have h : Real.exp (-(φ (w + y))) * ‖dbarFormFun f (w + y)‖ ≤ CG := by
          simpa only [Pi.mul_apply, Function.comp_apply, Pi.neg_apply,
            Real.norm_of_nonneg (mul_nonneg (Real.exp_nonneg _) (norm_nonneg _))]
            using hCG (w + y) hwy
        exact h.trans (le_max_left _ _)
      have hbound : Real.exp (-(φ w))
            * ‖inner ℂ (shiftForm φ y (dbarFormFun f) w) (X w)‖
          ≤ (max CG 0) * ((d : ℝ) * ‖X w‖) := by
        have h1 := mul_le_mul_of_nonneg_left (norm_inner_shiftForm_le φ f X y w)
          (Real.exp_nonneg (-(φ w)))
        have h2 : Real.exp (-(φ w))
              * (Real.exp (φ w - φ (w + y)) * ‖dbarFormFun f (w + y)‖
                * ∑ j : Fin d, ‖X w j‖)
            = (Real.exp (-(φ (w + y))) * ‖dbarFormFun f (w + y)‖)
              * ∑ j : Fin d, ‖X w j‖ := by
          have hexp : Real.exp (-(φ w)) * Real.exp (φ w - φ (w + y))
              = Real.exp (-(φ (w + y))) := by
            rw [← Real.exp_add]
            congr 1
            ring
          calc Real.exp (-(φ w)) * (Real.exp (φ w - φ (w + y)) * ‖dbarFormFun f (w + y)‖
                * ∑ j : Fin d, ‖X w j‖)
              = (Real.exp (-(φ w)) * Real.exp (φ w - φ (w + y))) * ‖dbarFormFun f (w + y)‖
                * ∑ j : Fin d, ‖X w j‖ := by ring
            _ = Real.exp (-(φ (w + y))) * ‖dbarFormFun f (w + y)‖
                * ∑ j : Fin d, ‖X w j‖ := by rw [hexp]
        rw [h2] at h1
        calc Real.exp (-(φ w)) * ‖inner ℂ (shiftForm φ y (dbarFormFun f) w) (X w)‖
            ≤ (Real.exp (-(φ (w + y))) * ‖dbarFormFun f (w + y)‖)
              * ∑ j : Fin d, ‖X w j‖ := h1
          _ ≤ (max CG 0) * ((d : ℝ) * ‖X w‖) :=
              mul_le_mul hCGb (sum_norm_apply_le d)
                (Finset.sum_nonneg fun j _ => norm_nonneg _)
                (le_trans (mul_nonneg (Real.exp_nonneg _) (norm_nonneg _)) hCGb)
      have hnorm : ‖convPairS φ f ρ X (y, w)‖
          = |ρ y| * (Real.exp (-(φ w))
              * ‖inner ℂ (shiftForm φ y (dbarFormFun f) w) (X w)‖) := by
        simp only [convPairS, norm_mul]
        rw [Complex.norm_def, Complex.normSq_ofReal, ← pow_two, Real.sqrt_sq_eq_abs,
          Complex.norm_def, Complex.normSq_ofReal, ← pow_two, Real.sqrt_sq_eq_abs,
          abs_of_nonneg (Real.exp_nonneg _)]
      rw [hnorm]
      calc |ρ y| * (Real.exp (-(φ w)) * ‖inner ℂ (shiftForm φ y (dbarFormFun f) w) (X w)‖)
          ≤ (max Cρ 0) * ((max CG 0) * ((d : ℝ) * ‖X w‖)) :=
            mul_le_mul hρb hbound (mul_nonneg (Real.exp_nonneg _) (norm_nonneg _))
              (le_trans (abs_nonneg _) hρb)
        _ = (max Cρ 0) * (max CG 0) * (d : ℝ) * ‖X w‖ := by ring
    · have h0 : dbarFormFun f (w + y) = 0 := image_eq_zero_of_notMem_tsupport hwy
      have hzero : convPairS φ f ρ X (y, w) = 0 := by
        simp [convPairS, shiftForm_apply, h0]
      rw [hzero, norm_zero]
      exact hnonneg
  · have hρ0 : ρ y = 0 := image_eq_zero_of_notMem_tsupport hy
    have hzero : convPairS φ f ρ X (y, w) = 0 := by
      show ((ρ y : ℝ) : ℂ) * (((Real.exp (-(φ w)) : ℝ) : ℂ)
        * inner ℂ (shiftForm φ y (dbarFormFun f) w) (X w)) = 0
      rw [hρ0, Complex.ofReal_zero, zero_mul]
    rw [hzero, norm_zero]
    exact hnonneg

lemma integrable_convPairD {φ : FormDu d → ℝ} (hφ : ContDiff ℝ 2 φ) {f : FormDu d → ℂ}
    (hf : ContDiff ℝ ∞ f) (hfs : HasCompactSupport f) {ρ : FormDu d → ℝ}
    (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) {X : FormDu d → FormSpace d}
    (hX : LocallyIntegrable X volume) :
    Integrable (convPairD φ f ρ X)
      ((volume : Measure (FormDu d)).prod (volume : Measure (FormDu d))) := by
  classical
  obtain ⟨R, hR⟩ := exists_subset_closedBall_of_isCompact hfs.isCompact
  obtain ⟨R', hR'⟩ := exists_subset_closedBall_of_isCompact hρs.isCompact
  obtain ⟨CE, hCE⟩ := hfs.exists_bound_of_continuousOn
      (Real.continuous_exp.comp hφ.continuous.neg).continuousOn
  obtain ⟨Cf, hCf⟩ := hfs.exists_bound_of_continuousOn hf.continuous.continuousOn
  obtain ⟨Cρ, hCρ⟩ := hρs.exists_bound_of_continuousOn hρc.continuousOn
  have hcontD : Continuous (fun q : FormDu d × FormDu d => ∑ j : Fin d,
      ‖partialZbar j (toC φ) q.1 - partialZbar j (toC φ) (q.1 + q.2)‖) :=
    continuous_finsetSum (Finset.univ : Finset (Fin d)) fun j _ =>
      (((continuous_partialZbar_toC hφ j).comp continuous_fst).sub
        ((continuous_partialZbar_toC hφ j).comp
          (continuous_fst.add continuous_snd))).norm
  obtain ⟨CΦ, hCΦ⟩ := ((isCompact_closedBall (0 : FormDu d) (R + R')).prod
      (isCompact_closedBall (0 : FormDu d) R')).exists_bound_of_continuousOn
    hcontD.continuousOn
  have hbase := integrable_indicator_prod_norm_snd (isCompact_closedBall (0 : FormDu d) R')
      (isCompact_closedBall (0 : FormDu d) (R + R')) hX
  have hg := hbase.const_mul ((max Cρ 0) * (max CE 0 * max Cf 0 * max CΦ 0) * (d : ℝ))
  refine hg.mono' (continuous_convPairD hφ hf hρc hX.aestronglyMeasurable) ?_
  filter_upwards with p
  obtain ⟨y, w⟩ := p
  have hnonneg : (0 : ℝ) ≤ (max Cρ 0) * (max CE 0 * max Cf 0 * max CΦ 0) * (d : ℝ)
      * ((Metric.closedBall (0 : FormDu d) R'
          ×ˢ Metric.closedBall (0 : FormDu d) (R + R')).indicator
        (fun q : FormDu d × FormDu d => ‖X q.2‖)) (y, w) :=
    mul_nonneg (mul_nonneg (mul_nonneg (le_max_right _ _)
      (mul_nonneg (mul_nonneg (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)))
      (Nat.cast_nonneg d)) (Set.indicator_nonneg (fun _ _ => norm_nonneg _) _)
  by_cases hy : y ∈ tsupport ρ
  · by_cases hwy : w + y ∈ tsupport f
    · have hym : y ∈ Metric.closedBall (0 : FormDu d) R' := hR' hy
      have hwm : w ∈ Metric.closedBall (0 : FormDu d) (R + R') := by
        rw [Metric.mem_closedBall]
        have h1 : ‖w + y‖ ≤ R := by
          have h := hR hwy
          rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
          exact h
        have h2 : ‖y‖ ≤ R' := by
          have h := hR' hy
          rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
          exact h
        calc dist w 0 = ‖w‖ := by rw [dist_eq_norm, sub_zero]
          _ = ‖(w + y) - y‖ := by rw [add_sub_cancel_right]
          _ ≤ ‖w + y‖ + ‖y‖ := norm_sub_le _ _
          _ ≤ R + R' := add_le_add h1 h2
      rw [Set.indicator_of_mem (Set.mk_mem_prod hym hwm)]
      have hρb : |ρ y| ≤ max Cρ 0 := by
        have h : |ρ y| ≤ Cρ := by simpa only [Real.norm_eq_abs] using hCρ y hy
        exact h.trans (le_max_left _ _)
      have hΦsum : ∑ j : Fin d, ‖partialZbar j (toC φ) w - partialZbar j (toC φ) (w + y)‖
          ≤ max CΦ 0 := by
        have h := hCΦ (w, y) (Set.mk_mem_prod hwm hym)
        rw [Real.norm_of_nonneg (Finset.sum_nonneg fun j _ => norm_nonneg _)] at h
        exact h.trans (le_max_left _ _)
      have hCEb : Real.exp (-(φ (w + y))) ≤ max CE 0 := by
        have h : Real.exp (-(φ (w + y))) ≤ CE := by
          simpa only [Function.comp_apply, Pi.neg_apply, Real.norm_of_nonneg (Real.exp_nonneg _)]
            using hCE (w + y) hwy
        exact h.trans (le_max_left _ _)
      have hCfb : ‖f (w + y)‖ ≤ max Cf 0 := (hCf (w + y) hwy).trans (le_max_left _ _)
      have hbound : Real.exp (-(φ w))
            * ‖inner ℂ (shiftDefectForm φ y f w) (X w)‖
          ≤ (max CE 0 * max Cf 0 * max CΦ 0) * ((d : ℝ) * ‖X w‖) := by
        have h1 := mul_le_mul_of_nonneg_left
          (norm_inner_shiftDefectForm_le φ f X y w (fun j => by
            have h := Finset.single_le_sum (f := fun k : Fin d =>
              ‖partialZbar k (toC φ) w - partialZbar k (toC φ) (w + y)‖)
              (fun k _ => norm_nonneg _) (Finset.mem_univ j)
            exact h.trans hΦsum))
          (Real.exp_nonneg (-(φ w)))
        have h2 : Real.exp (-(φ w)) * (Real.exp (φ w - φ (w + y)) * ‖f (w + y)‖
              * max CΦ 0 * ∑ j : Fin d, ‖X w j‖)
            = (Real.exp (-(φ (w + y))) * ‖f (w + y)‖ * max CΦ 0)
              * ∑ j : Fin d, ‖X w j‖ := by
          have hexp : Real.exp (-(φ w)) * Real.exp (φ w - φ (w + y))
              = Real.exp (-(φ (w + y))) := by
            rw [← Real.exp_add]
            congr 1
            ring
          calc Real.exp (-(φ w)) * (Real.exp (φ w - φ (w + y)) * ‖f (w + y)‖
                * max CΦ 0 * ∑ j : Fin d, ‖X w j‖)
              = (Real.exp (-(φ w)) * Real.exp (φ w - φ (w + y))) * ‖f (w + y)‖ * max CΦ 0
                * ∑ j : Fin d, ‖X w j‖ := by ring
            _ = Real.exp (-(φ (w + y))) * ‖f (w + y)‖ * max CΦ 0
                * ∑ j : Fin d, ‖X w j‖ := by rw [hexp]
        rw [h2] at h1
        have h3 : Real.exp (-(φ (w + y))) * ‖f (w + y)‖ * max CΦ 0
            ≤ (max CE 0 * max Cf 0) * max CΦ 0 := by
          refine mul_le_mul_of_nonneg_right ?_ (le_max_right _ _)
          exact mul_le_mul hCEb hCfb (norm_nonneg _)
            (le_trans (Real.exp_nonneg _) hCEb)
        calc Real.exp (-(φ w)) * ‖inner ℂ (shiftDefectForm φ y f w) (X w)‖
            ≤ (Real.exp (-(φ (w + y))) * ‖f (w + y)‖ * max CΦ 0)
              * ∑ j : Fin d, ‖X w j‖ := h1
          _ ≤ ((max CE 0 * max Cf 0) * max CΦ 0) * ((d : ℝ) * ‖X w‖) :=
              mul_le_mul h3 (sum_norm_apply_le d)
                (Finset.sum_nonneg fun j _ => norm_nonneg _)
                (mul_nonneg (mul_nonneg (le_max_right _ _) (le_max_right _ _))
                  (le_max_right _ _))
          _ = (max CE 0 * max Cf 0 * max CΦ 0) * ((d : ℝ) * ‖X w‖) := by ring
      have hnorm : ‖convPairD φ f ρ X (y, w)‖
          = |ρ y| * (Real.exp (-(φ w))
              * ‖inner ℂ (shiftDefectForm φ y f w) (X w)‖) := by
        simp only [convPairD, norm_mul]
        rw [Complex.norm_def, Complex.normSq_ofReal, ← pow_two, Real.sqrt_sq_eq_abs,
          Complex.norm_def, Complex.normSq_ofReal, ← pow_two, Real.sqrt_sq_eq_abs,
          abs_of_nonneg (Real.exp_nonneg _)]
      rw [hnorm]
      calc |ρ y| * (Real.exp (-(φ w)) * ‖inner ℂ (shiftDefectForm φ y f w) (X w)‖)
          ≤ (max Cρ 0) * ((max CE 0 * max Cf 0 * max CΦ 0) * ((d : ℝ) * ‖X w‖)) :=
            mul_le_mul hρb hbound (mul_nonneg (Real.exp_nonneg _) (norm_nonneg _))
              (le_trans (abs_nonneg _) hρb)
        _ = (max Cρ 0) * (max CE 0 * max Cf 0 * max CΦ 0) * (d : ℝ) * ‖X w‖ := by ring
    · have h0 : f (w + y) = 0 := image_eq_zero_of_notMem_tsupport hwy
      have hzero : convPairD φ f ρ X (y, w) = 0 := by
        show ((ρ y : ℝ) : ℂ) * (((Real.exp (-(φ w)) : ℝ) : ℂ)
          * inner ℂ (shiftDefectForm φ y f w) (X w)) = 0
        rw [shiftDefectForm_eq_zero_of_eq_zero h0, inner_zero_left, mul_zero, mul_zero]
      rw [hzero, norm_zero]
      exact hnonneg
  · have hρ0 : ρ y = 0 := image_eq_zero_of_notMem_tsupport hy
    have hzero : convPairD φ f ρ X (y, w) = 0 := by
      show ((ρ y : ℝ) : ℂ) * (((Real.exp (-(φ w)) : ℝ) : ℂ)
        * inner ℂ (shiftDefectForm φ y f w) (X w)) = 0
      rw [hρ0, Complex.ofReal_zero, zero_mul]
    rw [hzero, norm_zero]
    exact hnonneg

lemma inner_complex_apply' (a b : ℂ) : inner ℂ a b = star a * b := by
  rw [RCLike.inner_apply, mul_comm]
  rfl

lemma integral_convPairS {φ : FormDu d → ℝ} (hφ : ContDiff ℝ ∞ φ) (f : FormDu d → ℂ)
    (ρ : FormDu d → ℝ) (X : FormDu d → FormSpace d) (y : FormDu d) :
    (∫ w, convPairS φ f ρ X (y, w) ∂(volume : Measure (FormDu d)))
      = ρ y • (∫ w, inner ℂ (shiftForm φ y (dbarFormFun f) w) (X w) ∂(wtMeasure φ)) := by
  rw [integral_wtMeasure hφ.continuous,
    ← integral_smul (μ := (volume : Measure (FormDu d))) (ρ y)]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  dsimp only
  rw [real_smul_eq_mul', real_smul_eq_mul']
  rfl

lemma integral_convPairD {φ : FormDu d → ℝ} (hφ : Continuous φ) (f : FormDu d → ℂ)
    (ρ : FormDu d → ℝ) (X : FormDu d → FormSpace d) (y : FormDu d) :
    (∫ w, convPairD φ f ρ X (y, w) ∂(volume : Measure (FormDu d)))
      = ρ y • (∫ w, inner ℂ (shiftDefectForm φ y f w) (X w) ∂(wtMeasure φ)) := by
  rw [integral_wtMeasure hφ,
    ← integral_smul (μ := (volume : Measure (FormDu d))) (ρ y)]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  dsimp only
  rw [real_smul_eq_mul', real_smul_eq_mul']
  rfl

/-- **The `ϑ_φ`-side transfer**: convolving with a compactly supported kernel maps the domain of
`ϑ_φ` into itself, with `ϑ_φ(ρ*X) = ρ*(ϑ_φX) - V_ρ` where `V_ρ = dbarAdjDefect φ ρ X`. -/
theorem dbarAdjWeak_conv {φ : FormDu d → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {X : FormDu d → FormSpace d} {z : FormDu d → ℂ}
    (hXc : LocallyIntegrable X (volume : Measure (FormDu d)))
    (hzc : LocallyIntegrable z (volume : Measure (FormDu d)))
    (hXm : MemLp X 2 (wtMeasure φ)) (hzm : MemLp z 2 (wtMeasure φ))
    (hweak : dbarAdjWeak φ (hXm.toLp X) (hzm.toLp z))
    {ρ : FormDu d → ℝ} (hρc : Continuous ρ) (hρs : HasCompactSupport ρ)
    (hXρ : MemLp (convFun ρ X) 2 (wtMeasure φ))
    (hAz : MemLp (convFun ρ z) 2 (wtMeasure φ))
    (hAv : MemLp (dbarAdjDefect φ ρ X) 2 (wtMeasure φ)) :
    dbarAdjWeak φ (hXρ.toLp (convFun ρ X))
      ((hAz.sub hAv).toLp (fun u => convFun ρ z u - dbarAdjDefect φ ρ X u)) := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  intro f hf hfs hfm hwm
  have hconj : inner ℂ (hfm.toLp f)
        ((hAz.sub hAv).toLp (fun u => convFun ρ z u - dbarAdjDefect φ ρ X u))
      = inner ℂ (hwm.toLp (dbarFormFun f)) (hXρ.toLp (convFun ρ X)) := by
    -- the weak relation tested against the covariantly shifted test functions
    have hLHS : inner ℂ (hfm.toLp f) (hAz.toLp (convFun ρ z))
        = ∫ y, ρ y • (∫ w, inner ℂ (dbarFormFun (shiftFun φ y f) w) (X w)
            ∂(wtMeasure φ)) ∂(volume : Measure (FormDu d)) := by
      rw [inner_toLp_eq_integral hfm hAz,
        inner_convFun_eq hφ.continuous hf.continuous hfs hzc hρc hρs
          (integrable_uncurry_inner_conv hφ.continuous hf.continuous hfs hzc hρc hρs)]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      dsimp only
      congr 1
      have hψ1 : ContDiff ℝ ∞ (shiftFun φ y f) := contDiff_shiftFun hφ hf y
      have hψs : HasCompactSupport (shiftFun φ y f) := hasCompactSupport_shiftFun hfs
      have hψm : MemLp (shiftFun φ y f) 2 (wtMeasure φ) :=
        memLp_wtMeasure_of_contDiff_hasCompactSupport hφ.continuous hψ1 hψs
      have hϑm : MemLp (dbarFormFun (shiftFun φ y f)) 2 (wtMeasure φ) :=
        memLp_wtMeasure_of_contDiff_hasCompactSupport hφ.continuous (contDiff_dbarFormFun hψ1)
          (hasCompactSupport_dbarFormFun hψs)
      have hrel := congrArg star (hweak (shiftFun φ y f) hψ1 hψs hψm hϑm)
      simp only [star_inner_eq_inner_swap] at hrel
      rw [inner_toLp_eq_integral hψm hzm, inner_toLp_eq_integral hϑm hXm] at hrel
      rw [← hrel]
      refine integral_congr_ae (Eventually.of_forall fun w => rfl)
    -- the `S`-part is `⟪∂̄f, ρ*X⟫`
    have hSz : (∫ y, ρ y • (∫ w, inner ℂ (shiftForm φ y (dbarFormFun f) w) (X w)
          ∂(wtMeasure φ)) ∂(volume : Measure (FormDu d)))
        = ∫ w, inner ℂ (dbarFormFun f w) (convFun ρ X w) ∂(wtMeasure φ) :=
      (inner_convFun_eq hφ.continuous (contDiff_dbarFormFun hf).continuous
        (hasCompactSupport_dbarFormFun hfs) hXc hρc hρs
        (integrable_uncurry_inner_conv hφ.continuous (contDiff_dbarFormFun hf).continuous
          (hasCompactSupport_dbarFormFun hfs) hXc hρc hρs)).symm
    -- the `D`-part is `⟪f, V_ρ⟫`
    have hDz : (∫ y, ρ y • (∫ w, inner ℂ (shiftDefectForm φ y f w) (X w)
          ∂(wtMeasure φ)) ∂(volume : Measure (FormDu d)))
        = ∫ u, inner ℂ (f u) (dbarAdjDefect φ ρ X u) ∂(wtMeasure φ) := by
      rw [show (∫ u, inner ℂ (f u) (dbarAdjDefect φ ρ X u) ∂(wtMeasure φ))
          = ∫ u, star (f u) * dbarAdjDefect φ ρ X u ∂(wtMeasure φ) from
            integral_congr_ae (Eventually.of_forall fun u => inner_complex_apply' _ _)]
      exact integral_defectPair_eq hφ2 hf.continuous hfs hρc hρs hXc
    -- the pointwise splitting
    have hpery : ∀ y, ρ y • (∫ w, inner ℂ (dbarFormFun (shiftFun φ y f) w) (X w)
          ∂(wtMeasure φ))
        = ρ y • (∫ w, inner ℂ (shiftForm φ y (dbarFormFun f) w) (X w) ∂(wtMeasure φ))
          + ρ y • (∫ w, inner ℂ (shiftDefectForm φ y f w) (X w) ∂(wtMeasure φ)) := by
      intro y
      have hSm : MemLp (shiftForm φ y (dbarFormFun f)) 2 (wtMeasure φ) :=
        memLp_wtMeasure_of_continuous_hasCompactSupport hφ.continuous
          (contDiff_shiftForm hφ (contDiff_dbarFormFun hf)).continuous
          (hasCompactSupport_shiftForm (hasCompactSupport_dbarFormFun hfs))
      have hDm : MemLp (shiftDefectForm φ y f) 2 (wtMeasure φ) :=
        memLp_wtMeasure_of_continuous_hasCompactSupport hφ.continuous
          (continuous_shiftDefectForm hφ2 hf y) (hasCompactSupport_shiftDefectForm hfs)
      have hstep : (∫ w, inner ℂ (dbarFormFun (shiftFun φ y f) w) (X w) ∂(wtMeasure φ))
          = (∫ w, inner ℂ (shiftForm φ y (dbarFormFun f) w) (X w) ∂(wtMeasure φ))
            + (∫ w, inner ℂ (shiftDefectForm φ y f w) (X w) ∂(wtMeasure φ)) := by
        rw [← integral_add (integrable_inner_toLp hSm hXm) (integrable_inner_toLp hDm hXm)]
        refine integral_congr_ae (Eventually.of_forall fun w => ?_)
        dsimp only
        rw [dbarFormFun_shiftFun hφ2 hf y w, inner_add_left]
        rfl
      rw [hstep, smul_add]
    -- assembling the two sides
    have hsum : (∫ y, ρ y • (∫ w, inner ℂ (dbarFormFun (shiftFun φ y f) w) (X w)
          ∂(wtMeasure φ)) ∂(volume : Measure (FormDu d)))
        = (∫ y, ρ y • (∫ w, inner ℂ (shiftForm φ y (dbarFormFun f) w) (X w)
              ∂(wtMeasure φ)) ∂(volume : Measure (FormDu d)))
          + (∫ y, ρ y • (∫ w, inner ℂ (shiftDefectForm φ y f w) (X w)
              ∂(wtMeasure φ)) ∂(volume : Measure (FormDu d))) := by
      have hIntS := integrable_convPairS hφ hf hfs hρc hρs hXc
      have hIntD := integrable_convPairD hφ2 hf hfs hρc hρs hXc
      have hA : Integrable (fun y => ρ y • (∫ w, inner ℂ (shiftForm φ y (dbarFormFun f) w) (X w)
            ∂(wtMeasure φ))) volume := by
        refine hIntS.integral_prod_left.congr ?_
        filter_upwards with y
        show (∫ w, convPairS φ f ρ X (y, w)) = ρ y • (∫ w,
          inner ℂ (shiftForm φ y (dbarFormFun f) w) (X w) ∂(wtMeasure φ))
        exact integral_convPairS hφ f ρ X y
      have hB : Integrable (fun y => ρ y • (∫ w, inner ℂ (shiftDefectForm φ y f w) (X w)
            ∂(wtMeasure φ))) volume := by
        refine hIntD.integral_prod_left.congr ?_
        filter_upwards with y
        show (∫ w, convPairD φ f ρ X (y, w)) = ρ y • (∫ w,
          inner ℂ (shiftDefectForm φ y f w) (X w) ∂(wtMeasure φ))
        exact integral_convPairD hφ.continuous f ρ X y
      rw [← integral_add hA hB]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      dsimp only
      rw [hpery y]
    have hG : inner ℂ (hfm.toLp f)
          ((hAz.sub hAv).toLp (fun u => convFun ρ z u - dbarAdjDefect φ ρ X u))
        = inner ℂ (hfm.toLp f) (hAz.toLp (convFun ρ z))
          - inner ℂ (hfm.toLp f) (hAv.toLp (dbarAdjDefect φ ρ X)) := by
      rw [show (hAz.sub hAv).toLp (fun u => convFun ρ z u - dbarAdjDefect φ ρ X u)
          = (hAz.sub hAv).toLp (convFun ρ z - dbarAdjDefect φ ρ X) from rfl,
        MemLp.toLp_sub hAz hAv, inner_sub_right]
    rw [hG, hLHS, hsum, hSz, hDz, inner_toLp_eq_integral hfm hAv,
      inner_toLp_eq_integral hwm hXρ]
    ring
  have h := congrArg star hconj
  simp only [star_inner_eq_inner_swap] at h
  exact h

end Transfer