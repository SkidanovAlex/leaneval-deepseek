/-
# The transformation laws `𝓛(z+1) = 𝓛(z) - 𝓛_S(z) + πi`, `𝓛_S(z+1) = -𝓛_S(z)`

We prove the two `T`-laws for the normalised logarithms `Lfun` (of `λ`) and
`Lfun_S(z) = Lfun(-z⁻¹)` (of `λ_S`) at the level of `ℂ`.

The two defects

  `Φ(z) = Lfun(z+1) - Lfun(z) + Lfun(-z⁻¹) - πi`,   `Ψ(z) = Lfun(-(z+1)⁻¹) + Lfun(-z⁻¹)`

are continuous on the connected set `U = {im z > 0}` and take values in `2πiℤ` (their
exponentials are `λ(z+1)λ(z)⁻¹λ(-1/z)(-1) = 1` and `λ_S(z+1)λ_S(z) = 1`); hence each is a
constant.  The constants are evaluated at the cusp `∞` along `z = iT`, `T → ∞`: there
`Lfun = LU` and `Lfun(-z⁻¹) = Λ_S(z)` (the normalisation of `LogNormalisation`), which gives

  `Φ(iT) = LU(iT+1) - LU(iT) + Λ_S(iT) - πi → πi - 0 + 0 - πi = 0`
  `Ψ(iT) = Λ_S(iT+1) + Λ_S(iT) → 0 + 0 = 0`.

This is exactly the comparison of asymptotics used in CKMRV, Section 2.1.5.
-/
import Mathlib
import Submission.Work.Kernels.LogLambda.LogExtension
import Submission.Work.Kernels.LogLambda.LambdaLaws
import Submission.Work.Kernels.LogLambda.LogNormalisation

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Complex Set Filter Topology
open scoped Modular

namespace Work.Kernels.LogLambda

/-! ## Limits of `Λ_S` along the imaginary axis -/

lemma tendsto_thetaC00_imag_zero :
    Tendsto (fun T : ℝ => thetaC00 ((T : ℂ) * Complex.I)) atTop (𝓝 1) := by
  simpa using tendsto_thetaC00_imag 0

lemma thetaC01_eq_thetaC00_add_one (w : ℂ) :
    thetaC01 w = thetaC00 (w + 1) := by
  rw [thetaC01, Work.Kernels.ClassicalFacts.jacobiTheta₂_half_eq_jacobiTheta_add_one]
  rfl

lemma U_im_pos {z : ℂ} (hz : z ∈ U) : 0 < z.im := hz

lemma U_add_one {z : ℂ} (hz : z ∈ U) : z + 1 ∈ U := by
  simp only [U, Set.mem_ofPred_eq] at hz ⊢
  simpa [Complex.add_im] using hz

lemma W_im_pos {z : ℂ} (hz : z ∈ W) : 0 < z.im := by
  simp only [W, Set.mem_ofPred_eq] at hz
  linarith

lemma W_add_one {z : ℂ} (hz : z ∈ W) : z + 1 ∈ W := by
  simp only [W, Set.mem_ofPred_eq] at hz ⊢
  simpa [Complex.add_im] using hz

lemma tendsto_thetaC01_imag_zero :
    Tendsto (fun T : ℝ => thetaC01 ((T : ℂ) * Complex.I)) atTop (𝓝 1) := by
  have h := tendsto_thetaC00_imag 1
  have heq : (fun T : ℝ => thetaC01 ((T : ℂ) * Complex.I))
      = fun T : ℝ => thetaC00 ((T : ℂ) * Complex.I + 1) := by
    funext T
    rw [thetaC01_eq_thetaC00_add_one]
  rw [heq]
  exact h

lemma tendsto_log_thetaC00_imag_zero :
    Tendsto (fun T : ℝ => Complex.log (thetaC00 ((T : ℂ) * Complex.I))) atTop (𝓝 0) := by
  have h1 : (1 : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; left; norm_num
  have h := (continuousAt_clog h1).tendsto.comp tendsto_thetaC00_imag_zero
  rw [show (Complex.log ∘ fun T : ℝ => thetaC00 ((T : ℂ) * Complex.I))
      = fun T : ℝ => Complex.log (thetaC00 ((T : ℂ) * Complex.I)) from rfl, Complex.log_one] at h
  exact h

lemma tendsto_log_thetaC01_imag_zero :
    Tendsto (fun T : ℝ => Complex.log (thetaC01 ((T : ℂ) * Complex.I))) atTop (𝓝 0) := by
  have h1 : (1 : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; left; norm_num
  have h := (continuousAt_clog h1).tendsto.comp tendsto_thetaC01_imag_zero
  rw [show (Complex.log ∘ fun T : ℝ => thetaC01 ((T : ℂ) * Complex.I))
      = fun T : ℝ => Complex.log (thetaC01 ((T : ℂ) * Complex.I)) from rfl, Complex.log_one] at h
  exact h

/-- `Λ_S(iT) → 0` as `T → ∞`. -/
lemma tendsto_LamS_imag :
    Tendsto (fun T : ℝ => LamS ((T : ℂ) * Complex.I)) atTop (𝓝 0) := by
  have h := (Filter.Tendsto.const_mul (4 : ℂ) tendsto_log_thetaC01_imag_zero).sub
    (Filter.Tendsto.const_mul (4 : ℂ) tendsto_log_thetaC00_imag_zero)
  simpa [LamS] using h

/-- `Λ_S(iT+1) → 0` as `T → ∞`. -/
lemma tendsto_LamS_imag_add_one :
    Tendsto (fun T : ℝ => LamS ((T : ℂ) * Complex.I + 1)) atTop (𝓝 0) := by
  have h0 : Tendsto (fun T : ℝ => thetaC00 ((T : ℂ) * Complex.I + 1)) atTop (𝓝 1) :=
    tendsto_thetaC00_imag 1
  have h1 : Tendsto (fun T : ℝ => thetaC01 ((T : ℂ) * Complex.I + 1)) atTop (𝓝 1) := by
    have h := tendsto_thetaC00_imag 2
    have heq : (fun T : ℝ => thetaC01 ((T : ℂ) * Complex.I + 1))
        = fun T : ℝ => thetaC00 ((T : ℂ) * Complex.I + 2) := by
      funext T
      rw [thetaC01_eq_thetaC00_add_one]
      congr 1
      ring
    rw [heq]
    exact h
  have hmem : (1 : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; left; norm_num
  have hl0 := (continuousAt_clog hmem).tendsto.comp h0
  have hl1 := (continuousAt_clog hmem).tendsto.comp h1
  rw [show (Complex.log ∘ fun T : ℝ => thetaC00 ((T : ℂ) * Complex.I + 1))
      = fun T : ℝ => Complex.log (thetaC00 ((T : ℂ) * Complex.I + 1)) from rfl,
    Complex.log_one] at hl0
  rw [show (Complex.log ∘ fun T : ℝ => thetaC01 ((T : ℂ) * Complex.I + 1))
      = fun T : ℝ => Complex.log (thetaC01 ((T : ℂ) * Complex.I + 1)) from rfl,
    Complex.log_one] at hl1
  have h := (Filter.Tendsto.const_mul (4 : ℂ) hl1).sub (Filter.Tendsto.const_mul (4 : ℂ) hl0)
  simpa [LamS] using h

lemma mul_I_mem_U {T : ℝ} (hT : 0 < T) : ((T : ℂ) * Complex.I) ∈ U := by
  simp only [U, Set.mem_ofPred_eq, Complex.mul_I_im, Complex.ofReal_re]
  exact hT

lemma mul_I_mem_W {T : ℝ} (hT : 1 / 2 < T) : ((T : ℂ) * Complex.I) ∈ W := by
  simp only [W, Set.mem_ofPred_eq, Complex.mul_I_im, Complex.ofReal_re]
  exact hT

lemma mul_I_add_one_mem_W {T : ℝ} (hT : 1 / 2 < T) : ((T : ℂ) * Complex.I + 1) ∈ W := by
  simp only [W, Set.mem_ofPred_eq, Complex.add_im, Complex.mul_I_im, Complex.ofReal_re,
    Complex.one_im, add_zero]
  exact hT

/-! ## The `T`-defect `Φ` -/

/-- The defect of the `T`-law for `Lfun`. -/
def PhiT (z : ℂ) : ℂ := Lfun (z + 1) - Lfun z + Lfun (-z⁻¹) - (Real.pi : ℂ) * Complex.I

lemma continuousOn_PhiT : ContinuousOn PhiT U := by
  have h1 : ContinuousOn (fun z : ℂ => Lfun (z + 1)) U :=
    Lfun_spec.1.continuousOn.comp (by fun_prop) (fun z hz => U_add_one hz)
  have h2 : ContinuousOn (fun z : ℂ => Lfun (-z⁻¹)) U :=
    Lfun_spec.1.continuousOn.comp continuousOn_neg_inv (fun z hz => im_neg_inv_pos (U_im_pos hz))
  have h3 : ContinuousOn Lfun U := Lfun_spec.1.continuousOn
  have h4 : ContinuousOn (fun _ : ℂ => (Real.pi : ℂ) * Complex.I) U := continuousOn_const
  exact ((h1.sub h3).add h2).sub h4

lemma exp_PhiT {z : ℂ} (hz : z ∈ U) : Complex.exp (PhiT z) = 1 := by
  have hz1 : z + 1 ∈ U := by
    simp only [U, Set.mem_ofPred_eq] at hz ⊢
    simpa [Complex.add_im] using hz
  have hzU' : -z⁻¹ ∈ U := im_neg_inv_pos (U_im_pos hz)
  have ha : lamC z ≠ 0 := lamC_ne_zero (U_im_pos hz)
  have hb : lamSC z ≠ 0 := lamSC_ne_zero hz
  have hexp : Complex.exp (PhiT z)
      = Complex.exp (Lfun (z + 1)) * (Complex.exp (Lfun z))⁻¹ * Complex.exp (Lfun (-z⁻¹))
        * (Complex.exp ((Real.pi : ℂ) * Complex.I))⁻¹ := by
    rw [PhiT]
    rw [show Lfun (z + 1) - Lfun z + Lfun (-z⁻¹) - (Real.pi : ℂ) * Complex.I
        = Lfun (z + 1) + (-Lfun z) + Lfun (-z⁻¹) + (-((Real.pi : ℂ) * Complex.I)) by ring]
    rw [Complex.exp_add, Complex.exp_add, Complex.exp_add, Complex.exp_neg, Complex.exp_neg]
  rw [hexp, Lfun_spec.2.1 (z + 1) hz1, Lfun_spec.2.1 z hz, Lfun_spec.2.1 (-z⁻¹) hzU',
    Complex.exp_pi_mul_I, lamC_add_one hz, ← lamSC_eq_lamC_inv hz]
  field_simp

lemma exp_eq_one_PhiT {z : ℂ} (hz : z ∈ U) : ∃ n : ℤ, PhiT z = n * (2 * Real.pi * Complex.I) :=
  Complex.exp_eq_one_iff.mp (exp_PhiT hz)

lemma tendsto_PhiT : Tendsto (fun T : ℝ => PhiT ((T : ℂ) * Complex.I)) atTop (𝓝 0) := by
  have hLU := tendsto_LU_diff
  have hLam := tendsto_LamS_imag
  have hlim : Tendsto (fun T : ℝ => LU ((T : ℂ) * Complex.I + 1) - LU ((T : ℂ) * Complex.I)
      + LamS ((T : ℂ) * Complex.I) - (Real.pi : ℂ) * Complex.I) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℝ => (Real.pi : ℂ) * Complex.I) atTop
        (𝓝 ((Real.pi : ℂ) * Complex.I)) := tendsto_const_nhds
    have h := (hLU.add hLam).sub hc
    have h0 : (Real.pi : ℂ) * Complex.I + 0 - (Real.pi : ℂ) * Complex.I = 0 := by ring
    rwa [h0] at h
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  rw [PhiT, Lfun_eq_LU_on_W _ (mul_I_mem_W (by linarith)),
    Lfun_eq_LU_on_W _ (mul_I_add_one_mem_W (by linarith)),
    Lfun_inv_eq_LamS _ (mul_I_mem_W (by linarith))]

/-- The `T`-law for `Lfun` on `U`. -/
theorem lfun_add_one (z : ℂ) (hz : z ∈ U) :
    Lfun (z + 1) = Lfun z - Lfun (-z⁻¹) + (Real.pi : ℂ) * Complex.I := by
  have hconst : ∀ w ∈ U, PhiT w = PhiT (2 * Complex.I) :=
    Work.Analysis.DiscreteValues.eq_const_of_isPreconnected isPreconnected_U continuousOn_PhiT
      (fun w hw => exp_eq_one_PhiT hw)
      (by simp only [U, Set.mem_ofPred_eq, Complex.mul_I_im]; norm_num)
  have h2 : Tendsto (fun T : ℝ => PhiT ((T : ℂ) * Complex.I)) atTop (𝓝 (PhiT (2 * Complex.I))) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    exact (hconst _ (mul_I_mem_U (by linarith))).symm
  have hz0 : PhiT (2 * Complex.I) = 0 := tendsto_nhds_unique h2 tendsto_PhiT
  have hz' : PhiT z = 0 := by rw [hconst z hz, hz0]
  rw [PhiT] at hz'
  linear_combination hz'

/-! ## The `T`-defect `Ψ` -/

/-- The defect of the `T`-law for `Lfun_S`. -/
def PsiT (z : ℂ) : ℂ := Lfun (-(z + 1)⁻¹) + Lfun (-z⁻¹)

lemma continuousOn_PsiT : ContinuousOn PsiT U := by
  have h1 : ContinuousOn (fun z : ℂ => Lfun (-(z + 1)⁻¹)) U :=
    Lfun_spec.1.continuousOn.comp (by
      have hinv : ContinuousOn (fun z : ℂ => (z + 1)⁻¹) U :=
        ContinuousOn.inv₀ (by fun_prop) (fun z hz => by
          have hz1 : 0 < (z + 1).im := by
            have h := U_im_pos hz
            simpa [Complex.add_im] using h
          intro h
          rw [h] at hz1
          simp only [Complex.zero_im, lt_self_iff_false] at hz1)
      exact hinv.neg) (fun z hz => im_neg_inv_pos (U_im_pos (U_add_one hz)))
  have h2 : ContinuousOn (fun z : ℂ => Lfun (-z⁻¹)) U :=
    Lfun_spec.1.continuousOn.comp continuousOn_neg_inv (fun z hz => im_neg_inv_pos hz)
  exact h1.add h2

lemma exp_PsiT {z : ℂ} (hz : z ∈ U) : Complex.exp (PsiT z) = 1 := by
  have hz1 : z + 1 ∈ U := U_add_one hz
  have hzU' : -z⁻¹ ∈ U := im_neg_inv_pos (U_im_pos hz)
  have hzU'' : -(z + 1)⁻¹ ∈ U := im_neg_inv_pos (U_im_pos hz1)
  have hb : lamSC z ≠ 0 := lamSC_ne_zero (U_im_pos hz)
  have hb1 : lamSC (z + 1) ≠ 0 := lamSC_ne_zero (U_im_pos hz1)
  have hexp : Complex.exp (PsiT z) = Complex.exp (Lfun (-(z + 1)⁻¹)) * Complex.exp (Lfun (-z⁻¹)) := by
    rw [PsiT, Complex.exp_add]
  rw [hexp, Lfun_spec.2.1 _ hzU'', Lfun_spec.2.1 _ hzU', ← lamSC_eq_lamC_inv hz,
    ← lamSC_eq_lamC_inv hz1, lamSC_add_one hz]
  field_simp

lemma exp_eq_one_PsiT {z : ℂ} (hz : z ∈ U) : ∃ n : ℤ, PsiT z = n * (2 * Real.pi * Complex.I) :=
  Complex.exp_eq_one_iff.mp (exp_PsiT hz)

lemma tendsto_PsiT : Tendsto (fun T : ℝ => PsiT ((T : ℂ) * Complex.I)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun T : ℝ => LamS ((T : ℂ) * Complex.I + 1) + LamS ((T : ℂ) * Complex.I))
      atTop (𝓝 0) := by
    have h := tendsto_LamS_imag_add_one.add tendsto_LamS_imag
    simpa using h
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  rw [PsiT, Lfun_inv_eq_LamS _ (mul_I_add_one_mem_W (by linarith)),
    Lfun_inv_eq_LamS _ (mul_I_mem_W (by linarith))]

/-- The `T`-law for `Lfun_S(z) = Lfun(-z⁻¹)` on `U`. -/
theorem lfun_inv_add_one (z : ℂ) (hz : z ∈ U) :
    Lfun (-(z + 1)⁻¹) = -Lfun (-z⁻¹) := by
  have hconst : ∀ w ∈ U, PsiT w = PsiT (2 * Complex.I) :=
    Work.Analysis.DiscreteValues.eq_const_of_isPreconnected isPreconnected_U continuousOn_PsiT
      (fun w hw => exp_eq_one_PsiT hw)
      (by simp only [U, Set.mem_ofPred_eq, Complex.mul_I_im]; norm_num)
  have h2 : Tendsto (fun T : ℝ => PsiT ((T : ℂ) * Complex.I)) atTop (𝓝 (PsiT (2 * Complex.I))) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    exact (hconst _ (mul_I_mem_U (by linarith))).symm
  have hz0 : PsiT (2 * Complex.I) = 0 := tendsto_nhds_unique h2 tendsto_PsiT
  have hz' : PsiT z = 0 := by rw [hconst z hz, hz0]
  rw [PsiT] at hz'
  linear_combination hz'

end Work.Kernels.LogLambda
