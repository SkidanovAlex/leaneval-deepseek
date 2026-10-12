import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Submission.Work.BoseBoxFock.L1Tails.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.L1Tails.coulDualFubini`

The duality ("Fubini") identity behind T3 (`coulombDual`) of the `L¹`-weight tail chapter
(`Submission/Work/BoseBoxFock/L1Tails/`): for `W ∈ L¹(ℝ³, ℝ)` and `ψ ∈ C_c^∞(ℝ³, ℂ)`,

`∫_x W(x) ψ(x) dx = (2π)^{-3} ∫_p Ŵ(p) ψ̂(−p) dp`,   `Ŵ = kinFT W`, `ψ̂ = kinFT ψ`,

together with the integrability of the dual integrand `p ↦ Ŵ(p) ψ̂(−p)`.

Note that **no** `L²` hypothesis is imposed on `W`: the `p`-integral converges because `ψ̂` is
Schwartz.  The identity is the Fubini computation on the absolutely convergent double integral
`∬ W(x) ψ̂(−p) e^{−i⟪p,x⟫}`, the two analytic inputs being

* the pointwise Fourier inversion `(†) : ψ(x) = (2π)^{-3} ∫_p ψ̂(−p) e^{−i⟪p,x⟫} dp` of the
  smooth compactly supported `ψ` (`kinFT_inversion_neg`, from Mathlib's
  `MeasureTheory.Integrable.fourier_fourierInv_eq` with the rescaling `p = (2π) • w`), and
* the `L¹`-summability `ψ̂ ∈ L¹` (`integrable_kinFT_of_schwartz`) making the double integral
  absolutely convergent — this is what replaces the missing `W ∈ L²`.
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace Work.BoseBoxFock.L1Tails

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## 1. Analytic preliminaries -/

/-- The `p`-convention Fourier transform of an integrable function is continuous. -/
private lemma continuous_kinFT_of_integrable {u : E3 → ℂ} (hu : MeasureTheory.Integrable u) :
    Continuous (Submission.BoseGases.kinFT u) := by
  rw [show Submission.BoseGases.kinFT u
      = fun p : E3 => FourierTransform.fourier u ((2 * Real.pi)⁻¹ • p)
      from funext fun p => Work.SmallBoxBridge.Resolve.kinFT_eq_fourier u p]
  exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hu).comp (continuous_const_smul _)

/-- The `L^∞`-bound `‖kinFT u p‖ ≤ ∫_y ‖u y‖` for the `p`-convention Fourier transform. -/
private lemma norm_kinFT_le_integral_norm (u : E3 → ℂ) (p : E3) :
    ‖Submission.BoseGases.kinFT u p‖ ≤ ∫ y, ‖u y‖ := by
  rw [Submission.BoseGases.kinFT]
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  apply integral_congr_ae
  filter_upwards with y
  rw [norm_mul, Complex.norm_exp]
  simp

/-- The exponential factor `e^{−i t}` is unimodular. -/
private lemma norm_exp_neg_I_mul (t : ℝ) : ‖Complex.exp (-(Complex.I * (t : ℂ)))‖ = 1 := by
  rw [Complex.norm_exp]; simp

/-- The Fourier transform of a Schwartz function is integrable. -/
private lemma integrable_fourier_of_schwartz (S : SchwartzMap E3 ℂ) :
    MeasureTheory.Integrable (fun q : E3 => FourierTransform.fourier (S : E3 → ℂ) q) := by
  rw [← SchwartzMap.fourier_coe]
  exact (SchwartzMap.fourierTransformCLM ℂ S).integrable

/-- In the `p`-convention, the transform `kinFT` of a Schwartz function is integrable. -/
private lemma integrable_kinFT_of_schwartz (S : SchwartzMap E3 ℂ) :
    MeasureTheory.Integrable (fun p : E3 => Submission.BoseGases.kinFT (S : E3 → ℂ) p) := by
  have hF := integrable_fourier_of_schwartz S
  have hEq : (fun p : E3 => Submission.BoseGases.kinFT (S : E3 → ℂ) p)
      = fun p : E3 => FourierTransform.fourier (S : E3 → ℂ) ((2 * Real.pi)⁻¹ • p) :=
    funext fun p => Work.SmallBoxBridge.Resolve.kinFT_eq_fourier _ p
  rw [hEq]
  exact hF.comp_smul (by positivity : ((2 * Real.pi)⁻¹ : ℝ) ≠ 0)

/-- The prefactor `(2π)^{-3}`, in the two readings occurring in the statement of
`coulDualFubini` (the `π` of the statement is the complex number `(Real.pi : ℂ)`). -/
private lemma pi_cube_inv_eq :
    ((2 * (Real.pi : ℂ)) ^ 3)⁻¹ = ((((2 * Real.pi) ^ 3 : ℝ)) : ℂ)⁻¹ := by
  have h2 : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  rw [h2, ← Complex.ofReal_mul, ← Complex.ofReal_pow, ← Complex.ofReal_inv]

/-! ## 2. Fourier inversion in the `p`-convention, reflected form -/

/-- **Fourier inversion in the `p`-convention, with the reflection in the transform variable.**

For `g ∈ L¹(ℝ³, ℂ)` with `𝓕 g ∈ L¹` and `g` continuous at `z`,

`∫_p \hat g(−p) e^{−i⟪p,z⟫} dp = (2π)³ g(z)`,   where `\hat g = kinFT g`.

It is the sign convention consumed by the Fubini computation of `coulDualFubini`, and follows
from Mathlib's inversion theorem `𝓕 (𝓕⁻ g) = g`
(`MeasureTheory.Integrable.fourier_fourierInv_eq`) after the substitution `p = (2π) • w` and
`𝓕⁻ g w = 𝓕 g (−w)`. -/
theorem kinFT_inversion_neg {g : E3 → ℂ} (hg : MeasureTheory.Integrable g)
    (hg' : MeasureTheory.Integrable (FourierTransform.fourier g)) {z : E3}
    (hz : ContinuousAt g z) :
    (∫ p : E3, Submission.BoseGases.kinFT g (-p) *
        Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))))
      = (((2 * Real.pi) ^ 3 : ℝ) : ℂ) * g z := by
  have hfin : Module.finrank ℝ E3 = 3 := by simp
  have hR : (2 * Real.pi) ≠ 0 := by positivity
  set F : E3 → ℂ := fun w => FourierTransform.fourier g (-w) *
      Complex.exp ((↑(-2 * Real.pi * inner ℝ w z)) * Complex.I) with hFdef
  -- the pointwise rescaling `p = (2π) • w`
  have hpointwise : ∀ p : E3, Submission.BoseGases.kinFT g (-p) *
        Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) = F ((2 * Real.pi)⁻¹ • p) := by
    intro p
    have hneg : -((2 * Real.pi)⁻¹ • p) = (2 * Real.pi)⁻¹ • (-p) := by rw [smul_neg]
    have harith : -2 * Real.pi * inner ℝ ((2 * Real.pi)⁻¹ • p) z = - inner ℝ p z := by
      rw [real_inner_smul_left]
      field_simp
    have hexp : (↑(-2 * Real.pi * inner ℝ ((2 * Real.pi)⁻¹ • p) z) : ℂ) * Complex.I
        = -(Complex.I * (inner ℝ p z : ℂ)) := by
      rw [harith]
      push_cast
      ring
    simp only [hFdef]
    rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier g (-p), hneg, hexp.symm]
  have hI1 : (∫ p : E3, Submission.BoseGases.kinFT g (-p) *
        Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))) = ∫ p : E3, F ((2 * Real.pi)⁻¹ • p) :=
    integral_congr_ae (Filter.Eventually.of_forall hpointwise)
  have hI2 : (∫ p : E3, F ((2 * Real.pi)⁻¹ • p))
      = (((2 * Real.pi) ^ 3 : ℝ) : ℂ) * ∫ w : E3, F w := by
    rw [Measure.integral_comp_inv_smul_of_nonneg volume F
      (by positivity : (0 : ℝ) ≤ 2 * Real.pi), hfin, Complex.real_smul]
  have hI3 : (∫ w : E3, F w)
      = FourierTransform.fourier (FourierTransform.fourierInv g) z := by
    rw [Real.fourier_eq']
    apply integral_congr_ae
    filter_upwards with w
    simp only [hFdef, smul_eq_mul, Real.fourierInv_eq_fourier_neg]
    ring
  have hI4 : FourierTransform.fourier (FourierTransform.fourierInv g) z = g z :=
    MeasureTheory.Integrable.fourier_fourierInv_eq hg hg' hz
  rw [hI1, hI2, hI3, hI4]

/-! ## 3. The duality identity -/

theorem coulDualFubini {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hW : MeasureTheory.Integrable W)
    {ψ : EuclideanSpace ℝ (Fin 3) → ℂ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.kinFT (fun x => ((W x : ℝ) : ℂ)) p
          * Submission.BoseGases.kinFT ψ (-p)) ∧
    (∫ x, ((W x : ℝ) : ℂ) * ψ x)
      = ((2 * (Real.pi : ℂ)) ^ 3)⁻¹
          * ∫ p, Submission.BoseGases.kinFT (fun x => ((W x : ℝ) : ℂ)) p
              * Submission.BoseGases.kinFT ψ (-p) := by
  -- `ψ` is Schwartz; both `ψ` and its transform are integrable
  set S : SchwartzMap E3 ℂ := hψc.toSchwartzMap hψ with hSdef
  have hScoe : (S : E3 → ℂ) = ψ := by
    rw [hSdef]
    funext x
    simp
  have hψ_int : MeasureTheory.Integrable ψ := hScoe ▸ S.integrable
  have hψft_int : MeasureTheory.Integrable (FourierTransform.fourier ψ) := hScoe ▸
    integrable_fourier_of_schwartz S
  have hkin_int : MeasureTheory.Integrable (fun p : E3 => Submission.BoseGases.kinFT ψ p) :=
    hScoe ▸ integrable_kinFT_of_schwartz S
  have hkin_neg_int : MeasureTheory.Integrable (fun p : E3 =>
      Submission.BoseGases.kinFT ψ (-p)) := by
    have h := hkin_int.comp_smul (R := -1) (by norm_num)
    simpa using h
  have hWc_int : MeasureTheory.Integrable (fun x : E3 => ((W x : ℝ) : ℂ)) := hW.ofReal
  have hWc_norm_int : MeasureTheory.Integrable (fun x : E3 => ‖((W x : ℝ) : ℂ)‖) := hWc_int.norm
  have hne : (((2 * Real.pi) ^ 3 : ℝ) : ℂ) ≠ 0 := by
    rw [ne_eq, Complex.ofReal_eq_zero]
    positivity
  -- the pointwise inversion `(†)`
  have hInv : ∀ x : E3, ψ x = ((((2 * Real.pi) ^ 3 : ℝ)) : ℂ)⁻¹ *
      ∫ p : E3, Submission.BoseGases.kinFT ψ (-p) *
        Complex.exp (-(Complex.I * (inner ℝ p x : ℂ))) := by
    intro x
    have h := kinFT_inversion_neg hψ_int hψft_int hψ.continuous.continuousAt (z := x)
    rw [h, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  -- integrability of the dual integrand
  have hprod : MeasureTheory.Integrable (fun p : E3 =>
      Submission.BoseGases.kinFT (fun x => ((W x : ℝ) : ℂ)) p
        * Submission.BoseGases.kinFT ψ (-p)) := by
    have h := MeasureTheory.Integrable.mul_bdd (f := fun p : E3 =>
        Submission.BoseGases.kinFT ψ (-p))
      (g := fun p : E3 => Submission.BoseGases.kinFT (fun x => ((W x : ℝ) : ℂ)) p)
      (c := ∫ y : E3, ‖((W y : ℝ) : ℂ)‖) hkin_neg_int
      (continuous_kinFT_of_integrable hWc_int).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => norm_kinFT_le_integral_norm _ p)
    exact h.congr (Filter.Eventually.of_forall fun p => mul_comm _ _)
  refine ⟨hprod, ?_⟩
  -- the double integrand of the Fubini computation
  set Φ : E3 → E3 → ℂ := fun x p => ((W x : ℝ) : ℂ) *
      (Submission.BoseGases.kinFT ψ (-p) * Complex.exp (-(Complex.I * (inner ℝ p x : ℂ))))
    with hΦdef
  have hΦ_int : MeasureTheory.Integrable (Function.uncurry Φ)
      ((volume : MeasureTheory.Measure E3).prod (volume : MeasureTheory.Measure E3)) := by
    refine MeasureTheory.Integrable.mono' (hWc_norm_int.mul_prod hkin_neg_int.norm) ?_ ?_
    · -- a.e. strong measurability of the double integrand
      have hAfst : AEStronglyMeasurable (fun z : E3 × E3 => W z.1)
          ((volume : MeasureTheory.Measure E3).prod (volume : MeasureTheory.Measure E3)) :=
        hW.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
      have hA : AEStronglyMeasurable (fun z : E3 × E3 => ((W z.1 : ℝ) : ℂ))
          ((volume : MeasureTheory.Measure E3).prod (volume : MeasureTheory.Measure E3)) :=
        Complex.continuous_ofReal.comp_aestronglyMeasurable hAfst
      have hBcont : Continuous (fun z : E3 × E3 =>
          Submission.BoseGases.kinFT ψ (-z.2) *
            Complex.exp (-(Complex.I * (inner ℝ z.2 z.1 : ℂ)))) := by
        refine Continuous.mul ?_ ?_
        · exact (continuous_kinFT_of_integrable hψ_int).comp continuous_snd.neg
        · refine Complex.continuous_exp.comp (Continuous.neg ?_)
          exact Continuous.mul continuous_const
            (Complex.continuous_ofReal.comp (continuous_snd.inner continuous_fst))
      have hEq : Function.uncurry Φ = fun z : E3 × E3 => ((W z.1 : ℝ) : ℂ) *
          (Submission.BoseGases.kinFT ψ (-z.2) *
            Complex.exp (-(Complex.I * (inner ℝ z.2 z.1 : ℂ)))) := by
        funext z
        rw [hΦdef]
        rfl
      rw [hEq]
      exact hA.mul hBcont.aestronglyMeasurable
    · -- the pointwise norm bound
      filter_upwards with z
      rw [Function.uncurry_apply_pair, hΦdef]
      rw [norm_mul, norm_mul, norm_exp_neg_I_mul]
      simp
  have hswap := MeasureTheory.integral_integral_swap hΦ_int
  -- the left-hand side as the iterated integral
  have hLHS : (∫ x, ((W x : ℝ) : ℂ) * ψ x)
      = ((((2 * Real.pi) ^ 3 : ℝ)) : ℂ)⁻¹ * ∫ x, ∫ p, Φ x p := by
    have hpt : ∀ x : E3, ((W x : ℝ) : ℂ) * ψ x
        = ((((2 * Real.pi) ^ 3 : ℝ)) : ℂ)⁻¹ * ∫ p, Φ x p := by
      intro x
      have h1 : (∫ p : E3, Φ x p) = ((W x : ℝ) : ℂ) *
          ∫ p : E3, Submission.BoseGases.kinFT ψ (-p) *
            Complex.exp (-(Complex.I * (inner ℝ p x : ℂ))) := by
        rw [hΦdef]
        rw [← integral_const_mul]
      rw [hInv x, h1]
      ring
    calc (∫ x, ((W x : ℝ) : ℂ) * ψ x)
        = ∫ x, ((((2 * Real.pi) ^ 3 : ℝ)) : ℂ)⁻¹ * ∫ p, Φ x p := by
          apply integral_congr_ae
          filter_upwards with x
          exact hpt x
      _ = ((((2 * Real.pi) ^ 3 : ℝ)) : ℂ)⁻¹ * ∫ x, ∫ p, Φ x p := by
          rw [integral_const_mul]
  -- the right-hand side as the iterated integral
  have hRHS : (∫ p, ∫ x, Φ x p) = ∫ p, Submission.BoseGases.kinFT (fun x => ((W x : ℝ) : ℂ)) p
      * Submission.BoseGases.kinFT ψ (-p) := by
    apply integral_congr_ae
    filter_upwards with p
    have h1 : (∫ x : E3, Φ x p) = (∫ x : E3, ((W x : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (inner ℝ p x : ℂ)))) * Submission.BoseGases.kinFT ψ (-p) := by
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards with x
      rw [hΦdef]
      ring
    have h2 : (∫ x : E3, ((W x : ℝ) : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p x : ℂ))))
        = Submission.BoseGases.kinFT (fun x => ((W x : ℝ) : ℂ)) p := by
      rw [Submission.BoseGases.kinFT]
      apply integral_congr_ae
      filter_upwards with x
      ring
    rw [h1, h2]
  rw [hLHS, hswap, hRHS, pi_cube_inv_eq]

end Work.BoseBoxFock.L1Tails
