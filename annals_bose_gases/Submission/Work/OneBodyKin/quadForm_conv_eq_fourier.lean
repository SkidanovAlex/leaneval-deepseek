import Mathlib.Tactic.Have
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Fourier.Convolution
import Submission.Work.OneBodyKin.Defs
import Submission.Work.OneBodyKin.convForm_eq_doubleIntegral
import Submission.Work.OneBodyKin.integrable_fourier_mul_normSq
import Submission.Work.OneBodyKin.integral_fourier_re_of_integrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.quadForm_conv_eq_fourier` — the convolution quadratic form in Fourier space

For a *real* kernel `k ∈ L¹(ℝ³)` and a real `C_c^∞` test function `ψ`, the quadratic form of the
convolution operator with kernel `k`,

  `∫_x ∫_y k (x - y) ψ x ψ y`,

is diagonal in the `p`-convention Fourier transform `kinFT u q = ∫_z e^{-i⟪q,z⟫} u z dz`:

  `∫_x ∫_y k (x-y) ψ x ψ y = (2π)⁻³ ∫_q Re(kinFT k q) · ‖kinFT ψ q‖² dq`,

the real part appearing because `kinFT k (-q) = conj (kinFT k q)` (`k` real) while
`‖kinFT ψ (-q)‖² = ‖kinFT ψ q‖²` (`ψ` real), so the `q`-integral of `kinFT k · ‖kinFT ψ‖²`
is already real.

## Proof

Write `kc = (k : ℝ³ → ℂ)`, `ψc = (ψ : ℝ³ → ℂ)` and `G = kc ⋆ ψc` (Mathlib's convolution,
`G x = ∫_t kc t · ψc (x-t) dt`).

* `convForm_eq_doubleIntegral` rewrites the real double integral as the complex quadratic form
  `∫_x G x · ψc x` (change of variables in the inner integral, then `integral_ofReal`);
* `Commons.Analysis.Fourier.plancherel_one_sided_schwartz` (one-sided Plancherel, `G` integrable
  and `ψc` a Schwartz function) turns it into `∫_p 𝓕G p · 𝓕ψc (-p) dp`;
* `Real.fourier_mul_convolution_eq` computes `𝓕G = 𝓕kc · 𝓕ψc`, and
  `fourier_neg_eq_conj_ofReal` gives `𝓕ψc (-p) = conj (𝓕ψc p)`, so the integrand is
  `𝓕kc p · ↑(‖𝓕ψc p‖²)`;
* `integrable_fourier_mul_normSq` makes it integrable, and `integral_fourier_re_of_integrable`
  moves `re` inside the integral, producing `∫_p (𝓕kc p).re · ‖𝓕ψc p‖²`;
* `kinFT` is Mathlib's `𝓕` at the frequency `(2π)⁻¹ • q`
  (`Work.SmallBoxBridge.Resolve.kinFT_eq_fourier`), and the substitution `q ↦ (2π) • p`
  (`Measure.integral_comp_inv_smul_of_nonneg`) supplies the prefactor `(2π)⁻³`.
-/

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

namespace Work.OneBodyKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-- **Reflection/conjugation of the Fourier transform of a real-valued function**:
`𝓕 (u : ℂ) (-p) = conj (𝓕 (u : ℂ) p)` for `u : ℝ³ → ℝ` (no regularity needed). -/
lemma fourier_neg_eq_conj_ofReal (u : ℝ³ → ℝ) (p : ℝ³) :
    𝓕 (fun z => (u z : ℂ)) (-p) = (starRingEnd ℂ) (𝓕 (fun z => (u z : ℂ)) p) := by
  rw [Real.fourier_eq', Real.fourier_eq']
  simp only [smul_eq_mul]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with v
  rw [map_mul, Complex.conj_ofReal]
  congr 1
  rw [← Complex.exp_conj]
  congr 1
  rw [inner_neg_right]
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- Unfolding of `kinFT` with the factors in the order used downstream:
`kinFT k q = ∫_z (k z : ℂ) · e^{-i⟪q,z⟫} dz`. -/
private lemma kinFT_mul_exp (k : ℝ³ → ℝ) (q : ℝ³) :
    Submission.BoseGases.kinFT (fun z => (k z : ℂ)) q
      = ∫ z, (k z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ q z : ℂ))) := by
  rw [Submission.BoseGases.kinFT]
  apply integral_congr_ae
  filter_upwards with z
  rw [mul_comm]

/-- The change of variables `q ↦ (2π)⁻¹ • q` spelling out the `(2π)⁻³` prefactor of the
`p`-convention Fourier transform on `ℝ³`. -/
private lemma inv_cube_mul_integral_comp_inv_smul (g : ℝ³ → ℝ) :
    ((2 * Real.pi) ^ 3)⁻¹ * ∫ q, g ((2 * Real.pi)⁻¹ • q) = ∫ p, g p := by
  have h := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg (μ := volume) (f := g)
    (R := 2 * Real.pi) (by positivity)
  rw [show Module.finrank ℝ ℝ³ = 3 from by simp [EuclideanSpace], smul_eq_mul] at h
  rw [h, ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero 3 (by positivity : (2 * Real.pi : ℝ) ≠ 0)), one_mul]

theorem quadForm_conv_eq_fourier {k : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hk : MeasureTheory.Integrable k) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    (∫ x : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3), k (x - y) * ψ x * ψ y)
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ q : EuclideanSpace ℝ (Fin 3),
          (∫ z : EuclideanSpace ℝ (Fin 3),
              (k z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ q z : ℂ)))).re
            * ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ)) q‖ ^ 2 := by
  -- integrability of the two complexifications
  have hψ_int : MeasureTheory.Integrable ψ :=
    hψ.continuous.integrable_of_hasCompactSupport hcs
  have hkc_int : MeasureTheory.Integrable (fun z : ℝ³ => (k z : ℂ)) := hk.ofReal
  have hψc_int : MeasureTheory.Integrable (fun z : ℝ³ => (ψ z : ℂ)) := hψ_int.ofReal
  have hψc_cont : ContDiff ℝ (⊤ : ENat) (fun z : ℝ³ => (ψ z : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      Complex.ofRealCLM.contDiff.comp hψ
  have hψc_cs : HasCompactSupport (fun z : ℝ³ => (ψ z : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      hcs.comp_left (show ((0 : ℝ) : ℂ) = 0 by simp)
  -- the convolution `G = kc ⋆ ψc`
  set G : ℝ³ → ℂ := MeasureTheory.convolution (fun z : ℝ³ => (k z : ℂ))
      (fun z : ℝ³ => (ψ z : ℂ)) (ContinuousLinearMap.mul ℂ ℂ) MeasureTheory.volume with hG
  have hG_int : MeasureTheory.Integrable G := by
    rw [hG]
    exact hkc_int.integrable_convolution _ hψc_int
  -- one-sided Plancherel with `ψc` packaged as a Schwartz function
  let ψs : SchwartzMap ℝ³ ℂ := hψc_cs.toSchwartzMap hψc_cont
  have hψs_coe : (ψs : ℝ³ → ℂ) = fun z : ℝ³ => (ψ z : ℂ) := rfl
  have hplan : ∫ x : ℝ³, G x * (ψ x : ℂ)
      = ∫ p : ℝ³, 𝓕 G p * 𝓕 (fun z : ℝ³ => (ψ z : ℂ)) (-p) := by
    have h := Commons.Analysis.Fourier.plancherel_one_sided_schwartz (f := G) hG_int ψs
    simpa only [hψs_coe] using h
  -- the Fourier transform of a convolution
  have hGft : ∀ p : ℝ³, 𝓕 G p
      = 𝓕 (fun z : ℝ³ => (k z : ℂ)) p * 𝓕 (fun z : ℝ³ => (ψ z : ℂ)) p := by
    intro p
    rw [hG]
    exact Real.fourier_mul_convolution_eq hkc_int hψc_int p
  -- the Plancherel identity in the form `∫_x G x ψc x = ∫_p 𝓕kc p · ‖𝓕ψc p‖²`
  have key1 : ∫ x : ℝ³, G x * (ψ x : ℂ)
      = ∫ p : ℝ³, 𝓕 (fun z : ℝ³ => (k z : ℂ)) p
          * ((‖𝓕 (fun z : ℝ³ => (ψ z : ℂ)) p‖ ^ 2 : ℝ) : ℂ) := by
    rw [hplan]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with p
    rw [hGft p, fourier_neg_eq_conj_ofReal ψ p, mul_assoc, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
  -- the real double integral is the complex quadratic form of `G`
  have hA : ((∫ x : ℝ³, ∫ y : ℝ³, k (x - y) * ψ x * ψ y : ℝ) : ℂ)
      = ∫ x : ℝ³, G x * (ψ x : ℂ) := by
    rw [convForm_eq_doubleIntegral k ψ, ← hG]
  -- take real parts
  have hJ := integrable_fourier_mul_normSq (k := k) (ψ := ψ) hk hψ hcs
  have hre := congrArg Complex.re (hA.trans key1)
  simp only [Complex.ofReal_re] at hre
  rw [integral_fourier_re_of_integrable hJ] at hre
  rw [hre]
  -- the change of variables `(2π)⁻¹ • q`, and `kinFT` vs `𝓕`
  rw [← inv_cube_mul_integral_comp_inv_smul
    (g := fun p : ℝ³ => (𝓕 (fun z : ℝ³ => (k z : ℂ)) p).re
      * ‖𝓕 (fun z : ℝ³ => (ψ z : ℂ)) p‖ ^ 2)]
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with q
  rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier (fun z : ℝ³ => (ψ z : ℂ)) q]
  rw [← kinFT_mul_exp k q,
    ← Work.SmallBoxBridge.Resolve.kinFT_eq_fourier (fun z : ℝ³ => (k z : ℂ)) q]

end Work.OneBodyKin
