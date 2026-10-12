import Mathlib.Tactic.Have
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.OneBodyKin.ProfHatDecay
import Submission.Work.OneBodyKin.integrable_chiMul_integral
import Submission.Work.OneBodyKin.profHat_sq_integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.symA_fsKinCoeff_far_le` — the far-regime bound on the unprojected symbol

The unprojected symbol of the moving-box family at scale `ℓ = 1` is

    `symA 1 F ρ = (2π)⁻³ ∫_p F ‖ρ + p‖ · profHat(p)² dp`

(`Work.OneBodyKin.Defs`).  For the (untruncated) FS cut-off `F = fsKinCoeff C = [·−C]₊²` and
momenta `ρ` in the *far regime* `C ≤ ‖ρ‖`, the symbol is dominated by the quadratic polynomial

    `symA 1 (fsKinCoeff C) ρ ≤ (‖ρ‖−C)² + 2(‖ρ‖−C)·M₁ + M₂`,

with `M₁ = (2π)⁻³ ∫ profHat(t)²‖t‖ dt` and `M₂ = (2π)⁻³ ∫ profHat(t)²‖t‖² dt` the first two
moments of the bump profile.  This is the `symA`-half of the far-regime estimate behind
`Phi_far_nonneg` (README §5 item (i)): the quadratic growth of the symbol is explicit and *sharp
in the leading constant*, which is what lets `‖ρ‖² − @A(ρ)` be bounded below by
`2(C − M₁)‖ρ‖ − const`.

## The proof in three steps

1. **Pointwise domination.**  Since `C ≤ ‖ρ‖` we have `‖ρ + p‖ − C ≤ (‖ρ‖−C) + ‖p‖` with a
   nonnegative right side, so `[‖ρ+p‖−C]₊² ≤ ((‖ρ‖−C) + ‖p‖)²`; multiplying by `profHat(p)² ≥ 0`
   and integrating against the (positive) weight `(2π)⁻³` gives the bound by
   `∫_p ((‖ρ‖−C) + ‖p‖)² profHat(p)² dp`.
2. **Expansion of the majorant.**  `(a + ‖p‖)² = a² + 2a‖p‖ + ‖p‖²` with `a = ‖ρ‖ − C`, and the
   three pieces are integrable (`profHat` is Schwartz: `integrable_profHat_sq_mul_norm_pow`), so
   linearity of the integral gives the exact value
   `a²(2π)³ + 2a ∫profHat²‖t‖ + ∫profHat²‖t‖²`.
3. **Normalisation.**  `∫_p profHat(p)² dp = (2π)³` (`profHat_sq_integral`), so the `a²` term
   cancels the prefactor `(2π)⁻³` and leaves `a²`.
-/

noncomputable section

open MeasureTheory
open scoped Topology Real

namespace Work.OneBodyKin

open Submission.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000

/-! ## 1. Integrability of the weighted squared profile -/

/-- `p ↦ (1+‖p‖)^{-10}` is integrable on `ℝ³` (the exponent `10` beats the dimension `3`). -/
private lemma integrable_one_add_norm_inv_ten :
    Integrable (fun p : ℝ³ => ((1 + ‖p‖ : ℝ) ^ 10)⁻¹) := by
  have hb : Integrable (fun p : ℝ³ => (1 + ‖p‖) ^ (-(10 : ℝ))) := by
    refine integrable_one_add_norm (E := ℝ³) (μ := volume) (r := 10) ?_
    rw [finrank_euclideanSpace_fin]
    norm_num
  refine hb.congr (Filter.Eventually.of_forall (fun p => ?_))
  show (1 + ‖p‖) ^ (-(10 : ℝ)) = ((1 + ‖p‖ : ℝ) ^ 10)⁻¹
  rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + ‖p‖)]
  congr 1
  exact Real.rpow_natCast (1 + ‖p‖) 10

/-- Pointwise domination of `profHat(p)² ‖p‖^n` by `D² (1+‖p‖)^{-10}` for `n ≤ 2`, given the
decay `|profHat p| ≤ D/(1+‖p‖)^6`. -/
private lemma profHat_sq_mul_norm_pow_le {D : ℝ}
    (hD : ∀ p : ℝ³, |profHat p| ≤ D / (1 + ‖p‖) ^ 6) {n : ℕ} (hn : n ≤ 2) (p : ℝ³) :
    (profHat p) ^ 2 * ‖p‖ ^ n ≤ D ^ 2 * ((1 + ‖p‖) ^ 10)⁻¹ := by
  have hsq : (profHat p) ^ 2 ≤ D ^ 2 * ((1 + ‖p‖) ^ 12)⁻¹ := by
    have h1 : (profHat p) ^ 2 ≤ (D / (1 + ‖p‖) ^ 6) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hD p) 2
    have h2 : (D / (1 + ‖p‖) ^ 6) ^ 2 = D ^ 2 * ((1 + ‖p‖) ^ 12)⁻¹ := by
      rw [div_pow, ← pow_mul, div_eq_mul_inv]
    rwa [h2] at h1
  have hratio : (1 + ‖p‖) ^ n * ((1 + ‖p‖) ^ 12)⁻¹ ≤ ((1 + ‖p‖) ^ 10)⁻¹ := by
    have h12 : (0 : ℝ) < (1 + ‖p‖) ^ 12 := by positivity
    have h10 : (0 : ℝ) < (1 + ‖p‖) ^ 10 := by positivity
    rw [show (1 + ‖p‖) ^ n * ((1 + ‖p‖) ^ 12)⁻¹ = (1 + ‖p‖) ^ n / (1 + ‖p‖) ^ 12 from
          (div_eq_mul_inv _ _).symm,
        show ((1 + ‖p‖ : ℝ) ^ 10)⁻¹ = 1 / (1 + ‖p‖) ^ 10 from (one_div _).symm,
        div_le_div_iff₀ h12 h10]
    rw [one_mul, ← pow_add]
    exact pow_le_pow_right₀ (by linarith [norm_nonneg p]) (by omega)
  have hnn : 0 ≤ ‖p‖ ^ n := pow_nonneg (norm_nonneg p) n
  have hnk : ‖p‖ ^ n ≤ (1 + ‖p‖) ^ n :=
    pow_le_pow_left₀ (norm_nonneg p) (by linarith [norm_nonneg p]) n
  calc (profHat p) ^ 2 * ‖p‖ ^ n
      ≤ (D ^ 2 * ((1 + ‖p‖) ^ 12)⁻¹) * ‖p‖ ^ n := mul_le_mul_of_nonneg_right hsq hnn
    _ = D ^ 2 * (‖p‖ ^ n * ((1 + ‖p‖) ^ 12)⁻¹) := by ring
    _ ≤ D ^ 2 * ((1 + ‖p‖) ^ n * ((1 + ‖p‖) ^ 12)⁻¹) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hnk (by positivity)) (sq_nonneg D)
    _ ≤ D ^ 2 * ((1 + ‖p‖) ^ 10)⁻¹ := mul_le_mul_of_nonneg_left hratio (sq_nonneg D)

/-- `p ↦ profHat(p)² ‖p‖^n` is integrable for `n ≤ 2` (from the Schwartz decay of the bump
profile, `ProfHatDecay`). -/
private lemma integrable_profHat_sq_mul_norm_pow (n : ℕ) (hn : n ≤ 2) :
    Integrable (fun p : ℝ³ => (profHat p) ^ 2 * ‖p‖ ^ n) := by
  obtain ⟨D, _, hD⟩ := ProfHatDecay
  refine Integrable.mono' (integrable_one_add_norm_inv_ten.const_mul (D ^ 2)) ?_ ?_
  · exact ((continuous_profHat.pow 2).mul (continuous_norm.pow n)).aestronglyMeasurable
  · filter_upwards with p
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg (norm_nonneg p) n))]
    exact profHat_sq_mul_norm_pow_le hD hn p

/-! ## 2. The exact integral of the quadratic majorant -/

/-- **The `p`-integral of the quadratic majorant**, in closed form: for every `a : ℝ`,

    `∫_p (a + ‖p‖)² profHat(p)² dp = a²(2π)³ + 2a ∫profHat²‖t‖ + ∫profHat²‖t‖²`.

This is the pointwise expansion `(a+‖p‖)² = a² + 2a‖p‖ + ‖p‖²` pushed through the integral,
with the constant term evaluated by `profHat_sq_integral`. -/
private lemma integral_sq_shift_profHat (a : ℝ) :
    (∫ p : ℝ³, (a + ‖p‖) ^ 2 * (profHat p) ^ 2)
      = a ^ 2 * (2 * Real.pi) ^ 3
        + 2 * a * (∫ p : ℝ³, (profHat p) ^ 2 * ‖p‖)
        + ∫ p : ℝ³, (profHat p) ^ 2 * ‖p‖ ^ 2 := by
  have hI0 : Integrable (fun p : ℝ³ => (profHat p) ^ 2) := by
    have h := integrable_profHat_sq_mul_norm_pow 0 (by norm_num)
    simpa using h
  have hI1 : Integrable (fun p : ℝ³ => (profHat p) ^ 2 * ‖p‖) := by
    have h := integrable_profHat_sq_mul_norm_pow 1 (by norm_num)
    simpa using h
  have hI2 : Integrable (fun p : ℝ³ => (profHat p) ^ 2 * ‖p‖ ^ 2) :=
    integrable_profHat_sq_mul_norm_pow 2 (by norm_num)
  have hI0val : (∫ p : ℝ³, (profHat p) ^ 2) = (2 * Real.pi) ^ 3 := profHat_sq_integral
  have hEq : (fun p : ℝ³ => (a + ‖p‖) ^ 2 * (profHat p) ^ 2)
      = fun p : ℝ³ => a ^ 2 * (profHat p) ^ 2 + (2 * a) * ((profHat p) ^ 2 * ‖p‖)
          + (profHat p) ^ 2 * ‖p‖ ^ 2 := by
    funext p; ring
  rw [hEq]
  have hT1 : Integrable (fun p : ℝ³ => a ^ 2 * (profHat p) ^ 2) := hI0.const_mul _
  have hT2 : Integrable (fun p : ℝ³ => (2 * a) * ((profHat p) ^ 2 * ‖p‖)) := hI1.const_mul _
  change (∫ p : ℝ³, (((fun p : ℝ³ => a ^ 2 * (profHat p) ^ 2) : ℝ³ → ℝ)
      + ((fun p : ℝ³ => (2 * a) * ((profHat p) ^ 2 * ‖p‖)) : ℝ³ → ℝ)) p
      + ((fun p : ℝ³ => (profHat p) ^ 2 * ‖p‖ ^ 2) : ℝ³ → ℝ) p)
    = a ^ 2 * (2 * Real.pi) ^ 3
        + 2 * a * (∫ p : ℝ³, (profHat p) ^ 2 * ‖p‖)
        + ∫ p : ℝ³, (profHat p) ^ 2 * ‖p‖ ^ 2
  rw [integral_add (hT1.add hT2) hI2]
  simp only [Pi.add_apply]
  rw [integral_add hT1 hT2]
  rw [integral_const_mul, integral_const_mul, hI0val]

/-! ## 3. The far-regime bound -/

theorem symA_fsKinCoeff_far_le {C : ℝ} (ρ : EuclideanSpace ℝ (Fin 3)) (hρ : C ≤ ‖ρ‖) :
    Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff C) ρ
      ≤ (‖ρ‖ - C) ^ 2
        + 2 * (‖ρ‖ - C) * (((2 * Real.pi) ^ 3)⁻¹ *
            ∫ t : EuclideanSpace ℝ (Fin 3), (Work.OneBodyKin.profHat t) ^ 2 * ‖t‖)
        + ((2 * Real.pi) ^ 3)⁻¹ *
            ∫ t : EuclideanSpace ℝ (Fin 3), (Work.OneBodyKin.profHat t) ^ 2 * ‖t‖ ^ 2 := by
  have hI0 : Integrable (fun p : ℝ³ => (profHat p) ^ 2) := by
    have h := integrable_profHat_sq_mul_norm_pow 0 (by norm_num)
    simpa using h
  have hI1 : Integrable (fun p : ℝ³ => (profHat p) ^ 2 * ‖p‖) := by
    have h := integrable_profHat_sq_mul_norm_pow 1 (by norm_num)
    simpa using h
  have hI2 : Integrable (fun p : ℝ³ => (profHat p) ^ 2 * ‖p‖ ^ 2) :=
    integrable_profHat_sq_mul_norm_pow 2 (by norm_num)
  -- the pointwise domination of the integrand
  have hpt : ∀ p : ℝ³, fsKinCoeff C ‖ρ + p‖ * (profHat p) ^ 2
      ≤ ((‖ρ‖ - C) + ‖p‖) ^ 2 * (profHat p) ^ 2 := by
    intro p
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    show fsKinCoeff C ‖ρ + p‖ ≤ ((‖ρ‖ - C) + ‖p‖) ^ 2
    unfold fsKinCoeff
    refine pow_le_pow_left₀ (le_max_right (‖ρ + p‖ - C) 0) ?_ 2
    refine max_le ?_ ?_
    · have h : ‖ρ + p‖ ≤ ‖ρ‖ + ‖p‖ := norm_add_le _ _
      linarith
    · linarith [norm_nonneg p]
  -- integrability of the majorant
  have hGint : Integrable (fun p : ℝ³ => ((‖ρ‖ - C) + ‖p‖) ^ 2 * (profHat p) ^ 2) := by
    have hEq : (fun p : ℝ³ => ((‖ρ‖ - C) + ‖p‖) ^ 2 * (profHat p) ^ 2)
        = fun p : ℝ³ => (‖ρ‖ - C) ^ 2 * (profHat p) ^ 2
            + (2 * (‖ρ‖ - C)) * ((profHat p) ^ 2 * ‖p‖)
            + (profHat p) ^ 2 * ‖p‖ ^ 2 := by
      funext p; ring
    rw [hEq]
    exact ((hI0.const_mul _).add (hI1.const_mul _)).add hI2
  have hfint : Integrable (fun p : ℝ³ => fsKinCoeff C ‖ρ + p‖ * (profHat p) ^ 2) := by
    refine hGint.mono' ?_ ?_
    · have hc1 : Continuous (fun r : ℝ => fsKinCoeff C r) := by
        unfold fsKinCoeff
        exact ((continuous_id.sub continuous_const).max continuous_const).pow 2
      have hc2 : Continuous (fun p : ℝ³ => ‖ρ + p‖) := (continuous_const.add continuous_id).norm
      exact ((hc1.comp hc2).mul (continuous_profHat.pow 2)).aestronglyMeasurable
    · filter_upwards with p
      rw [Real.norm_of_nonneg (mul_nonneg (fsKinCoeff_nonneg C _) (sq_nonneg _))]
      exact hpt p
  have hmono : (∫ p : ℝ³, fsKinCoeff C ‖ρ + p‖ * (profHat p) ^ 2)
      ≤ ∫ p : ℝ³, ((‖ρ‖ - C) + ‖p‖) ^ 2 * (profHat p) ^ 2 :=
    integral_mono hfint hGint hpt
  have hsymA : symA 1 (fsKinCoeff C) ρ
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, fsKinCoeff C ‖ρ + p‖ * (profHat p) ^ 2 := by
    simp only [symA, inv_one, one_smul]
  rw [hsymA]
  calc ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, fsKinCoeff C ‖ρ + p‖ * (profHat p) ^ 2
      ≤ ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, ((‖ρ‖ - C) + ‖p‖) ^ 2 * (profHat p) ^ 2 :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = ((2 * Real.pi) ^ 3)⁻¹ * ((‖ρ‖ - C) ^ 2 * (2 * Real.pi) ^ 3
          + 2 * (‖ρ‖ - C) * (∫ p : ℝ³, (profHat p) ^ 2 * ‖p‖)
          + ∫ p : ℝ³, (profHat p) ^ 2 * ‖p‖ ^ 2) := by rw [integral_sq_shift_profHat]
    _ = (‖ρ‖ - C) ^ 2
          + 2 * (‖ρ‖ - C) * (((2 * Real.pi) ^ 3)⁻¹ * (∫ p : ℝ³, (profHat p) ^ 2 * ‖p‖))
          + ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : ℝ³, (profHat p) ^ 2 * ‖p‖ ^ 2) := by
        rw [show ((2 * Real.pi) ^ 3)⁻¹ * ((‖ρ‖ - C) ^ 2 * (2 * Real.pi) ^ 3
              + 2 * (‖ρ‖ - C) * (∫ p : ℝ³, (profHat p) ^ 2 * ‖p‖)
              + ∫ p : ℝ³, (profHat p) ^ 2 * ‖p‖ ^ 2)
            = (‖ρ‖ - C) ^ 2 * (((2 * Real.pi) ^ 3)⁻¹ * (2 * Real.pi) ^ 3)
              + 2 * (‖ρ‖ - C) * (((2 * Real.pi) ^ 3)⁻¹ * (∫ p : ℝ³, (profHat p) ^ 2 * ‖p‖))
              + ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : ℝ³, (profHat p) ^ 2 * ‖p‖ ^ 2) from by ring]
        rw [inv_mul_cancel₀ (by positivity : (2 * Real.pi) ^ 3 ≠ 0), mul_one]

end Work.OneBodyKin
