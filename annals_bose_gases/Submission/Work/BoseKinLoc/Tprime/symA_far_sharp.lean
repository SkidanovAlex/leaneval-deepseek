import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.OneBodyKin.integrable_fsKinCoeff_shift_mul_profHat_sq
import Submission.Work.OneBodyKin.symA_fsKinCoeff_far_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Tprime.symA_far_sharp`

The **sharp far-regime bound** for the unprojected symbol of the moving-box family at box
size `ℓ = 1`: for every cut-off `C ≥ 0` and *every* momentum `ρ`,

    `symA 1 (fsKinCoeff C) ρ
       ≤ (‖ρ‖ − C)² + (2π)⁻³ ∫ profHat(p)²‖p‖² dp + 2C · (2π)⁻³ ∫ profHat(p)²‖p‖ dp`,

with `symA 1 F ρ = (2π)⁻³ ∫_p F ‖ρ+p‖ · profHat(p)² dp` and `fsKinCoeff C r = [r − C]₊²`.

This is the `symA`-half of the *gap* estimate that pays the error terms of the two-regime
Brietzke–Solovej `lm:kinloc` bound (see `Tprime/tprime_two_regime.lean`): in the far region
`‖ρ‖ ≥ (5/6)σ⁻¹` the right-hand side `(‖ρ‖ − C)² + O(1)` is *below*
`tprSymOne σ C ‖ρ‖ = (‖ρ‖ − (2σ)⁻¹)₊²` by a uniform gap, and the two moments
`M₁ = (2π)⁻³∫profHat²‖p‖`, `M₂ = (2π)⁻³∫profHat²‖p‖²` are the explicit error constants.

## The mechanism (the *reverse-triangle trick*)

Unlike `symA_fsKinCoeff_far_le` (which needs `C ≤ ‖ρ‖` and pays `2(‖ρ‖−C)M₁`), the present
bound holds for all `ρ` and pays the *cut-off-sized* `2C M₁`.  The pointwise input is the
elementary inequality

    `[a − C]₊² ≤ a² − 2C a' + C²`      for `a ≥ 0`, `a' := ‖ρ‖ − ‖p‖ ≤ a`, `C ≥ 0`,

proved by splitting on `C ≤ a` (in which case `a' ≤ a` gives the claim) and on `a ≤ C`
(in which case `[a−C]₊² = 0 ≤ (a−C)²`).  Integrating against `profHat(p)² ≥ 0` and using
`‖ρ+p‖ ≥ ‖ρ‖ − ‖p‖` (i.e. `a' ≤ a`) gives

    `symA 1 (fsKinCoeff C) ρ ≤ (2π)⁻³ ∫_p (‖ρ+p‖² − 2C(‖ρ‖−‖p‖) + C²) profHat(p)² dp`,

and the majorant is elementary: by the parallelogram identity and the parity of `profHat`

    `(2π)⁻³ ∫_p ‖ρ+p‖² profHat(p)² dp = ‖ρ‖² + M₂`

(the cross term `∫_p ⟪ρ,p⟫ profHat(p)² dp` vanishes), while the linear pieces contribute
`−2C‖ρ‖ + 2C M₁ + C²` and `(2π)⁻³∫profHat² = 1` (`profHat_sq_integral`).
-/

noncomputable section

open MeasureTheory

namespace Work.BoseKinLoc.Tprime

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Work.OneBodyKin

set_option maxHeartbeats 800000

/-! ## 1. The scalar reverse-triangle bound -/

/-- **The scalar core of the sharp far bound.**  For `C ≥ 0` and every `ρ, p`,

    `[‖ρ+p‖ − C]₊² ≤ ‖ρ+p‖² − 2C(‖ρ‖ − ‖p‖) + C²`.

Write `a = ‖ρ+p‖ ≥ a' := ‖ρ‖ − ‖p‖` (reverse triangle inequality).  If `C ≤ a` then
`[a−C]₊² = (a−C)² = a² − 2Ca + C² ≤ a² − 2Ca' + C²`; if `a ≤ C` the left side vanishes and
`a² − 2Ca' + C² ≥ a² − 2Ca + C² = (a−C)² ≥ 0`. -/
private lemma fsKinCoeff_le_reverse {C : ℝ} (hC : 0 ≤ C) (ρ p : ℝ³) :
    Submission.BoseGases.fsKinCoeff C ‖ρ + p‖
      ≤ ‖ρ + p‖ ^ 2 - 2 * C * (‖ρ‖ - ‖p‖) + C ^ 2 := by
  unfold Submission.BoseGases.fsKinCoeff
  have hle : ‖ρ‖ - ‖p‖ ≤ ‖ρ + p‖ := by
    have h := norm_sub_le (ρ + p) p
    rw [show (ρ + p) - p = ρ from by abel] at h
    linarith
  set a := ‖ρ + p‖ with ha
  by_cases h : C ≤ a
  · rw [max_eq_left (sub_nonneg.mpr h)]
    nlinarith [hle, hC, ha]
  · rw [max_eq_right (sub_nonpos.mpr (le_of_lt (not_le.mp h)))]
    rw [not_le] at h
    nlinarith [hle, hC, ha]

/-! ## 2. Integrability of the shifted squared profile -/

/-- `p ↦ ‖ρ+p‖² profHat(p)²` is integrable: `‖ρ+p‖² ≤ 2‖ρ‖² + 2‖p‖²` and
`profHat(p)²‖p‖^n` is integrable for `n ≤ 2` (`integrable_profHat_sq_mul_norm_pow`). -/
private lemma integrable_norm_shift_sq (ρ : ℝ³) :
    Integrable (fun p : ℝ³ => ‖ρ + p‖ ^ 2 * (profHat p) ^ 2) := by
  have hI0 : Integrable (fun p : ℝ³ => (profHat p) ^ 2) := by
    simpa using integrable_profHat_sq_mul_norm_pow 0 (by norm_num)
  have hI2 : Integrable (fun p : ℝ³ => (profHat p) ^ 2 * ‖p‖ ^ 2) :=
    integrable_profHat_sq_mul_norm_pow 2 le_rfl
  refine ((hI0.const_mul (2 * ‖ρ‖ ^ 2)).add (hI2.const_mul 2)).mono' ?_ ?_
  · exact (((continuous_const.add continuous_id).norm.pow 2).mul
      (continuous_profHat.pow 2)).aestronglyMeasurable
  · filter_upwards with p
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    have h1 : ‖ρ + p‖ ^ 2 ≤ 2 * ‖ρ‖ ^ 2 + 2 * ‖p‖ ^ 2 := by
      have h := norm_add_le ρ p
      have h2 : ‖ρ + p‖ ^ 2 ≤ (‖ρ‖ + ‖p‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
      have h3 : (‖ρ‖ + ‖p‖) ^ 2 ≤ 2 * ‖ρ‖ ^ 2 + 2 * ‖p‖ ^ 2 := by
        nlinarith [sq_nonneg (‖ρ‖ - ‖p‖)]
      exact h2.trans h3
    calc ‖ρ + p‖ ^ 2 * (profHat p) ^ 2
        ≤ (2 * ‖ρ‖ ^ 2 + 2 * ‖p‖ ^ 2) * (profHat p) ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ = 2 * ‖ρ‖ ^ 2 * (profHat p) ^ 2 + 2 * ((profHat p) ^ 2 * ‖p‖ ^ 2) := by ring

/-- The reflected version, by the substitution `ρ ↦ −ρ`. -/
private lemma integrable_norm_shift_sq_sub (ρ : ℝ³) :
    Integrable (fun p : ℝ³ => ‖ρ - p‖ ^ 2 * (profHat p) ^ 2) := by
  refine (integrable_norm_shift_sq (-ρ)).congr (Filter.Eventually.of_forall (fun p => ?_))
  show ‖-ρ + p‖ ^ 2 * (profHat p) ^ 2 = ‖ρ - p‖ ^ 2 * (profHat p) ^ 2
  rw [show -ρ + p = -(ρ - p) from by abel, norm_neg]

/-! ## 3. The value of the shifted squared-profile integral -/

/-- **The second-order moment identity** behind the sharp far bound:

    `∫_p ‖ρ+p‖² profHat(p)² dp = ‖ρ‖² (2π)³ + ∫_p profHat(p)² ‖p‖² dp`.

The cross term `2⟪ρ,p⟫` drops out by parity (`profHat` is even), implemented by the
symmetrisation `∫_p ‖ρ+p‖²profHat(p)² dp = ∫_p ‖ρ−p‖²profHat(p)² dp` (`integral_neg_eq_self`)
followed by the parallelogram identity. -/
private lemma integral_shift_sq (ρ : ℝ³) :
    (∫ p : ℝ³, ‖ρ + p‖ ^ 2 * (profHat p) ^ 2)
      = ‖ρ‖ ^ 2 * (2 * Real.pi) ^ 3 + ∫ p : ℝ³, (profHat p) ^ 2 * ‖p‖ ^ 2 := by
  have hI0 : Integrable (fun p : ℝ³ => (profHat p) ^ 2) := by
    simpa using integrable_profHat_sq_mul_norm_pow 0 (by norm_num)
  have hI2 : Integrable (fun p : ℝ³ => (profHat p) ^ 2 * ‖p‖ ^ 2) :=
    integrable_profHat_sq_mul_norm_pow 2 le_rfl
  have hφI := integrable_norm_shift_sq ρ
  have hψI := integrable_norm_shift_sq_sub ρ
  have hsym : (∫ p : ℝ³, ‖ρ + p‖ ^ 2 * (profHat p) ^ 2)
      = ∫ p : ℝ³, ‖ρ - p‖ ^ 2 * (profHat p) ^ 2 := by
    have h := integral_neg_eq_self (fun p : ℝ³ => ‖ρ + p‖ ^ 2 * (profHat p) ^ 2) volume
    rw [← h]
    apply integral_congr_ae
    filter_upwards with p
    rw [show ρ + -p = ρ - p from by abel, profHat_even]
  have hpar : ∀ p : ℝ³, ‖ρ + p‖ ^ 2 * (profHat p) ^ 2 + ‖ρ - p‖ ^ 2 * (profHat p) ^ 2
      = 2 * (‖ρ‖ ^ 2 + ‖p‖ ^ 2) * (profHat p) ^ 2 := by
    intro p
    rw [← add_mul, norm_add_sq_real, norm_sub_sq_real]
    ring
  have h1 : (∫ p : ℝ³, ‖ρ + p‖ ^ 2 * (profHat p) ^ 2)
      = (1 / 2) * ∫ p : ℝ³,
          ((‖ρ + p‖ ^ 2 * (profHat p) ^ 2) + (‖ρ - p‖ ^ 2 * (profHat p) ^ 2)) := by
    rw [integral_add hφI hψI, hsym]
    ring
  rw [h1]
  have h2 : (fun p : ℝ³ =>
        (‖ρ + p‖ ^ 2 * (profHat p) ^ 2) + (‖ρ - p‖ ^ 2 * (profHat p) ^ 2))
      = fun p : ℝ³ => 2 * ‖ρ‖ ^ 2 * (profHat p) ^ 2 + 2 * ((profHat p) ^ 2 * ‖p‖ ^ 2) := by
    funext p
    rw [hpar p]
    ring
  rw [h2, integral_add (hI0.const_mul (2 * ‖ρ‖ ^ 2)) (hI2.const_mul 2),
    integral_const_mul, integral_const_mul, profHat_sq_integral]
  ring

/-! ## 4. The sharp far bound -/

theorem symA_far_sharp (C : ℝ) (hC : 0 ≤ C) (ρ : EuclideanSpace ℝ (Fin 3)) :
    Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff C) ρ
      ≤ (‖ρ‖ - C) ^ 2
        + ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3), (Work.OneBodyKin.profHat p) ^ 2 * ‖p‖ ^ 2)
        + 2 * C * (((2 * Real.pi) ^ 3)⁻¹ * (∫ p : EuclideanSpace ℝ (Fin 3), (Work.OneBodyKin.profHat p) ^ 2 * ‖p‖)) := by
  have hI0 : Integrable (fun p : ℝ³ => (profHat p) ^ 2) := by
    simpa using integrable_profHat_sq_mul_norm_pow 0 (by norm_num)
  have hI1 : Integrable (fun p : ℝ³ => (profHat p) ^ 2 * ‖p‖) := by
    simpa using integrable_profHat_sq_mul_norm_pow 1 (by norm_num)
  have hI2 : Integrable (fun p : ℝ³ => (profHat p) ^ 2 * ‖p‖ ^ 2) :=
    integrable_profHat_sq_mul_norm_pow 2 le_rfl
  have hφI := integrable_norm_shift_sq ρ
  have hfI : Integrable (fun p : ℝ³ =>
      Submission.BoseGases.fsKinCoeff C ‖ρ + p‖ * (profHat p) ^ 2) :=
    integrable_fsKinCoeff_shift_mul_profHat_sq C ρ
  -- pointwise domination of the cut-off by the quadratic majorant
  have hpt : ∀ p : ℝ³, Submission.BoseGases.fsKinCoeff C ‖ρ + p‖ * (profHat p) ^ 2
      ≤ (‖ρ + p‖ ^ 2 - 2 * C * (‖ρ‖ - ‖p‖) + C ^ 2) * (profHat p) ^ 2 := fun p =>
    mul_le_mul_of_nonneg_right (fsKinCoeff_le_reverse hC ρ p) (sq_nonneg _)
  -- the majorant, split into integrable pieces (each with a literal lambda type, so that
  -- `rw [integral_add …]` matches syntactically)
  have hmaj : (fun p : ℝ³ => (‖ρ + p‖ ^ 2 - 2 * C * (‖ρ‖ - ‖p‖) + C ^ 2) * (profHat p) ^ 2)
      = fun p : ℝ³ => ‖ρ + p‖ ^ 2 * (profHat p) ^ 2
          + (-(2 * C * ‖ρ‖)) * (profHat p) ^ 2 + (2 * C) * ((profHat p) ^ 2 * ‖p‖)
          + C ^ 2 * (profHat p) ^ 2 := by
    funext p
    ring
  have hI12 : Integrable (fun p : ℝ³ =>
      ‖ρ + p‖ ^ 2 * (profHat p) ^ 2 + (-(2 * C * ‖ρ‖)) * (profHat p) ^ 2) :=
    hφI.add (hI0.const_mul (-(2 * C * ‖ρ‖)))
  have hI123 : Integrable (fun p : ℝ³ =>
      (‖ρ + p‖ ^ 2 * (profHat p) ^ 2 + (-(2 * C * ‖ρ‖)) * (profHat p) ^ 2)
        + (2 * C) * ((profHat p) ^ 2 * ‖p‖)) :=
    hI12.add (hI1.const_mul (2 * C))
  have hI4 : Integrable (fun p : ℝ³ => C ^ 2 * (profHat p) ^ 2) :=
    hI0.const_mul (C ^ 2)
  have hGI : Integrable (fun p : ℝ³ =>
      (‖ρ + p‖ ^ 2 - 2 * C * (‖ρ‖ - ‖p‖) + C ^ 2) * (profHat p) ^ 2) := by
    rw [hmaj]
    exact hI123.add hI4
  have hmono := integral_mono hfI hGI hpt
  -- the value of the majorant integral
  have hsplit : (∫ p : ℝ³, (‖ρ + p‖ ^ 2 - 2 * C * (‖ρ‖ - ‖p‖) + C ^ 2) * (profHat p) ^ 2)
      = (∫ p : ℝ³, ‖ρ + p‖ ^ 2 * (profHat p) ^ 2)
        + (∫ p : ℝ³, (-(2 * C * ‖ρ‖)) * (profHat p) ^ 2)
        + (∫ p : ℝ³, (2 * C) * ((profHat p) ^ 2 * ‖p‖))
        + (∫ p : ℝ³, C ^ 2 * (profHat p) ^ 2) := by
    rw [hmaj]
    rw [integral_add hI123 hI4, integral_add hI12 (hI1.const_mul (2 * C)),
      integral_add hφI (hI0.const_mul (-(2 * C * ‖ρ‖)))]
  have hGval : (∫ p : ℝ³, (‖ρ + p‖ ^ 2 - 2 * C * (‖ρ‖ - ‖p‖) + C ^ 2) * (profHat p) ^ 2)
      = ‖ρ‖ ^ 2 * (2 * Real.pi) ^ 3 + (∫ p : ℝ³, (profHat p) ^ 2 * ‖p‖ ^ 2)
        - 2 * C * ‖ρ‖ * (2 * Real.pi) ^ 3
        + 2 * C * (∫ p : ℝ³, (profHat p) ^ 2 * ‖p‖) + C ^ 2 * (2 * Real.pi) ^ 3 := by
    rw [hsplit, integral_shift_sq ρ, integral_const_mul, integral_const_mul,
      integral_const_mul, profHat_sq_integral]
    ring
  have hKne : (2 * Real.pi) ^ 3 ≠ 0 := by positivity
  calc symA 1 (Submission.BoseGases.fsKinCoeff C) ρ
      = ((2 * Real.pi) ^ 3)⁻¹ *
          ∫ p : ℝ³, Submission.BoseGases.fsKinCoeff C ‖ρ + p‖ * (profHat p) ^ 2 := by
        simp only [symA, inv_one, one_smul]
    _ ≤ ((2 * Real.pi) ^ 3)⁻¹ *
          ∫ p : ℝ³, (‖ρ + p‖ ^ 2 - 2 * C * (‖ρ‖ - ‖p‖) + C ^ 2) * (profHat p) ^ 2 :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = ((2 * Real.pi) ^ 3)⁻¹ *
          (‖ρ‖ ^ 2 * (2 * Real.pi) ^ 3 + (∫ p : ℝ³, (profHat p) ^ 2 * ‖p‖ ^ 2)
            - 2 * C * ‖ρ‖ * (2 * Real.pi) ^ 3
            + 2 * C * (∫ p : ℝ³, (profHat p) ^ 2 * ‖p‖) + C ^ 2 * (2 * Real.pi) ^ 3) := by
        rw [hGval]
    _ = (‖ρ‖ - C) ^ 2
          + ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : ℝ³, (profHat p) ^ 2 * ‖p‖ ^ 2)
          + 2 * C * (((2 * Real.pi) ^ 3)⁻¹ * (∫ p : ℝ³, (profHat p) ^ 2 * ‖p‖)) := by
        field_simp [hKne]
        ring

end Work.BoseKinLoc.Tprime
