import Mathlib
import Submission.Work.BourgainPlan.Maximal.ell2MaxShiftWeakOne
import Submission.Work.BourgainPlan.Maximal.ell2MaxShiftLpLtTwo
import Submission.Work.BourgainPlan.Maximal.ell2F_hlMax_twoGrids
import Submission.Work.BourgainPlan.Maximal.hlMaxTwoGrid
import Submission.Work.BourgainPlan.Maximal.ell2Maximal
import Submission.Work.BourgainPlan.Maximal.dyMax_le_two_dyMaxShift
import Submission.Work.BourgainPlan.Maximal.ell2MaxLpLtTwo
import Submission.Work.BourgainPlan.Maximal.ell2MaxWeakOne

/-!
# The vector-valued `hlMax` maximal inequality on `L^p(ℓ²)`, `1 < p < 2`

Target: the `ℓ²`-valued (`per-component`) Hardy--Littlewood maximal inequality for the corpus's
centred maximal function `Commons.Analysis.Maximal.hlMax` in the range `1 < p < 2`:

`∫⁻ (Σ_t (hlMax ‖f_t‖ₑ)²)^{p/2} ≤ C^p ∫⁻ (Σ_t ‖f_t‖ₑ²)^{p/2}`,  `C` uniform in the number of
components `n` (`f : Fin n → ℝ → ℝ`).

The proof is a two-line reduction.  Mirek--Stein--Trojan's `ell2F_hlMax_le_twoGrids_sep` bounds the
`ℓ²`-valued `hlMax` maximal function pointwise by the sum of the two dyadic-grid ones,

`(Σ_t (hlMax f_t)²)^{1/2} ≤ 4 ((Σ_t (dyMax f_t)²)^{1/2} + (Σ_t (dyMaxShift 1/2 f_t)²)^{1/2})`,

and each of the two dyadic-grid summands obeys the vector-valued `L^p(ℓ²)` inequality for
`1 < p < 2` (`ell2MaxLpLtTwo` for the standard grid, `ell2MaxShiftLpLtTwo` for the half-shifted
grid, whose inputs are the weak-`(1,1)` bounds `ell2MaxWeakOne` / `ell2MaxShiftWeakOne`).
Raising the pointwise bound to the power `p`, using the `ℝ≥0∞` convexity inequality
`ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow` and integrating gives the result.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Work.BourgainPlan.Maximal

/-- The pointwise reduction, raised to the power `p`: the `ℓ²`-valued `hlMax` maximal function is
controlled by the two dyadic-grid `ℓ²`-valued maximal functions, with the factor `4^p · 2^p` that
the triangle inequality in `ℓ²` and the convexity inequality `(a+b)^p ≤ 2^p (a^p + b^p)` produce. -/
private lemma hlMax_rpow_le_twoGrids {n : ℕ} (f : Fin n → ℝ → ℝ) {p : ℝ} (hp : 0 ≤ p) (x : ℝ) :
    (∑ t, (Commons.Analysis.Maximal.hlMax (fun y => ‖f t y‖ₑ) x) ^ (2 : ℝ)) ^ (p / 2)
      ≤ (4 : ℝ≥0∞) ^ p * (2 : ℝ≥0∞) ^ p *
          ((ell2Max f x) ^ (p / 2) + (ell2MaxShift f x) ^ (p / 2)) := by
  have h := ell2F_hlMax_le_twoGrids_sep f x
  have h' : (∑ t, (Commons.Analysis.Maximal.hlMax (fun y => ‖f t y‖ₑ) x) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
      ≤ 4 * ((ell2Max f x) ^ ((1 : ℝ) / 2) + (ell2MaxShift f x) ^ ((1 : ℝ) / 2)) := by
    simpa only [ell2Max, ell2MaxShift] using h
  calc (∑ t, (Commons.Analysis.Maximal.hlMax (fun y => ‖f t y‖ₑ) x) ^ (2 : ℝ)) ^ (p / 2)
      = ((∑ t, (Commons.Analysis.Maximal.hlMax (fun y => ‖f t y‖ₑ) x) ^ (2 : ℝ)) ^
            ((1 : ℝ) / 2)) ^ p := (rpow_half_rpow _ p).symm
    _ ≤ (4 * ((ell2Max f x) ^ ((1 : ℝ) / 2) + (ell2MaxShift f x) ^ ((1 : ℝ) / 2))) ^ p :=
          ENNReal.rpow_le_rpow h' hp
    _ = (4 : ℝ≥0∞) ^ p *
        ((ell2Max f x) ^ ((1 : ℝ) / 2) + (ell2MaxShift f x) ^ ((1 : ℝ) / 2)) ^ p :=
          ENNReal.mul_rpow_of_nonneg _ _ hp
    _ ≤ (4 : ℝ≥0∞) ^ p * ((2 : ℝ≥0∞) ^ p *
          (((ell2Max f x) ^ ((1 : ℝ) / 2)) ^ p + ((ell2MaxShift f x) ^ ((1 : ℝ) / 2)) ^ p)) := by
          refine mul_le_mul_right ?_ _
          exact ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow _ _ hp
    _ = (4 : ℝ≥0∞) ^ p * (2 : ℝ≥0∞) ^ p *
          ((ell2Max f x) ^ (p / 2) + (ell2MaxShift f x) ^ (p / 2)) := by
          rw [rpow_half_rpow, rpow_half_rpow, mul_assoc]

/-- The constant bookkeeping: `4^p · 2^p · (C₁^p + C₂^p) ≤ C^p` for the explicit choice
`C = 64 (C₁^p + C₂^p) + 1` (which is `> 1`, so `C^p ≥ C` since `p ≥ 1`, and `4^p 2^p = 8^p ≤ 64`
since `p ≤ 2`). -/
private lemma hlMaxLtTwo_const_bound {p C₁ C₂ : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (h1 : 0 < C₁) (h2 : 0 < C₂) :
    (4 : ℝ≥0∞) ^ p * (2 : ℝ≥0∞) ^ p *
        (ENNReal.ofReal (C₁ ^ p) + ENNReal.ofReal (C₂ ^ p))
      ≤ ENNReal.ofReal ((64 * (C₁ ^ p + C₂ ^ p) + 1) ^ p) := by
  have hA : (0 : ℝ) ≤ C₁ ^ p := Real.rpow_nonneg h1.le p
  have hB : (0 : ℝ) ≤ C₂ ^ p := Real.rpow_nonneg h2.le p
  have h8p : (4 : ℝ) ^ p * 2 ^ p ≤ 64 := by
    rw [← Real.mul_rpow (show (0 : ℝ) ≤ 4 by norm_num) (show (0 : ℝ) ≤ 2 by norm_num),
        show (4 : ℝ) * 2 = 8 by norm_num]
    have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 8 by norm_num) hp2
    rwa [show (8 : ℝ) ^ (2 : ℝ) = 64 by norm_num] at h
  have hCge1 : (1 : ℝ) ≤ 64 * (C₁ ^ p + C₂ ^ p) + 1 := by linarith
  have hCp : 64 * (C₁ ^ p + C₂ ^ p) + 1 ≤ (64 * (C₁ ^ p + C₂ ^ p) + 1) ^ p := by
    have h := Real.rpow_le_rpow_of_exponent_le hCge1 hp1
    rwa [Real.rpow_one] at h
  have hmain : 4 ^ p * 2 ^ p * (C₁ ^ p + C₂ ^ p) ≤ (64 * (C₁ ^ p + C₂ ^ p) + 1) ^ p := by
    have hsum : 0 ≤ C₁ ^ p + C₂ ^ p := by linarith
    have h64 : 4 ^ p * 2 ^ p * (C₁ ^ p + C₂ ^ p) ≤ 64 * (C₁ ^ p + C₂ ^ p) :=
      mul_le_mul_of_nonneg_right h8p hsum
    linarith
  calc (4 : ℝ≥0∞) ^ p * (2 : ℝ≥0∞) ^ p *
        (ENNReal.ofReal (C₁ ^ p) + ENNReal.ofReal (C₂ ^ p))
      = ENNReal.ofReal (4 ^ p * 2 ^ p * (C₁ ^ p + C₂ ^ p)) := by
        rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
            show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
            ENNReal.ofReal_rpow_of_nonneg (show (0 : ℝ) ≤ 4 by norm_num) (by linarith),
            ENNReal.ofReal_rpow_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (by linarith),
            ← ENNReal.ofReal_add hA hB,
            ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal ((64 * (C₁ ^ p + C₂ ^ p) + 1) ^ p) := ENNReal.ofReal_le_ofReal hmain

theorem ell2HLMaxLpLtTwo {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (f : Fin n → ℝ → ℝ), (∀ t, Measurable (f t)) → ∫⁻ x, (∑ t, (Commons.Analysis.Maximal.hlMax (fun y => ‖f t y‖ₑ) x) ^ (2 : ℝ)) ^ (p / 2) ≤ ENNReal.ofReal (C ^ p) * ∫⁻ x, (Work.BourgainPlan.Maximal.ell2Sq f x) ^ (p / 2) := by
  obtain ⟨C₀, hC₀, hweak₀⟩ := ell2MaxWeakOne
  obtain ⟨C₁, hC₁, hdy⟩ := ell2MaxLpLtTwo hC₀ hweak₀ hp1 hp2
  obtain ⟨C₂, hC₂, hsh⟩ := ell2MaxShiftLpLtTwo ell2MaxShiftWeakOne hp1 hp2
  have hp0 : 0 ≤ p := le_of_lt (lt_trans zero_lt_one hp1)
  have hp1' : (1 : ℝ) ≤ p := le_of_lt hp1
  have hp2' : p ≤ 2 := le_of_lt hp2
  refine ⟨64 * (C₁ ^ p + C₂ ^ p) + 1, by positivity, ?_⟩
  intro n f hf
  have hmeasA : Measurable (fun x => (ell2Max f x) ^ (p / 2)) :=
    (ENNReal.continuous_rpow_const (y := p / 2)).measurable.comp (ell2Max_measurable f)
  have hmeasB : Measurable (fun x => (ell2MaxShift f x) ^ (p / 2)) :=
    (ENNReal.continuous_rpow_const (y := p / 2)).measurable.comp (ell2MaxShift_measurable f)
  have hmeasAB : Measurable
      (fun x => (ell2Max f x) ^ (p / 2) + (ell2MaxShift f x) ^ (p / 2)) :=
    hmeasA.add hmeasB
  calc ∫⁻ x, (∑ t, (Commons.Analysis.Maximal.hlMax (fun y => ‖f t y‖ₑ) x) ^ (2 : ℝ)) ^ (p / 2)
      ≤ ∫⁻ x, ((4 : ℝ≥0∞) ^ p * (2 : ℝ≥0∞) ^ p *
          ((ell2Max f x) ^ (p / 2) + (ell2MaxShift f x) ^ (p / 2))) :=
        lintegral_mono fun x => hlMax_rpow_le_twoGrids f hp0 x
    _ = (4 : ℝ≥0∞) ^ p * (2 : ℝ≥0∞) ^ p *
          ((∫⁻ x, (ell2Max f x) ^ (p / 2)) + (∫⁻ x, (ell2MaxShift f x) ^ (p / 2))) := by
        rw [MeasureTheory.lintegral_const_mul _ hmeasAB, MeasureTheory.lintegral_add_left hmeasA]
    _ ≤ (4 : ℝ≥0∞) ^ p * (2 : ℝ≥0∞) ^ p *
          ((ENNReal.ofReal (C₁ ^ p)) * (∫⁻ x, (ell2Sq f x) ^ (p / 2))
            + (ENNReal.ofReal (C₂ ^ p)) * (∫⁻ x, (ell2Sq f x) ^ (p / 2))) := by
        refine mul_le_mul_right ?_ _
        exact add_le_add (hdy n f hf) (by simpa only [ell2MaxShift] using hsh n f hf)
    _ = ((4 : ℝ≥0∞) ^ p * (2 : ℝ≥0∞) ^ p *
            (ENNReal.ofReal (C₁ ^ p) + ENNReal.ofReal (C₂ ^ p)))
          * (∫⁻ x, (ell2Sq f x) ^ (p / 2)) := by
        rw [← add_mul, ← mul_assoc]
    _ ≤ ENNReal.ofReal ((64 * (C₁ ^ p + C₂ ^ p) + 1) ^ p)
          * (∫⁻ x, (ell2Sq f x) ^ (p / 2)) :=
        mul_le_mul_left (hlMaxLtTwo_const_bound hp1' hp2' hC₁ hC₂) _

end Work.BourgainPlan.Maximal
