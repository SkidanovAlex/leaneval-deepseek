import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs
import Submission.Work.BourgainPlan.Oscillation.plancherel_circle_enorm_sq_Ioc
import Submission.Work.BourgainPlan.Oscillation.oscZ_lacunary_defs
import Submission.Work.BourgainPlan.Oscillation.lacScale_error_tsum_le
import Submission.Work.BourgainPlan.Oscillation.Lacunary.tscale_defs
import Submission.Work.BourgainPlan.Oscillation.Lacunary.gapFam_sq_le
import Submission.Work.Oscillation.Lacunary.gap_count

/-!
# The cut family at the floored lacunary radii `t / ⌊ρ^i⌋`

Bourgain's oscillation inequality at the lacunary scales `⌊ρ^i⌋` is available for the family of
**sharp cuts at the exact geometric radii** `s · ρ^{-i}` (`oscZ_cut_weighted` /
`oscZ_cut_shift`), with a constant uniform in the shift `s`.  The oscillation statement however
uses the **floored** radii `t / ⌊ρ^i⌋`, whose ratio to the geometric ones is the *flooring factor*
`ρ^i / ⌊ρ^i⌋` — not a constant in `i`, and not of the form `s ρ^{-i}` for any single `s`.

This file bridges the two: `oscZ_cut_tscale` shows that the uniform (in `s`) bound for the shifted
family *implies* the same bound for the floored family, at the price of a constant depending only on
`ρ` (through the maximal number `M` of flooring annuli `(t ρ^{-i}, t / ⌊ρ^i⌋]` meeting a single
frequency, which is finite by `gap_count`).

## The argument

Fix `t ≥ 0` and split the floored cut off the shifted one, pointwise in `θ`:

`1_{θ ≤ t/⌊ρ^i⌋} = 1_{θ ≤ t ρ^{-i}} + 1_{t ρ^{-i} < θ ≤ t/⌊ρ^i⌋}`

(`cut_split_pointwise`, valid because `t ρ^{-i} ≤ t / ⌊ρ^i⌋`), giving the pointwise splitting of the
families `A = B + G` (`A` the floored, `B` the shifted, `G` the flooring-gap family).  Then

* `oscZ_add_le` gives `oscZ A ≤ 4 oscZ B + 4 oscZ G`;
* `oscZ B` is bounded by the hypothesis `hcut` applied with `s = t`;
* `oscZ G ≤ 8 Σ_i ∫⁻_x ‖G_i x‖ₑ²` (`oscZ_le_eight_tsum`) and the square function of the gap family
  is controlled by the *multiplicity* bound `Σ_i 1_{annulus i}(θ) ≤ M` (`gapFam_sq_le`), which is
  `gap_count`.

The gap annuli meet only `O_ρ(1)` at a time precisely because their right endpoints are the floored
lacunary radii `t/⌊ρ^i⌋` and their left endpoints the geometric ones `t ρ^{-i}`: both sequences
decrease geometrically with ratio `ρ`, and the flooring perturbs the ratio by a bounded factor.
-/

namespace Work.BourgainPlan.Oscillation.Lacunary

open Finset MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-! ## The integrand and its elementary estimates -/

/-- The common integrand of the cut families: `m θ · (Σ_{n ∈ T} f n e(nθ)) · e(-2πi x θ)`. -/
def famIntegrand (m : ℝ → ℂ) (f : ℤ → ℂ) (T : Finset ℤ) (x : ℤ) (θ : ℝ) : ℂ :=
  m θ * trigP T f θ * Echar x θ

lemma famIntegrand_def (m : ℝ → ℂ) (f : ℤ → ℂ) (T : Finset ℤ) (x : ℤ) (θ : ℝ) :
    famIntegrand m f T x θ = m θ * trigP T f θ * Echar x θ := rfl

lemma measurable_famIntegrand (m : ℝ → ℂ) (hm : Measurable m) (f : ℤ → ℂ) (T : Finset ℤ)
    (x : ℤ) : Measurable (famIntegrand m f T x) :=
  (hm.mul (measurable_trigP T f)).mul ((continuous_Echar x).measurable)

lemma norm_famIntegrand_le (m : ℝ → ℂ) (A : ℝ) (hm : ∀ θ, ‖m θ‖ ≤ A)
    (f : ℤ → ℂ) (T : Finset ℤ) (θ : ℝ) (x : ℤ) :
    ‖famIntegrand m f T x θ‖ ≤ A * ∑ n ∈ T, ‖f n‖ := by
  rw [famIntegrand_def, norm_mul, norm_mul, norm_Echar, mul_one]
  exact mul_le_mul (hm θ) (norm_trigP_le T f θ) (by positivity)
    (le_trans (norm_nonneg _) (hm θ))

/-- A measurable cut multiplier. -/
lemma measurable_cut_mul (r : ℝ → ℂ) (hr : Measurable r) (c : ℝ) :
    Measurable (fun θ : ℝ => r θ * (if θ ≤ c then (1:ℂ) else 0)) :=
  hr.mul (Measurable.ite measurableSet_Iic measurable_const measurable_const)

/-- A measurable flooring-gap multiplier. -/
lemma measurable_gap_mul (r : ℝ → ℂ) (hr : Measurable r) (d c : ℝ) :
    Measurable (fun θ : ℝ => r θ * (if d < θ ∧ θ ≤ c then (1:ℂ) else 0)) :=
  hr.mul (Measurable.ite (p := fun θ : ℝ => θ ∈ Set.Ioc d c) measurableSet_Ioc
    measurable_const measurable_const)

/-- The norm of a cut multiplier is at most the bound on `r`. -/
lemma norm_cut_mul_le (r : ℝ → ℂ) {cap : ℝ} (hrb : ∀ θ, ‖r θ‖ ≤ cap) (c θ : ℝ) :
    ‖r θ * (if θ ≤ c then (1:ℂ) else 0)‖ ≤ cap := by
  have hif : ‖(if θ ≤ c then (1:ℂ) else 0)‖ ≤ 1 := by split <;> simp
  calc ‖r θ * (if θ ≤ c then (1:ℂ) else 0)‖ = ‖r θ‖ * ‖(if θ ≤ c then (1:ℂ) else 0)‖ :=
        norm_mul _ _
    _ ≤ ‖r θ‖ * 1 := mul_le_mul_of_nonneg_left hif (norm_nonneg _)
    _ = ‖r θ‖ := mul_one _
    _ ≤ cap := hrb θ

/-- The norm of a flooring-gap multiplier is at most the bound on `r`. -/
lemma norm_gap_mul_le (r : ℝ → ℂ) {cap : ℝ} (hrb : ∀ θ, ‖r θ‖ ≤ cap) (d c θ : ℝ) :
    ‖r θ * (if d < θ ∧ θ ≤ c then (1:ℂ) else 0)‖ ≤ cap := by
  have hif : ‖(if d < θ ∧ θ ≤ c then (1:ℂ) else 0)‖ ≤ 1 := by split <;> simp
  calc ‖r θ * (if d < θ ∧ θ ≤ c then (1:ℂ) else 0)‖
        = ‖r θ‖ * ‖(if d < θ ∧ θ ≤ c then (1:ℂ) else 0)‖ := norm_mul _ _
    _ ≤ ‖r θ‖ * 1 := mul_le_mul_of_nonneg_left hif (norm_nonneg _)
    _ = ‖r θ‖ := mul_one _
    _ ≤ cap := hrb θ

/-- The elementary constant comparison of the assembly. -/
lemma tscale_const_le (C₁ M cap : ℝ) (hC₁ : 0 < C₁) (hM : 0 ≤ M) (hcap : 0 ≤ cap) :
    4 * (C₁ * cap) ^ 2 + 32 * (M * cap ^ 2) ≤
      (Real.sqrt (4 + 32 * M / C₁ ^ 2 + 1) * C₁ * cap) ^ 2 := by
  have hC₁2 : (0:ℝ) < C₁^2 := by positivity
  have h : (4 + 32*M/C₁^2 + 1) * C₁^2 = 5*C₁^2 + 32*M := by
    field_simp
    ring
  have hsq : (Real.sqrt (4 + 32*M/C₁^2 + 1))^2 * C₁^2 * cap^2 = (5*C₁^2 + 32*M) * cap^2 := by
    rw [Real.sq_sqrt (by positivity), h]
  rw [show (Real.sqrt (4 + 32*M/C₁^2 + 1) * C₁ * cap)^2
        = (Real.sqrt (4 + 32*M/C₁^2 + 1))^2 * C₁^2 * cap^2 by ring, hsq]
  nlinarith [sq_nonneg C₁, sq_nonneg cap, hcap, hM, mul_nonneg hcap hM]

/-! ## The main comparison -/

theorem oscZ_cut_tscale (ρ : ℝ) (hρ : 1 < ρ) (C₁ : ℝ) (hC₁ : 0 < C₁)
    (hcut : ∀ (s : ℝ), 0 < s → ∀ (r : ℝ → ℂ), Measurable r → ∀ (cap : ℝ), 0 ≤ cap →
      (∀ θ, ‖r θ‖ ≤ cap) →
      ∀ (J : ℕ) (k : ℕ → ℕ), StrictMono k →
      ∀ (f : ℤ → ℂ) (T : Finset ℤ), (∀ n, n ∉ T → f n = 0) →
        Work.BourgainPlan.Oscillation.oscZ (fun i x =>
            ∫ θ in (0:ℝ)..1,
              (r θ * (if θ ≤ s * ρ ^ (-(i:ℤ)) then (1:ℂ) else 0)) *
              (∑ n ∈ T, f n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (θ : ℂ))) *
              Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))) J k
          ≤ ENNReal.ofReal ((C₁ * cap) ^ 2) *
              ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (t : ℝ), 0 ≤ t → ∀ (r : ℝ → ℂ), Measurable r → ∀ (cap : ℝ), 0 ≤ cap →
      (∀ θ, ‖r θ‖ ≤ cap) →
      ∀ (J : ℕ) (k : ℕ → ℕ), StrictMono k →
      ∀ (f : ℤ → ℂ) (T : Finset ℤ), (∀ n, n ∉ T → f n = 0) →
        Work.BourgainPlan.Oscillation.oscZ (fun i x =>
            ∫ θ in (0:ℝ)..1,
              (r θ * (if θ ≤ t / (Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ)
                then (1:ℂ) else 0)) *
              (∑ n ∈ T, f n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (θ : ℂ))) *
              Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))) J k
          ≤ ENNReal.ofReal ((C * C₁ * cap) ^ 2) *
              ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
  obtain ⟨M, hMpos, hMgap⟩ := Work.Oscillation.Lacunary.gap_count ρ hρ
  refine ⟨Real.sqrt (4 + 32 * M / C₁ ^ 2 + 1), Real.sqrt_pos.mpr (by positivity), ?_⟩
  intro t ht r hr cap hcap hcapbd J k hk f T hf
  have hmain : Work.BourgainPlan.Oscillation.oscZ
        (cutFam r f T (fun i => t / (Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ))) J k
      ≤ ENNReal.ofReal ((Real.sqrt (4 + 32 * M / C₁ ^ 2 + 1) * C₁ * cap) ^ 2) *
          ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
    by_cases ht0 : t = 0
    · -- the floored family degenerates to `0`
      have hfam : ∀ i x,
          cutFam r f T (fun i => t / (Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ)) i x = 0 := by
        intro i x
        unfold cutFam
        rw [intervalIntegral.integral_congr_ae (g := fun _ : ℝ => (0:ℂ))
          (Filter.Eventually.of_forall (fun θ hθ => ?_))]
        · simp
        · rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hθ
          have hc : ¬ (θ ≤ t / (Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ)) := by
            rw [ht0, zero_div]
            exact not_le.mpr hθ.1
          rw [if_neg hc]
          ring
      have hzero : cutFam r f T (fun i => t / (Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ))
          = fun _ _ => (0:ℂ) := funext fun i => funext fun x => hfam i x
      rw [hzero]
      have : Work.BourgainPlan.Oscillation.oscZ (fun _ _ => (0:ℂ)) J k = 0 := by
        simp [Work.BourgainPlan.Oscillation.oscZ]
      rw [this]
      exact bot_le
    · -- the genuine comparison
      have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      -- the pointwise splitting of the families
      have hsplit : ∀ i x,
          cutFam r f T (fun i => t / (Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ)) i x
            = cutFam r f T (fun i => t * ρ ^ (-(i:ℤ))) i x + gapFam ρ t r f T i x := by
        intro i x
        have hdc : t * ρ ^ (-(i:ℤ)) ≤ t / (Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) :=
          mul_zpow_le_div_lacScale (le_of_lt hρ) ht i
        refine intervalIntegral_split
          (famIntegrand (fun θ => r θ * (if θ ≤ t * ρ ^ (-(i:ℤ)) then (1:ℂ) else 0)) f T x)
          (famIntegrand (fun θ => r θ * (if t * ρ ^ (-(i:ℤ)) < θ ∧
            θ ≤ t / (Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) then (1:ℂ) else 0)) f T x)
          (famIntegrand (fun θ => r θ * (if θ ≤ t /
            (Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ) then (1:ℂ) else 0)) f T x)
          (measurable_famIntegrand _ (measurable_cut_mul r hr _) f T x)
          (measurable_famIntegrand _ (measurable_gap_mul r hr _ _) f T x)
          (cap * ∑ n ∈ T, ‖f n‖) (cap * ∑ n ∈ T, ‖f n‖)
          (fun θ' => norm_famIntegrand_le _ cap (fun θ'' => norm_cut_mul_le r hcapbd _ θ'') f T θ' x)
          (fun θ' => norm_famIntegrand_le _ cap (fun θ'' => norm_gap_mul_le r hcapbd _ _ θ'') f T θ' x)
          (fun θ => by
            simp only [famIntegrand_def]
            rw [← cut_split_pointwise r (t * ρ ^ (-(i:ℤ)))
              (t / (Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ)) θ hdc]
            ring)
      -- the shifted family is bounded by the hypothesis
      have hB : Work.BourgainPlan.Oscillation.oscZ
          (cutFam r f T (fun i => t * ρ ^ (-(i:ℤ)))) J k
          ≤ ENNReal.ofReal ((C₁ * cap) ^ 2) *
              ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count :=
        hcut t htpos r hr cap hcap hcapbd J k hk f T hf
      -- the gap family: square function from the multiplicity bound
      have hGsq : (∑' i : ℕ, ∫⁻ x : ℤ,
            ‖gapFam ρ t r f T i x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count)
          ≤ ENNReal.ofReal (M * cap ^ 2) *
              ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count :=
        gapFam_sq_le ρ t cap M hMpos hcap (fun θ s => hMgap t θ s ht) r hr hcapbd f T
      have hGosc : Work.BourgainPlan.Oscillation.oscZ (gapFam ρ t r f T) J k
          ≤ 8 * (∑' i : ℕ, ∫⁻ x : ℤ,
              ‖gapFam ρ t r f T i x‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count) :=
        Work.BourgainPlan.Oscillation.oscZ_le_eight_tsum (gapFam ρ t r f T) J k hk
      -- assemble
      calc Work.BourgainPlan.Oscillation.oscZ
            (cutFam r f T (fun i => t / (Work.BourgainPlan.Oscillation.lacScale ρ i : ℝ))) J k
          ≤ 4 * Work.BourgainPlan.Oscillation.oscZ
              (cutFam r f T (fun i => t * ρ ^ (-(i:ℤ)))) J k
            + 4 * Work.BourgainPlan.Oscillation.oscZ (gapFam ρ t r f T) J k :=
              Work.BourgainPlan.Oscillation.oscZ_add_le _ _ _ hsplit J k
        _ ≤ 4 * (ENNReal.ofReal ((C₁ * cap) ^ 2) *
              ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count)
            + 4 * (8 * (ENNReal.ofReal (M * cap ^ 2) *
              ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count)) :=
              add_le_add
                (mul_le_mul_of_nonneg_left hB (by norm_num))
                (mul_le_mul_of_nonneg_left (le_trans hGosc
                  (mul_le_mul_of_nonneg_left hGsq (by norm_num))) (by norm_num))
        _ ≤ ENNReal.ofReal ((Real.sqrt (4 + 32 * M / C₁ ^ 2 + 1) * C₁ * cap) ^ 2) *
              (∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count) := by
              have h1 : (4:ℝ≥0∞) * ENNReal.ofReal ((C₁ * cap) ^ 2)
                  = ENNReal.ofReal (4 * (C₁ * cap) ^ 2) := by
                rw [show (4:ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
                  ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
              have h2 : (32:ℝ≥0∞) * ENNReal.ofReal (M * cap ^ 2)
                  = ENNReal.ofReal (32 * (M * cap ^ 2)) := by
                rw [show (32:ℝ≥0∞) = ENNReal.ofReal 32 by norm_num,
                  ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 32)]
              have hkey := tscale_const_le C₁ M cap hC₁ hMpos.le hcap
              calc 4 * (ENNReal.ofReal ((C₁ * cap) ^ 2) *
                    ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count)
                  + 4 * (8 * (ENNReal.ofReal (M * cap ^ 2) *
                    ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count))
                  = ((4:ℝ≥0∞) * ENNReal.ofReal ((C₁ * cap) ^ 2)
                      + 32 * ENNReal.ofReal (M * cap ^ 2)) *
                    (∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count) := by ring
                _ = (ENNReal.ofReal (4 * (C₁ * cap) ^ 2)
                      + ENNReal.ofReal (32 * (M * cap ^ 2))) *
                    (∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count) := by
                      rw [h1, h2]
                _ = ENNReal.ofReal (4 * (C₁ * cap) ^ 2 + 32 * (M * cap ^ 2)) *
                    (∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count) := by
                      rw [ENNReal.ofReal_add (by positivity) (by positivity)]
                _ ≤ ENNReal.ofReal ((Real.sqrt (4 + 32 * M / C₁ ^ 2 + 1) * C₁ * cap) ^ 2) *
                    (∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count) :=
                      mul_le_mul' (ENNReal.ofReal_le_ofReal hkey) le_rfl
  exact hmain

end

end Work.BourgainPlan.Oscillation.Lacunary
