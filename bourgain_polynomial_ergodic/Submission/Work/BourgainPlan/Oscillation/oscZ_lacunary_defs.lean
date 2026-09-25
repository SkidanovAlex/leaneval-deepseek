import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs
import Submission.Work.BourgainPlan.Oscillation.lacunary_truncated_maximal_l2

/-!
# Tools and interfaces for the per-block oscillation inequality at the lacunary scales

This file collects

* the real-valued indicator `W T r θ` of the periodised `r`-neighbourhood of a finite frequency
  set `T`, together with the elementary facts used to *multiply* the nested indicator families of
  Bourgain's oscillation argument (`W_mul_band`, `W_self_band`);
* the two elementary consequences of the definition of `oscZ` (`oscZ_add_le`,
  `oscZ_le_eight_tsum`) and the "domination by the square function" form
  `oscZ_le_four_tsum_of_enorm_le`;
* the *interfaces* `NbrhdMaximalLacunary`, `OscZCoreLacunary`, `OscZErrLacunary` of the three
  analytic inputs of `oscZ_block_lacunary_v2`.
-/

namespace Work.BourgainPlan.Oscillation

open Finset MeasureTheory
open scoped BigOperators ENNReal
open Classical
open Commons.Analysis.ExponentialSums

noncomputable section

/-! ## The real-valued neighbourhood indicator -/

/-- The real-valued indicator of the periodised `r`-neighbourhood of the frequencies of `T`. -/
def W (T : Finset (ℝ × ℂ)) (r θ : ℝ) : ℝ :=
  if ∃ p ∈ T, ∃ l : ℤ, |θ + (l : ℝ) - p.1| ≤ r then 1 else 0

lemma unNbhd_eq_W (T : Finset (ℝ × ℂ)) (r θ : ℝ) : unNbhd T r θ = (W T r θ : ℂ) := by
  rw [W, unNbhd]
  by_cases h : ∃ p ∈ T, ∃ l : ℤ, |θ + (l : ℝ) - p.1| ≤ r <;> simp [h]

lemma W_eq_zero_or_one (T : Finset (ℝ × ℂ)) (r θ : ℝ) : W T r θ = 0 ∨ W T r θ = 1 := by
  rw [W]
  by_cases h : ∃ p ∈ T, ∃ l : ℤ, |θ + (l : ℝ) - p.1| ≤ r
  · rw [if_pos h]; right; norm_num
  · rw [if_neg h]; left; norm_num

lemma W_nonneg (T : Finset (ℝ × ℂ)) (r θ : ℝ) : 0 ≤ W T r θ := by
  rw [W]; by_cases h : ∃ p ∈ T, ∃ l : ℤ, |θ + (l : ℝ) - p.1| ≤ r <;> simp [h]

lemma W_le_one (T : Finset (ℝ × ℂ)) (r θ : ℝ) : W T r θ ≤ 1 := by
  rw [W]; by_cases h : ∃ p ∈ T, ∃ l : ℤ, |θ + (l : ℝ) - p.1| ≤ r <;> simp [h]

lemma W_mono (T : Finset (ℝ × ℂ)) {r r' : ℝ} (h : r ≤ r') (θ : ℝ) :
    W T r θ ≤ W T r' θ := by
  rw [W, W]
  by_cases h1 : ∃ p ∈ T, ∃ l : ℤ, |θ + (l : ℝ) - p.1| ≤ r
  · rw [if_pos h1, if_pos (by obtain ⟨p, hp, l, hl⟩ := h1; exact ⟨p, hp, l, le_trans hl h⟩)]
  · rw [if_neg h1]
    by_cases h2 : ∃ p ∈ T, ∃ l : ℤ, |θ + (l : ℝ) - p.1| ≤ r' <;> simp [h2]

lemma W_mono_one (T : Finset (ℝ × ℂ)) {r r' : ℝ} (h : r ≤ r') (θ : ℝ) :
    W T r θ = 1 → W T r' θ = 1 := by
  intro h1
  have := W_mono T h θ
  rw [h1] at this
  exact le_antisymm (W_le_one T r' θ) this

lemma W_mono_zero (T : Finset (ℝ × ℂ)) {r r' : ℝ} (h : r ≤ r') (θ : ℝ) :
    W T r' θ = 0 → W T r θ = 0 := by
  intro h1
  have := W_mono T h θ
  rw [h1] at this
  exact le_antisymm this (W_nonneg T r θ)

/-- The fundamental `0/1` identity of the oscillation argument: for `r₃ ≤ r₁ ≤ r₂`, the difference
of the two outer indicators is unchanged by multiplication with the band indicator `W r₂ - W r₃`. -/
lemma W_mul_band (T : Finset (ℝ × ℂ)) {r₁ r₂ r₃ : ℝ} (h31 : r₃ ≤ r₁) (h12 : r₁ ≤ r₂) (θ : ℝ) :
    (W T r₁ θ - W T r₂ θ) * (W T r₂ θ - W T r₃ θ) = W T r₁ θ - W T r₂ θ := by
  rcases W_eq_zero_or_one T r₁ θ with h1 | h1
  · have h3 : W T r₃ θ = 0 := W_mono_zero T h31 θ h1
    rw [h1, h3, zero_sub, sub_zero]
    rcases W_eq_zero_or_one T r₂ θ with h2 | h2
    · rw [h2]; ring
    · rw [h2]; ring
  · have h2 : W T r₂ θ = 1 := W_mono_one T h12 θ h1
    rw [h1, h2]; ring

lemma W_self_band (T : Finset (ℝ × ℂ)) {r₂ r₃ : ℝ} (h32 : r₃ ≤ r₂) (θ : ℝ) :
    W T r₂ θ * (W T r₂ θ - W T r₃ θ) = W T r₂ θ - W T r₃ θ := by
  rcases W_eq_zero_or_one T r₂ θ with h2 | h2
  · have h3 : W T r₃ θ = 0 := W_mono_zero T h32 θ h2
    rw [h2, h3]; ring
  · rw [h2, one_mul]

/-! ## Elementary properties of `oscZ` -/

private lemma enorm_sub_le_two (a b : ℂ) : ‖a - b‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ := by
  calc ‖a - b‖ₑ = ‖a + (-b)‖ₑ := by rw [sub_eq_add_neg]
    _ ≤ ‖a‖ₑ + ‖(-b)‖ₑ := enorm_add_le a (-b)
    _ = ‖a‖ₑ + ‖b‖ₑ := by rw [enorm_neg]

private lemma iSup_finset_le_sum {s : Finset ℕ} (f : ℕ → ℝ≥0∞) :
    (⨆ i ∈ s, f i) ≤ ∑ i ∈ s, f i :=
  iSup_le fun i => iSup_le fun hi => Finset.single_le_sum (fun _ _ => zero_le) hi

lemma iSup_finset_rpow_two {s : Finset ℕ} (f : ℕ → ℝ≥0∞) :
    (⨆ i ∈ s, f i) ^ (2 : ℝ) = ⨆ i ∈ s, (f i) ^ (2 : ℝ) := by
  have h2 : (⨆ i, ⨆ _ : i ∈ s, f i) ^ (2 : ℝ) = ⨆ i, (⨆ _ : i ∈ s, f i) ^ (2 : ℝ) :=
    Lacunary.iSup_rpow_two (fun i => ⨆ _ : i ∈ s, f i)
  rw [h2]
  refine iSup_congr (fun i => ?_)
  by_cases h : i ∈ s
  · rw [iSup_pos h, iSup_pos h]
  · rw [iSup_neg h, iSup_neg h]; simp

/-- `oscZ` is subadditive on a pointwise splitting of the family. -/
lemma oscZ_add_le (A B C : ℕ → ℤ → ℂ) (h : ∀ i x, A i x = B i x + C i x) (J : ℕ)
    (k : ℕ → ℕ) :
    oscZ A J k ≤ 4 * oscZ B J k + 4 * oscZ C J k := by
  unfold oscZ
  have hstep : ∀ j ∈ Finset.range J,
      (∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
          ‖A i x - A (k j) x‖ₑ) ^ (2 : ℝ) ∂MeasureTheory.Measure.count)
        ≤ 4 * (∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
              ‖B i x - B (k j) x‖ₑ) ^ (2 : ℝ) ∂MeasureTheory.Measure.count)
          + 4 * (∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
              ‖C i x - C (k j) x‖ₑ) ^ (2 : ℝ) ∂MeasureTheory.Measure.count) := by
    intro j _
    have hpt : ∀ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖A i x - A (k j) x‖ₑ) ^ (2 : ℝ)
        ≤ 4 * ((⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖B i x - B (k j) x‖ₑ) ^ (2 : ℝ)
          + (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖C i x - C (k j) x‖ₑ) ^ (2 : ℝ)) := by
      intro x
      refine le_trans (ENNReal.rpow_le_rpow ?_ (by norm_num)) (Lacunary.add_sq_le _ _)
      refine iSup_le fun i => iSup_le fun hi => ?_
      have hAi : A i x - A (k j) x = (B i x - B (k j) x) + (C i x - C (k j) x) := by
        rw [h i x, h (k j) x]; ring
      rw [hAi]
      exact le_trans (enorm_add_le _ _)
        (add_le_add (le_iSup₂_of_le i hi le_rfl) (le_iSup₂_of_le i hi le_rfl))
    calc (∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖A i x - A (k j) x‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count)
        ≤ ∫⁻ x : ℤ, 4 * ((⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖B i x - B (k j) x‖ₑ) ^ (2 : ℝ)
            + (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖C i x - C (k j) x‖ₑ) ^ (2 : ℝ))
            ∂MeasureTheory.Measure.count := lintegral_mono hpt
      _ = 4 * ∫⁻ x : ℤ, ((⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖B i x - B (k j) x‖ₑ) ^ (2 : ℝ)
            + (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖C i x - C (k j) x‖ₑ) ^ (2 : ℝ))
            ∂MeasureTheory.Measure.count := lintegral_const_mul' _ _ (by norm_num)
      _ = 4 * ((∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖B i x - B (k j) x‖ₑ) ^ (2 : ℝ)
              ∂MeasureTheory.Measure.count)
            + (∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖C i x - C (k j) x‖ₑ) ^ (2 : ℝ)
              ∂MeasureTheory.Measure.count)) := by
          rw [lintegral_add_left (measurable_of_countable _)]
      _ = 4 * (∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖B i x - B (k j) x‖ₑ) ^ (2 : ℝ)
              ∂MeasureTheory.Measure.count)
            + 4 * (∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖C i x - C (k j) x‖ₑ) ^ (2 : ℝ)
              ∂MeasureTheory.Measure.count) := by ring
  calc (∑ j ∈ Finset.range J, ∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
        ‖A i x - A (k j) x‖ₑ) ^ (2 : ℝ) ∂MeasureTheory.Measure.count)
      ≤ ∑ j ∈ Finset.range J, (4 * (∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
            ‖B i x - B (k j) x‖ₑ) ^ (2 : ℝ) ∂MeasureTheory.Measure.count)
          + 4 * (∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
            ‖C i x - C (k j) x‖ₑ) ^ (2 : ℝ) ∂MeasureTheory.Measure.count)) :=
        Finset.sum_le_sum hstep
    _ = 4 * (∑ j ∈ Finset.range J, ∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
            ‖B i x - B (k j) x‖ₑ) ^ (2 : ℝ) ∂MeasureTheory.Measure.count)
          + 4 * (∑ j ∈ Finset.range J, ∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
            ‖C i x - C (k j) x‖ₑ) ^ (2 : ℝ) ∂MeasureTheory.Measure.count) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- **The square-function bound for `oscZ`.**  The oscillation of a family is controlled by the
sum over *all* scales of the squared norms of its members. -/
lemma oscZ_le_eight_tsum (A : ℕ → ℤ → ℂ) (J : ℕ) (k : ℕ → ℕ) (hk : StrictMono k) :
    oscZ A J k
      ≤ 8 * ∑' i : ℕ, ∫⁻ x : ℤ, ‖A i x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by
  have hterm : ∀ j : ℕ,
      ∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖A i x - A (k j) x‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count
        ≤ 4 * (∑ i ∈ Finset.Ico (k j) (k (j + 1)),
              ∫⁻ x : ℤ, ‖A i x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count)
          + 4 * (∫⁻ x : ℤ, ‖A (k j) x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count) := by
    intro j
    have hpt : ∀ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖A i x - A (k j) x‖ₑ) ^ (2 : ℝ)
        ≤ 4 * ((⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖A i x‖ₑ) ^ (2 : ℝ)
          + ‖A (k j) x‖ₑ ^ (2 : ℝ)) := by
      intro x
      refine le_trans (ENNReal.rpow_le_rpow ?_ (by norm_num)) (Lacunary.add_sq_le _ _)
      refine iSup_le fun i => iSup_le fun hi => ?_
      exact le_trans (enorm_sub_le_two _ _) (add_le_add (le_iSup₂_of_le i hi le_rfl) le_rfl)
    have hsup : ∀ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖A i x‖ₑ) ^ (2 : ℝ)
        ≤ ∑ i ∈ Finset.Ico (k j) (k (j + 1)), ‖A i x‖ₑ ^ (2 : ℝ) := by
      intro x
      rw [iSup_finset_rpow_two]
      exact iSup_finset_le_sum _
    calc ∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖A i x - A (k j) x‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count
        ≤ ∫⁻ x : ℤ, 4 * ((⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖A i x‖ₑ) ^ (2 : ℝ)
            + ‖A (k j) x‖ₑ ^ (2 : ℝ)) ∂MeasureTheory.Measure.count := lintegral_mono hpt
      _ = 4 * ∫⁻ x : ℤ, ((⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖A i x‖ₑ) ^ (2 : ℝ)
            + ‖A (k j) x‖ₑ ^ (2 : ℝ)) ∂MeasureTheory.Measure.count :=
          lintegral_const_mul' _ _ (by norm_num)
      _ = 4 * ((∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖A i x‖ₑ) ^ (2 : ℝ)
              ∂MeasureTheory.Measure.count)
            + (∫⁻ x : ℤ, ‖A (k j) x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count)) := by
          rw [lintegral_add_left (measurable_of_countable _)]
      _ ≤ 4 * ((∑ i ∈ Finset.Ico (k j) (k (j + 1)),
              ∫⁻ x : ℤ, ‖A i x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count)
            + (∫⁻ x : ℤ, ‖A (k j) x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count)) := by
          refine mul_le_mul_of_nonneg_left (add_le_add ?_ le_rfl) (by norm_num)
          calc ∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖A i x‖ₑ) ^ (2 : ℝ)
                ∂MeasureTheory.Measure.count
              ≤ ∫⁻ x : ℤ, ∑ i ∈ Finset.Ico (k j) (k (j + 1)), ‖A i x‖ₑ ^ (2 : ℝ)
                ∂MeasureTheory.Measure.count := lintegral_mono hsup
            _ = ∑ i ∈ Finset.Ico (k j) (k (j + 1)),
                  ∫⁻ x : ℤ, ‖A i x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count :=
                lintegral_finsetSum _ (fun i _ => measurable_of_countable _)
      _ = 4 * (∑ i ∈ Finset.Ico (k j) (k (j + 1)),
              ∫⁻ x : ℤ, ‖A i x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count)
          + 4 * (∫⁻ x : ℤ, ‖A (k j) x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count) := by ring
  have hdisj : Set.PairwiseDisjoint (Finset.range J : Set ℕ)
      (fun j => Finset.Ico (k j) (k (j + 1))) := by
    intro a _ b _ hab
    rw [Function.onFun, Finset.disjoint_left]
    intro i hi hj
    rw [Finset.mem_Ico] at hi hj
    rcases lt_or_gt_of_ne hab with h | h
    · have := hk.monotone (show a + 1 ≤ b by omega)
      omega
    · have := hk.monotone (show b + 1 ≤ a by omega)
      omega
  have hbase : (∑ j ∈ Finset.range J, ∫⁻ x : ℤ, ‖A (k j) x‖ₑ ^ (2 : ℝ)
        ∂MeasureTheory.Measure.count)
      ≤ ∑' i : ℕ, ∫⁻ x : ℤ, ‖A i x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by
    have h1 : (∑ j ∈ Finset.range J, ∫⁻ x : ℤ, ‖A (k j) x‖ₑ ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count)
        = ∑ i ∈ (Finset.range J).image k, ∫⁻ x : ℤ, ‖A i x‖ₑ ^ (2 : ℝ)
            ∂MeasureTheory.Measure.count := by
      rw [Finset.sum_image]
      exact fun a _ b _ hab => hk.injective hab
    rw [h1]
    exact ENNReal.sum_le_tsum _
  calc oscZ A J k
      = ∑ j ∈ Finset.range J, ∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
          ‖A i x - A (k j) x‖ₑ) ^ (2 : ℝ) ∂MeasureTheory.Measure.count := rfl
    _ ≤ ∑ j ∈ Finset.range J, (4 * (∑ i ∈ Finset.Ico (k j) (k (j + 1)),
              ∫⁻ x : ℤ, ‖A i x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count)
          + 4 * (∫⁻ x : ℤ, ‖A (k j) x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count)) :=
        Finset.sum_le_sum (fun j _ => hterm j)
    _ = 4 * (∑ j ∈ Finset.range J, ∑ i ∈ Finset.Ico (k j) (k (j + 1)),
            ∫⁻ x : ℤ, ‖A i x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count)
          + 4 * (∑ j ∈ Finset.range J,
            ∫⁻ x : ℤ, ‖A (k j) x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 4 * (∑' i : ℕ, ∫⁻ x : ℤ, ‖A i x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count)
          + 4 * (∑' i : ℕ, ∫⁻ x : ℤ, ‖A i x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count) := by
        refine add_le_add ?_ ?_
        · refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          rw [← Finset.sum_biUnion hdisj]
          exact ENNReal.sum_le_tsum _
        · refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact hbase
    _ = 8 * ∑' i : ℕ, ∫⁻ x : ℤ, ‖A i x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by ring

/-- If `A` is pointwise dominated by `B` in norm, the oscillation of `A` is controlled by the
square function of `B`. -/
lemma oscZ_le_eight_tsum_of_enorm_le (A B : ℕ → ℤ → ℂ)
    (h : ∀ i x, ‖A i x‖ₑ ≤ ‖B i x‖ₑ) (J : ℕ) (k : ℕ → ℕ) (hk : StrictMono k) :
    oscZ A J k
      ≤ 8 * ∑' i : ℕ, ∫⁻ x : ℤ, ‖B i x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by
  have hterm : ∀ j : ℕ,
      ∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖A i x - A (k j) x‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count
        ≤ 8 * (∑ i ∈ Finset.Ico (k j) (k (j + 1)),
              ∫⁻ x : ℤ, ‖B i x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count) := by
    intro j
    have hpt : ∀ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖A i x - A (k j) x‖ₑ) ^ (2 : ℝ)
        ≤ 8 * (∑ i ∈ Finset.Ico (k j) (k (j + 1)), ‖B i x‖ₑ ^ (2 : ℝ)) := by
      intro x
      have h1 : (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖A i x - A (k j) x‖ₑ)
          ≤ (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖B i x‖ₑ)
            + (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖B i x‖ₑ) := by
        refine iSup_le fun i => iSup_le fun hi => ?_
        refine le_trans (enorm_sub_le_two _ _) (add_le_add ?_ ?_)
        · exact le_trans (h i x) (le_iSup₂_of_le i hi le_rfl)
        · refine le_trans (h (k j) x) (le_iSup₂_of_le (k j) ?_ le_rfl)
          rw [Finset.mem_Ico]
          exact ⟨le_rfl, hk (Nat.lt_succ_self j)⟩
      have h2 : (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖B i x‖ₑ) ^ (2 : ℝ)
          ≤ ∑ i ∈ Finset.Ico (k j) (k (j + 1)), ‖B i x‖ₑ ^ (2 : ℝ) := by
        rw [iSup_finset_rpow_two]
        exact iSup_finset_le_sum _
      calc (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖A i x - A (k j) x‖ₑ) ^ (2 : ℝ)
          ≤ ((⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖B i x‖ₑ)
              + (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖B i x‖ₑ)) ^ (2 : ℝ) :=
            ENNReal.rpow_le_rpow h1 (by norm_num)
        _ ≤ 4 * ((⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖B i x‖ₑ) ^ (2 : ℝ)
              + (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖B i x‖ₑ) ^ (2 : ℝ)) :=
            Lacunary.add_sq_le _ _
        _ ≤ 4 * ((∑ i ∈ Finset.Ico (k j) (k (j + 1)), ‖B i x‖ₑ ^ (2 : ℝ))
              + (∑ i ∈ Finset.Ico (k j) (k (j + 1)), ‖B i x‖ₑ ^ (2 : ℝ))) := by
            refine mul_le_mul_of_nonneg_left (add_le_add h2 h2) (by norm_num)
        _ = 8 * (∑ i ∈ Finset.Ico (k j) (k (j + 1)), ‖B i x‖ₑ ^ (2 : ℝ)) := by
            rw [← two_mul, ← mul_assoc]; norm_num
    calc ∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖A i x - A (k j) x‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count
        ≤ ∫⁻ x : ℤ, 8 * (∑ i ∈ Finset.Ico (k j) (k (j + 1)), ‖B i x‖ₑ ^ (2 : ℝ))
            ∂MeasureTheory.Measure.count := lintegral_mono hpt
      _ = 8 * ∫⁻ x : ℤ, (∑ i ∈ Finset.Ico (k j) (k (j + 1)), ‖B i x‖ₑ ^ (2 : ℝ))
            ∂MeasureTheory.Measure.count := lintegral_const_mul' _ _ (by norm_num)
      _ = 8 * (∑ i ∈ Finset.Ico (k j) (k (j + 1)),
              ∫⁻ x : ℤ, ‖B i x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count) := by
          rw [lintegral_finsetSum _ (fun i _ => measurable_of_countable _)]
  have hdisj : Set.PairwiseDisjoint (Finset.range J : Set ℕ)
      (fun j => Finset.Ico (k j) (k (j + 1))) := by
    intro a _ b _ hab
    rw [Function.onFun, Finset.disjoint_left]
    intro i hi hj
    rw [Finset.mem_Ico] at hi hj
    rcases lt_or_gt_of_ne hab with h | h
    · have := hk.monotone (show a + 1 ≤ b by omega)
      omega
    · have := hk.monotone (show b + 1 ≤ a by omega)
      omega
  calc oscZ A J k
      = ∑ j ∈ Finset.range J, ∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
          ‖A i x - A (k j) x‖ₑ) ^ (2 : ℝ) ∂MeasureTheory.Measure.count := rfl
    _ ≤ ∑ j ∈ Finset.range J, 8 * (∑ i ∈ Finset.Ico (k j) (k (j + 1)),
              ∫⁻ x : ℤ, ‖B i x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count) :=
        Finset.sum_le_sum (fun j _ => hterm j)
    _ = 8 * (∑ j ∈ Finset.range J, ∑ i ∈ Finset.Ico (k j) (k (j + 1)),
            ∫⁻ x : ℤ, ‖B i x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count) := by
        rw [← Finset.mul_sum]
    _ ≤ 8 * (∑' i : ℕ, ∫⁻ x : ℤ, ‖B i x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        rw [← Finset.sum_biUnion hdisj]
        exact ENNReal.sum_le_tsum _


/-! ## The three analytic interfaces

The per-block oscillation inequality `oscZ_block_lacunary_v2` is assembled from three inputs.

`NbrhdMaximalLacunary` is the multi-frequency neighbourhood maximal function at an *arbitrary
antitone* family of radii `ρ` (the dyadic family `2^{-t-1}` being the special case covered by
`CircleNeighborhoodMaximal`): the `t`-th radius is sandwiched between two consecutive dyadic radii,
and the extra hypothesis `hwin` says that at most `M` consecutive indices have their radius in the
same dyadic window, which is what makes the "half-shell" correction square-summable.

`OscZCoreLacunary` is the resulting block-oscillation estimate for the (weighted) sharp core
`∑_{p ∈ T} p.2 · perNbhd p.1 (ρ i)` at the lacunary scales `ρ i`.

`OscZErrLacunary P ρ` is the same for the profile-replacement error family
`polyErrMultCutN P m N₀ (lacScale ρ i)`, whose multipliers are square-summable in the scale by
`polyErrMultCutN_tsum_sq_le`. -/

/-- **The multi-frequency neighbourhood maximal at an antitone family of radii.** -/
def NbrhdMaximalLacunary : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (T : Finset (ℝ × ℂ)) (ρ : ℕ → ℝ) (M : ℕ),
      (∀ t, 0 < ρ t) → (∀ t, ρ t ≤ 1 / 2) → Antitone ρ →
      (∀ (j t : ℕ), ρ t ≤ (2 : ℝ) ^ (-(j : ℝ) - 1) →
        ρ (t + M) ≤ (2 : ℝ) ^ (-(j : ℝ) - 2)) →
      ∀ (Q : ℝ → ℂ), MemLp Q 2 (volume.restrict (Set.Ioc (0:ℝ) 1)) →
        (∫⁻ x : ℤ, (⨆ t : ℕ, ‖∫ θ in (0 : ℝ)..1, unNbhd T (ρ t) θ * Q θ *
            Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count)
        ≤ ENNReal.ofReal ((C * ((Real.log ((T.card : ℝ) + 2)) ^ 2 + (M : ℝ) + 1)) ^ 2)
            * ∫⁻ θ in Set.Ioc (0 : ℝ) 1, ‖Q θ‖ₑ ^ (2 : ℝ)

/-- **The block oscillation of the weighted sharp core at the lacunary scales.** -/
def OscZCoreLacunary : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (T : Finset (ℝ × ℂ)) (cap δ : ℝ), 0 < δ → δ ≤ 1 / 2 → 0 ≤ cap →
      (∀ p ∈ T, ‖p.2‖ ≤ cap) →
      (∀ p ∈ T, ∀ q ∈ T, p ≠ q → ∀ l : ℤ, δ ≤ |p.1 - q.1 + (l : ℝ)|) →
      ∀ (ρ : ℕ → ℝ) (M : ℕ), (∀ t, 0 < ρ t) → Antitone ρ →
      (∀ (j t : ℕ), ρ t ≤ (2 : ℝ) ^ (-(j : ℝ) - 1) →
        ρ (t + M) ≤ (2 : ℝ) ^ (-(j : ℝ) - 2)) →
      ∀ (j₀ : ℕ), (∀ t, j₀ ≤ t → ρ t ≤ δ / 3) →
      ∀ (J : ℕ) (k : ℕ → ℕ), StrictMono k → j₀ ≤ k 0 →
      ∀ (f : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → f n = 0) →
        oscZ (fun i x => ∫ θ in (0 : ℝ)..1,
            (if j₀ ≤ i then ∑ p ∈ T, p.2 * perNbhd p.1 (ρ i) θ else 0) *
            (∑ n ∈ s, f n * Complex.exp (2 * Real.pi * Complex.I * ((n : ℤ) : ℂ) * (θ : ℂ))) *
            Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ)))) J k
          ≤ ENNReal.ofReal ((C * cap * ((Real.log ((T.card : ℝ) + 2)) ^ 2 + (M : ℝ) + 1)) ^ 2) *
            ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count

/-- **The block oscillation of the profile-replacement error at the lacunary scales.** -/
def OscZErrLacunary (P : Polynomial ℤ) (ρ : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (m N₀ : ℕ), 2 ^ (4 * m + 4) ≤ N₀ → ∀ (j₀ : ℕ) (J : ℕ) (k : ℕ → ℕ), StrictMono k →
      ∀ (g : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → g n = 0) →
        oscZ (fun i x => if j₀ ≤ i then ∫ θ in (0 : ℝ)..1,
            polyErrMultCutN P m N₀ (lacScale ρ i) θ *
            (∑ n ∈ s, g n * Complex.exp (2 * Real.pi * Complex.I * ((n : ℤ) : ℂ) * (θ : ℂ))) *
            Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ))) else 0) J k
          ≤ ENNReal.ofReal (C * (2 : ℝ) ^ (-(m : ℝ) * Maximal.polySig P)) ^ 2 *
              ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count

end

end Work.BourgainPlan.Oscillation
