import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs
import Submission.Work.BourgainPlan.Oscillation.shifted_cut_maximal
import Submission.Work.BourgainPlan.Oscillation.oscZ_cut_of_maximal

/-!
# From the shifted-cut maximal inequality to the shifted-cut block oscillation
(for an arbitrary bounded measurable density)

This is the `L²`-density version of `Oscillation.oscZ_cut_of_maximal`: there the band-limiting
argument was carried out for a *finitely supported* trig polynomial `P = Σ_{n ∈ T} f n e(nθ)`
(so that the blockwise `L²` norms could be summed by Plancherel).  Here the same argument is run
for an arbitrary **bounded measurable** `g : ℝ → ℂ` (hence `g ∈ L²(μ₀₁)`), and the blockwise
`L²` norms of the band-restricted pieces `1_{band_j} · g` are estimated directly by the fact that
the bands `band_j = (s ρ^{-(k(j+1)-1)}, s ρ^{-k j}]` are pairwise disjoint.

Nothing changes in the geometry: the helper lemmas are the ones of `oscZ_cut_of_maximal`, copied
here (they are `private` there) since the two developments live in different namespaces.
-/

namespace Work.BourgainPlan.Oscillation.Lacunary

open Finset MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The band `(s ρ^{-(b-1)}, s ρ^{-a}]` attached to the block `[a,b)` of lacunary scales. -/
private def cutBandG (s ρ : ℝ) (a b : ℕ) : Set ℝ :=
  Set.Ioc (s * ρ ^ (-((b - 1 : ℕ) : ℤ))) (s * ρ ^ (-(a : ℤ)))

/-- The lacunary truncated maximal operator of the shifted cut family. -/
private noncomputable def cutMaxG (ρ s : ℝ) (G : ℝ → ℂ) (x : ℤ) : ℝ≥0∞ :=
  ⨆ i : ℕ, ‖∫ θ, (if θ ≤ s * ρ ^ (-(i : ℤ)) then (1 : ℂ) else 0) * G θ
      * Echar x θ ∂mu01‖ₑ

private lemma cutMaxG_le (ρ s : ℝ) (G : ℝ → ℂ) (x : ℤ) (i : ℕ) :
    ‖∫ θ, (if θ ≤ s * ρ ^ (-(i : ℤ)) then (1 : ℂ) else 0) * G θ
        * Echar x θ ∂mu01‖ₑ ≤ cutMaxG ρ s G x :=
  le_iSup (fun i' : ℕ => ‖∫ θ, (if θ ≤ s * ρ ^ (-(i' : ℤ)) then (1 : ℂ) else 0) * G θ
      * Echar x θ ∂mu01‖ₑ) i

private lemma cut_sub_cut_revG (θ b a : ℝ) (hba : b ≤ a) :
    (if θ ≤ b then (1 : ℂ) else 0) - (if θ ≤ a then (1 : ℂ) else 0)
      = -(if b < θ ∧ θ ≤ a then (1 : ℂ) else 0) := by
  by_cases h1 : θ ≤ b
  · have h2 : θ ≤ a := le_trans h1 hba
    have h3 : ¬ (b < θ) := not_lt.mpr h1
    simp [h1, h2, h3]
  · have h3 : b < θ := lt_of_not_ge h1
    by_cases h2 : θ ≤ a
    · simp [h1, h2, h3]
    · simp [h1, h2, h3]

private lemma measurable_cutG (c : ℝ) :
    Measurable (fun θ : ℝ => if θ ≤ c then (1 : ℂ) else 0) :=
  Measurable.ite measurableSet_Iic measurable_const measurable_const

private lemma memLp_mu01_of_boundG {F : ℝ → ℂ} (hF : Measurable F) {K : ℝ}
    (hK : ∀ θ, ‖F θ‖ ≤ K) : MemLp F 2 mu01 :=
  letI : IsFiniteMeasure mu01 := isFiniteMeasure_mu01
  MemLp.of_bound hF.aestronglyMeasurable K (Filter.Eventually.of_forall hK)

private lemma integrable_cut_mulG {c : ℝ} {G : ℝ → ℂ} (hG : Measurable G) {K : ℝ}
    (hK : ∀ θ, ‖G θ‖ ≤ K) (x : ℤ) :
    Integrable (fun θ : ℝ => (if θ ≤ c then (1 : ℂ) else 0) * G θ * Echar x θ) mu01 := by
  refine integrable_Ioc_of_bound (((measurable_cutG c).mul hG).mul
    (continuous_Echar x).measurable) (C := K) (fun θ => ?_)
  rw [norm_mul, norm_mul, norm_Echar, mul_one]
  calc ‖(if θ ≤ c then (1 : ℂ) else 0)‖ * ‖G θ‖ ≤ 1 * ‖G θ‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        by_cases h : θ ≤ c <;> simp [h]
    _ = ‖G θ‖ := one_mul _
    _ ≤ K := hK θ

/-- The support of the cut difference `1_{θ ≤ s ρ^{-i}} - 1_{θ ≤ s ρ^{-a}}` (for `a ≤ i ≤ b-1`)
lies in the band `(s ρ^{-(b-1)}, s ρ^{-a}]`: multiplying the difference by the band-limited piece
gives the same result as multiplying by the original function. -/
private lemma cut_diff_mul_indicatorG {ρ s : ℝ} (hρ : 1 < ρ) (hs : 0 < s)
    {a b i : ℕ} (hi1 : a ≤ i) (hi2 : i ≤ b - 1) (G : ℝ → ℂ) (θ : ℝ) :
    ((if θ ≤ s * ρ ^ (-(i : ℤ)) then (1 : ℂ) else 0)
        - (if θ ≤ s * ρ ^ (-(a : ℤ)) then (1 : ℂ) else 0)) * G θ
      = ((if θ ≤ s * ρ ^ (-(i : ℤ)) then (1 : ℂ) else 0)
        - (if θ ≤ s * ρ ^ (-(a : ℤ)) then (1 : ℂ) else 0))
        * Set.indicator (cutBandG s ρ a b) G θ := by
  have hρ1 : (1 : ℝ) ≤ ρ := le_of_lt hρ
  have hle : s * ρ ^ (-(i : ℤ)) ≤ s * ρ ^ (-(a : ℤ)) := by
    refine mul_le_mul_of_nonneg_left ?_ hs.le
    refine zpow_le_zpow_right₀ hρ1 ?_
    have h : (a : ℤ) ≤ (i : ℤ) := by exact_mod_cast hi1
    omega
  rw [cut_sub_cut_revG θ _ _ hle]
  by_cases hE : s * ρ ^ (-(i : ℤ)) < θ ∧ θ ≤ s * ρ ^ (-(a : ℤ))
  · rw [if_pos hE]
    have hmem : θ ∈ cutBandG s ρ a b := by
      rw [cutBandG]
      refine ⟨lt_of_le_of_lt ?_ hE.1, hE.2⟩
      refine mul_le_mul_of_nonneg_left ?_ hs.le
      refine zpow_le_zpow_right₀ hρ1 ?_
      have h : (i : ℤ) ≤ ((b - 1 : ℕ) : ℤ) := by
        have : i ≤ b - 1 := hi2
        omega
      omega
    rw [Set.indicator_of_mem hmem G]
  · rw [if_neg hE]; ring

/-- **The key pointwise bound.**  For `i` in the block `[a,b)`, the deviation of the `i`-th shifted
cut of `G` from the `a`-th one is dominated by twice the lacunary truncated maximal function of the
band-limited piece `1_{(sρ^{-(b-1)}, sρ^{-a}]} G`. -/
private lemma cut_shift_pointwiseG {ρ s : ℝ} (hρ : 1 < ρ) (hs : 0 < s)
    {G : ℝ → ℂ} (hG : Measurable G) {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ θ, ‖G θ‖ ≤ K)
    {a b i : ℕ} (hi1 : a ≤ i) (hi2 : i ≤ b - 1) (x : ℤ) :
    ‖(∫ θ, (if θ ≤ s * ρ ^ (-(i : ℤ)) then (1 : ℂ) else 0) * G θ
          * Echar x θ ∂mu01)
        - (∫ θ, (if θ ≤ s * ρ ^ (-(a : ℤ)) then (1 : ℂ) else 0) * G θ
          * Echar x θ ∂mu01)‖ₑ
      ≤ 2 * cutMaxG ρ s (Set.indicator (cutBandG s ρ a b) G) x := by
  have hQmeas : Measurable (Set.indicator (cutBandG s ρ a b) G) :=
    hG.indicator (by rw [cutBandG]; exact measurableSet_Ioc)
  have hQbound : ∀ θ, ‖Set.indicator (cutBandG s ρ a b) G θ‖ ≤ K := by
    intro θ
    by_cases h : θ ∈ cutBandG s ρ a b
    · rw [Set.indicator_of_mem h]; exact hK θ
    · rw [Set.indicator_of_notMem h, norm_zero]; exact hK0
  have hsplit : (∫ θ, (if θ ≤ s * ρ ^ (-(i : ℤ)) then (1 : ℂ) else 0) * G θ
        * Echar x θ ∂mu01)
      - (∫ θ, (if θ ≤ s * ρ ^ (-(a : ℤ)) then (1 : ℂ) else 0) * G θ
        * Echar x θ ∂mu01)
      = (∫ θ, (if θ ≤ s * ρ ^ (-(i : ℤ)) then (1 : ℂ) else 0)
          * Set.indicator (cutBandG s ρ a b) G θ * Echar x θ ∂mu01)
        - (∫ θ, (if θ ≤ s * ρ ^ (-(a : ℤ)) then (1 : ℂ) else 0)
          * Set.indicator (cutBandG s ρ a b) G θ * Echar x θ ∂mu01) := by
    rw [← integral_sub (integrable_cut_mulG hG hK x)
        (integrable_cut_mulG hG hK x),
      ← integral_sub (integrable_cut_mulG hQmeas hQbound x)
        (integrable_cut_mulG hQmeas hQbound x)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
    have hkey := cut_diff_mul_indicatorG hρ hs hi1 hi2 G θ
    calc (if θ ≤ s * ρ ^ (-(i : ℤ)) then (1 : ℂ) else 0) * G θ * Echar x θ
          - (if θ ≤ s * ρ ^ (-(a : ℤ)) then (1 : ℂ) else 0) * G θ * Echar x θ
        = (((if θ ≤ s * ρ ^ (-(i : ℤ)) then (1 : ℂ) else 0)
            - (if θ ≤ s * ρ ^ (-(a : ℤ)) then (1 : ℂ) else 0)) * G θ)
            * Echar x θ := by ring
      _ = (((if θ ≤ s * ρ ^ (-(i : ℤ)) then (1 : ℂ) else 0)
            - (if θ ≤ s * ρ ^ (-(a : ℤ)) then (1 : ℂ) else 0))
            * Set.indicator (cutBandG s ρ a b) G θ) * Echar x θ := by rw [hkey]
      _ = (if θ ≤ s * ρ ^ (-(i : ℤ)) then (1 : ℂ) else 0)
            * Set.indicator (cutBandG s ρ a b) G θ * Echar x θ
          - (if θ ≤ s * ρ ^ (-(a : ℤ)) then (1 : ℂ) else 0)
            * Set.indicator (cutBandG s ρ a b) G θ * Echar x θ := by ring
  rw [hsplit]
  refine le_trans (enorm_sub_le) ?_
  rw [two_mul]
  exact add_le_add (cutMaxG_le ρ s _ x i) (cutMaxG_le ρ s _ x a)

/-- The bands attached to distinct blocks are disjoint. -/
private lemma cutBandG_disjoint {ρ s : ℝ} (hρ : 1 < ρ) (hs : 0 < s) {k : ℕ → ℕ}
    (hk : StrictMono k) {j j' : ℕ} (h : j < j') :
    Disjoint (cutBandG s ρ (k j) (k (j + 1))) (cutBandG s ρ (k j') (k (j' + 1))) := by
  rw [Set.disjoint_left]
  intro θ hθ hθ'
  rw [cutBandG] at hθ hθ'
  obtain ⟨h1, h2⟩ := hθ
  obtain ⟨h3, h4⟩ := hθ'
  have hkj : k (j + 1) ≤ k j' := hk.monotone (by omega)
  have hle : s * ρ ^ (-((k j' : ℕ) : ℤ)) ≤ s * ρ ^ (-(((k (j + 1) - 1 : ℕ)) : ℤ)) := by
    refine mul_le_mul_of_nonneg_left ?_ hs.le
    refine zpow_le_zpow_right₀ (le_of_lt hρ) ?_
    have hle_nat : k (j + 1) - 1 ≤ k j' := le_trans (Nat.sub_le _ _) hkj
    have hcast : (((k (j + 1) - 1 : ℕ)) : ℤ) ≤ ((k j' : ℕ) : ℤ) := by exact_mod_cast hle_nat
    omega
  linarith

theorem oscZ_cut_of_maximal_bd (ρ : ℝ) (hρ : 1 < ρ) (C₀ : ℝ) (hC₀ : 0 < C₀)
    (hmax : ∀ (s : ℝ), 0 < s → ∀ (h : ℝ → ℂ),
      MeasureTheory.MemLp h 2 Work.BourgainPlan.Oscillation.Lacunary.mu01 →
      ∫⁻ x : ℤ, (⨆ i : ℕ, ‖∫ θ, (if θ ≤ s * ρ ^ (-(i : ℤ)) then (1 : ℂ) else 0) * h θ
          * Work.BourgainPlan.Oscillation.Lacunary.Echar x θ
            ∂Work.BourgainPlan.Oscillation.Lacunary.mu01‖ₑ) ^ (2 : ℝ)
        ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C₀ ^ 2) * ∫⁻ θ : ℝ, ‖h θ‖ₑ ^ (2 : ℝ)
          ∂Work.BourgainPlan.Oscillation.Lacunary.mu01) :
    ∀ (s : ℝ), 0 < s → ∀ (g : ℝ → ℂ), Measurable g → ∀ (K : ℝ), 0 ≤ K →
      (∀ θ, ‖g θ‖ ≤ K) →
      ∀ (J : ℕ) (k : ℕ → ℕ), StrictMono k →
        Work.BourgainPlan.Oscillation.oscZ (fun i x =>
            ∫ θ, (if θ ≤ s * ρ ^ (-(i : ℤ)) then (1 : ℂ) else 0) * g θ
              * Work.BourgainPlan.Oscillation.Lacunary.Echar x θ
                ∂Work.BourgainPlan.Oscillation.Lacunary.mu01) J k
          ≤ ENNReal.ofReal (4 * C₀ ^ 2) * ∫⁻ θ : ℝ, ‖g θ‖ₑ ^ (2 : ℝ)
              ∂Work.BourgainPlan.Oscillation.Lacunary.mu01 := by
  intro s hs g hg K hK0 hK J k hk
  set A : ℕ → ℤ → ℂ := fun i x => ∫ θ, (if θ ≤ s * ρ ^ (-(i : ℤ)) then (1 : ℂ) else 0)
      * g θ * Echar x θ ∂mu01 with hAdef
  have hblock : ∀ j : ℕ,
      ∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖A i x - A (k j) x‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count
        ≤ 4 * (ENNReal.ofReal (C₀ ^ 2) *
            ∫⁻ θ, ‖Set.indicator (cutBandG s ρ (k j) (k (j + 1))) g θ‖ₑ ^ (2 : ℝ) ∂mu01) := by
    intro j
    set Q : ℝ → ℂ := Set.indicator (cutBandG s ρ (k j) (k (j + 1))) g with hQdef
    have hQmeas : Measurable Q := by
      rw [hQdef]
      exact hg.indicator (by rw [cutBandG]; exact measurableSet_Ioc)
    have hQbound : ∀ θ, ‖Q θ‖ ≤ K := by
      intro θ
      rw [hQdef]
      by_cases h : θ ∈ cutBandG s ρ (k j) (k (j + 1))
      · rw [Set.indicator_of_mem h]; exact hK θ
      · rw [Set.indicator_of_notMem h, norm_zero]; exact hK0
    have hmaxQ : ∫⁻ x : ℤ, (cutMaxG ρ s Q x) ^ (2 : ℝ) ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C₀ ^ 2) * ∫⁻ θ, ‖Q θ‖ₑ ^ (2 : ℝ) ∂mu01 := by
      simpa only [cutMaxG] using hmax s hs Q (memLp_mu01_of_boundG hQmeas hQbound)
    have hpt : ∀ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖A i x - A (k j) x‖ₑ)
        ≤ 2 * cutMaxG ρ s Q x := by
      intro x
      refine iSup_le fun i => iSup_le fun hi => ?_
      obtain ⟨hi1, hi2⟩ := Finset.mem_Ico.mp hi
      have hi2' : i ≤ k (j + 1) - 1 := Nat.le_sub_one_of_lt hi2
      have h := cut_shift_pointwiseG hρ hs hg hK0 hK hi1 hi2' x
      simpa only [hAdef, hQdef] using h
    calc ∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖A i x - A (k j) x‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count
        ≤ ∫⁻ x : ℤ, (2 * cutMaxG ρ s Q x) ^ (2 : ℝ) ∂MeasureTheory.Measure.count :=
          lintegral_mono (fun x => ENNReal.rpow_le_rpow (hpt x) (by norm_num))
      _ = ∫⁻ x : ℤ, 4 * (cutMaxG ρ s Q x) ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by
          refine lintegral_congr (fun x => ?_)
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
          rw [show ((2 : ℝ≥0∞) ^ (2 : ℝ)) = 4 from by norm_num [ENNReal.rpow_two]]
      _ = 4 * ∫⁻ x : ℤ, (cutMaxG ρ s Q x) ^ (2 : ℝ) ∂MeasureTheory.Measure.count :=
          lintegral_const_mul' 4 _ (by norm_num)
      _ ≤ 4 * (ENNReal.ofReal (C₀ ^ 2) * ∫⁻ θ, ‖Q θ‖ₑ ^ (2 : ℝ) ∂mu01) :=
          mul_le_mul_of_nonneg_left hmaxQ (by norm_num : (0 : ℝ≥0∞) ≤ 4)
      _ = 4 * (ENNReal.ofReal (C₀ ^ 2) *
            ∫⁻ θ, ‖Set.indicator (cutBandG s ρ (k j) (k (j + 1))) g θ‖ₑ ^ (2 : ℝ) ∂mu01) := by
          rw [hQdef]
  have hpairdisj : ∀ j j' : ℕ, j ≠ j' →
      Disjoint (cutBandG s ρ (k j) (k (j + 1))) (cutBandG s ρ (k j') (k (j' + 1))) := by
    intro j j' hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact cutBandG_disjoint hρ hs hk h
    · exact (cutBandG_disjoint hρ hs hk h).symm
  have hsum : (∑ j ∈ Finset.range J,
        ∫⁻ θ, ‖Set.indicator (cutBandG s ρ (k j) (k (j + 1))) g θ‖ₑ ^ (2 : ℝ) ∂mu01)
      ≤ ∫⁻ θ, ‖g θ‖ₑ ^ (2 : ℝ) ∂mu01 := by
    rw [← lintegral_finsetSum (Finset.range J)
      (f := fun j θ => ‖Set.indicator (cutBandG s ρ (k j) (k (j + 1))) g θ‖ₑ ^ (2 : ℝ))
      (fun j _ => ((hg.indicator (by rw [cutBandG]; exact measurableSet_Ioc)).enorm).pow_const 2)]
    refine lintegral_mono (fun θ => ?_)
    by_cases hex : ∃ j ∈ Finset.range J, θ ∈ cutBandG s ρ (k j) (k (j + 1))
    · obtain ⟨j0, hj0mem, hj0⟩ := hex
      have huniq : ∀ j ∈ Finset.range J, θ ∈ cutBandG s ρ (k j) (k (j + 1)) → j = j0 := by
        intro j hj hjθ
        by_contra hne
        rcases lt_or_gt_of_ne hne with h | h
        · exact (Set.disjoint_left.mp (hpairdisj j j0 hne) hjθ) hj0
        · exact (Set.disjoint_left.mp (hpairdisj j0 j (Ne.symm hne)) hj0) hjθ
      rw [Finset.sum_eq_single j0]
      · rw [Set.indicator_of_mem hj0]
      · intro j hj hne
        rw [Set.indicator_of_notMem (fun hcon => hne (huniq j hj hcon)), enorm_zero]
        simp
      · intro hcon; exact absurd hj0mem hcon
    · have hz : ∀ j ∈ Finset.range J,
          ‖Set.indicator (cutBandG s ρ (k j) (k (j + 1))) g θ‖ₑ ^ (2 : ℝ) = 0 := by
        intro j hj
        rw [Set.indicator_of_notMem (fun hcon => hex ⟨j, hj, hcon⟩), enorm_zero]
        simp
      rw [Finset.sum_eq_zero hz]
      exact bot_le
  have h4C : (4 : ℝ≥0∞) * ENNReal.ofReal (C₀ ^ 2) = ENNReal.ofReal (4 * C₀ ^ 2) := by
    rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  calc oscZ A J k
      = ∑ j ∈ Finset.range J, ∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j + 1)), ‖A i x - A (k j) x‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count := by simp only [oscZ]
    _ ≤ ∑ j ∈ Finset.range J, 4 * (ENNReal.ofReal (C₀ ^ 2) * ∫⁻ θ, ‖Set.indicator (cutBandG s ρ (k j) (k (j + 1))) g θ‖ₑ ^ (2 : ℝ) ∂mu01) :=
        Finset.sum_le_sum (fun j _ => hblock j)
    _ = 4 * ENNReal.ofReal (C₀ ^ 2) * ∑ j ∈ Finset.range J, ∫⁻ θ, ‖Set.indicator (cutBandG s ρ (k j) (k (j + 1))) g θ‖ₑ ^ (2 : ℝ) ∂mu01 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
    _ ≤ 4 * ENNReal.ofReal (C₀ ^ 2) * ∫⁻ θ, ‖g θ‖ₑ ^ (2 : ℝ) ∂mu01 :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ENNReal.ofReal (4 * C₀ ^ 2) * ∫⁻ θ : ℝ, ‖g θ‖ₑ ^ (2 : ℝ) ∂mu01 := by
        rw [h4C]

end

end Work.BourgainPlan.Oscillation.Lacunary
