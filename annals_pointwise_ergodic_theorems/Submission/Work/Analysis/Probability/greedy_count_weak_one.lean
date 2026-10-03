import Mathlib
import Submission.Work.Analysis.Probability.greedySampling

/-!
# Weak `(1,1)` bound for the greedy `δ`-jump count of a martingale

This file contains the proof of `greedy_count_weak_one`: for a martingale `H` with
`sup n ∫ |H n| ≤ B` and any `δ, y > 0`,

`μ {ω | y < greedyJumps (fun n => H n ω) δ} ≤ C B / (δ √y)`.

The heart of the proof is the energy estimate `energy_bound_core` below: for an abstract martingale
`u` with a decreasing family of "good" events `E k` on which `u` is bounded by `M`, the expected
total squared increment along the first `K` blocks is at most `7 M B`.  The remaining steps
(Doob's maximal inequality and an instantiation to the sampled martingale `greedyAnchor`) are
carried out in the same file.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace Work.Analysis.Probability

/-- Abel summation by parts. -/
theorem sum_Icc_mul_sub_eq' (c x : ℕ → ℝ) {K : ℕ} (hK : 1 ≤ K) :
    (∑ k ∈ Finset.Icc 1 K, c k * (x k - x (k - 1))) =
      c K * x K - c 1 * x 0 + ∑ k ∈ Finset.Icc 1 (K - 1), (c k - c (k + 1)) * x k := by
  induction K with
  | zero => omega
  | succ K ih =>
      rcases Nat.eq_zero_or_pos K with h0 | hpos
      · subst h0
        have hsub : (1 : ℕ) - 1 = 0 := rfl
        rw [Finset.Icc_eq_empty_of_lt (by omega : (0:ℕ) < 1), Finset.sum_empty, add_zero]
        simp only [Finset.Icc_self, Finset.sum_singleton, hsub]
        ring
      · have h1 : (∑ k ∈ Finset.Icc 1 (K + 1), c k * (x k - x (k - 1)))
            = (∑ k ∈ Finset.Icc 1 K, c k * (x k - x (k - 1)))
              + c (K + 1) * (x (K + 1) - x K) :=
          Finset.sum_Icc_succ_top (by omega) _
        rw [h1, ih hpos, Nat.add_sub_cancel]
        have h2 : (∑ k ∈ Finset.Icc 1 K, (c k - c (k + 1)) * x k)
            = (∑ k ∈ Finset.Icc 1 (K - 1), (c k - c (k + 1)) * x k) + (c K - c (K + 1)) * x K := by
          have hthis := Finset.sum_Icc_succ_top (a := 1) (b := K - 1)
            (f := fun k => (c k - c (k + 1)) * x k) (by omega : 1 ≤ K - 1 + 1)
          rw [Nat.sub_add_cancel hpos] at hthis
          exact hthis
        rw [h2]
        ring

private lemma abs_sub_le_abs_add (a b : ℝ) : |a - b| ≤ |a| + |b| :=
  abs_sub_le_iff.mpr ⟨by linarith [le_abs_self a, neg_le_abs b],
    by linarith [le_abs_self b, neg_le_abs a]⟩

private lemma integrable_finset_sum {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    {ι : Type*} [DecidableEq ι] (s : Finset ι) {f : ι → Ω → ℝ}
    (h : ∀ i ∈ s, MeasureTheory.Integrable (f i) μ) :
    MeasureTheory.Integrable (fun ω => ∑ i ∈ s, f i ω) μ := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (MeasureTheory.integrable_zero Ω ℝ μ)
  | insert a s ha ih =>
      have h1 : MeasureTheory.Integrable (fun ω => f a ω) μ := h a (Finset.mem_insert_self a s)
      have h2 : MeasureTheory.Integrable (fun ω => ∑ i ∈ s, f i ω) μ :=
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      have hfun : (fun ω => ∑ i ∈ insert a s, f i ω)
          = (fun ω => f a ω) + (fun ω => ∑ i ∈ s, f i ω) := by
        funext ω; simp [Finset.sum_insert ha, Pi.add_apply]
      rw [hfun]
      exact h1.add h2

/-- Energy bound for the sampled martingale: the expected sum of squared increments along the
greedy chain over `K` blocks is at most `7 M B`. -/
theorem energy_bound_core {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.SigmaFinite μ] {u : ℕ → Ω → ℝ} {𝓖 : ℕ → MeasurableSpace Ω}
    (h𝓖le : ∀ k, 𝓖 k ≤ mΩ)
    (hmono : ∀ {i j : ℕ}, i ≤ j → 𝓖 i ≤ 𝓖 j)
    (hmart : ∀ {i j : ℕ}, i ≤ j → u i =ᵐ[μ] μ[u j | 𝓖 i])
    (hint : ∀ k, MeasureTheory.Integrable (u k) μ)
    (h𝓖fin : ∀ k, MeasureTheory.SigmaFinite (μ.trim (h𝓖le k)))
    (humeas : ∀ k, AEStronglyMeasurable[𝓖 k] (u k) μ)
    {M B : ℝ} (hM : 0 < M) (hB : 0 ≤ B)
    {E : ℕ → Set Ω} (hEmeas : ∀ k, MeasurableSet[𝓖 k] (E k))
    (hEmono : ∀ {i j : ℕ}, i ≤ j → E j ⊆ E i)
    (hEband : ∀ k, ∀ ω ∈ E k, |u k ω| ≤ M)
    (hsetint : ∀ (i j : ℕ), i ≤ j → ∀ S : Set Ω,
      MeasurableSet[𝓖 i] S → ∫ ω in S, |u j ω| ∂μ ≤ B)
    {K : ℕ} (hK : 1 ≤ K)
    (hexit1 : ∑ j ∈ Finset.Icc 1 (K - 1), (μ (E j \ E (j + 1))).toReal ≤ B / M)
    (hexit2 : ∑ k ∈ Finset.Icc 1 K, (μ (E (k - 1) \ E k)).toReal ≤ B / M)
    (hexit_abs : ∑ k ∈ Finset.Icc 1 K, ∫ ω in (E (k - 1) \ E k), |u k ω| ∂μ ≤ B)
    (hexit_fin : ∀ i j : ℕ, j ≤ i → μ (E j \ E i) ≠ ⊤) :
    ∫ ω, (∑ k ∈ Finset.Icc 1 K, (E k).indicator (fun ω => (u k ω - u (k - 1) ω) ^ 2) ω) ∂μ
      ≤ 7 * M * B := by
  classical
  have hEamb : ∀ k, MeasurableSet (E k) := fun k => h𝓖le k _ (hEmeas k)
  -- band: `|u k| ≤ M` on `E i` for `k ≤ i`
  have hband : ∀ {i k : ℕ}, k ≤ i → ∀ ω ∈ E i, |u k ω| ≤ M :=
    fun {i k} hik ω hω => hEband k ω (hEmono hik hω)
  -- generic domination: `1_{E k} f` is integrable when `|f| ≤ C (|u k| + |u (k-1)|)` on `E k`
  have hdomgen : ∀ (k : ℕ) (f : Ω → ℝ) (C : ℝ), 0 ≤ C →
      (∀ ω ∈ E k, |f ω| ≤ C * (|u k ω| + |u (k - 1) ω|)) →
      AEStronglyMeasurable f μ → MeasureTheory.Integrable ((E k).indicator f) μ := by
    intro k f C hC hf hm
    have hg : MeasureTheory.Integrable (fun ω => C * (|u k ω| + |u (k - 1) ω|)) μ :=
      (((hint k).abs).add ((hint (k - 1)).abs)).const_mul C
    refine hg.mono' (hm.indicator (hEamb k)) ?_
    filter_upwards with ω
    by_cases hω : ω ∈ E k
    · rw [Set.indicator_of_mem hω, Real.norm_eq_abs]
      exact hf ω hω
    · rw [Set.indicator_of_notMem hω, Real.norm_eq_abs, abs_zero]
      positivity
  -- (1) integrability of the squared increments
  have hsq_int : ∀ k, MeasureTheory.Integrable
      ((E k).indicator (fun ω => (u k ω - u (k - 1) ω) ^ 2)) μ := by
    intro k
    refine hdomgen k _ (2 * M) (by positivity) ?_ ?_
    · intro ω hω
      have h1 : |u (k - 1) ω| ≤ M := hband (by omega : k - 1 ≤ k) ω hω
      have h2 : |u k ω| ≤ M := hEband k ω hω
      have h3 : (u k ω - u (k - 1) ω) ^ 2 ≤ 2 * M * (|u k ω| + |u (k - 1) ω|) := by
        have h5 : (u k ω) ^ 2 ≤ M * |u k ω| := by
          nlinarith [h2, abs_nonneg (u k ω), sq_nonneg (u k ω), sq_abs (u k ω)]
        have h6 : (u (k - 1) ω) ^ 2 ≤ M * |u (k - 1) ω| := by
          nlinarith [h1, abs_nonneg (u (k - 1) ω), sq_nonneg (u (k - 1) ω),
            sq_abs (u (k - 1) ω)]
        nlinarith [h5, h6, sq_nonneg (u k ω - u (k - 1) ω),
          sq_nonneg (u k ω + u (k - 1) ω), hM]
      rwa [abs_of_nonneg (sq_nonneg _)]
    · have h2 : (fun ω => (u k ω - u (k - 1) ω) ^ 2)
          = fun ω => (u k ω - u (k - 1) ω) * (u k ω - u (k - 1) ω) := by funext ω; ring
      rw [h2]
      exact (((hint k).aestronglyMeasurable.sub (hint (k - 1)).aestronglyMeasurable).mul
        ((hint k).aestronglyMeasurable.sub (hint (k - 1)).aestronglyMeasurable))
  -- (2) integrability of the cross term on `E k`
  have hcr_int : ∀ k, MeasureTheory.Integrable
      ((E k).indicator (fun ω => u (k - 1) ω * (u k ω - u (k - 1) ω))) μ := by
    intro k
    refine hdomgen k _ M hM.le ?_ ?_
    · intro ω hω
      have h1 : |u (k - 1) ω| ≤ M := hband (by omega : k - 1 ≤ k) ω hω
      rw [abs_mul]
      calc |u (k - 1) ω| * |u k ω - u (k - 1) ω|
          ≤ |u (k - 1) ω| * (|u k ω| + |u (k - 1) ω|) :=
            mul_le_mul_of_nonneg_left (abs_sub_le_abs_add _ _) (abs_nonneg _)
        _ ≤ M * (|u k ω| + |u (k - 1) ω|) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
    · exact (hint (k - 1)).aestronglyMeasurable.mul
        ((hint k).aestronglyMeasurable.sub (hint (k - 1)).aestronglyMeasurable)
  -- (3) integrability of the squared values on the blocks used in the telescope
  have hsq_meas : ∀ k, AEStronglyMeasurable (fun ω => (u k ω) ^ 2) μ := by
    intro k
    have h2 : (fun ω => (u k ω) ^ 2) = fun ω => u k ω * u k ω := by funext ω; ring
    rw [h2]
    exact (hint k).aestronglyMeasurable.mul (hint k).aestronglyMeasurable
  have hK2_int : MeasureTheory.Integrable ((E K).indicator (fun ω => (u K ω) ^ 2)) μ := by
    refine hdomgen K _ M hM.le ?_ (hsq_meas K)
    intro ω hω
    have h1 : |u K ω| ≤ M := hEband K ω hω
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [h1, abs_nonneg (u K ω), abs_nonneg (u (K - 1) ω), sq_nonneg (u K ω),
      sq_abs (u K ω)]
  have h0_int : MeasureTheory.Integrable ((E 1).indicator (fun ω => (u 0 ω) ^ 2)) μ := by
    have h11 : (1 : ℕ) - 1 = 0 := by norm_num
    refine hdomgen 1 _ M hM.le ?_ (hsq_meas 0)
    intro ω hω
    have h1 : |u 0 ω| ≤ M := hband (by omega : 0 ≤ 1) ω hω
    rw [h11, abs_of_nonneg (sq_nonneg _)]
    nlinarith [h1, abs_nonneg (u 0 ω), abs_nonneg (u 1 ω), sq_nonneg (u 0 ω), sq_abs (u 0 ω)]
  have hexit_int : ∀ k, MeasureTheory.Integrable
      ((E k \ E (k + 1)).indicator (fun ω => (u k ω) ^ 2)) μ := by
    intro k
    have hms : MeasurableSet (E k \ E (k + 1)) := (hEamb k).diff (hEamb (k + 1))
    have hg : MeasureTheory.Integrable (fun ω => M * (|u k ω| + |u (k - 1) ω|)) μ :=
      (((hint k).abs).add ((hint (k - 1)).abs)).const_mul M
    refine hg.mono' ((hsq_meas k).indicator hms) ?_
    filter_upwards with ω
    by_cases h : ω ∈ E k \ E (k + 1)
    · rw [Set.indicator_of_mem h, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h1 : |u k ω| ≤ M := hEband k ω h.1
      nlinarith [h1, abs_nonneg (u k ω), abs_nonneg (u (k - 1) ω), sq_nonneg (u k ω),
        sq_abs (u k ω)]
    · rw [Set.indicator_of_notMem h, Real.norm_eq_abs, abs_zero]
      nlinarith [abs_nonneg (u k ω), abs_nonneg (u (k - 1) ω), hM]
  -- pointwise algebraic identity
  have hId : ∀ ω, (∑ k ∈ Finset.Icc 1 K, (E k).indicator (fun ω => (u k ω - u (k - 1) ω) ^ 2) ω)
      = (∑ k ∈ Finset.Icc 1 K, (E k).indicator (fun ω => (u k ω) ^ 2 - (u (k - 1) ω) ^ 2) ω)
        - 2 * (∑ k ∈ Finset.Icc 1 K,
            (E k).indicator (fun ω => u (k - 1) ω * (u k ω - u (k - 1) ω)) ω) := by
    intro ω
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    by_cases h : ω ∈ E k
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Set.indicator_of_mem h]
      ring
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, Set.indicator_of_notMem h]
      ring
  -- the Abel/telescoping identity, as an identity of functions
  have hAbel_fun : (fun ω => ∑ k ∈ Finset.Icc 1 K,
        (E k).indicator (fun ω => (u k ω) ^ 2 - (u (k - 1) ω) ^ 2) ω)
      = fun ω => (E K).indicator (fun ω => (u K ω) ^ 2) ω
          - (E 1).indicator (fun ω => (u 0 ω) ^ 2) ω
          + ∑ k ∈ Finset.Icc 1 (K - 1), (E k \ E (k + 1)).indicator (fun ω => (u k ω) ^ 2) ω := by
    funext ω
    have h := sum_Icc_mul_sub_eq' (fun k => (E k).indicator (fun _ => (1:ℝ)) ω)
      (fun k => (u k ω) ^ 2) hK
    have h1 : ∀ k : ℕ, (E k).indicator (fun _ => (1:ℝ)) ω * ((u k ω) ^ 2 - (u (k - 1) ω) ^ 2)
        = (E k).indicator (fun ω => (u k ω) ^ 2 - (u (k - 1) ω) ^ 2) ω := by
      intro k
      by_cases hk : ω ∈ E k
      · rw [Set.indicator_of_mem hk, Set.indicator_of_mem hk, one_mul]
      · rw [Set.indicator_of_notMem hk, Set.indicator_of_notMem hk, zero_mul]
    have h2 : ∀ k : ℕ, (E k).indicator (fun _ => (1:ℝ)) ω * (u k ω) ^ 2
        = (E k).indicator (fun ω => (u k ω) ^ 2) ω := by
      intro k
      by_cases hk : ω ∈ E k
      · rw [Set.indicator_of_mem hk, Set.indicator_of_mem hk, one_mul]
      · rw [Set.indicator_of_notMem hk, Set.indicator_of_notMem hk, zero_mul]
    have h4 : (E 1).indicator (fun _ => (1:ℝ)) ω * (u 0 ω) ^ 2
        = (E 1).indicator (fun ω => (u 0 ω) ^ 2) ω := by
      by_cases hk : ω ∈ E 1
      · rw [Set.indicator_of_mem hk, Set.indicator_of_mem hk, one_mul]
      · rw [Set.indicator_of_notMem hk, Set.indicator_of_notMem hk, zero_mul]
    have h3 : ∀ k : ℕ, ((E k).indicator (fun _ => (1:ℝ)) ω
          - (E (k + 1)).indicator (fun _ => (1:ℝ)) ω) * (u k ω) ^ 2
        = (E k \ E (k + 1)).indicator (fun ω => (u k ω) ^ 2) ω := by
      intro k
      by_cases hk : ω ∈ E k
      · by_cases hk' : ω ∈ E (k + 1)
        · rw [Set.indicator_of_mem hk, Set.indicator_of_mem hk',
            Set.indicator_of_notMem (by
              simp only [Set.mem_diff]; exact fun h => h.2 hk'), sub_self, zero_mul]
        · rw [Set.indicator_of_mem hk, Set.indicator_of_notMem hk', sub_zero, one_mul,
            Set.indicator_of_mem (by simp only [Set.mem_diff]; exact ⟨hk, hk'⟩)]
      · have h2' : ω ∉ E (k + 1) := fun hc => hk (hEmono (by omega : k ≤ k + 1) hc)
        have h3' : ω ∉ E k \ E (k + 1) := fun hc => hk hc.1
        rw [Set.indicator_of_notMem hk, Set.indicator_of_notMem h2', zero_sub,
          Set.indicator_of_notMem h3', neg_zero, zero_mul]
    simp only [h1, h2, h3, h4] at h
    exact h
  -- integrability of the three sums appearing in the identity
  have hexit_sum_int : MeasureTheory.Integrable (fun ω =>
      ∑ k ∈ Finset.Icc 1 (K - 1), (E k \ E (k + 1)).indicator (fun ω => (u k ω) ^ 2) ω) μ :=
    integrable_finset_sum _ (fun k hk => hexit_int k)
  have hsum_d2_int : MeasureTheory.Integrable (fun ω => ∑ k ∈ Finset.Icc 1 K,
      (E k).indicator (fun ω => (u k ω) ^ 2 - (u (k - 1) ω) ^ 2) ω) μ := by
    rw [hAbel_fun]
    exact (hK2_int.sub h0_int).add hexit_sum_int
  have hsum_cr_int : MeasureTheory.Integrable (fun ω => ∑ k ∈ Finset.Icc 1 K,
      (E k).indicator (fun ω => u (k - 1) ω * (u k ω - u (k - 1) ω)) ω) μ :=
    integrable_finset_sum _ (fun k hk => hcr_int k)
  -- the basic integral identity
  have hE1 : ∫ ω, (∑ k ∈ Finset.Icc 1 K,
        (E k).indicator (fun ω => (u k ω - u (k - 1) ω) ^ 2) ω) ∂μ
      = (∫ ω, (∑ k ∈ Finset.Icc 1 K,
          (E k).indicator (fun ω => (u k ω) ^ 2 - (u (k - 1) ω) ^ 2) ω) ∂μ)
        - 2 * (∫ ω, (∑ k ∈ Finset.Icc 1 K,
            (E k).indicator (fun ω => u (k - 1) ω * (u k ω - u (k - 1) ω)) ω) ∂μ) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hId),
      integral_sub hsum_d2_int (hsum_cr_int.const_mul 2), integral_const_mul]
  -- bound on the difference-of-squares sum
  have hAK : ∫ ω, (E K).indicator (fun ω => (u K ω) ^ 2) ω ∂μ ≤ M * B := by
    rw [integral_indicator (hEamb K)]
    have h1 : ∫ ω in E K, (u K ω) ^ 2 ∂μ ≤ ∫ ω in E K, M * |u K ω| ∂μ :=
      setIntegral_mono_on ((integrable_indicator_iff (hEamb K)).mp hK2_int)
        (((hint K).abs.const_mul M).integrableOn) (hEamb K) fun ω hω => by
          have hb : |u K ω| ≤ M := hEband K ω hω
          nlinarith [hb, abs_nonneg (u K ω), sq_nonneg (u K ω), sq_abs (u K ω)]
    refine le_trans h1 ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hsetint K K le_rfl (E K) (hEmeas K)) hM.le
  have hA0 : 0 ≤ ∫ ω, (E 1).indicator (fun ω => (u 0 ω) ^ 2) ω ∂μ := by
    rw [integral_indicator (hEamb 1)]
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun ω => by positivity)
  have hAC : ∫ ω, ∑ k ∈ Finset.Icc 1 (K - 1),
        (E k \ E (k + 1)).indicator (fun ω => (u k ω) ^ 2) ω ∂μ ≤ M * B := by
    rw [integral_finsetSum _ (fun k hk => hexit_int k)]
    calc ∑ k ∈ Finset.Icc 1 (K - 1),
            ∫ ω, (E k \ E (k + 1)).indicator (fun ω => (u k ω) ^ 2) ω ∂μ
        ≤ ∑ k ∈ Finset.Icc 1 (K - 1), M * M * ((μ (E k \ E (k + 1))).toReal) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hms : MeasurableSet (E k \ E (k + 1)) := (hEamb k).diff (hEamb (k + 1))
          rw [integral_indicator hms]
          have h1 : ∫ ω in E k \ E (k + 1), (u k ω) ^ 2 ∂μ
              ≤ ∫ ω in E k \ E (k + 1), M * M ∂μ :=
            setIntegral_mono_on ((integrable_indicator_iff hms).mp (hexit_int k))
              (integrableOn_const (hexit_fin (k + 1) k (by omega)) (by finiteness)) hms
              fun ω hω => by
                have hb : |u k ω| ≤ M := hEband k ω hω.1
                nlinarith [hb, abs_nonneg (u k ω), sq_nonneg (u k ω), sq_abs (u k ω)]
          refine le_trans h1 (le_of_eq ?_)
          rw [setIntegral_const, smul_eq_mul, Measure.real, mul_comm]
      _ = M * M * (∑ k ∈ Finset.Icc 1 (K - 1), (μ (E k \ E (k + 1))).toReal) := by
          rw [Finset.mul_sum]
      _ ≤ M * M * (B / M) := mul_le_mul_of_nonneg_left hexit1 (by positivity)
      _ = M * B := by field_simp
  have hA : ∫ ω, (∑ k ∈ Finset.Icc 1 K,
        (E k).indicator (fun ω => (u k ω) ^ 2 - (u (k - 1) ω) ^ 2) ω) ∂μ ≤ 2 * M * B := by
    have hAB : MeasureTheory.Integrable (fun ω => (E K).indicator (fun ω => (u K ω) ^ 2) ω
        - (E 1).indicator (fun ω => (u 0 ω) ^ 2) ω) μ := hK2_int.sub h0_int
    have hC : MeasureTheory.Integrable (fun ω => ∑ k ∈ Finset.Icc 1 (K - 1),
        (E k \ E (k + 1)).indicator (fun ω => (u k ω) ^ 2) ω) μ := hexit_sum_int
    have hdec : ∫ ω, ((E K).indicator (fun ω => (u K ω) ^ 2) ω
          - (E 1).indicator (fun ω => (u 0 ω) ^ 2) ω
          + ∑ k ∈ Finset.Icc 1 (K - 1), (E k \ E (k + 1)).indicator (fun ω => (u k ω) ^ 2) ω) ∂μ
        = (∫ ω, ((E K).indicator (fun ω => (u K ω) ^ 2) ω
            - (E 1).indicator (fun ω => (u 0 ω) ^ 2) ω) ∂μ)
          + (∫ ω, ∑ k ∈ Finset.Icc 1 (K - 1),
              (E k \ E (k + 1)).indicator (fun ω => (u k ω) ^ 2) ω ∂μ) :=
      integral_add hAB hC
    have hdec2 : ∫ ω, ((E K).indicator (fun ω => (u K ω) ^ 2) ω
          - (E 1).indicator (fun ω => (u 0 ω) ^ 2) ω) ∂μ
        = (∫ ω, (E K).indicator (fun ω => (u K ω) ^ 2) ω ∂μ)
          - (∫ ω, (E 1).indicator (fun ω => (u 0 ω) ^ 2) ω ∂μ) :=
      integral_sub hK2_int h0_int
    rw [hAbel_fun, hdec, hdec2]
    linarith [hAK, hA0, hAC]
  -- vanishing of the cross term against the predictable event
  have hvanish : ∀ k, ∫ ω, (E (k - 1)).indicator
      (fun ω => u (k - 1) ω * (u k ω - u (k - 1) ω)) ω ∂μ = 0 := by
    intro k
    haveI := h𝓖fin (k - 1)
    set Z : Ω → ℝ := (E (k - 1)).indicator (fun ω => u (k - 1) ω) with hZdef
    have hZmeas : AEStronglyMeasurable[𝓖 (k - 1)] Z μ := by
      obtain ⟨g, hg, hge⟩ := humeas (k - 1)
      refine ⟨(E (k - 1)).indicator g, hg.indicator (hEmeas (k - 1)), ?_⟩
      filter_upwards [hge] with ω hω
      rw [hZdef]
      by_cases h : ω ∈ E (k - 1)
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, hω]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
    have hZint : MeasureTheory.Integrable Z μ := by
      rw [hZdef]
      refine ((hint (k - 1)).abs).mono' ?_ ?_
      · exact (hint (k - 1)).aestronglyMeasurable.indicator (hEamb (k - 1))
      · filter_upwards with ω
        by_cases h : ω ∈ E (k - 1)
        · rw [Set.indicator_of_mem h, Real.norm_eq_abs]
        · rw [Set.indicator_of_notMem h, Real.norm_eq_abs, abs_zero]
          exact abs_nonneg _
    have hZk : MeasureTheory.Integrable (fun ω => Z ω * u k ω) μ := by
      have hg : MeasureTheory.Integrable (fun ω => M * |u k ω|) μ := ((hint k).abs).const_mul M
      refine hg.mono' ((hZmeas.mono (h𝓖le (k - 1))).mul (hint k).aestronglyMeasurable) ?_
      filter_upwards with ω
      have hb : |Z ω| ≤ M := by
        rw [hZdef]
        by_cases h : ω ∈ E (k - 1)
        · rw [Set.indicator_of_mem h]
          exact hEband (k - 1) ω h
        · rw [Set.indicator_of_notMem h, abs_zero]
          exact hM.le
      rw [Real.norm_eq_abs, abs_mul]
      nlinarith [hb, abs_nonneg (u k ω), abs_nonneg (Z ω)]
    have hZkm : MeasureTheory.Integrable (fun ω => Z ω * u (k - 1) ω) μ := by
      have hg : MeasureTheory.Integrable (fun ω => M * |u (k - 1) ω|) μ :=
        ((hint (k - 1)).abs).const_mul M
      refine hg.mono' ((hZmeas.mono (h𝓖le (k - 1))).mul (hint (k - 1)).aestronglyMeasurable) ?_
      filter_upwards with ω
      have hb : |Z ω| ≤ M := by
        rw [hZdef]
        by_cases h : ω ∈ E (k - 1)
        · rw [Set.indicator_of_mem h]
          exact hEband (k - 1) ω h
        · rw [Set.indicator_of_notMem h, abs_zero]
          exact hM.le
      rw [Real.norm_eq_abs, abs_mul]
      nlinarith [hb, abs_nonneg (u (k - 1) ω), abs_nonneg (Z ω)]
    have heq : (fun ω => (E (k - 1)).indicator
          (fun ω => u (k - 1) ω * (u k ω - u (k - 1) ω)) ω)
        = fun ω => Z ω * (u k ω - u (k - 1) ω) := by
      funext ω
      by_cases h : ω ∈ E (k - 1)
      · rw [Set.indicator_of_mem h, hZdef, Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h, hZdef, Set.indicator_of_notMem h, zero_mul]
    have hEqZ : ∀ ω, Z ω * (u k ω - u (k - 1) ω) = Z ω * u k ω - Z ω * u (k - 1) ω :=
      fun ω => by ring
    rw [heq, integral_congr_ae (Filter.Eventually.of_forall hEqZ), integral_sub hZk hZkm]
    have h1 : ∫ ω, Z ω * u k ω ∂μ = ∫ ω, Z ω * μ[u k | 𝓖 (k - 1)] ω ∂μ := by
      calc ∫ ω, Z ω * u k ω ∂μ = ∫ ω, μ[fun ω => Z ω * u k ω | 𝓖 (k - 1)] ω ∂μ :=
            (integral_condExp (h𝓖le (k - 1))).symm
        _ = ∫ ω, Z ω * μ[u k | 𝓖 (k - 1)] ω ∂μ := by
            refine integral_congr_ae ?_
            exact condExp_mul_of_aestronglyMeasurable_left hZmeas hZk (hint k)
    have h2 : ∫ ω, Z ω * μ[u k | 𝓖 (k - 1)] ω ∂μ = ∫ ω, Z ω * u (k - 1) ω ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [hmart (show k - 1 ≤ k by omega)] with ω hω
      rw [hω]
    rw [h1, h2, sub_self]
  -- the cross term on `E k` equals minus the one on the exit set
  have hper : ∀ k ∈ Finset.Icc 1 K, ∫ ω, (E k).indicator
        (fun ω => u (k - 1) ω * (u k ω - u (k - 1) ω)) ω ∂μ
      = -(∫ ω, (E (k - 1) \ E k).indicator
          (fun ω => u (k - 1) ω * (u k ω - u (k - 1) ω)) ω ∂μ) := by
    intro k hk
    have hsplit : ∀ ω, (E k).indicator (fun ω => u (k - 1) ω * (u k ω - u (k - 1) ω)) ω
        = (E (k - 1)).indicator (fun ω => u (k - 1) ω * (u k ω - u (k - 1) ω)) ω
          - (E (k - 1) \ E k).indicator
              (fun ω => u (k - 1) ω * (u k ω - u (k - 1) ω)) ω := by
      intro ω
      have hsub : E k ⊆ E (k - 1) := hEmono (by omega : k - 1 ≤ k)
      by_cases h1 : ω ∈ E k
      · have h2 : ω ∈ E (k - 1) := hsub h1
        have h3 : ω ∉ E (k - 1) \ E k := fun hc => hc.2 h1
        rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2, Set.indicator_of_notMem h3]
        ring
      · rw [Set.indicator_of_notMem h1]
        by_cases h2 : ω ∈ E (k - 1)
        · have h3 : ω ∈ E (k - 1) \ E k := ⟨h2, h1⟩
          rw [Set.indicator_of_mem h2, Set.indicator_of_mem h3]
          ring
        · have h3 : ω ∉ E (k - 1) \ E k := fun hc => h2 hc.1
          rw [Set.indicator_of_notMem h2, Set.indicator_of_notMem h3]
          ring
    have hI2 : MeasureTheory.Integrable ((E (k - 1)).indicator
        (fun ω => u (k - 1) ω * (u k ω - u (k - 1) ω))) μ := by
      have hg : MeasureTheory.Integrable (fun ω => M * (|u k ω| + |u (k - 1) ω|)) μ :=
        (((hint k).abs).add ((hint (k - 1)).abs)).const_mul M
      refine hg.mono' (((hint (k - 1)).aestronglyMeasurable.mul
        ((hint k).aestronglyMeasurable.sub (hint (k - 1)).aestronglyMeasurable)).indicator
          (hEamb (k - 1))) ?_
      filter_upwards with ω
      by_cases h : ω ∈ E (k - 1)
      · rw [Set.indicator_of_mem h, Real.norm_eq_abs, abs_mul]
        have hb : |u (k - 1) ω| ≤ M := hEband (k - 1) ω h
        calc |u (k - 1) ω| * |u k ω - u (k - 1) ω|
            ≤ |u (k - 1) ω| * (|u k ω| + |u (k - 1) ω|) :=
              mul_le_mul_of_nonneg_left (abs_sub_le_abs_add _ _) (abs_nonneg _)
          _ ≤ M * (|u k ω| + |u (k - 1) ω|) := mul_le_mul_of_nonneg_right hb (by positivity)
      · rw [Set.indicator_of_notMem h, Real.norm_eq_abs, abs_zero]
        nlinarith [abs_nonneg (u k ω), abs_nonneg (u (k - 1) ω), hM]
    have hI3 : MeasureTheory.Integrable ((E (k - 1) \ E k).indicator
        (fun ω => u (k - 1) ω * (u k ω - u (k - 1) ω))) μ := by
      have hms : MeasurableSet (E (k - 1) \ E k) := (hEamb (k - 1)).diff (hEamb k)
      have hg : MeasureTheory.Integrable (fun ω => M * (|u k ω| + |u (k - 1) ω|)) μ :=
        (((hint k).abs).add ((hint (k - 1)).abs)).const_mul M
      refine hg.mono' (((hint (k - 1)).aestronglyMeasurable.mul
        ((hint k).aestronglyMeasurable.sub (hint (k - 1)).aestronglyMeasurable)).indicator hms) ?_
      filter_upwards with ω
      by_cases h : ω ∈ E (k - 1) \ E k
      · rw [Set.indicator_of_mem h, Real.norm_eq_abs, abs_mul]
        have hb : |u (k - 1) ω| ≤ M := hEband (k - 1) ω h.1
        calc |u (k - 1) ω| * |u k ω - u (k - 1) ω|
            ≤ |u (k - 1) ω| * (|u k ω| + |u (k - 1) ω|) :=
              mul_le_mul_of_nonneg_left (abs_sub_le_abs_add _ _) (abs_nonneg _)
          _ ≤ M * (|u k ω| + |u (k - 1) ω|) := mul_le_mul_of_nonneg_right hb (by positivity)
      · rw [Set.indicator_of_notMem h, Real.norm_eq_abs, abs_zero]
        nlinarith [abs_nonneg (u k ω), abs_nonneg (u (k - 1) ω), hM]
    rw [integral_congr_ae (Filter.Eventually.of_forall hsplit), integral_sub hI2 hI3,
      hvanish k, zero_sub]
  -- the lower bound for the cross term
  have hBc : -(2 * M * B) ≤ ∫ ω, (∑ k ∈ Finset.Icc 1 K,
        (E k).indicator (fun ω => u (k - 1) ω * (u k ω - u (k - 1) ω)) ω) ∂μ := by
    rw [integral_finsetSum _ (fun k hk => hcr_int k)]
    have hsum : ∑ k ∈ Finset.Icc 1 K, ∫ ω, (E k).indicator
          (fun ω => u (k - 1) ω * (u k ω - u (k - 1) ω)) ω ∂μ
        = - ∑ k ∈ Finset.Icc 1 K, ∫ ω, (E (k - 1) \ E k).indicator
            (fun ω => u (k - 1) ω * (u k ω - u (k - 1) ω)) ω ∂μ := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun k hk => hper k hk
    rw [hsum, neg_le, neg_neg]
    have habs : ∀ k ∈ Finset.Icc 1 K, ∫ ω, (E (k - 1) \ E k).indicator
          (fun ω => u (k - 1) ω * (u k ω - u (k - 1) ω)) ω ∂μ
        ≤ M * (∫ ω in (E (k - 1) \ E k), |u k ω| ∂μ)
          + M * (∫ ω in (E (k - 1) \ E k), |u (k - 1) ω| ∂μ) := by
      intro k hk
      set s : Set Ω := E (k - 1) \ E k with hsdef
      have hms : MeasurableSet s := (hEamb (k - 1)).diff (hEamb k)
      have hI : MeasureTheory.IntegrableOn
          (fun ω => u (k - 1) ω * (u k ω - u (k - 1) ω)) s μ := by
        rw [← integrable_indicator_iff hms]
        have hg : MeasureTheory.Integrable (fun ω => M * (|u k ω| + |u (k - 1) ω|)) μ :=
          (((hint k).abs).add ((hint (k - 1)).abs)).const_mul M
        refine hg.mono' (((hint (k - 1)).aestronglyMeasurable.mul
          ((hint k).aestronglyMeasurable.sub (hint (k - 1)).aestronglyMeasurable)).indicator hms) ?_
        filter_upwards with ω
        by_cases h : ω ∈ s
        · rw [Set.indicator_of_mem h, Real.norm_eq_abs, abs_mul]
          have hb : |u (k - 1) ω| ≤ M := hEband (k - 1) ω h.1
          calc |u (k - 1) ω| * |u k ω - u (k - 1) ω|
              ≤ |u (k - 1) ω| * (|u k ω| + |u (k - 1) ω|) :=
                mul_le_mul_of_nonneg_left (abs_sub_le_abs_add _ _) (abs_nonneg _)
            _ ≤ M * (|u k ω| + |u (k - 1) ω|) := mul_le_mul_of_nonneg_right hb (by positivity)
        · rw [Set.indicator_of_notMem h, Real.norm_eq_abs, abs_zero]
          nlinarith [abs_nonneg (u k ω), abs_nonneg (u (k - 1) ω), hM]
      have hstep1 : ∫ ω in s, u (k - 1) ω * (u k ω - u (k - 1) ω) ∂μ
          ≤ ∫ ω in s, |u (k - 1) ω * (u k ω - u (k - 1) ω)| ∂μ :=
        setIntegral_mono_on hI hI.abs hms fun ω _ => le_abs_self _
      have hstep2 : ∫ ω in s, |u (k - 1) ω * (u k ω - u (k - 1) ω)| ∂μ
          ≤ ∫ ω in s, M * (|u k ω| + |u (k - 1) ω|) ∂μ := by
        refine setIntegral_mono_on hI.abs
          ((((hint k).abs).add ((hint (k - 1)).abs)).const_mul M).integrableOn hms fun ω hω => ?_
        rw [abs_mul]
        have hb : |u (k - 1) ω| ≤ M := hEband (k - 1) ω hω.1
        calc |u (k - 1) ω| * |u k ω - u (k - 1) ω|
            ≤ |u (k - 1) ω| * (|u k ω| + |u (k - 1) ω|) :=
              mul_le_mul_of_nonneg_left (abs_sub_le_abs_add _ _) (abs_nonneg _)
          _ ≤ M * (|u k ω| + |u (k - 1) ω|) := mul_le_mul_of_nonneg_right hb (by positivity)
      have hstep3 : ∫ ω in s, M * (|u k ω| + |u (k - 1) ω|) ∂μ
          = M * (∫ ω in s, |u k ω| ∂μ) + M * (∫ ω in s, |u (k - 1) ω| ∂μ) := by
        have hmid : ∫ ω in s, M * (|u k ω| + |u (k - 1) ω|) ∂μ
            = ∫ ω in s, (M * |u k ω| + M * |u (k - 1) ω|) ∂μ := by
          refine setIntegral_congr_ae hms (Filter.Eventually.of_forall fun ω _ => ?_)
          ring
        rw [hmid, integral_add (((hint k).abs.const_mul M).integrableOn)
          (((hint (k - 1)).abs.const_mul M).integrableOn), integral_const_mul, integral_const_mul]
      rw [integral_indicator hms]
      calc ∫ ω in s, u (k - 1) ω * (u k ω - u (k - 1) ω) ∂μ
          ≤ ∫ ω in s, |u (k - 1) ω * (u k ω - u (k - 1) ω)| ∂μ := hstep1
        _ ≤ ∫ ω in s, M * (|u k ω| + |u (k - 1) ω|) ∂μ := hstep2
        _ = M * (∫ ω in s, |u k ω| ∂μ) + M * (∫ ω in s, |u (k - 1) ω| ∂μ) := hstep3
    have hexit2' : ∀ k ∈ Finset.Icc 1 K, ∫ ω in (E (k - 1) \ E k), |u (k - 1) ω| ∂μ
        ≤ M * ((μ (E (k - 1) \ E k)).toReal) := by
      intro k hk
      have hms : MeasurableSet (E (k - 1) \ E k) := (hEamb (k - 1)).diff (hEamb k)
      have h1 : ∫ ω in (E (k - 1) \ E k), |u (k - 1) ω| ∂μ
          ≤ ∫ ω in (E (k - 1) \ E k), M ∂μ :=
        setIntegral_mono_on ((hint (k - 1)).abs.integrableOn)
          (integrableOn_const (hexit_fin k (k - 1) (by omega)) (by finiteness)) hms
          fun ω hω => hEband (k - 1) ω hω.1
      refine le_trans h1 (le_of_eq ?_)
      rw [setIntegral_const, smul_eq_mul, Measure.real]
      ring
    calc ∑ k ∈ Finset.Icc 1 K, ∫ ω, (E (k - 1) \ E k).indicator
            (fun ω => u (k - 1) ω * (u k ω - u (k - 1) ω)) ω ∂μ
        ≤ ∑ k ∈ Finset.Icc 1 K, (M * (∫ ω in (E (k - 1) \ E k), |u k ω| ∂μ)
            + M * (∫ ω in (E (k - 1) \ E k), |u (k - 1) ω| ∂μ)) :=
          Finset.sum_le_sum habs
      _ = M * (∑ k ∈ Finset.Icc 1 K, ∫ ω in (E (k - 1) \ E k), |u k ω| ∂μ)
            + M * (∑ k ∈ Finset.Icc 1 K, ∫ ω in (E (k - 1) \ E k), |u (k - 1) ω| ∂μ) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ M * B + M * B := by
          refine add_le_add (mul_le_mul_of_nonneg_left hexit_abs hM.le) ?_
          refine mul_le_mul_of_nonneg_left ?_ hM.le
          calc ∑ k ∈ Finset.Icc 1 K, ∫ ω in (E (k - 1) \ E k), |u (k - 1) ω| ∂μ
              ≤ ∑ k ∈ Finset.Icc 1 K, M * ((μ (E (k - 1) \ E k)).toReal) :=
                Finset.sum_le_sum hexit2'
            _ = M * (∑ k ∈ Finset.Icc 1 K, (μ (E (k - 1) \ E k)).toReal) := by
                rw [Finset.mul_sum]
            _ ≤ M * (B / M) := mul_le_mul_of_nonneg_left hexit2 hM.le
            _ = B := by field_simp
      _ = 2 * M * B := by ring
  linarith [hE1, hA, hBc, mul_nonneg hM.le hB]




/-- Set-integral bound for a conditional expectation. -/
private lemma setIntegral_abs_condExp_le' {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} {m : MeasurableSpace Ω} {f : Ω → ℝ} {S : Set Ω}
    (hS : MeasurableSet[m] S) :
    ∫ ω in S, |μ[f | m] ω| ∂μ ≤ ∫ ω in S, |f ω| ∂μ := by
  have h := setIntegral_norm_condExp_le (μ := μ) (m := m) (E := ℝ) hS f
  simpa only [Real.norm_eq_abs] using h

/-- Set-integral bound for the anchor process against the horizon value `H N`. -/
private lemma greedyAnchor_setIntegral_le_HN {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.SigmaFinite μ]
    {ℱ : MeasureTheory.Filtration ℕ ‹MeasurableSpace Ω›} [MeasureTheory.SigmaFiniteFiltration μ ℱ]
    {H : ℕ → Ω → ℝ} (hH : MeasureTheory.Martingale H ℱ μ) (δ : ℝ) (N j : ℕ) {S : Set Ω}
    (hS : MeasurableSet[(isStoppingTime_greedyStop hH.stronglyAdapted δ N j).measurableSpace] S) :
    ∫ ω in S, |greedyAnchor H δ N j ω| ∂μ ≤ ∫ ω in S, |H N ω| ∂μ := by
  haveI hfin : MeasureTheory.SigmaFinite (μ.trim
      (isStoppingTime_greedyStop hH.stronglyAdapted δ N j).measurableSpace_le) :=
    MeasureTheory.IsStoppingTime.sigmaFinite_stopping_time
      (isStoppingTime_greedyStop hH.stronglyAdapted δ N j)
  have h1 : ∫ ω in S, |greedyAnchor H δ N j ω| ∂μ
      = ∫ ω in S,
        |μ[H N | (isStoppingTime_greedyStop hH.stronglyAdapted δ N j).measurableSpace] ω| ∂μ := by
    refine MeasureTheory.setIntegral_congr_ae
      ((isStoppingTime_greedyStop hH.stronglyAdapted δ N j).measurableSpace_le S hS) ?_
    filter_upwards [greedyAnchor_condExp hH δ N j] with ω hω _
    rw [hω]
  rw [h1]
  exact setIntegral_abs_condExp_le' hS

/-- On the event that the greedy chain survives `K` jumps within the horizon `N` and the path
stays below the level `M`, every block `k ≤ K` lies in the good set and the `k`-th increment
exceeds `δ`. -/
private lemma greedyAnchor_mem_and_jump {Ω : Type*} [MeasurableSpace Ω] {H : ℕ → Ω → ℝ}
    {δ M : ℝ} (hδ : 0 < δ) {N K k : ℕ} {ω : Ω}
    (hk : k ∈ Finset.Icc 1 K) (hA : ∀ n, |H n ω| ≤ M)
    (hτ : greedyTimeProc H δ K ω < (N : ℕ∞)) :
    (∀ j ≤ k, |greedyAnchor H δ N j ω| ≤ M) ∧
      δ ^ 2 < (greedyAnchor H δ N k ω - greedyAnchor H δ N (k - 1) ω) ^ 2 := by
  classical
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hkK : k ≤ K := (Finset.mem_Icc.mp hk).2
  have hτN : greedyTime (fun n => H n ω) δ K < (N : ℕ∞) := hτ
  have hτK : greedyTime (fun n => H n ω) δ K < ⊤ := lt_of_lt_of_le hτN le_top
  have hmin : ∀ j : ℕ, j ≤ K →
      min (greedyTimeProc H δ j ω) (N : ℕ∞) = greedyTimeProc H δ j ω := by
    intro j hj
    refine min_eq_left ?_
    rw [show greedyTimeProc H δ j ω = greedyTime (fun n => H n ω) δ j from rfl]
    exact le_of_lt (lt_of_le_of_lt (greedyTime_mono (fun n => H n ω) δ hj) hτN)
  have hanchor : ∀ j : ℕ, j ≤ K → greedyAnchor H δ N j ω
      = H (greedyTimeProc H δ j ω).toNat ω := by
    intro j hj
    rw [show greedyAnchor H δ N j ω = H (greedyStop H δ N j ω).untopA ω from rfl]
    rw [show greedyStop H δ N j ω = min (greedyTimeProc H δ j ω) (N : ℕ∞) from rfl, hmin j hj]
    refine congrArg (fun a => H a ω) (untopA_eq_toNat_of_lt_top ?_)
    rw [show greedyTimeProc H δ j ω = greedyTime (fun n => H n ω) δ j from rfl]
    exact lt_of_le_of_lt (greedyTime_mono (fun n => H n ω) δ hj) hτK
  constructor
  · intro j hj
    rw [hanchor j (le_trans hj hkK)]
    exact hA _
  · have hpred : k - 1 + 1 = k := Nat.succ_pred_eq_of_pos hk1
    have hstep := greedyTime_succ_jump (fun n => H n ω) δ (k - 1) (by
      rw [hpred]
      exact lt_of_le_of_lt (greedyTime_mono (fun n => H n ω) δ hkK) hτK)
    rw [hpred] at hstep
    rw [hanchor k hkK, hanchor (k - 1) (by omega)]
    have hsq : δ ^ 2 < |H (greedyTimeProc H δ k ω).toNat ω
        - H (greedyTimeProc H δ (k-1) ω).toNat ω| ^ 2 := by
      have h1 : δ < |H (greedyTimeProc H δ k ω).toNat ω
          - H (greedyTimeProc H δ (k-1) ω).toNat ω| := hstep
      have h3 : 0 < |H (greedyTimeProc H δ k ω).toNat ω
          - H (greedyTimeProc H δ (k-1) ω).toNat ω| - δ := sub_pos.mpr h1
      have h4 : 0 < |H (greedyTimeProc H δ k ω).toNat ω
          - H (greedyTimeProc H δ (k-1) ω).toNat ω| + δ := by positivity
      have h5 : 0 < (|H (greedyTimeProc H δ k ω).toNat ω
          - H (greedyTimeProc H δ (k-1) ω).toNat ω| - δ)
            * (|H (greedyTimeProc H δ k ω).toNat ω
          - H (greedyTimeProc H δ (k-1) ω).toNat ω| + δ) := mul_pos h3 h4
      nlinarith [h5]
    rwa [sq_abs] at hsq


private lemma sum_Icc_sub_shift_eq (f : ℕ → ℝ) (K : ℕ) :
    ∑ k ∈ Finset.Icc 1 K, (f (k - 1) - f k) = f 0 - f K := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1),
        Nat.add_sub_cancel]
      rw [ih]
      ring

private lemma integrable_finset_sum' {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} {ι : Type*} [DecidableEq ι] (s : Finset ι) {f : ι → Ω → ℝ}
    (h : ∀ i ∈ s, MeasureTheory.Integrable (f i) μ) :
    MeasureTheory.Integrable (fun ω => ∑ i ∈ s, f i ω) μ := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (MeasureTheory.integrable_zero Ω ℝ μ)
  | insert a s ha ih =>
      have h1 : MeasureTheory.Integrable (fun ω => f a ω) μ := h a (Finset.mem_insert_self a s)
      have h2 : MeasureTheory.Integrable (fun ω => ∑ i ∈ s, f i ω) μ :=
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      have hfun : (fun ω => ∑ i ∈ insert a s, f i ω)
          = (fun ω => f a ω) + (fun ω => ∑ i ∈ s, f i ω) := by
        funext ω; simp [Finset.sum_insert ha, Pi.add_apply]
      rw [hfun]
      exact h1.add h2

private lemma aestronglyMeasurable_finset_sum {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} {ι : Type*} [DecidableEq ι] (s : Finset ι) {f : ι → Ω → ℝ}
    (h : ∀ i ∈ s, AEStronglyMeasurable (f i) μ) :
    AEStronglyMeasurable (fun ω => ∑ i ∈ s, f i ω) μ := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (aestronglyMeasurable_const (μ := μ) (m := ‹MeasurableSpace Ω›) (b := (0:ℝ)))
  | insert a s ha ih =>
      have h1 : AEStronglyMeasurable (fun ω => f a ω) μ := h a (Finset.mem_insert_self a s)
      have h2 : AEStronglyMeasurable (fun ω => ∑ i ∈ s, f i ω) μ :=
        ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      have hfun : (fun ω => ∑ i ∈ insert a s, f i ω)
          = (fun ω => f a ω) + (fun ω => ∑ i ∈ s, f i ω) := by
        funext ω; simp [Finset.sum_insert ha, Pi.add_apply]
      rw [hfun]
      exact h1.add h2

/-- Markov/energy step: on a set `S` where the `K` sampled increments are all at least `δ²` and
which lies in every good set `E k`, the measure of `S` is controlled by the energy integral. -/
private lemma greedy_markov_step {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    {u : ℕ → Ω → ℝ} {E : ℕ → Set Ω} {K : ℕ} {δ : ℝ} {S : Set Ω} (hS : MeasurableSet S)
    (hSE : ∀ ω ∈ S, ∀ k ∈ Finset.Icc 1 K, ω ∈ E k)
    (hjump : ∀ ω ∈ S, ∀ k ∈ Finset.Icc 1 K, δ ^ 2 ≤ (u k ω - u (k - 1) ω) ^ 2) :
    ENNReal.ofReal ((K : ℝ) * δ ^ 2) * μ S
      ≤ ∫⁻ ω, ENNReal.ofReal (∑ k ∈ Finset.Icc 1 K,
          (E k).indicator (fun ω => (u k ω - u (k - 1) ω) ^ 2) ω) ∂μ := by
  have hcard : ((Finset.Icc 1 K).card : ℝ) = (K : ℝ) := by
    simp
  have hpt : ∀ ω, ENNReal.ofReal ((K : ℝ) * δ ^ 2) * S.indicator (fun _ => (1 : ℝ≥0∞)) ω
      ≤ ENNReal.ofReal (∑ k ∈ Finset.Icc 1 K,
          (E k).indicator (fun ω => (u k ω - u (k - 1) ω) ^ 2) ω) := by
    intro ω
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω, mul_one]
      refine ENNReal.ofReal_le_ofReal ?_
      have h2 : ∑ k ∈ Finset.Icc 1 K,
            (E k).indicator (fun ω => (u k ω - u (k - 1) ω) ^ 2) ω
          = ∑ k ∈ Finset.Icc 1 K, (u k ω - u (k - 1) ω) ^ 2 := by
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [Set.indicator_of_mem (hSE ω hω k hk)]
      have h3 : (K : ℝ) * δ ^ 2 = ∑ k ∈ Finset.Icc 1 K, δ ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
      rw [h3, h2]
      exact Finset.sum_le_sum fun k hk => hjump ω hω k hk
    · rw [Set.indicator_of_notMem hω, mul_zero]
      exact bot_le
  calc ENNReal.ofReal ((K : ℝ) * δ ^ 2) * μ S
      = ∫⁻ ω, ENNReal.ofReal ((K : ℝ) * δ ^ 2) * S.indicator (fun _ => (1 : ℝ≥0∞)) ω ∂μ := by
        have h1 : (fun ω => ENNReal.ofReal ((K : ℝ) * δ ^ 2)
              * S.indicator (fun _ => (1 : ℝ≥0∞)) ω)
            = S.indicator (fun _ => ENNReal.ofReal ((K : ℝ) * δ ^ 2)) := by
          funext ω
          by_cases h : ω ∈ S
          · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, mul_one]
          · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]
        rw [h1, lintegral_indicator hS, MeasureTheory.setLIntegral_const]
    _ ≤ ∫⁻ ω, ENNReal.ofReal (∑ k ∈ Finset.Icc 1 K,
          (E k).indicator (fun ω => (u k ω - u (k - 1) ω) ^ 2) ω) ∂μ := lintegral_mono hpt

/-- Energy bound for the sampled martingale at the horizon `N`. -/
theorem greedy_anchor_energy {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.SigmaFinite μ] {ℱ : MeasureTheory.Filtration ℕ ‹MeasurableSpace Ω›}
    [MeasureTheory.SigmaFiniteFiltration μ ℱ] {H : ℕ → Ω → ℝ}
    (hH : MeasureTheory.Martingale H ℱ μ) {B : ℝ} (hB : ∀ n, ∫ ω, |H n ω| ∂μ ≤ B)
    {M : ℝ} (hM : 0 < M) {δ : ℝ} (hδ : 0 < δ) {K : ℕ} (hK : 1 ≤ K) (N : ℕ) :
    μ ({ω | ∀ n, |H n ω| ≤ M} ∩ {ω | greedyTimeProc H δ K ω < (N : ℕ∞)})
      ≤ ENNReal.ofReal (7 * M * B / (K * δ ^ 2)) := by
  classical
  have hB0 : 0 ≤ B := le_trans (integral_nonneg fun ω => abs_nonneg _) (hB 0)
  let u : ℕ → Ω → ℝ := fun k => greedyAnchor H δ N k
  let 𝓖 : ℕ → MeasurableSpace Ω :=
    fun k => (isStoppingTime_greedyStop hH.stronglyAdapted δ N k).measurableSpace
  let E : ℕ → Set Ω := fun k => {ω | ∀ j ≤ k, |u j ω| ≤ M}
  let S : Set Ω := {ω | ∀ n, |H n ω| ≤ M} ∩ {ω | greedyTimeProc H δ K ω < (N : ℕ∞)}
  change μ S ≤ ENNReal.ofReal (7 * M * B / ((K : ℝ) * δ ^ 2))
  -- (1) basic facts about the sampled martingale
  have hprog : MeasureTheory.IsStronglyProgressive ℱ H :=
    hH.stronglyAdapted.isStronglyProgressive_of_discrete
  have h𝓖le : ∀ k, 𝓖 k ≤ ‹MeasurableSpace Ω› := fun k =>
    (isStoppingTime_greedyStop hH.stronglyAdapted δ N k).measurableSpace_le
  have h𝓖fin : ∀ k, MeasureTheory.SigmaFinite (μ.trim (h𝓖le k)) := fun k =>
    MeasureTheory.IsStoppingTime.sigmaFinite_stopping_time
      (isStoppingTime_greedyStop hH.stronglyAdapted δ N k)
  have h𝓖mono : ∀ {i j : ℕ}, i ≤ j → 𝓖 i ≤ 𝓖 j := by
    intro i j hij
    exact (isStoppingTime_greedyStop hH.stronglyAdapted δ N i).measurableSpace_mono
      (isStoppingTime_greedyStop hH.stronglyAdapted δ N j)
      (fun ω => min_le_min (greedyTime_mono (fun n => H n ω) δ hij) le_rfl)
  have hu_meas : ∀ k, Measurable[𝓖 k] (u k) := by
    intro k
    exact measurable_stoppedValue hprog (isStoppingTime_greedyStop hH.stronglyAdapted δ N k)
  have hu_int : ∀ k, MeasureTheory.Integrable (u k) μ := by
    intro k
    haveI := h𝓖fin k
    exact (MeasureTheory.integrable_condExp (μ := μ) (m := 𝓖 k) (f := H N)).congr
      (greedyAnchor_condExp hH δ N k).symm
  have hu_mart : ∀ {i j : ℕ}, i ≤ j → u i =ᵐ[μ] μ[u j | 𝓖 i] := by
    intro i j hij
    haveI hfi := h𝓖fin i
    haveI hfj := h𝓖fin j
    calc u i =ᵐ[μ] μ[H N | 𝓖 i] := greedyAnchor_condExp hH δ N i
      _ =ᵐ[μ] μ[μ[H N | 𝓖 j] | 𝓖 i] :=
          (MeasureTheory.condExp_condExp_of_le (h𝓖mono hij) (h𝓖le j)).symm
      _ =ᵐ[μ] μ[u j | 𝓖 i] :=
          (MeasureTheory.condExp_congr_ae (greedyAnchor_condExp hH δ N j)).symm
  have hu_measae : ∀ k, AEStronglyMeasurable[𝓖 k] (u k) μ := by
    intro k
    refine (stronglyMeasurable_condExp (μ := μ) (m := 𝓖 k) (f := H N)).aestronglyMeasurable.congr ?_
    exact (greedyAnchor_condExp hH δ N k).symm
  have hu_band : ∀ k, MeasureTheory.Integrable (fun ω => M * |u k ω|) μ :=
    fun k => (hu_int k).abs.const_mul M
  -- (2) set-integral bounds
  have hu_setint : ∀ (i j : ℕ), i ≤ j → ∀ T : Set Ω, MeasurableSet[𝓖 i] T →
      ∫ ω in T, |u j ω| ∂μ ≤ B := by
    intro i j hij T hT
    have hTj : MeasurableSet[𝓖 j] T := h𝓖mono hij T hT
    calc ∫ ω in T, |u j ω| ∂μ ≤ ∫ ω in T, |H N ω| ∂μ :=
          greedyAnchor_setIntegral_le_HN hH δ N j hTj
      _ ≤ ∫ ω, |H N ω| ∂μ :=
          MeasureTheory.setIntegral_le_integral (hH.integrable N).abs
            (Filter.Eventually.of_forall fun ω => abs_nonneg _)
      _ ≤ B := hB N
  -- (3) the good sets
  have hEamb : ∀ k, MeasurableSet (E k) := by
    intro k
    have hset : E k = ⋂ j ∈ Finset.range (k + 1), {ω | |u j ω| ≤ M} := by
      ext ω
      rw [show (ω ∈ E k) = (∀ j ≤ k, |u j ω| ≤ M) from rfl]
      constructor
      · intro h
        refine Set.mem_iInter₂.mpr fun j hj => ?_
        exact h j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
      · intro h j hj
        exact (Set.mem_iInter₂.mp h) j (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))
    rw [hset]
    refine Finset.measurableSet_biInter _ fun j hj => ?_
    have hjle : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hsetj : MeasurableSet[𝓖 j] {ω | |u j ω| ≤ M} := by
      rw [show {ω : Ω | |u j ω| ≤ M} = (fun ω => u j ω) ⁻¹' Set.Icc (-M) M from by
        ext ω; simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Icc, abs_le]]
      exact (hu_meas j) measurableSet_Icc
    exact (h𝓖le j) _ hsetj
  have hEmeas : ∀ k, MeasurableSet[𝓖 k] (E k) := by
    intro k
    have hset : E k = ⋂ j ∈ Finset.range (k + 1), {ω | |u j ω| ≤ M} := by
      ext ω
      rw [show (ω ∈ E k) = (∀ j ≤ k, |u j ω| ≤ M) from rfl]
      constructor
      · intro h
        refine Set.mem_iInter₂.mpr fun j hj => ?_
        exact h j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
      · intro h j hj
        exact (Set.mem_iInter₂.mp h) j (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))
    rw [hset]
    refine Finset.measurableSet_biInter _ fun j hj => ?_
    have hjle : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hsetj : MeasurableSet[𝓖 j] {ω | |u j ω| ≤ M} := by
      rw [show {ω : Ω | |u j ω| ≤ M} = (fun ω => u j ω) ⁻¹' Set.Icc (-M) M from by
        ext ω; simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Icc, abs_le]]
      exact (hu_meas j) measurableSet_Icc
    exact (h𝓖mono hjle) _ hsetj
  have hEmono : ∀ {i j : ℕ}, i ≤ j → E j ⊆ E i := by
    intro i j hij ω hω k hk
    exact hω k (le_trans hk hij)
  have hEband : ∀ k, ∀ ω ∈ E k, |u k ω| ≤ M := fun k ω hω => hω k le_rfl
  -- (4) the exit bounds, via Doob's weak (1,1) inequality for the anchor martingale
  have hu_max : μ {ω | ENNReal.ofReal M < ⨆ n, ‖u n ω‖ₑ} ≤ ENNReal.ofReal (B / M) := by
    let hF : MeasureTheory.Filtration ℕ ‹MeasurableSpace Ω› :=
      ⟨𝓖, fun i j hij => h𝓖mono hij, h𝓖le⟩
    haveI hfin : MeasureTheory.SigmaFiniteFiltration μ hF := ⟨fun n => h𝓖fin n⟩
    have hmart : MeasureTheory.Martingale u hF μ :=
      ⟨fun k => (hu_meas k).stronglyMeasurable, fun i j hij => (hu_mart hij).symm⟩
    refine martingale_max_weak hmart hM ?_
    intro n
    simpa using hu_setint n n le_rfl Set.univ MeasurableSet.univ
  have hmax : μ {ω | ∃ n, M < |u n ω|} ≤ ENNReal.ofReal (B / M) := by
    refine le_trans (measure_mono ?_) hu_max
    intro ω hω
    obtain ⟨n, hn⟩ := hω
    simp only [Set.mem_setOf_eq]
    calc ENNReal.ofReal M < ENNReal.ofReal |u n ω| := by
          rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg hM.le]; exact hn
      _ = ‖u n ω‖ₑ := (Real.enorm_eq_ofReal_abs _).symm
      _ ≤ ⨆ n, ‖u n ω‖ₑ := le_iSup (fun m => ‖u m ω‖ₑ) n
  have hconsec : ∀ l : ℕ, μ (E l \ E (l + 1)) ≤ ENNReal.ofReal (B / M) := by
    intro l
    refine le_trans (measure_mono ?_) hmax
    intro ω hω
    simp only [Set.mem_setOf_eq]
    by_contra hcon
    push_neg at hcon
    exact hω.2 fun j hj => hcon j
  have hexit_fin : ∀ i j : ℕ, j ≤ i → μ (E j \ E i) ≠ ⊤ := by
    intro i j hji
    refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans (measure_mono ?_) hmax)
    intro ω hω
    simp only [Set.mem_setOf_eq]
    by_contra hcon
    push_neg at hcon
    exact hω.2 fun k hk => hcon k
  have hdisj1 : Set.PairwiseDisjoint (↑(Finset.Icc 1 (K - 1)) : Set ℕ)
      (fun j => E j \ E (j + 1)) := by
    intro a ha b hb hab
    refine Set.disjoint_left.mpr fun ω hωa hωb => ?_
    rcases lt_or_gt_of_ne hab with hlt | hlt
    · exact hωa.2 (hEmono (by omega : a + 1 ≤ b) hωb.1)
    · exact hωb.2 (hEmono (by omega : b + 1 ≤ a) hωa.1)
  have hexit1 : ∑ j ∈ Finset.Icc 1 (K - 1), (μ (E j \ E (j + 1))).toReal ≤ B / M := by
    have hsum_eq : ∑ j ∈ Finset.Icc 1 (K - 1), μ (E j \ E (j + 1))
        = μ (⋃ j ∈ Finset.Icc 1 (K - 1), (E j \ E (j + 1))) :=
      (MeasureTheory.measure_biUnion_finset hdisj1 fun j _ => (hEamb j).diff (hEamb (j + 1))).symm
    have hle : μ (⋃ j ∈ Finset.Icc 1 (K - 1), (E j \ E (j + 1))) ≤ ENNReal.ofReal (B / M) := by
      refine le_trans (measure_mono ?_) hmax
      intro ω hω
      obtain ⟨j, hj, hωj⟩ := Set.mem_iUnion₂.mp hω
      change ∃ n, M < |u n ω|
      by_contra hcon
      push_neg at hcon
      exact hωj.2 fun i hi => hcon i
    rw [← ENNReal.toReal_sum (fun j hj => hexit_fin (j + 1) j (by omega)), hsum_eq]
    calc (μ (⋃ j ∈ Finset.Icc 1 (K - 1), (E j \ E (j + 1)))).toReal
        ≤ (ENNReal.ofReal (B / M)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      _ = B / M := ENNReal.toReal_ofReal (div_nonneg hB0 hM.le)
  have hdisj2 : Set.PairwiseDisjoint (↑(Finset.Icc 1 K) : Set ℕ) (fun k => E (k - 1) \ E k) := by
    intro a ha b hb hab
    refine Set.disjoint_left.mpr fun ω hωa hωb => ?_
    rcases lt_or_gt_of_ne hab with hlt | hlt
    · exact hωa.2 (hEmono (by omega : a ≤ b - 1) hωb.1)
    · exact hωb.2 (hEmono (by omega : b ≤ a - 1) hωa.1)
  have hexit2 : ∑ k ∈ Finset.Icc 1 K, (μ (E (k - 1) \ E k)).toReal ≤ B / M := by
    have hsum_eq : ∑ k ∈ Finset.Icc 1 K, μ (E (k - 1) \ E k)
        = μ (⋃ k ∈ Finset.Icc 1 K, (E (k - 1) \ E k)) :=
      (MeasureTheory.measure_biUnion_finset hdisj2 fun k _ => (hEamb (k - 1)).diff (hEamb k)).symm
    have hle : μ (⋃ k ∈ Finset.Icc 1 K, (E (k - 1) \ E k)) ≤ ENNReal.ofReal (B / M) := by
      refine le_trans (measure_mono ?_) hmax
      intro ω hω
      obtain ⟨k, hk, hωk⟩ := Set.mem_iUnion₂.mp hω
      change ∃ n, M < |u n ω|
      by_contra hcon
      push_neg at hcon
      exact hωk.2 fun i hi => hcon i
    rw [← ENNReal.toReal_sum (fun k hk => hexit_fin k (k - 1) (by omega)), hsum_eq]
    calc (μ (⋃ k ∈ Finset.Icc 1 K, (E (k - 1) \ E k))).toReal
        ≤ (ENNReal.ofReal (B / M)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      _ = B / M := ENNReal.toReal_ofReal (div_nonneg hB0 hM.le)
  have hu_int_dom : ∀ k, MeasureTheory.Integrable
      ((E k).indicator (fun ω => (u k ω - u (k - 1) ω) ^ 2)) μ := by
    intro k
    have hdom : MeasureTheory.Integrable (fun ω => 2 * M * (|u k ω| + |u (k - 1) ω|)) μ :=
      (((hu_int k).abs).add ((hu_int (k - 1)).abs)).const_mul (2 * M)
    refine hdom.mono' ?_ ?_
    · have h2 : (fun ω => (u k ω - u (k - 1) ω) ^ 2)
          = fun ω => (u k ω - u (k - 1) ω) * (u k ω - u (k - 1) ω) := by funext ω; ring
      rw [h2]
      exact ((((hu_int k).aestronglyMeasurable).sub
        ((hu_int (k - 1)).aestronglyMeasurable)).mul
        (((hu_int k).aestronglyMeasurable).sub
          ((hu_int (k - 1)).aestronglyMeasurable))).indicator (hEamb k)
    · filter_upwards with ω
      by_cases h : ω ∈ E k
      · rw [Set.indicator_of_mem h, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have h1 : |u (k - 1) ω| ≤ M := hEband (k - 1) ω (hEmono (by omega : k - 1 ≤ k) h)
        have h2 : |u k ω| ≤ M := hEband k ω h
        nlinarith [h1, h2, sq_nonneg (u k ω - u (k - 1) ω),
          sq_nonneg (u k ω + u (k - 1) ω), sq_abs (u k ω), sq_abs (u (k - 1) ω),
          abs_nonneg (u k ω), abs_nonneg (u (k - 1) ω), hM]
      · rw [Set.indicator_of_notMem h, Real.norm_eq_abs, abs_zero]
        positivity
  have hsum_int : MeasureTheory.Integrable (fun ω => ∑ k ∈ Finset.Icc 1 K,
      (E k).indicator (fun ω => (u k ω - u (k - 1) ω) ^ 2) ω) μ :=
    integrable_finset_sum' _ (fun k hk => hu_int_dom k)
  have hnonneg : 0 ≤ᵐ[μ] (fun ω => ∑ k ∈ Finset.Icc 1 K,
      (E k).indicator (fun ω => (u k ω - u (k - 1) ω) ^ 2) ω) :=
    Filter.Eventually.of_forall fun ω => Finset.sum_nonneg fun k hk => by
      by_cases h : ω ∈ E k
      · rw [Set.indicator_of_mem h]; positivity
      · rw [Set.indicator_of_notMem h]
  have hexit_abs : ∑ k ∈ Finset.Icc 1 K, ∫ ω in (E (k - 1) \ E k), |u k ω| ∂μ ≤ B := by
    have h1 : ∀ k ∈ Finset.Icc 1 K, ∫ ω in (E (k - 1) \ E k), |u k ω| ∂μ
        ≤ ∫ ω in (E (k - 1) \ E k), |H N ω| ∂μ := by
      intro k hk
      refine greedyAnchor_setIntegral_le_HN hH δ N k ?_
      exact ((h𝓖mono (by omega : k - 1 ≤ k)) _ (hEmeas (k - 1))).diff (hEmeas k)
    have h2 : ∑ k ∈ Finset.Icc 1 K, ∫ ω in (E (k - 1) \ E k), |H N ω| ∂μ
        = ∫ ω, ∑ k ∈ Finset.Icc 1 K,
            (E (k - 1) \ E k).indicator (fun ω => |H N ω|) ω ∂μ := by
      rw [MeasureTheory.integral_finsetSum]
      · refine Finset.sum_congr rfl fun k hk => ?_
        rw [MeasureTheory.integral_indicator ((hEamb (k - 1)).diff (hEamb k))]
      · intro k hk
        exact ((hH.integrable N).abs).indicator ((hEamb (k - 1)).diff (hEamb k))
    have h3 : ∫ ω, ∑ k ∈ Finset.Icc 1 K,
          (E (k - 1) \ E k).indicator (fun ω => |H N ω|) ω ∂μ ≤ ∫ ω, |H N ω| ∂μ := by
      have hsum_int2 : MeasureTheory.Integrable (fun ω => ∑ k ∈ Finset.Icc 1 K,
          (E (k - 1) \ E k).indicator (fun ω => |H N ω|) ω) μ := by
        have hdom : MeasureTheory.Integrable (fun ω => ∑ k ∈ Finset.Icc 1 K, |H N ω|) μ :=
          integrable_finset_sum' _ (fun k hk => (hH.integrable N).abs)
        refine hdom.mono' (aestronglyMeasurable_finset_sum _
          (fun k hk => ((hH.integrable N).abs.aestronglyMeasurable).indicator
            ((hEamb (k - 1)).diff (hEamb k)))) ?_
        filter_upwards with ω
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun k hk => ?_)
        by_cases h : ω ∈ E (k - 1) \ E k
        · rw [Set.indicator_of_mem h, abs_of_nonneg (abs_nonneg _)]
        · rw [Set.indicator_of_notMem h, abs_zero]
          exact abs_nonneg _
      refine MeasureTheory.integral_mono_ae hsum_int2 (hH.integrable N).abs ?_
      filter_upwards with ω
      have hpt : ∀ k ∈ Finset.Icc 1 K,
          (E (k - 1) \ E k).indicator (fun ω => |H N ω|) ω
            = (E (k - 1) \ E k).indicator (fun _ => (1 : ℝ)) ω * |H N ω| := by
        intro k hk
        by_cases h : ω ∈ E (k - 1) \ E k
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, one_mul]
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]
      rw [Finset.sum_congr rfl hpt, ← Finset.sum_mul]
      have htel : ∑ k ∈ Finset.Icc 1 K, (E (k - 1) \ E k).indicator (fun _ => (1 : ℝ)) ω ≤ 1 := by
        have hid : ∀ k : ℕ, (E (k - 1) \ E k).indicator (fun _ => (1 : ℝ)) ω
            = (fun j => (E j).indicator (fun _ => (1 : ℝ)) ω) (k - 1)
              - (fun j => (E j).indicator (fun _ => (1 : ℝ)) ω) k := by
          intro k
          show (E (k - 1) \ E k).indicator (fun _ => (1 : ℝ)) ω
            = (E (k - 1)).indicator (fun _ => (1 : ℝ)) ω
              - (E k).indicator (fun _ => (1 : ℝ)) ω
          by_cases h : ω ∈ E (k - 1)
          · by_cases h' : ω ∈ E k
            · rw [Set.indicator_of_mem h, Set.indicator_of_mem h',
                Set.indicator_of_notMem (by simp only [Set.mem_diff]; exact fun hc => hc.2 h'),
                sub_self]
            · rw [Set.indicator_of_mem h, Set.indicator_of_notMem h',
                Set.indicator_of_mem (by simp only [Set.mem_diff]; exact ⟨h, h'⟩), sub_zero]
          · have h1 : ω ∉ E k := fun hc => h (hEmono (by omega : k - 1 ≤ k) hc)
            have h2 : ω ∉ E (k - 1) \ E k := fun hc => h hc.1
            rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
            ring
        calc ∑ k ∈ Finset.Icc 1 K, (E (k - 1) \ E k).indicator (fun _ => (1 : ℝ)) ω
            = ∑ k ∈ Finset.Icc 1 K, ((fun j => (E j).indicator (fun _ => (1 : ℝ)) ω) (k - 1)
                - (fun j => (E j).indicator (fun _ => (1 : ℝ)) ω) k) :=
              Finset.sum_congr rfl fun k hk => hid k
          _ = (fun j => (E j).indicator (fun _ => (1 : ℝ)) ω) 0
                - (fun j => (E j).indicator (fun _ => (1 : ℝ)) ω) K :=
              sum_Icc_sub_shift_eq (fun j => (E j).indicator (fun _ => (1 : ℝ)) ω) K
          _ ≤ 1 := by
              have h0 : (fun j => (E j).indicator (fun _ => (1 : ℝ)) ω) 0 ≤ 1 := by
                show (E 0).indicator (fun _ => (1 : ℝ)) ω ≤ 1
                by_cases h : ω ∈ E 0
                · simp [Set.indicator_of_mem h]
                · simp [Set.indicator_of_notMem h]
              have hK0 : 0 ≤ (fun j => (E j).indicator (fun _ => (1 : ℝ)) ω) K := by
                show 0 ≤ (E K).indicator (fun _ => (1 : ℝ)) ω
                by_cases h : ω ∈ E K
                · simp [Set.indicator_of_mem h]
                · simp [Set.indicator_of_notMem h]
              linarith
      calc (∑ k ∈ Finset.Icc 1 K, (E (k - 1) \ E k).indicator (fun _ => (1 : ℝ)) ω)
            * |H N ω| ≤ 1 * |H N ω| := mul_le_mul_of_nonneg_right htel (abs_nonneg _)
        _ = |H N ω| := one_mul _
    calc ∑ k ∈ Finset.Icc 1 K, ∫ ω in (E (k - 1) \ E k), |u k ω| ∂μ
        ≤ ∑ k ∈ Finset.Icc 1 K, ∫ ω in (E (k - 1) \ E k), |H N ω| ∂μ := Finset.sum_le_sum h1
      _ = ∫ ω, ∑ k ∈ Finset.Icc 1 K, (E (k - 1) \ E k).indicator (fun ω => |H N ω|) ω ∂μ := h2
      _ ≤ ∫ ω, |H N ω| ∂μ := h3
      _ ≤ B := hB N
  -- (5) the energy bound
  have henergy : ∫ ω, (∑ k ∈ Finset.Icc 1 K,
        (E k).indicator (fun ω => (u k ω - u (k - 1) ω) ^ 2) ω) ∂μ ≤ 7 * M * B :=
    energy_bound_core (u := u) (𝓖 := 𝓖) (E := E)
      h𝓖le h𝓖mono hu_mart hu_int h𝓖fin hu_measae hM hB0
      hEmeas hEmono hEband hu_setint hK hexit1 hexit2 hexit_abs hexit_fin
  -- (6) the level set
  have hSmeas : MeasurableSet S := by
    refine MeasurableSet.inter ?_ ?_
    · have hseteq : {ω : Ω | ∀ n, |H n ω| ≤ M} = ⋂ n, {ω | |H n ω| ≤ M} := by
        ext ω
        rw [Set.mem_iInter]
        simp only [Set.mem_ofPred_eq]
      rw [hseteq]
      refine MeasurableSet.iInter (f := fun n => {ω | |H n ω| ≤ M}) fun n => ?_
      have hsetn : MeasurableSet[ℱ n] {ω | |H n ω| ≤ M} := by
        rw [show {ω : Ω | |H n ω| ≤ M} = (fun ω => H n ω) ⁻¹' Set.Icc (-M) M from by
          ext ω; simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Icc, abs_le]]
        exact (hH.stronglyAdapted n).measurable measurableSet_Icc
      exact (ℱ.le n) _ hsetn
    · exact (ℱ.le N) _ ((isStoppingTime_greedyTimeProc hH.stronglyAdapted δ K).measurableSet_lt N)
  have hSE : ∀ ω ∈ S, ∀ k ∈ Finset.Icc 1 K, ω ∈ E k := by
    intro ω hω k hk j hj
    have h := hω.1 ((greedyStop H δ N j ω).untopA)
    exact h
  have hjump : ∀ ω ∈ S, ∀ k ∈ Finset.Icc 1 K, δ ^ 2 ≤ (u k ω - u (k - 1) ω) ^ 2 := by
    intro ω hω k hk
    exact le_of_lt (greedyAnchor_mem_and_jump hδ hk hω.1 hω.2).2
  have hmarkov := greedy_markov_step (μ := μ) (u := u) (E := E) (K := K) (δ := δ) (S := S)
    hSmeas hSE hjump
  have hbridge : ∫⁻ ω, ENNReal.ofReal (∑ k ∈ Finset.Icc 1 K,
        (E k).indicator (fun ω => (u k ω - u (k - 1) ω) ^ 2) ω) ∂μ
      ≤ ENNReal.ofReal (7 * M * B) := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hsum_int hnonneg]
    exact ENNReal.ofReal_le_ofReal henergy
  have h1 : ENNReal.ofReal ((K : ℝ) * δ ^ 2) * μ S ≤ ENNReal.ofReal (7 * M * B) :=
    le_trans hmarkov hbridge
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hKδ : 0 < (K : ℝ) * δ ^ 2 := by positivity
  have hne0 : ENNReal.ofReal ((K : ℝ) * δ ^ 2) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le.mpr hKδ
  have hnetop : ENNReal.ofReal ((K : ℝ) * δ ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hle : μ S ≤ ENNReal.ofReal (7 * M * B) / ENNReal.ofReal ((K : ℝ) * δ ^ 2) :=
    (ENNReal.le_div_iff_mul_le (Or.inl hne0) (Or.inl hnetop)).mpr (by
      rw [mul_comm]; exact h1)
  calc μ S ≤ ENNReal.ofReal (7 * M * B) / ENNReal.ofReal ((K : ℝ) * δ ^ 2) := hle
    _ = ENNReal.ofReal (7 * M * B / ((K : ℝ) * δ ^ 2)) := by
        rw [← ENNReal.ofReal_div_of_pos hKδ]

theorem greedy_count_weak_one :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
      [MeasureTheory.SigmaFinite μ] (ℱ : MeasureTheory.Filtration ℕ ‹MeasurableSpace Ω›)
      [MeasureTheory.SigmaFiniteFiltration μ ℱ] (H : ℕ → Ω → ℝ)
      (hH : MeasureTheory.Martingale H ℱ μ) (B : ℝ) (hB : ∀ n, ∫ ω, |H n ω| ∂μ ≤ B),
      ∀ δ : ℝ, 0 < δ → ∀ y : ℝ, 0 < y →
        μ {ω | ENNReal.ofReal y < Work.Analysis.Probability.greedyJumps (fun n => H n ω) δ}
          ≤ ENNReal.ofReal (C * B / (δ * Real.sqrt y)) := by
  classical
  refine ⟨26, by norm_num, ?_⟩
  intro Ω _ μ _ ℱ _ H hH B hB δ hδ y hy
  by_cases hB0 : B ≤ 0
  · -- the degenerate case: all values vanish a.e.
    have hzero : ∀ n, H n =ᵐ[μ] 0 := by
      intro n
      have h1 : ∫ ω, |H n ω| ∂μ ≤ 0 := le_trans (hB n) hB0
      have h1' : ∫ ω, |H n ω| ∂μ = 0 :=
        le_antisymm h1 (integral_nonneg fun ω => abs_nonneg _)
      have h2 : (fun ω => |H n ω|) =ᵐ[μ] (fun _ => (0:ℝ)) :=
        (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae
          (Filter.Eventually.of_forall fun ω => abs_nonneg _) (hH.integrable n).abs).mp h1'
      filter_upwards [h2] with ω hω
      simpa using abs_eq_zero.mp hω
    have hU : μ (⋃ n : ℕ, {ω | H n ω ≠ 0}) = 0 :=
      measure_iUnion_null fun n : ℕ => by
        have h1 : ∀ᵐ ω ∂μ, ¬ (H n ω ≠ 0) := by
          filter_upwards [hzero n] with ω hω
          simpa [ne_eq] using hω
        rw [MeasureTheory.ae_iff] at h1
        simpa using h1
    have hnull : μ {ω | ENNReal.ofReal y < greedyJumps (fun n => H n ω) δ} = 0 := by
      refine measure_mono_null ?_ hU
      · intro ω hω
        simp only [Set.mem_iUnion, Set.mem_setOf_eq]
        by_contra hcon
        push_neg at hcon
        have hJ : greedyJumps (fun n => H n ω) δ = 0 :=
          greedyJumps_eq_zero_of_const hδ.le (fun n => by rw [hcon n, hcon 0])
        simp only [Set.mem_setOf_eq] at hω
        rw [hJ] at hω
        exact absurd hω (not_lt.mpr bot_le)

    rw [hnull]
    exact bot_le
  · push_neg at hB0
    set M : ℝ := δ * Real.sqrt y with hMdef
    have hMpos : 0 < M := by
      rw [hMdef]; exact mul_pos hδ (Real.sqrt_pos.mpr hy)
    set K : ℕ := ⌊y⌋₊ + 1 with hKdef
    have hKpos : 1 ≤ K := Nat.succ_le_succ (Nat.zero_le _)
    have hyp : (0:ℝ) < Real.sqrt y := Real.sqrt_pos.mpr hy
    -- Doob
    have hbad : μ {ω | ∃ n, M < |H n ω|} ≤ ENNReal.ofReal (B / M) := by
      refine le_trans (measure_mono ?_) (martingale_max_weak hH hMpos hB)
      intro ω hω
      obtain ⟨n, hn⟩ := hω
      simp only [Set.mem_setOf_eq]
      calc ENNReal.ofReal M < ENNReal.ofReal |H n ω| := by
            rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg hMpos.le]; exact hn
        _ = ‖H n ω‖ₑ := (Real.enorm_eq_ofReal_abs _).symm
        _ ≤ ⨆ n, ‖H n ω‖ₑ := le_iSup (fun n => ‖H n ω‖ₑ) n
    have hAc : μ ({ω | ∀ n, |H n ω| ≤ M})ᶜ ≤ ENNReal.ofReal (B / M) := by
      refine le_trans (measure_mono ?_) hbad
      intro ω hω
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] at hω
      obtain ⟨n, hn⟩ := hω
      exact ⟨n, lt_of_not_ge hn⟩
    -- the energy bound, then the limit in N
    have hlim : μ ({ω | ∀ n, |H n ω| ≤ M}
        ∩ {ω | greedyTime (fun n => H n ω) δ K < ⊤})
        ≤ ENNReal.ofReal (7 * M * B / (K * δ ^ 2)) := by
      have hset : ({ω | ∀ n, |H n ω| ≤ M}
          ∩ {ω | greedyTime (fun n => H n ω) δ K < ⊤})
          = Set.iUnion (fun N : ℕ => ({ω | ∀ n, |H n ω| ≤ M}
              ∩ {ω | greedyTimeProc H δ K ω < (N : ℕ∞)})) := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iUnion]
        constructor
        · rintro ⟨hA, hlt⟩
          cases hval : greedyTime (fun n => H n ω) δ K with
          | top => rw [hval] at hlt; exact absurd hlt (lt_irrefl ⊤)
          | coe m => exact ⟨m + 1, hA, by
              rw [greedyTimeProc, hval]
              exact ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self m)⟩
        · rintro ⟨N, hA, hlt⟩
          exact ⟨hA, lt_of_lt_of_le hlt le_top⟩
      rw [hset]
      have hmono : Monotone (fun N : ℕ => ({ω | ∀ n, |H n ω| ≤ M}
          ∩ {ω | greedyTimeProc H δ K ω < (N : ℕ∞)})) := by
        intro i j hij ω hω
        exact ⟨hω.1, lt_of_lt_of_le hω.2 (by
          show (i : ℕ∞) ≤ (j : ℕ∞)
          exact_mod_cast hij)⟩
      refine le_trans (le_of_eq (Monotone.measure_iUnion hmono)) ?_
      exact iSup_le fun N => greedy_anchor_energy hH hB hMpos hδ hKpos N
    -- assembly
    have hsub : {ω | ENNReal.ofReal y < greedyJumps (fun n => H n ω) δ}
        ⊆ ({ω | ∀ n, |H n ω| ≤ M})ᶜ ∪ ({ω | ∀ n, |H n ω| ≤ M}
            ∩ {ω | greedyTime (fun n => H n ω) δ K < ⊤}) := by
      intro ω hω
      by_cases hA : ω ∈ {ω | ∀ n, |H n ω| ≤ M}
      · right
        refine ⟨hA, ?_⟩
        exact greedyTime_lt_top_of_lt_greedyJumps hy hω
      · left; exact hA
    have hKge : (y : ℝ) ≤ K := by
      rw [hKdef]
      exact le_of_lt (by exact_mod_cast Nat.lt_floor_add_one y : (y:ℝ) < ↑(⌊y⌋₊ + 1))
    have hKBpos : (0:ℝ) < K := by exact_mod_cast hKpos
    have harith : B / M + 7 * M * B / (K * δ ^ 2) ≤ 26 * B / (δ * Real.sqrt y) := by
      have h1 : B / M = B / (δ * Real.sqrt y) := by rw [hMdef]
      have h2 : 7 * M * B / (K * δ ^ 2) ≤ 7 * (B / (δ * Real.sqrt y)) := by
        rw [hMdef, ← mul_div_assoc]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hs2 : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy.le
        have hsq : (δ * Real.sqrt y) * (δ * Real.sqrt y) = δ ^ 2 * y := by
          rw [← pow_two, mul_pow, hs2]
        have h7 : 7 * (δ * Real.sqrt y) * B * (δ * Real.sqrt y) = 7 * B * δ ^ 2 * y := by
          nlinarith [hsq]
        have h8 : 7 * B * (↑K * δ ^ 2) = 7 * B * δ ^ 2 * ↑K := by ring
        rw [h7, h8]
        exact mul_le_mul_of_nonneg_left hKge (by positivity)
      have h3 : B / (δ * Real.sqrt y) + 7 * (B / (δ * Real.sqrt y))
          = 8 * (B / (δ * Real.sqrt y)) := by ring
      have h4 : 8 * (B / (δ * Real.sqrt y)) ≤ 26 * (B / (δ * Real.sqrt y)) := by
        have hx : (0:ℝ) < B / (δ * Real.sqrt y) := div_pos hB0 (by positivity)
        linarith
      calc B / M + 7 * M * B / (K * δ ^ 2)
          = B / (δ * Real.sqrt y) + 7 * M * B / (K * δ ^ 2) := by rw [h1]
        _ ≤ B / (δ * Real.sqrt y) + 7 * (B / (δ * Real.sqrt y)) := add_le_add le_rfl h2
        _ = 8 * (B / (δ * Real.sqrt y)) := h3
        _ ≤ 26 * (B / (δ * Real.sqrt y)) := h4
        _ = 26 * B / (δ * Real.sqrt y) := by ring
    calc μ {ω | ENNReal.ofReal y < greedyJumps (fun n => H n ω) δ}
        ≤ μ (({ω | ∀ n, |H n ω| ≤ M})ᶜ ∪ ({ω | ∀ n, |H n ω| ≤ M}
            ∩ {ω | greedyTime (fun n => H n ω) δ K < ⊤})) := measure_mono hsub
      _ ≤ μ ({ω | ∀ n, |H n ω| ≤ M})ᶜ + μ ({ω | ∀ n, |H n ω| ≤ M}
            ∩ {ω | greedyTime (fun n => H n ω) δ K < ⊤}) := measure_union_le _ _
      _ ≤ ENNReal.ofReal (B / M) + ENNReal.ofReal (7 * M * B / (K * δ ^ 2)) :=
          add_le_add hAc hlim
      _ = ENNReal.ofReal (B / M + 7 * M * B / (K * δ ^ 2)) := by
          rw [ENNReal.ofReal_add] <;> positivity
      _ ≤ ENNReal.ofReal (26 * B / (δ * Real.sqrt y)) := ENNReal.ofReal_le_ofReal harith


end Work.Analysis.Probability
