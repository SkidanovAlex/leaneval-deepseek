import Mathlib
import Submission.Work.BourgainPlan.Oscillation.oscZ_lacunary_defs

/-!
# `oscZ_core_lacunary`: the block oscillation of the weighted sharp core

This file derives the *block-oscillation* estimate `OscZCoreLacunary` for the weighted sharp core
`∑_{p ∈ T} p.2 · perNbhd p.1 (ρ i)` at an arbitrary antitone family of radii `ρ` from the
*neighbourhood maximal* input `NbrhdMaximalLacunary`.

The argument is the band / nestedness argument of `oscZ_ngbd_dyadic` (and of
`oscFunctional_of_neighborhood_family`), with the two modifications needed for an arbitrary
antitone radius family:

* the maximal input is now the abstract `Hmax : NbrhdMaximalLacunary`, i.e. the neighbourhood
  maximal for the family `ρ` itself (rather than for the dyadic family `2^{-t-1}`);
* the family is zero on the indices `i < j₀` and `ρ t ≤ δ/3` only for `t ≥ j₀`, so the maximal
  estimate is applied to the *shifted* family `ρ' t = ρ (t + j₀)`, which satisfies all the
  hypotheses of `Hmax` and dominates the radii that actually occur.

The weighted sum is identified with `coreW T δ · unNbhd T (ρ i)` through `coreW_mul_unNbhd`.
-/

namespace Work.BourgainPlan.Oscillation

open Finset MeasureTheory Commons.Analysis.ExponentialSums
open scoped BigOperators ENNReal

open Lacunary

noncomputable section

private lemma norm_ofReal_C (r : ℝ) : ‖((r:ℝ):ℂ)‖ = |r| := by simp

private lemma enorm_sub_le' (a b : ℂ) : ‖a - b‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ := by
  calc ‖a - b‖ₑ = ‖a + (-b)‖ₑ := by rw [sub_eq_add_neg]
    _ ≤ ‖a‖ₑ + ‖(-b)‖ₑ := enorm_add_le a (-b)
    _ = ‖a‖ₑ + ‖b‖ₑ := by rw [enorm_neg]

/-- The integrands of the family are interval-integrable: bounded measurable functions on `(0,1)`.
-/
private lemma intervalIntegrable_mult (T : Finset (ℝ × ℂ)) (cap δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ p ∈ T, ∀ q ∈ T, p ≠ q → ∀ l : ℤ, δ ≤ |p.1 - q.1 + (l : ℝ)|)
    (hcap0 : 0 ≤ cap) (hcap : ∀ p ∈ T, ‖p.2‖ ≤ cap)
    (ρ : ℕ → ℝ) (f : ℤ → ℂ) (s : Finset ℤ) (I : ℕ) (x : ℤ) :
    IntervalIntegrable (fun θ : ℝ =>
      coreW T δ θ * unNbhd T (ρ I) θ * trigP s f θ * Echar x θ) volume 0 1 := by
  have hmeas : Measurable (fun θ : ℝ =>
      coreW T δ θ * unNbhd T (ρ I) θ * trigP s f θ * Echar x θ) :=
    (((measurable_coreW T δ).mul (measurable_unNbhd T (ρ I))).mul
      (Lacunary.measurable_trigP s f)).mul (Lacunary.continuous_Echar x).measurable
  have hbound : ∀ θ : ℝ, ‖coreW T δ θ * unNbhd T (ρ I) θ * trigP s f θ * Echar x θ‖
      ≤ cap * (∑ n ∈ s, ‖f n‖) := by
    intro θ
    have h1 : ‖coreW T δ θ‖ ≤ cap := norm_coreW_le T δ hδ hsep hcap0 hcap θ
    have h2 : ‖unNbhd T (ρ I) θ‖ ≤ 1 := by rw [unNbhd]; split <;> norm_num
    have h3 : ‖trigP s f θ‖ ≤ ∑ n ∈ s, ‖f n‖ := Lacunary.norm_trigP_le s f θ
    have h4 : ‖Echar x θ‖ = 1 := Lacunary.norm_Echar x θ
    calc ‖coreW T δ θ * unNbhd T (ρ I) θ * trigP s f θ * Echar x θ‖
        = ‖coreW T δ θ‖ * ‖unNbhd T (ρ I) θ‖ * ‖trigP s f θ‖ * ‖Echar x θ‖ := by
          rw [norm_mul, norm_mul, norm_mul]
      _ ≤ cap * 1 * (∑ n ∈ s, ‖f n‖) * 1 := by
          refine mul_le_mul (mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) hcap0) h3
            (norm_nonneg _) (by positivity)) (le_of_eq h4) (norm_nonneg _) (by positivity)
      _ = cap * (∑ n ∈ s, ‖f n‖) := by ring
  have hInt : Integrable (fun θ : ℝ =>
      coreW T δ θ * unNbhd T (ρ I) θ * trigP s f θ * Echar x θ) Lacunary.mu01 :=
    Lacunary.integrable_Ioc_of_bound hmeas hbound
  refine ⟨?_, ?_⟩
  · show Integrable (fun θ : ℝ =>
        coreW T δ θ * unNbhd T (ρ I) θ * trigP s f θ * Echar x θ)
        (volume.restrict (Set.Ioc 0 1))
    exact hInt
  · rw [show Set.Ioc (1:ℝ) 0 = ∅ by ext t; simp]
    exact integrableOn_empty

/-- **The block-oscillation estimate for the fixed `coreW`-weight times the neighbourhood
indicator of an arbitrary antitone radius family**, derived from the neighbourhood maximal
`Hmax`. -/
private theorem core (Hmax : NbrhdMaximalLacunary) :
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
              (if j₀ ≤ i then coreW T δ θ * unNbhd T (ρ i) θ else 0) *
              trigP s f θ * Echar x θ) J k
            ≤ ENNReal.ofReal ((C * cap * ((Real.log ((T.card : ℝ) + 2)) ^ 2 + (M : ℝ) + 1)) ^ 2) *
                ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Hmax
  refine ⟨2 * C₀, by positivity, ?_⟩
  intro T cap δ hδ hδ₂ hcap0 hcap hsep ρ M hρpos hρanti hwin j₀ hj₀ J k hk hk0 f s hf
  classical
  set K₂ : ℝ := (T.card : ℝ) + 2 with hK₂def
  set L : ℝ := Real.log K₂ ^ 2 + (M : ℝ) + 1 with hLdef
  -- the shifted family used for the maximal estimate
  let ρ' : ℕ → ℝ := fun t => ρ (t + j₀)
  have hρ'pos : ∀ t, 0 < ρ' t := fun t => hρpos (t + j₀)
  have hρ'anti : Antitone ρ' := fun a b hab => hρanti (Nat.add_le_add_right hab j₀)
  have hρ'le : ∀ t, ρ' t ≤ 1 / 2 := by
    intro t
    have h1 : ρ (t + j₀) ≤ δ / 3 := hj₀ (t + j₀) (Nat.le_add_left j₀ t)
    show ρ (t + j₀) ≤ 1 / 2
    linarith
  have hρ'win : ∀ (j t : ℕ), ρ' t ≤ (2 : ℝ) ^ (-(j : ℝ) - 1) →
      ρ' (t + M) ≤ (2 : ℝ) ^ (-(j : ℝ) - 2) := by
    intro j t ht
    have ht' : ρ (t + j₀) ≤ (2 : ℝ) ^ (-(j : ℝ) - 1) := ht
    have h := hwin j (t + j₀) ht'
    show ρ ((t + M) + j₀) ≤ (2 : ℝ) ^ (-(j : ℝ) - 2)
    rw [← Nat.add_right_comm t j₀ M]
    exact h
  -- the (real valued) periodised neighbourhood indicator
  set NS : ℕ → Set ℝ := fun t => {θ' : ℝ | ∃ p ∈ T, ∃ l : ℤ, |θ' + (l:ℝ) - p.1| ≤ ρ t}
    with hNSdef
  set W : ℕ → ℝ → ℝ := fun t => (NS t).indicator (fun _ => (1:ℝ)) with hWdef
  have hW_apply : ∀ t θ, W t θ = (NS t).indicator (fun _ => (1:ℝ)) θ := fun t θ => rfl
  have hNS_mem : ∀ t θ, (θ ∈ NS t) ↔ (∃ p ∈ T, ∃ l : ℤ, |θ + (l:ℝ) - p.1| ≤ ρ t) := by
    intro t θ
    have h2 : NS t = {θ' : ℝ | ∃ p ∈ T, ∃ l : ℤ, |θ' + (l:ℝ) - p.1| ≤ ρ t} := congrFun hNSdef t
    rw [h2, Set.mem_ofPred_eq]
  have hNS_meas : ∀ t, MeasurableSet (NS t) := by
    intro t
    change MeasurableSet {θ' : ℝ | ∃ p ∈ T, ∃ l : ℤ, |θ' + (l:ℝ) - p.1| ≤ ρ t}
    rw [show {θ' : ℝ | ∃ p ∈ T, ∃ l : ℤ, |θ' + (l:ℝ) - p.1| ≤ ρ t}
        = ⋃ p ∈ T, ⋃ l : ℤ, {θ' : ℝ | |θ' + (l:ℝ) - p.1| ≤ ρ t} from by
          ext θ; simp [Set.mem_iUnion, exists_prop]]
    exact MeasurableSet.biUnion T.countable_toSet (fun p _ =>
      MeasurableSet.iUnion (fun l => measurableSet_le (by fun_prop) measurable_const))
  have hW_one : ∀ t θ, θ ∈ NS t → W t θ = 1 := by
    intro t θ h; rw [hW_apply, Set.indicator_of_mem h]
  have hW_zero : ∀ t θ, θ ∉ NS t → W t θ = 0 := by
    intro t θ h; rw [hW_apply, Set.indicator_of_notMem h]
  have hW_one' : ∀ t θ, (∃ p ∈ T, ∃ l : ℤ, |θ + (l:ℝ) - p.1| ≤ ρ t) → W t θ = 1 :=
    fun t θ h => hW_one t θ ((hNS_mem t θ).mpr h)
  have hW_zero' : ∀ t θ, ¬(∃ p ∈ T, ∃ l : ℤ, |θ + (l:ℝ) - p.1| ≤ ρ t) → W t θ = 0 :=
    fun t θ h => hW_zero t θ (fun hc => h ((hNS_mem t θ).mp hc))
  have hWmeas : ∀ t, Measurable (W t) := by
    intro t
    rw [show W t = (NS t).indicator (fun _ => (1:ℝ)) from rfl]
    exact measurable_const.indicator (hNS_meas t)
  have hW_nonneg : ∀ t θ, 0 ≤ W t θ := by
    intro t θ
    by_cases h : θ ∈ NS t
    · rw [hW_one t θ h]; norm_num
    · rw [hW_zero t θ h]
  have hW_le : ∀ t θ, W t θ ≤ 1 := by
    intro t θ
    by_cases h : θ ∈ NS t
    · rw [hW_one t θ h]
    · rw [hW_zero t θ h]; norm_num
  have hNS_anti : ∀ t t', t ≤ t' → NS t' ⊆ NS t := by
    intro t t' htt θ hθ
    rw [hNS_mem] at hθ ⊢
    obtain ⟨p, hp, l, hl⟩ := hθ
    exact ⟨p, hp, l, le_trans hl (hρanti htt)⟩
  have hWmono : ∀ t t' θ, t ≤ t' → W t' θ ≤ W t θ := by
    intro t t' θ htt
    by_cases h : θ ∈ NS t'
    · rw [hW_one t' θ h, hW_one t θ (hNS_anti t t' htt h)]
    · rw [hW_zero t' θ h]
      exact hW_nonneg t θ
  have hunW : ∀ t θ, unNbhd T (ρ t) θ = (W t θ : ℂ) := by
    intro t θ
    rw [unNbhd]
    by_cases h : θ ∈ NS t
    · rw [if_pos ((hNS_mem t θ).mp h), hW_one t θ h]; norm_num
    · rw [if_neg (fun hc => h ((hNS_mem t θ).mpr hc)), hW_zero t θ h]; norm_num
  -- Plancherel for the trigonometric polynomial
  have hpl : (∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖trigP s f θ‖ₑ ^ (2:ℝ))
      = ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
    have h1 : (∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖trigP s f θ‖ₑ ^ (2:ℝ))
        = ∫⁻ θ, ‖trigP s f θ‖ₑ ^ (2:ℝ) ∂Lacunary.mu01 := rfl
    rw [h1, Lacunary.trig_lintegral s f, ← Lacunary.f_lintegral s f hf]
  -- telescoping of the block bands
  have htel : ∀ θ, (∑ j ∈ Finset.range J, (W (k j) θ - W (k (j+1) - 1) θ)) ≤ 1 := by
    intro θ
    have h1 : ∀ j : ℕ, W (k (j+1)) θ ≤ W (k (j+1) - 1) θ :=
      fun j => hWmono (k (j+1) - 1) (k (j+1)) θ (Nat.sub_le _ _)
    calc (∑ j ∈ Finset.range J, (W (k j) θ - W (k (j+1) - 1) θ))
        ≤ ∑ j ∈ Finset.range J, (W (k j) θ - W (k (j+1)) θ) := by
          refine Finset.sum_le_sum (fun j _ => ?_); linarith [h1 j]
      _ = W (k 0) θ - W (k J) θ := by
          rw [show (∑ j ∈ Finset.range J, (W (k j) θ - W (k (j+1)) θ))
              = -∑ j ∈ Finset.range J, (W (k (j+1)) θ - W (k j) θ) from by
                rw [← Finset.sum_neg_distrib]
                exact Finset.sum_congr rfl (fun j _ => by ring),
            Finset.sum_range_sub (fun j => W (k j) θ) J, neg_sub]
      _ ≤ 1 := by linarith [hW_nonneg (k J) θ, hW_le (k 0) θ]
  have hpred : ∀ j : ℕ, k j ≤ k (j+1) - 1 :=
    fun j => Nat.le_sub_one_of_lt (hk (Nat.lt_succ_self j))
  -- the per-block maximal bound
  have hblock : ∀ j : ℕ,
      (∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j+1)),
          ‖∫ θ in (0:ℝ)..1, coreW T δ θ * (unNbhd T (ρ i) θ - unNbhd T (ρ (k j)) θ)
            * trigP s f θ * Echar x θ‖ₑ) ^ (2:ℝ) ∂MeasureTheory.Measure.count)
        ≤ ENNReal.ofReal ((2*C₀ * L)^2) *
            ∫⁻ θ in Set.Ioc (0:ℝ) 1,
              ‖coreW T δ θ * ((W (k j) θ : ℂ) - (W (k (j+1) - 1) θ : ℂ)) * trigP s f θ‖ₑ^(2:ℝ) := by
    intro j
    have hjk : j₀ ≤ k j := le_trans hk0 (hk.monotone (Nat.zero_le j))
    set Qj : ℝ → ℂ := fun θ =>
        coreW T δ θ * ((W (k j) θ : ℂ) - (W (k (j+1) - 1) θ : ℂ)) * trigP s f θ with hQjdef
    have hQj_meas : Measurable Qj := by
      rw [hQjdef]
      refine ((measurable_coreW T δ).mul ?_).mul (Lacunary.measurable_trigP s f)
      exact (Complex.measurable_ofReal.comp (hWmeas (k j))).sub
        (Complex.measurable_ofReal.comp (hWmeas (k (j+1) - 1)))
    have hQj_bound : ∀ θ, ‖Qj θ‖ ≤ cap * (∑ n ∈ s, ‖f n‖) := by
      intro θ
      rw [hQjdef]
      have h1 : ‖coreW T δ θ‖ ≤ cap := norm_coreW_le T δ hδ hsep hcap0 hcap θ
      have h2 : ‖((W (k j) θ : ℂ) - (W (k (j+1) - 1) θ : ℂ))‖ ≤ 1 := by
        rw [show ((W (k j) θ : ℂ) - (W (k (j+1) - 1) θ : ℂ))
              = ((W (k j) θ - W (k (j+1) - 1) θ : ℝ) : ℂ) from by rw [Complex.ofReal_sub],
          norm_ofReal_C, abs_le]
        exact ⟨by linarith [hW_nonneg (k j) θ, hW_le (k (j+1) - 1) θ],
               by linarith [hW_le (k j) θ, hW_nonneg (k (j+1) - 1) θ]⟩
      have h3 : ‖trigP s f θ‖ ≤ ∑ n ∈ s, ‖f n‖ := Lacunary.norm_trigP_le s f θ
      calc ‖coreW T δ θ * ((W (k j) θ : ℂ) - (W (k (j+1) - 1) θ : ℂ)) * trigP s f θ‖
          = ‖coreW T δ θ‖ * ‖((W (k j) θ : ℂ) - (W (k (j+1) - 1) θ : ℂ))‖ * ‖trigP s f θ‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ cap * 1 * (∑ n ∈ s, ‖f n‖) :=
            mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) hcap0) h3 (norm_nonneg _)
              (mul_nonneg hcap0 zero_le_one)
        _ = cap * (∑ n ∈ s, ‖f n‖) := by ring
    have hQj_memLp : MemLp Qj 2 (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
      MemLp.of_bound hQj_meas.aestronglyMeasurable (cap * (∑ n ∈ s, ‖f n‖))
        (Filter.Eventually.of_forall hQj_bound)
    have hint : ∀ (t : ℕ) (x : ℤ),
        Integrable (fun θ => unNbhd T (ρ t) θ * Qj θ * Echar x θ) Lacunary.mu01 := by
      intro t x
      refine Lacunary.integrable_Ioc_of_bound (C := cap * (∑ n ∈ s, ‖f n‖)) ?_ ?_
      · exact ((measurable_unNbhd T (ρ t)).mul hQj_meas).mul
          (Lacunary.continuous_Echar x).measurable
      · intro θ
        have h1 : ‖unNbhd T (ρ t) θ‖ ≤ 1 := by
          rw [unNbhd]; split <;> norm_num
        calc ‖unNbhd T (ρ t) θ * Qj θ * Echar x θ‖
            = ‖unNbhd T (ρ t) θ‖ * ‖Qj θ‖ * ‖Echar x θ‖ := by rw [norm_mul, norm_mul]
          _ ≤ 1 * (cap * (∑ n ∈ s, ‖f n‖)) * 1 := by
              refine mul_le_mul (mul_le_mul h1 (hQj_bound θ) (norm_nonneg _) zero_le_one)
                (le_of_eq (Lacunary.norm_Echar x θ)) (norm_nonneg _) (by positivity)
          _ = cap * (∑ n ∈ s, ‖f n‖) := by ring
    have hsplit : ∀ i ∈ Finset.Ico (k j) (k (j+1)), ∀ x : ℤ,
        ‖∫ θ in (0:ℝ)..1, coreW T δ θ * (unNbhd T (ρ i) θ - unNbhd T (ρ (k j)) θ)
            * trigP s f θ * Echar x θ‖ₑ
          ≤ 2 * (⨆ t : ℕ, ‖∫ θ in (0:ℝ)..1, unNbhd T (ρ' t) θ * Qj θ * Echar x θ‖ₑ) := by
      intro i hi x
      have hki : k j ≤ i := (Finset.mem_Ico.mp hi).1
      have hji : j₀ ≤ i := le_trans hjk hki
      have hik : i ≤ k (j+1) - 1 := by
        have := (Finset.mem_Ico.mp hi).2; omega
      have hkeyC : ∀ θ, ((W i θ : ℂ) - (W (k j) θ : ℂ)) * ((W (k j) θ : ℂ) - (W (k (j+1) - 1) θ : ℂ))
          = ((W i θ : ℂ) - (W (k j) θ : ℂ)) := by
        intro θ
        by_cases hRi : ∃ p ∈ T, ∃ l : ℤ, |θ + (l:ℝ) - p.1| ≤ ρ i
        · have h1 : W i θ = 1 := hW_one' i θ hRi
          obtain ⟨p, hp, l, hl⟩ := hRi
          have hRkj : ∃ p ∈ T, ∃ l : ℤ, |θ + (l:ℝ) - p.1| ≤ ρ (k j) :=
            ⟨p, hp, l, le_trans hl (hρanti hki)⟩
          have h2 : W (k j) θ = 1 := hW_one' (k j) θ hRkj
          rw [h1, h2]; norm_num
        · have h1 : W i θ = 0 := hW_zero' i θ hRi
          have h3 : W (k (j+1) - 1) θ = 0 := by
            refine hW_zero' _ _ (fun hc => hRi ?_)
            obtain ⟨p, hp, l, hl⟩ := hc
            exact ⟨p, hp, l, le_trans hl (hρanti hik)⟩
          rw [h1, h3]
          by_cases hRkj : ∃ p ∈ T, ∃ l : ℤ, |θ + (l:ℝ) - p.1| ≤ ρ (k j)
          · have h2 : W (k j) θ = 1 := hW_one' (k j) θ hRkj
            rw [h2]; norm_num
          · have h2 : W (k j) θ = 0 := hW_zero' (k j) θ hRkj
            rw [h2]; norm_num
      have hdec : (∫ θ in (0:ℝ)..1, coreW T δ θ * (unNbhd T (ρ i) θ - unNbhd T (ρ (k j)) θ)
            * trigP s f θ * Echar x θ)
          = (∫ θ in (0:ℝ)..1, ((W i θ : ℂ) - (W (k j) θ : ℂ)) * Qj θ * Echar x θ) := by
        refine intervalIntegral.integral_congr (fun θ _ => ?_)
        rw [hunW i θ, hunW (k j) θ, hQjdef]
        set X := ((W i θ : ℂ) - (W (k j) θ : ℂ)) with hXdef
        set A := ((W (k j) θ : ℂ) - (W (k (j+1) - 1) θ : ℂ)) with hAdef
        have hXA : X * A = X := by rw [hXdef, hAdef]; exact hkeyC θ
        have hgoal : X * (coreW T δ θ * A * trigP s f θ) = coreW T δ θ * X * trigP s f θ := by
          calc X * (coreW T δ θ * A * trigP s f θ)
              = X * A * coreW T δ θ * trigP s f θ := by ring
            _ = X * coreW T δ θ * trigP s f θ := by rw [hXA]
            _ = coreW T δ θ * X * trigP s f θ := by ring
        rw [hgoal]
      have hline : (∫ θ in (0:ℝ)..1, ((W i θ : ℂ) - (W (k j) θ : ℂ)) * Qj θ * Echar x θ)
          = (∫ θ in (0:ℝ)..1, unNbhd T (ρ i) θ * Qj θ * Echar x θ)
            - (∫ θ in (0:ℝ)..1, unNbhd T (ρ (k j)) θ * Qj θ * Echar x θ) := by
        rw [show (fun θ => ((W i θ : ℂ) - (W (k j) θ : ℂ)) * Qj θ * Echar x θ)
              = (fun θ => unNbhd T (ρ i) θ * Qj θ * Echar x θ
                  - unNbhd T (ρ (k j)) θ * Qj θ * Echar x θ) from by
            funext θ; rw [hunW i θ, hunW (k j) θ]; ring]
        rw [Lacunary.intervalIntegral_eq_mu01, Lacunary.intervalIntegral_eq_mu01,
          Lacunary.intervalIntegral_eq_mu01, MeasureTheory.integral_sub (hint i x) (hint (k j) x)]
      have hmm : ρ' (i - j₀) = ρ i := by
        show ρ ((i - j₀) + j₀) = ρ i
        rw [Nat.sub_add_cancel hji]
      have hkk : ρ' (k j - j₀) = ρ (k j) := by
        show ρ ((k j - j₀) + j₀) = ρ (k j)
        rw [Nat.sub_add_cancel hjk]
      rw [hdec, hline]
      calc ‖(∫ θ in (0:ℝ)..1, unNbhd T (ρ i) θ * Qj θ * Echar x θ)
              - (∫ θ in (0:ℝ)..1, unNbhd T (ρ (k j)) θ * Qj θ * Echar x θ)‖ₑ
          ≤ ‖(∫ θ in (0:ℝ)..1, unNbhd T (ρ i) θ * Qj θ * Echar x θ)‖ₑ
            + ‖(∫ θ in (0:ℝ)..1, unNbhd T (ρ (k j)) θ * Qj θ * Echar x θ)‖ₑ := enorm_sub_le' _ _
        _ = ‖(∫ θ in (0:ℝ)..1, unNbhd T (ρ' (i - j₀)) θ * Qj θ * Echar x θ)‖ₑ
            + ‖(∫ θ in (0:ℝ)..1, unNbhd T (ρ' (k j - j₀)) θ * Qj θ * Echar x θ)‖ₑ := by
              rw [← hmm, ← hkk]
        _ ≤ (⨆ t : ℕ, ‖∫ θ in (0:ℝ)..1, unNbhd T (ρ' t) θ * Qj θ * Echar x θ‖ₑ)
            + (⨆ t : ℕ, ‖∫ θ in (0:ℝ)..1, unNbhd T (ρ' t) θ * Qj θ * Echar x θ‖ₑ) :=
              add_le_add
                (le_iSup (fun t : ℕ => ‖∫ θ in (0:ℝ)..1, unNbhd T (ρ' t) θ * Qj θ * Echar x θ‖ₑ) (i - j₀))
                (le_iSup (fun t : ℕ => ‖∫ θ in (0:ℝ)..1, unNbhd T (ρ' t) θ * Qj θ * Echar x θ‖ₑ) (k j - j₀))
        _ = 2 * (⨆ t : ℕ, ‖∫ θ in (0:ℝ)..1, unNbhd T (ρ' t) θ * Qj θ * Echar x θ‖ₑ) := by rw [two_mul]
    have hsup : ∀ x : ℤ,
        (⨆ i ∈ Finset.Ico (k j) (k (j+1)),
          ‖∫ θ in (0:ℝ)..1, coreW T δ θ * (unNbhd T (ρ i) θ - unNbhd T (ρ (k j)) θ)
            * trigP s f θ * Echar x θ‖ₑ)
          ≤ 2 * (⨆ t : ℕ, ‖∫ θ in (0:ℝ)..1, unNbhd T (ρ' t) θ * Qj θ * Echar x θ‖ₑ) := by
      intro x
      refine iSup_le (fun i => iSup_le (fun hi => hsplit i hi x))
    have hH := hC₀ T ρ' M hρ'pos hρ'le hρ'anti hρ'win Qj hQj_memLp
    calc (∫⁻ x : ℤ, (⨆ i ∈ Finset.Ico (k j) (k (j+1)),
            ‖∫ θ in (0:ℝ)..1, coreW T δ θ * (unNbhd T (ρ i) θ - unNbhd T (ρ (k j)) θ)
              * trigP s f θ * Echar x θ‖ₑ) ^ (2:ℝ) ∂MeasureTheory.Measure.count)
        ≤ ∫⁻ x : ℤ, (2 * (⨆ t : ℕ, ‖∫ θ in (0:ℝ)..1, unNbhd T (ρ' t) θ * Qj θ * Echar x θ‖ₑ)) ^ (2:ℝ)
            ∂MeasureTheory.Measure.count :=
          lintegral_mono (fun x => ENNReal.rpow_le_rpow (hsup x) (by norm_num))
      _ = 4 * ∫⁻ x : ℤ, (⨆ t : ℕ, ‖∫ θ in (0:ℝ)..1, unNbhd T (ρ' t) θ * Qj θ * Echar x θ‖ₑ) ^ (2:ℝ)
            ∂MeasureTheory.Measure.count := by
          rw [show (fun x : ℤ => (2 * (⨆ t : ℕ, ‖∫ θ in (0:ℝ)..1, unNbhd T (ρ' t) θ * Qj θ * Echar x θ‖ₑ)) ^ (2:ℝ))
              = (fun x : ℤ => 4 * (⨆ t : ℕ, ‖∫ θ in (0:ℝ)..1, unNbhd T (ρ' t) θ * Qj θ * Echar x θ‖ₑ) ^ (2:ℝ)) from by
                funext x
                rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast, mul_pow]
                norm_num]
          rw [lintegral_const_mul 4 (measurable_of_countable _)]
      _ ≤ 4 * (ENNReal.ofReal ((C₀ * L)^2) * ∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖Qj θ‖ₑ ^ (2:ℝ)) :=
          mul_le_mul_of_nonneg_left hH (by norm_num : (0:ℝ≥0∞) ≤ 4)
      _ = ENNReal.ofReal ((2*C₀ * L)^2) *
            ∫⁻ θ in Set.Ioc (0:ℝ) 1,
              ‖coreW T δ θ * ((W (k j) θ : ℂ) - (W (k (j+1) - 1) θ : ℂ)) * trigP s f θ‖ₑ ^ (2:ℝ) := by
          have h4 : (4:ℝ≥0∞) * ENNReal.ofReal ((C₀ * L)^2)
              = ENNReal.ofReal ((2*C₀ * L)^2) := by
            rw [show (4:ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
              ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
            congr 1
            ring
          rw [← mul_assoc, h4]
  -- the sum over blocks
  have hsum : (∑ j ∈ Finset.range J, ∫⁻ θ in Set.Ioc (0:ℝ) 1,
        ‖coreW T δ θ * ((W (k j) θ : ℂ) - (W (k (j+1) - 1) θ : ℂ)) * trigP s f θ‖ₑ ^ (2:ℝ))
      ≤ ENNReal.ofReal (cap ^ 2) * ∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖trigP s f θ‖ₑ ^ (2:ℝ) := by
    have hm : ∀ j, Measurable (fun θ : ℝ =>
        ‖coreW T δ θ * ((W (k j) θ : ℂ) - (W (k (j+1) - 1) θ : ℂ)) * trigP s f θ‖ₑ ^ (2:ℝ)) := by
      intro j
      refine (Measurable.enorm ?_).pow_const 2
      exact ((measurable_coreW T δ).mul ((Complex.measurable_ofReal.comp (hWmeas (k j))).sub
        (Complex.measurable_ofReal.comp (hWmeas (k (j+1) - 1))))).mul (Lacunary.measurable_trigP s f)
    rw [← lintegral_finsetSum (Finset.range J) (fun j _ => hm j)]
    have hmG : Measurable (fun θ : ℝ => ‖trigP s f θ‖ₑ ^ (2:ℝ)) :=
      (Measurable.enorm (Lacunary.measurable_trigP s f)).pow_const 2
    calc ∫⁻ θ in Set.Ioc (0:ℝ) 1,
            (∑ j ∈ Finset.range J, ‖coreW T δ θ * ((W (k j) θ : ℂ) - (W (k (j+1) - 1) θ : ℂ)) * trigP s f θ‖ₑ ^ (2:ℝ))
        ≤ ∫⁻ θ in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (cap ^ 2) * ‖trigP s f θ‖ₑ ^ (2:ℝ) :=
          lintegral_mono (fun θ => by
            have hpt : ∀ j, ‖coreW T δ θ * ((W (k j) θ : ℂ) - (W (k (j+1) - 1) θ : ℂ)) * trigP s f θ‖ₑ ^ (2:ℝ)
                ≤ ENNReal.ofReal (cap ^ 2) * ENNReal.ofReal (W (k j) θ - W (k (j+1) - 1) θ)
                    * ‖trigP s f θ‖ₑ ^ (2:ℝ) := by
              intro j
              rw [enorm_mul, enorm_mul,
                ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2),
                ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
              gcongr
              · rw [Lacunary.rpow_two_ofReal]
                exact ENNReal.ofReal_le_ofReal
                  (pow_le_pow_left₀ (norm_nonneg _) (norm_coreW_le T δ hδ hsep hcap0 hcap θ) 2)
              · have hle1 : W (k (j+1) - 1) θ ≤ W (k j) θ := hWmono (k j) (k (j+1) - 1) θ (hpred j)
                have hWr : (0:ℝ) ≤ W (k j) θ - W (k (j+1) - 1) θ
                    ∧ W (k j) θ - W (k (j+1) - 1) θ ≤ 1 :=
                  ⟨by linarith [hW_nonneg (k j) θ, hW_le (k (j+1) - 1) θ],
                   by linarith [hW_le (k j) θ, hW_nonneg (k (j+1) - 1) θ, hle1]⟩
                rw [show ((W (k j) θ : ℂ) - (W (k (j+1) - 1) θ : ℂ))
                      = ((W (k j) θ - W (k (j+1) - 1) θ : ℝ) : ℂ) from by rw [Complex.ofReal_sub],
                  Lacunary.rpow_two_ofReal, norm_ofReal_C, sq_abs]
                refine ENNReal.ofReal_le_ofReal ?_
                nlinarith [mul_nonneg hWr.1 (sub_nonneg.mpr hWr.2)]
            calc (∑ j ∈ Finset.range J, ‖coreW T δ θ * ((W (k j) θ : ℂ) - (W (k (j+1) - 1) θ : ℂ)) * trigP s f θ‖ₑ ^ (2:ℝ))
                ≤ ∑ j ∈ Finset.range J, ENNReal.ofReal (cap ^ 2)
                    * ENNReal.ofReal (W (k j) θ - W (k (j+1) - 1) θ) * ‖trigP s f θ‖ₑ ^ (2:ℝ) :=
                  Finset.sum_le_sum (fun j _ => hpt j)
              _ = ENNReal.ofReal (cap ^ 2)
                    * (∑ j ∈ Finset.range J, ENNReal.ofReal (W (k j) θ - W (k (j+1) - 1) θ))
                    * ‖trigP s f θ‖ₑ ^ (2:ℝ) := by
                  rw [← Finset.sum_mul, ← Finset.mul_sum]
              _ ≤ ENNReal.ofReal (cap ^ 2) * 1 * ‖trigP s f θ‖ₑ ^ (2:ℝ) := by
                  gcongr
                  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => by
                    have := hWmono (k j) (k (j+1) - 1) θ (hpred j)
                    linarith [hW_nonneg (k (j+1) - 1) θ])]
                  simpa using ENNReal.ofReal_le_ofReal (htel θ)
              _ = ENNReal.ofReal (cap ^ 2) * ‖trigP s f θ‖ₑ ^ (2:ℝ) := by rw [mul_one])
      _ = ENNReal.ofReal (cap ^ 2) * ∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖trigP s f θ‖ₑ ^ (2:ℝ) :=
          lintegral_const_mul (ENNReal.ofReal (cap ^ 2)) hmG
  -- the `oscZ` form with `A_i - A_(k_j)` is the symbol-difference form
  have heq : oscZ (fun i x => ∫ θ in (0 : ℝ)..1,
        (if j₀ ≤ i then coreW T δ θ * unNbhd T (ρ i) θ else 0) *
        trigP s f θ * Echar x θ) J k
      = ∑ j ∈ Finset.range J, ∫⁻ x : ℤ,
          (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
            ‖∫ θ in (0 : ℝ)..1, coreW T δ θ *
                (unNbhd T (ρ i) θ - unNbhd T (ρ (k j)) θ) *
                trigP s f θ * Echar x θ‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count := by
    rw [oscZ]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    refine lintegral_congr (fun x => ?_)
    refine congrArg (fun z : ℝ≥0∞ => z ^ (2 : ℝ)) ?_
    refine iSup_congr (fun i => iSup_congr (fun hi => ?_))
    have hjk : j₀ ≤ k j := le_trans hk0 (hk.monotone (Nat.zero_le j))
    have hji : j₀ ≤ i := le_trans hjk (Finset.mem_Ico.mp hi).1
    have hsub : (∫ θ in (0 : ℝ)..1,
          (if j₀ ≤ i then coreW T δ θ * unNbhd T (ρ i) θ else 0) *
          trigP s f θ * Echar x θ)
        - (∫ θ in (0 : ℝ)..1,
          (if j₀ ≤ k j then coreW T δ θ * unNbhd T (ρ (k j)) θ else 0) *
          trigP s f θ * Echar x θ)
        = ∫ θ in (0 : ℝ)..1, coreW T δ θ *
            (unNbhd T (ρ i) θ - unNbhd T (ρ (k j)) θ) *
            trigP s f θ * Echar x θ := by
      have hi1 : (∫ θ in (0 : ℝ)..1,
            (if j₀ ≤ i then coreW T δ θ * unNbhd T (ρ i) θ else 0) *
            trigP s f θ * Echar x θ)
          = ∫ θ in (0 : ℝ)..1,
              coreW T δ θ * unNbhd T (ρ i) θ * trigP s f θ * Echar x θ := by
        refine intervalIntegral.integral_congr (fun θ _ => ?_)
        rw [if_pos hji]
      have hk1 : (∫ θ in (0 : ℝ)..1,
            (if j₀ ≤ k j then coreW T δ θ * unNbhd T (ρ (k j)) θ else 0) *
            trigP s f θ * Echar x θ)
          = ∫ θ in (0 : ℝ)..1,
              coreW T δ θ * unNbhd T (ρ (k j)) θ * trigP s f θ * Echar x θ := by
        refine intervalIntegral.integral_congr (fun θ _ => ?_)
        rw [if_pos hjk]
      rw [hi1, hk1]
      rw [← intervalIntegral.integral_sub
        (intervalIntegrable_mult T cap δ hδ hsep hcap0 hcap ρ f s i x)
        (intervalIntegrable_mult T cap δ hδ hsep hcap0 hcap ρ f s (k j) x)]
      refine intervalIntegral.integral_congr (fun θ _ => ?_)
      ring
    rw [hsub]
  rw [heq]
  calc (∑ j ∈ Finset.range J, ∫⁻ x : ℤ,
          (⨆ i ∈ Finset.Ico (k j) (k (j + 1)),
            ‖∫ θ in (0 : ℝ)..1, coreW T δ θ *
                (unNbhd T (ρ i) θ - unNbhd T (ρ (k j)) θ) *
                trigP s f θ * Echar x θ‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count)
    _ ≤ ∑ j ∈ Finset.range J, ENNReal.ofReal ((2*C₀ * L)^2) *
            ∫⁻ θ in Set.Ioc (0:ℝ) 1,
              ‖coreW T δ θ * ((W (k j) θ : ℂ) - (W (k (j+1) - 1) θ : ℂ)) * trigP s f θ‖ₑ ^ (2:ℝ) :=
          Finset.sum_le_sum (fun j _ => hblock j)
    _ = ENNReal.ofReal ((2*C₀ * L)^2) *
          (∑ j ∈ Finset.range J, ∫⁻ θ in Set.Ioc (0:ℝ) 1,
              ‖coreW T δ θ * ((W (k j) θ : ℂ) - (W (k (j+1) - 1) θ : ℂ)) * trigP s f θ‖ₑ ^ (2:ℝ)) := by
          rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal ((2*C₀ * L)^2) *
          (ENNReal.ofReal (cap ^ 2) * ∫⁻ θ in Set.Ioc (0:ℝ) 1, ‖trigP s f θ‖ₑ ^ (2:ℝ)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ENNReal.ofReal ((2*C₀ * L)^2) * ENNReal.ofReal (cap ^ 2) *
          ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
          rw [hpl, ← mul_assoc]
    _ = ENNReal.ofReal (((2*C₀) * cap * L) ^ 2) *
          ∫⁻ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) ∂MeasureTheory.Measure.count := by
          have hof : ENNReal.ofReal ((2*C₀ * L)^2) * ENNReal.ofReal (cap^2)
              = ENNReal.ofReal (((2*C₀) * cap * L)^2) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1
            ring
          rw [hof]

/-- **The requested lemma.**  The block-oscillation estimate for the weighted sharp core
`∑_p p.2 · perNbhd p.1 (ρ i)` at an arbitrary antitone radius family, derived from the
neighbourhood maximal `Hmax`. -/
theorem oscZ_core_lacunary (Hmax : Work.BourgainPlan.Oscillation.NbrhdMaximalLacunary) :
    Work.BourgainPlan.Oscillation.OscZCoreLacunary := by
  obtain ⟨C, hCpos, hC⟩ := core Hmax
  refine ⟨C, hCpos, ?_⟩
  intro T cap δ hδ hδ₂ hcap0 hcap hsep ρ M hρpos hρanti hwin j₀ hj₀ J k hk hk0 f s hf
  set Araw : ℕ → ℤ → ℂ := fun i x => ∫ θ in (0:ℝ)..1,
      (if j₀ ≤ i then ∑ p ∈ T, p.2 * perNbhd p.1 (ρ i) θ else 0) *
      (∑ n ∈ s, f n * Complex.exp (2 * Real.pi * Complex.I * ((n : ℤ) : ℂ) * (θ : ℂ))) *
      Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℤ) : ℂ) * (θ : ℂ))) with hAraw
  set Acore : ℕ → ℤ → ℂ := fun i x => ∫ θ in (0:ℝ)..1,
      (if j₀ ≤ i then coreW T δ θ * unNbhd T (ρ i) θ else 0) *
      trigP s f θ * Echar x θ with hAcore
  have hpoint : ∀ i, j₀ ≤ i → ∀ x, Araw i x = Acore i x := by
    intro i hi x
    have hri : ρ i ≤ δ / 3 := hj₀ i hi
    simp only [hAraw, hAcore]
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    rw [if_pos hi, if_pos hi, ← coreW_mul_unNbhd T δ hδ hsep hri θ]
    rfl
  have hosc : oscZ Araw J k = oscZ Acore J k := by
    unfold oscZ
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine lintegral_congr (fun x => ?_)
    refine congrArg (fun z : ℝ≥0∞ => z ^ (2:ℝ)) ?_
    refine iSup_congr (fun i => iSup_congr (fun hi => ?_))
    have hjk : j₀ ≤ k j := le_trans hk0 (hk.monotone (Nat.zero_le j))
    have hji : j₀ ≤ i := le_trans hjk (Finset.mem_Ico.mp hi).1
    rw [hpoint i hji x, hpoint (k j) hjk x]
  rw [hosc]
  exact hC T cap δ hδ hδ₂ hcap0 hcap hsep ρ M hρpos hρanti hwin j₀ hj₀ J k hk hk0 f s hf

end

end Work.BourgainPlan.Oscillation
