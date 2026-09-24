/-
# `APSwitchUpper.mass_identity` — the mass identity `Tv (n+1) = ∫_2^{2n+4} oddSum n · log ((u+1)/3)`

The level constants `Cv n = ∫_2^{2n+4} oddSum n` and `Tv n = ∫_3^{2n+3} evenSum n`
(`APSwitchUpper.riPhi_le_env`) are the partial sums of the two profiles
`riPsi = Σ_j profC (2j+1)` and `riPhi = Σ_j profC (2j)`:

* `Cv n` is the `n`-th level of `C = ∫_2^∞ riPsi`,
* `Tv n` is the `n`-th level of `T = ∫_3^∞ riPhi`.

The identity proved here relates two *consecutive* levels of the two families:

  `Tv (n+1) = ∫_2^{2n+4} oddSum n u · log ((u+1)/3) du`

(the `n`-th odd level integrated against the logarithmic kernel `log ((u+1)/3)`, the kernel
being the integral `∫_3^{u+1} ds/s` of the reciprocal).  It is the integrated form of the
delay recursion `s·evenSum (n+1) s = ∫_{max (s-1) 2}^{2n+4} oddSum n` (the identity
`oddSum_formula`/`evenSum_succ_mul` of the sibling modules):

```
Tv (n+1) = ∫_3^{2n+5} (1/s)·(∫_{s-1}^{2n+4} oddSum n) ds      (the recursion)
         = ∫_2^{2n+4} oddSum n u ·(∫_3^{u+1} ds/s) du         (Fubini on the triangle)
         = ∫_2^{2n+4} oddSum n u · log ((u+1)/3) du,
```

the triangle being `{3 ≤ s ≤ u+1, 2 ≤ u ≤ 2n+4}`: for `u` in the inner range the truncation
point `u+1` never exceeds the top `2n+5` of the `s`-range, so the `s`-integration runs over
`[3,u+1]`.

The formalisation proceeds by *(i)* rewriting the inner interval integral with the truncation
point `s-1` as a set integral over `(2, 2n+4]` with the indicator of `(s-1, ∞)`, *(ii)* the
Fubini swap `intervalIntegral_intervalIntegral_swap` over the *rectangle*
`(3, 2n+5] × (2, 2n+4]` (the integrand is bounded, hence integrable there), and *(iii)* the
truncation lemma `integral_indicator_Iio_of_le` reducing the `s`-integral to
`∫_3^{u+1} 1/s = log ((u+1)/3)`.
-/
import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhiLevelCore

namespace Work.NumberTheory.Chen.APSwitchUpper

open MeasureTheory Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## The kernel of the double integral -/

/-- The kernel `kern n s u = (1/s)·1_{s-1<u}·oddSum n u` whose iterated integrals occur in
the mass identity. -/
noncomputable def kern (n : ℕ) (s u : ℝ) : ℝ :=
  (1 / s) * (if s - 1 < u then oddSum n u else 0)

/-! ## Measurability and boundedness of `oddSum n` -/

/-- `oddSum n = Σ_{i≤n} profC (2i+1)` is measurable. -/
lemma measurable_oddSum (n : ℕ) : Measurable (oddSum n) := by
  unfold oddSum
  exact Finset.measurable_sum _ (fun i _ => profC_measurable (2 * i + 1))

/-- `oddSum n` is bounded: a finite sum of bounded profiles. -/
lemma exists_bound_oddSum (n : ℕ) : ∃ C : ℝ, ∀ s : ℝ, ‖oddSum n s‖ ≤ C := by
  refine ⟨∑ i ∈ Finset.range (n + 1), Classical.choose (profC_bound (2 * i + 1)), fun s => ?_⟩
  refine le_trans (norm_sum_le (Finset.range (n + 1)) (fun i => profC (2 * i + 1) s)) ?_
  exact Finset.sum_le_sum (fun i _ => (Classical.choose_spec (profC_bound (2 * i + 1))).2 s)

/-! ## Two truncation lemmas for interval integrals

Both are the elementary statement that integrating a one-sided indicator out of an interval
integral truncates the interval.  They are proved by converting to set integrals over `uIoc`,
where the intersection with `Ioi c` (resp. `Iio c`) is an exact interval. -/

/-- Truncating an interval integral at a lower limit: for `a ≤ c ≤ b`,
`∫_a^b (Ioi c).indicator f = ∫_c^b f`. -/
lemma integral_indicator_Ioi_of_le (a b c : ℝ) (hac : a ≤ c) (hcb : c ≤ b) (f : ℝ → ℝ) :
    ∫ x in a..b, (Set.Ioi c).indicator f x = ∫ x in c..b, f x := by
  have hab : a ≤ b := le_trans hac hcb
  have hset : Set.uIoc a b ∩ Set.Ioi c = Set.Ioc (max a c) b := by
    rw [Set.uIoc_of_le hab]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro ⟨⟨hax, hxb⟩, hcx⟩
      exact ⟨max_lt hax hcx, hxb⟩
    · rintro ⟨hmx, hxb⟩
      exact ⟨⟨lt_of_le_of_lt (le_max_left a c) hmx, hxb⟩,
        lt_of_le_of_lt (le_max_right a c) hmx⟩
  calc ∫ x in a..b, (Set.Ioi c).indicator f x
      = ∫ x in Set.uIoc a b, (Set.Ioi c).indicator f x := by
        rw [Set.uIoc_of_le hab, intervalIntegral.integral_of_le hab]
    _ = ∫ x in Set.uIoc a b ∩ Set.Ioi c, f x := by
        rw [← MeasureTheory.integral_indicator measurableSet_uIoc, Set.indicator_indicator,
          MeasureTheory.integral_indicator (measurableSet_uIoc.inter measurableSet_Ioi)]
    _ = ∫ x in Set.Ioc (max a c) b, f x := by rw [hset]
    _ = ∫ x in Set.Ioc c b, f x := by rw [max_eq_right hac]
    _ = ∫ x in c..b, f x := by rw [intervalIntegral.integral_of_le hcb]

/-- Truncating an interval integral at an upper limit: for `a ≤ c ≤ b`,
`∫_a^b (Iio c).indicator f = ∫_a^c f`. -/
lemma integral_indicator_Iio_of_le (a b c : ℝ) (hac : a ≤ c) (hcb : c ≤ b) (f : ℝ → ℝ) :
    ∫ x in a..b, (Set.Iio c).indicator f x = ∫ x in a..c, f x := by
  have hab : a ≤ b := le_trans hac hcb
  have hset : Set.uIoc a b ∩ Set.Iio c = Set.Ioo a c := by
    rw [Set.uIoc_of_le hab]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iio, Set.mem_Ioo]
    constructor
    · rintro ⟨⟨hax, -⟩, hxc⟩
      exact ⟨hax, hxc⟩
    · rintro ⟨hax, hxc⟩
      exact ⟨⟨hax, le_trans hxc.le hcb⟩, hxc⟩
  calc ∫ x in a..b, (Set.Iio c).indicator f x
      = ∫ x in Set.uIoc a b, (Set.Iio c).indicator f x := by
        rw [Set.uIoc_of_le hab, intervalIntegral.integral_of_le hab]
    _ = ∫ x in Set.uIoc a b ∩ Set.Iio c, f x := by
        rw [← MeasureTheory.integral_indicator measurableSet_uIoc, Set.indicator_indicator,
          MeasureTheory.integral_indicator (measurableSet_uIoc.inter measurableSet_Iio)]
    _ = ∫ x in Set.Ioo a c, f x := by rw [hset]
    _ = ∫ x in Set.Ioc a c, f x := by rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo]
    _ = ∫ x in a..c, f x := by rw [intervalIntegral.integral_of_le hac]

/-! ## Integrability of the kernel on the rectangle -/

/-- The kernel `(s,u) ↦ (1/s)·1_{s-1<u}·oddSum n u` is integrable on the rectangle
`(3, 2n+5] × (2, 2n+4]`: it is measurable, and bounded there by `(1/3)·C`. -/
lemma integrableOn_uncurry_kern (n : ℕ) {N M : ℝ} (hN : N = ((2 * n + 4 : ℕ) : ℝ))
    (hM : M = N + 1) :
    IntegrableOn (Function.uncurry (kern n))
      (Set.uIoc (3 : ℝ) M ×ˢ Set.uIoc (2 : ℝ) N) volume := by
  obtain ⟨C, hC⟩ := exists_bound_oddSum n
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (oddSum n 0)) (hC 0)
  have h2N : (2 : ℝ) ≤ N := by
    rw [hN]; exact_mod_cast (by omega : 2 ≤ 2 * n + 4)
  have h3M : (3 : ℝ) ≤ M := by rw [hM]; linarith
  have hfin : volume (Set.uIoc (3 : ℝ) M ×ˢ Set.uIoc (2 : ℝ) N) ≠ ⊤ := by
    rw [Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, Real.volume_uIoc, Real.volume_uIoc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hmeas : AEStronglyMeasurable (Function.uncurry (kern n)) volume := by
    refine Measurable.aestronglyMeasurable ?_
    have hfun : Function.uncurry (kern n)
        = fun p : ℝ × ℝ => (1 / p.1) * (if p.1 - 1 < p.2 then oddSum n p.2 else 0) := rfl
    rw [hfun]
    refine Measurable.mul ?_ ?_
    · exact measurable_const.div measurable_fst
    · refine Measurable.ite ?_ ((measurable_oddSum n).comp measurable_snd) measurable_const
      exact measurableSet_lt (measurable_fst.sub measurable_const) measurable_snd
  refine Measure.integrableOn_of_bounded hfin hmeas (M := (1 / 3) * C) ?_
  filter_upwards [self_mem_ae_restrict (measurableSet_uIoc.prod measurableSet_uIoc)] with p hp
  have hp1 : (3 : ℝ) < p.1 := by
    have h := hp.1
    rw [Set.uIoc_of_le h3M, Set.mem_Ioc] at h
    exact h.1
  have hspos : (0 : ℝ) < p.1 := lt_trans (by norm_num) hp1
  have hinv : p.1⁻¹ ≤ (1 : ℝ) / 3 := by
    simpa only [one_div] using
      one_div_le_one_div_of_le (a := (3 : ℝ)) (show (0 : ℝ) < 3 by norm_num) (le_of_lt hp1)
  have hodd : ‖(if p.1 - 1 < p.2 then oddSum n p.2 else (0 : ℝ))‖ ≤ C := by
    by_cases h : p.1 - 1 < p.2
    · rw [if_pos h]; exact hC p.2
    · rw [if_neg h]; simpa using hC0
  have hkern : Function.uncurry (kern n) p
      = p.1⁻¹ * (if p.1 - 1 < p.2 then oddSum n p.2 else 0) := by
    simp only [Function.uncurry, kern, one_div]
  rw [hkern, norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr (le_of_lt hspos))]
  exact mul_le_mul hinv hodd (norm_nonneg _) (by norm_num)

/-! ## The iterated integral computation -/

/-- **The mass identity, in parametrised form.**  For `N = 2n+4` and `M = N + 1`,

  `∫_3^M evenSum (n+1) = ∫_2^N oddSum n · log ((u+1)/3)`. -/
lemma integral_evenSum_succ_eq (n : ℕ) {N M : ℝ} (hN : N = ((2 * n + 4 : ℕ) : ℝ))
    (hM : M = N + 1) :
    (∫ s in (3 : ℝ)..M, evenSum (n + 1) s)
      = ∫ u in (2 : ℝ)..N, oddSum n u * Real.log ((u + 1) / 3) := by
  have h2N : (2 : ℝ) ≤ N := by
    rw [hN]; exact_mod_cast (by omega : 2 ≤ 2 * n + 4)
  have h3M : (3 : ℝ) ≤ M := by rw [hM]; linarith
  -- **Step 1.**  `evenSum (n+1) s = ∫_2^N kern s u` for `s ∈ [3,M]`.
  have step1 : (∫ s in (3 : ℝ)..M, evenSum (n + 1) s)
      = ∫ s in (3 : ℝ)..M, ∫ u in (2 : ℝ)..N, kern n s u := by
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    have hs' := hs
    rw [Set.uIcc_of_le h3M, Set.mem_Icc] at hs'
    obtain ⟨hs3, hsM⟩ := hs'
    have hle : s - 1 ≤ N := by rw [hM] at hsM; linarith
    have hge : (2 : ℝ) ≤ s - 1 := by linarith
    have hrec := evenSum_succ_mul n (show (1 : ℝ) ≤ s by linarith)
    have hif0 : (if s ≤ 3 then (3 : ℝ) - s else 0) = 0 := by
      by_cases h : s ≤ 3
      · rw [if_pos h]
        have hs3' : s = 3 := le_antisymm h hs3
        rw [hs3']; norm_num
      · rw [if_neg h]
    have hmax : max (s - 1) 2 = s - 1 := max_eq_left (by linarith)
    rw [hif0, hmax, zero_add, ← hN] at hrec
    -- the truncated integral over `[2,N]`
    have htrunc : (∫ u in (2 : ℝ)..N, (if s - 1 < u then oddSum n u else 0))
        = ∫ u in s - 1..N, oddSum n u := by
      rw [← integral_indicator_Ioi_of_le (2 : ℝ) N (s - 1) hge hle (oddSum n)]
      refine intervalIntegral.integral_congr (fun u _ => ?_)
      by_cases h : s - 1 < u
      · rw [if_pos h, Set.indicator_of_mem (show u ∈ Set.Ioi (s - 1) from h)]
      · rw [if_neg h, Set.indicator_of_notMem (show u ∉ Set.Ioi (s - 1) from h)]
    have hkern : (∫ u in (2 : ℝ)..N, kern n s u)
        = (1 / s) * ∫ u in (2 : ℝ)..N, (if s - 1 < u then oddSum n u else 0) := by
      simp only [kern]
      exact intervalIntegral.integral_const_mul _ _
    rw [hkern, htrunc]
    have hsne : s ≠ 0 := by linarith
    have : evenSum (n + 1) s = (∫ u in s - 1..N, oddSum n u) / s := by
      rw [eq_div_iff hsne]
      linarith [hrec]
    rw [this, div_eq_inv_mul, one_div]
  -- **Step 2.**  Fubini on the rectangle `(3,M] × (2,N]`.
  have step2 : (∫ s in (3 : ℝ)..M, ∫ u in (2 : ℝ)..N, kern n s u)
      = ∫ u in (2 : ℝ)..N, ∫ s in (3 : ℝ)..M, kern n s u :=
    intervalIntegral_intervalIntegral_swap (integrableOn_uncurry_kern n hN hM)
  -- **Step 3.**  The `s`-integral at fixed `u`.
  have step3 : (∫ u in (2 : ℝ)..N, ∫ s in (3 : ℝ)..M, kern n s u)
      = ∫ u in (2 : ℝ)..N, oddSum n u * Real.log ((u + 1) / 3) := by
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    have hu' := hu
    rw [Set.uIcc_of_le h2N, Set.mem_Icc] at hu'
    obtain ⟨hu2, huN⟩ := hu'
    have hge : (3 : ℝ) ≤ u + 1 := by linarith
    have hle : u + 1 ≤ M := by rw [hM]; linarith
    have hupos : (0 : ℝ) < u + 1 := by linarith
    -- pull the constant `oddSum n u` out of the integrand
    have hcongr : (∫ s in (3 : ℝ)..M, kern n s u)
        = (∫ s in (3 : ℝ)..M, (if s - 1 < u then (1 / s) else 0)) * oddSum n u := by
      have h1 : (∫ s in (3 : ℝ)..M, kern n s u)
          = ∫ s in (3 : ℝ)..M, (if s - 1 < u then (1 / s) else 0) * oddSum n u := by
        refine intervalIntegral.integral_congr (fun s _ => ?_)
        simp only [kern]
        by_cases h : s - 1 < u <;> simp [h]
      rw [h1, intervalIntegral.integral_mul_const]
    -- the truncated reciprocal integrates to `log ((u+1)/3)`
    have htrunc : (∫ s in (3 : ℝ)..M, (if s - 1 < u then (1 / s) else 0))
        = Real.log ((u + 1) / 3) := by
      have hpt : ∀ s : ℝ, (if s - 1 < u then (1 / s) else 0)
          = (Set.Iio (u + 1)).indicator (fun s => 1 / s) s := by
        intro s
        by_cases h : s - 1 < u
        · rw [if_pos h, Set.indicator_of_mem (show s ∈ Set.Iio (u + 1) by
            simp only [Set.mem_Iio]; linarith)]
        · rw [if_neg h, Set.indicator_of_notMem (show s ∉ Set.Iio (u + 1) by
            simp only [Set.mem_Iio]; linarith)]
      rw [intervalIntegral.integral_congr (fun s _ => hpt s)]
      rw [integral_indicator_Iio_of_le (3 : ℝ) M (u + 1) hge hle (fun s => 1 / s)]
      exact integral_one_div_of_pos (by norm_num) hupos
    rw [hcongr, htrunc, mul_comm]
  rw [step1, step2, step3]

theorem mass_identity (n : ℕ) :
    Tv (n + 1)
      = ∫ u in (2 : ℝ)..((2 * n + 4 : ℕ) : ℝ), oddSum n u * Real.log ((u + 1) / 3) := by
  have hM : ((2 * (n + 1) + 3 : ℕ) : ℝ) = ((2 * n + 5 : ℕ) : ℝ) := by
    have : 2 * (n + 1) + 3 = 2 * n + 5 := by omega
    exact_mod_cast this
  have hMN : ((2 * n + 5 : ℕ) : ℝ) = ((2 * n + 4 : ℕ) : ℝ) + 1 := by
    have : 2 * n + 5 = (2 * n + 4) + 1 := by omega
    exact_mod_cast this
  rw [Tv, hM]
  exact integral_evenSum_succ_eq n rfl hMN

end

end Work.NumberTheory.Chen.APSwitchUpper
