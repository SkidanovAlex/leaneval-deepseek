import Mathlib
import Submission.Work.ZeroDensity.Ingham.fourthMomentDefs
import Submission.Work.Analysis.Integral.norm_intervalIntegral_exp_I_mul_le
import Submission.Work.Analysis.Complex.cpow_nat_eq_exp
import Submission.Work.Analysis.Real.log_diff_ge_div
import Submission.Commons.Analysis.Complex.intervalIntegral_re_comm
import Submission.Work.ZeroDensity.Montgomery.divisorSqSum
import Submission.Work.ZeroDensity.Montgomery.divisorsCardDivSum_le
import Submission.Work.ZeroDensity.Ingham.divPairKernelBound
import Submission.Work.ZeroDensity.Ingham.zetaAfeTruncationSharp
import Submission.Work.ZeroDensity.Ingham.stepPairIntegralKernel
import Submission.Work.ZeroDensity.Ingham.sumGroupByPairProd
import Submission.Work.ZeroDensity.Ingham.twoPiSqLeIffFloor

/-!
# The integral fourth moment of `ζ` on the critical line

We prove Ingham's bound `∫_0^T ‖ζ(1/2+it)‖^4 dt ≪ T (log T)^4`.

The two inputs are

* the sharp truncated approximate functional equation for `ζ`
  (`Work.ZeroDensity.Ingham.zetaAfeTruncationSharp`), which bounds `‖ζ(1/2+it)‖` by
  `1 + ‖Σ_{n ≤ ⌊√(t/2π)⌋+1} n^{-(1/2+it)}‖`, and
* the elementary fourth-moment bound for the *step-truncated* Dirichlet polynomial
  `stepPoly M t = Σ_{n ≤ M} stepTerm n t` (definitions in
  `Work.ZeroDensity.Ingham.fourthMomentDefs`), whose length is tied to `t` through the step
  functions `stepTerm n t = 1_{t ≥ 2π(n-1)²} n^{-(1/2+it)}`.

The second is the heart of the proof: expanding `‖stepPoly M t‖^4 = ‖stepPoly M t ^ 2‖^2` into a
double sum over index pairs `p = (m, m')`, grouping the pairs by the product `K = m m'`, and
integrating the exponentials `e^{it (log K' - log K)}` over the interval where the step functions
are positive gives

`∫_0^T ‖stepPoly M t‖^4 dt ≤ Σ_{K,K' ≤ M²} τ(K)τ(K') · pairKernel T K K'`,

whose diagonal part is `≤ T Σ_{K ≤ M²} τ(K)²/K ≪ T (log T)^4`
(`Work.ZeroDensity.Montgomery.divisorSqSum`) and whose off-diagonal part is
`≤ 2 Σ_{K ≠ K' ≤ M²} τ(K)τ(K')max(K,K')/(√(KK')|K-K'|) ≪ T (log T)^4`
(`Work.ZeroDensity.Ingham.divPairKernelBound`, using
`|log K - log K'| ≥ |K-K'|/\max(K,K')`).
-/

namespace Work.ZeroDensity.Ingham

open scoped BigOperators
open MeasureTheory

noncomputable section

lemma measurable_stepPair (m n : ℕ) : Measurable (stepPair m n) := by
  unfold stepPair
  refine Measurable.ite ?_ ?_ measurable_const
  · exact (measurableSet_le measurable_const measurable_id).inter
      (measurableSet_le measurable_const measurable_id)
  · fun_prop

lemma measurable_stepPair_mul_conj (m n m' n' : ℕ) :
    Measurable (fun t : ℝ => stepPair m n t * (starRingEnd ℂ) (stepPair m' n' t)) :=
  (measurable_stepPair m n).mul
    ((Complex.continuous_conj.measurable.comp (measurable_stepPair m' n')))

lemma norm_stepPair_le (m n : ℕ) (t : ℝ) :
    ‖stepPair m n t‖ ≤ ((Real.sqrt ((m:ℝ)*(n:ℝ)))⁻¹) := by
  rw [stepPair_apply]
  split_ifs with h
  · rw [norm_mul,
      show -(Complex.I * ((t * Real.log ((m:ℝ)*(n:ℝ)) : ℝ) : ℂ))
        = ((-(t * Real.log ((m:ℝ)*(n:ℝ))) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one, ← Complex.ofReal_inv, Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  · rw [norm_zero]
    exact inv_nonneg.mpr (Real.sqrt_nonneg _)

lemma norm_stepPair_mul_conj_le (m n m' n' : ℕ) (t : ℝ) :
    ‖stepPair m n t * (starRingEnd ℂ) (stepPair m' n' t)‖
      ≤ ((Real.sqrt (((m:ℝ)*(n:ℝ)) * ((m':ℝ)*(n':ℝ))))⁻¹) := by
  rw [norm_mul, Complex.norm_conj]
  have h3 : ((Real.sqrt ((m:ℝ)*(n:ℝ)))⁻¹) * ((Real.sqrt ((m':ℝ)*(n':ℝ)))⁻¹)
      = ((Real.sqrt (((m:ℝ)*(n:ℝ)) * ((m':ℝ)*(n':ℝ))))⁻¹) := by
    rw [Real.sqrt_mul (mul_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n)), mul_inv]
  have h1 := norm_stepPair_le m n t
  have h2 := norm_stepPair_le m' n' t
  calc ‖stepPair m n t‖ * ‖stepPair m' n' t‖
      ≤ ((Real.sqrt ((m:ℝ)*(n:ℝ)))⁻¹) * ((Real.sqrt ((m':ℝ)*(n':ℝ)))⁻¹) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = ((Real.sqrt (((m:ℝ)*(n:ℝ)) * ((m':ℝ)*(n':ℝ))))⁻¹) := h3

/-- A measurable complex function bounded by a nonnegative constant is interval integrable. -/
lemma intervalIntegrable_of_measurable_of_norm_le {T c : ℝ} (hc : 0 ≤ c) {f : ℝ → ℂ}
    (hmeas : Measurable f) (hb : ∀ t, ‖f t‖ ≤ c) :
    IntervalIntegrable f MeasureTheory.volume 0 T := by
  refine IntervalIntegrable.mono_fun (f := fun _ : ℝ => (c : ℂ))
    (intervalIntegrable_const (c := (c : ℂ))) hmeas.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Complex.norm_real, Real.norm_of_nonneg hc]
  exact hb x

/-- The real part of a measurable complex function bounded by a constant is interval
integrable (as a real-valued function). -/
lemma intervalIntegrable_re_of_measurable_of_norm_le {T c : ℝ} (hc : 0 ≤ c) {f : ℝ → ℂ}
    (hmeas : Measurable f) (hb : ∀ t, ‖f t‖ ≤ c) :
    IntervalIntegrable (fun t => (f t).re) MeasureTheory.volume 0 T := by
  refine IntervalIntegrable.mono_fun (f := fun _ : ℝ => (c : ℂ))
    (intervalIntegrable_const (c := (c : ℂ)))
    (Complex.continuous_re.measurable.comp hmeas).aestronglyMeasurable ?_
  filter_upwards with x
  rw [Complex.norm_real, Real.norm_of_nonneg hc]
  exact le_trans (Complex.abs_re_le_norm _) (hb x)

lemma intervalIntegrable_stepPair_mul_conj (T : ℝ) (p q : ℕ × ℕ)
    (hp1 : 1 ≤ p.1) (hp2 : 1 ≤ p.2) (hq1 : 1 ≤ q.1) (hq2 : 1 ≤ q.2) :
    IntervalIntegrable (fun t : ℝ => stepPair p.1 p.2 t * (starRingEnd ℂ) (stepPair q.1 q.2 t))
      MeasureTheory.volume 0 T := by
  have hc : (0:ℝ) ≤ (Real.sqrt (((p.1:ℝ) * (p.2:ℝ)) * ((q.1:ℝ) * (q.2:ℝ))))⁻¹ :=
    inv_nonneg.mpr (Real.sqrt_nonneg _)
  refine intervalIntegrable_of_measurable_of_norm_le
    (T := T) (c := (Real.sqrt (((p.1:ℝ) * (p.2:ℝ)) * ((q.1:ℝ) * (q.2:ℝ))))⁻¹) hc
    (measurable_stepPair_mul_conj _ _ _ _) ?_
  intro t
  simpa using norm_stepPair_mul_conj_le p.1 p.2 q.1 q.2 t

/-- The number of pairs of the box with a given product is at most the number of divisors. -/
theorem card_fiber_pairProd_le (M K : ℕ) :
    ((pairBox M).filter (fun p => pairProd p = K)).card ≤ (Nat.divisors K).card := by
  refine Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.1) ?_ ?_
  · rintro ⟨a1, a2⟩ hp
    simp only [Finset.mem_coe, Finset.mem_filter, pairBox_apply, Finset.mem_product,
      Finset.mem_Icc] at hp
    obtain ⟨⟨⟨ha1, _⟩, ⟨ha2, _⟩⟩, hprod⟩ := hp
    rw [pairProd_apply] at hprod
    refine Nat.mem_divisors.mpr ⟨⟨a2, hprod.symm⟩, ?_⟩
    rw [← hprod]
    exact (Nat.mul_pos (by omega) (by omega)).ne'
  · rintro ⟨a1, a2⟩ hp ⟨c1, c2⟩ hq hpq
    simp only [Finset.mem_coe, Finset.mem_filter, pairBox_apply, Finset.mem_product,
      Finset.mem_Icc] at hp hq hpq
    obtain ⟨⟨⟨ha1, _⟩, ⟨ha2, _⟩⟩, hprod⟩ := hp
    obtain ⟨⟨⟨hc1, _⟩, ⟨hc2, _⟩⟩, hqprod⟩ := hq
    obtain rfl := hpq
    rw [pairProd_apply] at hprod hqprod
    have h3 : a2 = c2 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < a1) (hprod.trans hqprod.symm)
    rw [h3]

/-- The summand written as a complex power (the form in which the approximate functional equation
produces it). -/
theorem stepTerm_eq_cpow (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    stepTerm n t = if 2 * Real.pi * ((n : ℝ) - 1) ^ 2 ≤ t then
      (n : ℂ) ^ (-((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) else 0 := by
  have hn0' : (0:ℝ) < (n:ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  have hn0 : (n : ℂ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]; omega
  have h1 : (n : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt (n : ℝ) : ℂ)) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_natCast n,
      ← Complex.ofReal_cpow (le_of_lt hn0'), Real.sqrt_eq_rpow]
  have hsqrt : ((Real.sqrt (n : ℝ) : ℂ))⁻¹ = (n : ℂ) ^ (-(1 / 2 : ℂ)) := by
    rw [Complex.cpow_neg, h1]
  have hexp : Complex.exp (-(Complex.I * ((t * Real.log (n : ℝ) : ℝ) : ℂ)))
      = (n : ℂ) ^ (-((t : ℂ) * Complex.I)) := by
    rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.ofReal_natCast n,
      ← Complex.ofReal_log (show (0:ℝ) ≤ (n:ℝ) by positivity)]
    congr 1
    push_cast
    ring
  rw [stepTerm_apply]
  split_ifs with h
  · rw [hsqrt, hexp, ← Complex.cpow_add _ _ hn0]
    congr 1
    ring
  · rfl

/-- The step polynomial evaluated at `t ≥ 0` is the truncated Dirichlet sum, as long as the
truncation index is at most `M`. -/
theorem stepPoly_eq_dirichletSum (M : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (hM : ⌊Real.sqrt (t / (2 * Real.pi))⌋₊ + 1 ≤ M) :
    stepPoly M t = ∑ n ∈ Finset.Icc 1 (⌊Real.sqrt (t / (2 * Real.pi))⌋₊ + 1),
      (n : ℂ) ^ (-((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) := by
  have h1 : stepPoly M t
      = ∑ n ∈ (Finset.Icc 1 M).filter (fun n : ℕ => 2 * Real.pi * ((n : ℝ) - 1) ^ 2 ≤ t),
          (n : ℂ) ^ (-((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) := by
    rw [stepPoly, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [stepTerm_eq_cpow n (Finset.mem_Icc.mp hn).1 t]
  have hset : (Finset.Icc 1 M).filter (fun n : ℕ => 2 * Real.pi * ((n : ℝ) - 1) ^ 2 ≤ t)
      = Finset.Icc 1 (⌊Real.sqrt (t / (2 * Real.pi))⌋₊ + 1) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hn1, _⟩, hc⟩
      exact ⟨hn1, (twoPiSqLeIffFloor n hn1 t ht).mp hc⟩
    · rintro ⟨hn1, hN⟩
      exact ⟨⟨hn1, le_trans hN hM⟩, (twoPiSqLeIffFloor n hn1 t ht).mpr hN⟩
  rw [h1, hset]

/-- The kernel is bounded by the sum of its diagonal and oscillatory parts. -/
lemma pairKernel_le_split (T : ℝ) (K K' : ℕ) :
    pairKernel T K K' ≤ (if K = K' then T / (K : ℝ) else 0)
      + 2 * max (K : ℝ) (K' : ℝ) / (Real.sqrt ((K : ℝ) * (K' : ℝ)) * |(K : ℝ) - (K' : ℝ)|) := by
  rw [pairKernel_apply]
  by_cases h : K = K'
  · rw [if_pos h, if_pos h]
    have hy : (0:ℝ) ≤ 2 * max (K:ℝ) (K':ℝ)
        / (Real.sqrt ((K:ℝ) * (K':ℝ)) * |(K:ℝ) - (K':ℝ)|) :=
      div_nonneg (by
        have h1 : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg K
        have h2 : (0:ℝ) ≤ max (K:ℝ) (K':ℝ) := le_trans h1 (le_max_left _ _)
        linarith) (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
    linarith
  · rw [if_neg h, if_neg h, zero_add]

/-- The kernel is nonnegative for `T ≥ 0`. -/
lemma pairKernel_nonneg {T : ℝ} (hT : 0 ≤ T) {K : ℕ} (hK : 1 ≤ K) (K' : ℕ) :
    0 ≤ pairKernel T K K' := by
  rw [pairKernel_apply]
  by_cases h : K = K'
  · rw [if_pos h]
    positivity
  · rw [if_neg h]
    refine div_nonneg ?_ (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
    have h1 : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg K
    have h2 : (0:ℝ) ≤ max (K:ℝ) (K':ℝ) := le_trans h1 (le_max_left _ _)
    linarith

/-- The modulus of a pair product is at most one. -/
lemma norm_stepPair_mul_conj_le_one (m n m' n' : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hm' : 1 ≤ m')
    (hn' : 1 ≤ n') (t : ℝ) :
    ‖stepPair m n t * (starRingEnd ℂ) (stepPair m' n' t)‖ ≤ 1 := by
  refine le_trans (norm_stepPair_mul_conj_le m n m' n' t) ?_
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hm1' : (1:ℝ) ≤ (m':ℝ) := by exact_mod_cast hm'
  have hn1' : (1:ℝ) ≤ (n':ℝ) := by exact_mod_cast hn'
  have hge : (1:ℝ) ≤ ((m:ℝ)*(n:ℝ)) * ((m':ℝ)*(n':ℝ)) := by
    have h1 : (1:ℝ) ≤ (m:ℝ) * (n:ℝ) := by nlinarith
    have h2 : (1:ℝ) ≤ (m':ℝ) * (n':ℝ) := by nlinarith
    nlinarith
  have hge2 : (1:ℝ) ≤ Real.sqrt (((m:ℝ)*(n:ℝ)) * ((m':ℝ)*(n':ℝ))) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hge
  exact inv_le_one_of_one_le₀ hge2

/-- The inner (`q`-summed) real part is interval integrable. -/
lemma intervalIntegrable_innerSum_re (M : ℕ) (T : ℝ) (p : ℕ × ℕ) (hp : p ∈ pairBox M) :
    IntervalIntegrable (fun t : ℝ => ∑ q ∈ pairBox M,
      (stepPair p.1 p.2 t * (starRingEnd ℂ) (stepPair q.1 q.2 t)).re)
      MeasureTheory.volume 0 T := by
  have hbox : ∀ q ∈ pairBox M, 1 ≤ q.1 ∧ 1 ≤ q.2 := by
    intro q hq
    rw [pairBox_apply, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hq
    exact ⟨hq.1.1, hq.2.1⟩
  have hp' := hbox p hp
  refine IntervalIntegrable.mono_fun (f := fun _ : ℝ => ((((pairBox M).card : ℝ)) : ℂ))
    (intervalIntegrable_const (c := ((((pairBox M).card : ℝ)) : ℂ))) ?_ ?_
  · exact (Finset.measurable_sum _ (fun q hq => (Complex.continuous_re.measurable.comp
      (measurable_stepPair_mul_conj p.1 p.2 q.1 q.2)))).aestronglyMeasurable
  · filter_upwards with t
    rw [Real.norm_eq_abs, Complex.norm_real,
      Real.norm_of_nonneg (Nat.cast_nonneg ((pairBox M).card))]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    calc ∑ q ∈ pairBox M, |(stepPair p.1 p.2 t * (starRingEnd ℂ) (stepPair q.1 q.2 t)).re|
        ≤ ∑ _q ∈ pairBox M, (1:ℝ) := Finset.sum_le_sum (fun q hq => ?_)
      _ = (((pairBox M).card : ℕ) : ℝ) := by simp
    · exact le_trans (Complex.abs_re_le_norm _) (norm_stepPair_mul_conj_le_one p.1 p.2 q.1 q.2
        hp'.1 hp'.2 (hbox q hq).1 (hbox q hq).2 t)

/-- **The fourth moment of the step-truncated Dirichlet polynomial.**  For `T ≥ 2`, `M ≥ 1` with
`M² ≤ 4T`, the integral of `‖stepPoly M t‖⁴` over `[0,T]` is `≪ T (log T)^4`. -/
theorem stepPoly_fourthMoment :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : ℝ) (M : ℕ), 1 ≤ M → (M : ℝ) ^ 2 ≤ 4 * T → 2 ≤ T →
      (∫ t in (0:ℝ)..T, ‖stepPoly M t‖ ^ 4) ≤ C * T * (Real.log T) ^ 4 := by
  obtain ⟨C2, hC2pos, hC2⟩ := divPairKernelBound
  obtain ⟨C1, hC1pos, hC1⟩ := _root_.Work.ZeroDensity.Montgomery.divisorSqSum
  refine ⟨256 * C1 + 648 * C2 + 100, by positivity, ?_⟩
  intro T M hM1 hMsq hT
  have hT0 : (0:ℝ) ≤ T := by linarith
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  -- trivial case `M = 1`
  rcases eq_or_lt_of_le hM1 with hM | hM
  · subst hM
    have hstep : ∀ t ∈ Set.Icc (0:ℝ) T, stepPoly 1 t = 1 := by
      intro t ht
      rw [stepPoly, Finset.Icc_self, Finset.sum_singleton, stepTerm_apply]
      have hcond : 2 * Real.pi * (((1:ℕ):ℝ) - 1) ^ 2 ≤ t := by
        norm_num
        linarith [ht.1]
      rw [if_pos hcond]
      norm_num
    have hval : (∫ t in (0:ℝ)..T, ‖stepPoly 1 t‖ ^ 4) = T := by
      have hcongr : (∫ t in (0:ℝ)..T, ‖stepPoly 1 t‖ ^ 4) = ∫ t in (0:ℝ)..T, (1:ℝ) := by
        refine intervalIntegral.integral_congr (fun t ht => ?_)
        rw [Set.uIcc_of_le hT0] at ht
        rw [hstep t ht]
        norm_num
      rw [hcongr, intervalIntegral.integral_const]
      simp
    rw [hval]
    have hconst : (1:ℝ) ≤ (256 * C1 + 648 * C2 + 100) * (Real.log T) ^ 4 := by
      have hlog2 : (0.5:ℝ) ≤ Real.log T := by
        have h2 : (0.5:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
        exact le_trans h2 (Real.log_le_log (by norm_num) hT)
      have h4 : (0.0625:ℝ) ≤ (Real.log T) ^ 4 := by
        have h5 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 0.5) hlog2 4
        norm_num at h5 ⊢
        linarith [h5]
      nlinarith [hC1pos, hC2pos, h4]
    calc T = 1 * T := by ring
      _ ≤ ((256 * C1 + 648 * C2 + 100) * (Real.log T) ^ 4) * T :=
          mul_le_mul_of_nonneg_right hconst hT0
      _ = (256 * C1 + 648 * C2 + 100) * T * (Real.log T) ^ 4 := by ring
  -- main case `M ≥ 2`
  have hM2 : 2 ≤ M := hM
  set Y : ℕ := M * M with hYdef
  have hY1 : 1 ≤ Y := by
    have : 1 * 1 ≤ M * M := Nat.mul_le_mul hM1 hM1
    simpa [Y] using this
  have hY2 : 2 ≤ Y := by
    have : 2 * 2 ≤ M * M := Nat.mul_le_mul hM2 hM2
    have h4 : 4 ≤ M * M := by simpa using this
    omega
  have hYR : (Y : ℝ) = (M : ℝ) ^ 2 := by rw [hYdef]; push_cast; ring
  have hY4T : (Y : ℝ) ≤ 4 * T := by rw [hYR]; exact hMsq
  -- integrability of the pair products
  have hbox : ∀ p ∈ pairBox M, 1 ≤ p.1 ∧ 1 ≤ p.2 := by
    intro p hp
    rw [pairBox_apply, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
    exact ⟨hp.1.1, hp.2.1⟩
  have hii : ∀ p ∈ pairBox M, ∀ q ∈ pairBox M,
      IntervalIntegrable (fun t : ℝ => stepPair p.1 p.2 t * (starRingEnd ℂ) (stepPair q.1 q.2 t))
        MeasureTheory.volume 0 T := by
    intro p hp q hq
    exact intervalIntegrable_stepPair_mul_conj T p q (hbox p hp).1 (hbox p hp).2
      (hbox q hq).1 (hbox q hq).2
  have hii1 : ∀ p ∈ pairBox M, ∀ q ∈ pairBox M,
      IntervalIntegrable (fun t : ℝ =>
        (stepPair p.1 p.2 t * (starRingEnd ℂ) (stepPair q.1 q.2 t)).re)
        MeasureTheory.volume 0 T := by
    intro p hp q hq
    refine intervalIntegrable_re_of_measurable_of_norm_le (c := 1) (by norm_num)
      (measurable_stepPair_mul_conj _ _ _ _) (fun t => ?_)
    exact norm_stepPair_mul_conj_le_one p.1 p.2 q.1 q.2 (hbox p hp).1 (hbox p hp).2
      (hbox q hq).1 (hbox q hq).2 t
  -- pointwise expansion
  have hpt : ∀ t : ℝ, ‖stepPoly M t‖ ^ 4
      = (∑ p ∈ pairBox M, ∑ q ∈ pairBox M,
          stepPair p.1 p.2 t * (starRingEnd ℂ) (stepPair q.1 q.2 t)).re := by
    intro t
    have hsq : (stepPoly M t) ^ 2 = ∑ p ∈ pairBox M, stepPair p.1 p.2 t := by
      rw [stepPoly, sq, Finset.sum_mul_sum, pairBox, Finset.sum_product]
      refine Finset.sum_congr rfl (fun m hm => Finset.sum_congr rfl (fun n hn => ?_))
      exact stepTerm_mul m n (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hn).1 t
    have hw : ∀ w : ℂ, ‖w‖ ^ 2 = (w * (starRingEnd ℂ) w).re := by
      intro w
      rw [← Complex.normSq_eq_norm_sq, ← Complex.ofReal_re (Complex.normSq w), Complex.mul_conj]
    rw [show ‖stepPoly M t‖ ^ 4 = ‖(stepPoly M t) ^ 2‖ ^ 2 by rw [norm_pow]; ring, hsq,
      hw, map_sum, Finset.sum_mul_sum, Complex.re_sum]
  -- the integral of the expansion
  have hInt : (∫ t in (0:ℝ)..T, ‖stepPoly M t‖ ^ 4)
      = ∑ p ∈ pairBox M, ∑ q ∈ pairBox M,
          (∫ t in (0:ℝ)..T, stepPair p.1 p.2 t * (starRingEnd ℂ) (stepPair q.1 q.2 t)).re := by
    rw [intervalIntegral.integral_congr (fun t _ => hpt t)]
    have hfun : (fun t : ℝ => (∑ p ∈ pairBox M, ∑ q ∈ pairBox M,
          stepPair p.1 p.2 t * (starRingEnd ℂ) (stepPair q.1 q.2 t)).re)
        = fun t : ℝ => ∑ p ∈ pairBox M, ∑ q ∈ pairBox M,
            (stepPair p.1 p.2 t * (starRingEnd ℂ) (stepPair q.1 q.2 t)).re := by
      funext t
      simp only [Complex.re_sum]
    rw [hfun]
    have hstep1 : (∫ t in (0:ℝ)..T, ∑ p ∈ pairBox M, ∑ q ∈ pairBox M,
          (stepPair p.1 p.2 t * (starRingEnd ℂ) (stepPair q.1 q.2 t)).re)
        = ∑ p ∈ pairBox M, ∫ t in (0:ℝ)..T, ∑ q ∈ pairBox M,
            (stepPair p.1 p.2 t * (starRingEnd ℂ) (stepPair q.1 q.2 t)).re :=
      intervalIntegral.integral_finsetSum (fun p hp => intervalIntegrable_innerSum_re M T p hp)
    rw [hstep1]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have hstep2 : (∫ t in (0:ℝ)..T, ∑ q ∈ pairBox M,
          (stepPair p.1 p.2 t * (starRingEnd ℂ) (stepPair q.1 q.2 t)).re)
        = ∑ q ∈ pairBox M, ∫ t in (0:ℝ)..T,
            (stepPair p.1 p.2 t * (starRingEnd ℂ) (stepPair q.1 q.2 t)).re :=
      intervalIntegral.integral_finsetSum (fun q hq => hii1 p hp q hq)
    rw [hstep2]
    exact Finset.sum_congr rfl (fun q hq => intervalIntegral.intervalIntegral_re (hii p hp q hq))
  -- the bound by the pair kernel
  have hK : (∫ t in (0:ℝ)..T, ‖stepPoly M t‖ ^ 4)
      ≤ ∑ p ∈ pairBox M, ∑ q ∈ pairBox M, pairKernel T (pairProd p) (pairProd q) := by
    rw [hInt]
    refine Finset.sum_le_sum (fun p hp => Finset.sum_le_sum (fun q hq => ?_))
    refine le_trans (Complex.re_le_norm _) ?_
    exact stepPairIntegralKernel T hT0 p q (hbox p hp).1 (hbox p hp).2 (hbox q hq).1 (hbox q hq).2
  refine le_trans hK ?_
  -- group by products
  rw [sumGroupByPairProd M (fun K K' => pairKernel T K K')]
  -- relax the multiplicities to the divisor function
  have hrelax : (∑ K ∈ Finset.Icc 1 Y, ∑ K' ∈ Finset.Icc 1 Y,
        (((pairBox M).filter (fun p => pairProd p = K)).card : ℝ) *
          (((pairBox M).filter (fun p => pairProd p = K')).card : ℝ) * pairKernel T K K')
      ≤ ∑ K ∈ Finset.Icc 1 Y, ∑ K' ∈ Finset.Icc 1 Y,
          (((Nat.divisors K).card : ℝ) * ((Nat.divisors K').card : ℝ) * pairKernel T K K') := by
    refine Finset.sum_le_sum (fun K hK' => Finset.sum_le_sum (fun K' hK'' => ?_))
    have hK1 : 1 ≤ K := (Finset.mem_Icc.mp hK').1
    have h1 : (((pairBox M).filter (fun p => pairProd p = K)).card : ℝ)
        ≤ ((Nat.divisors K).card : ℝ) := by
      exact_mod_cast card_fiber_pairProd_le M K
    have h2 : (((pairBox M).filter (fun p => pairProd p = K')).card : ℝ)
        ≤ ((Nat.divisors K').card : ℝ) := by
      exact_mod_cast card_fiber_pairProd_le M K'
    have h3 : 0 ≤ pairKernel T K K' := pairKernel_nonneg hT0 hK1 K'
    have hc2 : (0:ℝ) ≤ (((pairBox M).filter (fun p => pairProd p = K')).card : ℝ) :=
      Nat.cast_nonneg _
    have ht1 : (0:ℝ) ≤ ((Nat.divisors K).card : ℝ) := Nat.cast_nonneg _
    have key : (((pairBox M).filter (fun p => pairProd p = K)).card : ℝ)
          * (((pairBox M).filter (fun p => pairProd p = K')).card : ℝ)
        ≤ ((Nat.divisors K).card : ℝ) * ((Nat.divisors K').card : ℝ) :=
      mul_le_mul h1 h2 hc2 ht1
    exact mul_le_mul_of_nonneg_right key h3
  refine le_trans hrelax ?_
  -- logarithms
  have hYlog : Real.log (Y : ℝ) ≤ 3 * Real.log T := by
    have hYpos : (0:ℝ) < (Y:ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hY1)
    have h1 : Real.log (Y:ℝ) ≤ Real.log (4 * T) := Real.log_le_log hYpos hY4T
    have h2 : Real.log (4 * T) = Real.log 4 + Real.log T := Real.log_mul (by norm_num) (by linarith)
    have h3 : Real.log 4 ≤ 2 * Real.log T := by
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num
      rw [h4]
      exact mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num) hT) (by norm_num)
    rw [h2] at h1
    linarith
  have h2Ylog : Real.log (2 * (Y:ℝ)) ≤ 4 * Real.log T := by
    have hpos : (0:ℝ) < 2 * (Y:ℝ) := by positivity
    have h1 : Real.log (2 * (Y:ℝ)) ≤ Real.log (8 * T) := Real.log_le_log hpos (by linarith)
    have h2 : Real.log (8 * T) = Real.log 8 + Real.log T := Real.log_mul (by norm_num) (by linarith)
    have h3 : Real.log 8 ≤ 3 * Real.log T := by
      have h8 : Real.log 8 = 3 * Real.log 2 := by
        rw [show (8:ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
        norm_num
      rw [h8]
      exact mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num) hT) (by norm_num)
    rw [h2] at h1
    linarith
  have hpow256 : Real.log (2 * (Y:ℝ)) ^ 4 ≤ 256 * (Real.log T) ^ 4 := by
    have hnn : (0:ℝ) ≤ Real.log (2 * (Y:ℝ)) := by
      refine Real.log_nonneg ?_
      have : (1:ℝ) ≤ (Y:ℝ) := by exact_mod_cast hY1
      linarith
    calc Real.log (2 * (Y:ℝ)) ^ 4 ≤ (4 * Real.log T) ^ 4 := pow_le_pow_left₀ hnn h2Ylog 4
      _ = 256 * (Real.log T) ^ 4 := by ring
  have hpow81 : (Real.log (Y:ℝ)) ^ 4 ≤ 81 * (Real.log T) ^ 4 := by
    have hnn : (0:ℝ) ≤ Real.log (Y:ℝ) := Real.log_nonneg (by exact_mod_cast hY1)
    calc Real.log (Y:ℝ) ^ 4 ≤ (3 * Real.log T) ^ 4 := pow_le_pow_left₀ hnn hYlog 4
      _ = 81 * (Real.log T) ^ 4 := by ring
  -- the two parts of the kernel
  have hdiag : (∑ K ∈ Finset.Icc 1 Y, ∑ K' ∈ Finset.Icc 1 Y,
        ((Nat.divisors K).card : ℝ) * ((Nat.divisors K').card : ℝ)
          * (if K = K' then T / (K : ℝ) else 0)) ≤ 256 * C1 * (T * (Real.log T) ^ 4) := by
    have hd : (∑ K ∈ Finset.Icc 1 Y, ∑ K' ∈ Finset.Icc 1 Y,
        ((Nat.divisors K).card : ℝ) * ((Nat.divisors K').card : ℝ)
          * (if K = K' then T / (K : ℝ) else 0))
        = T * ∑ K ∈ Finset.Icc 1 Y, ((Nat.divisors K).card : ℝ) ^ 2 / (K : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun K hK' => ?_)
      have h1 : ∀ K' : ℕ, ((Nat.divisors K).card : ℝ) * ((Nat.divisors K').card : ℝ)
            * (if K = K' then T / (K : ℝ) else 0)
          = (if K = K' then ((Nat.divisors K).card : ℝ) * ((Nat.divisors K').card : ℝ)
              * (T / (K : ℝ)) else 0) := by
        intro K'; by_cases h : K = K'
        · rw [if_pos h, if_pos h]
        · rw [if_neg h, if_neg h, mul_zero]
      simp only [h1]
      rw [Finset.sum_ite_eq]
      rw [if_pos hK']
      ring
    rw [hd]
    calc T * (∑ K ∈ Finset.Icc 1 Y, ((Nat.divisors K).card : ℝ) ^ 2 / (K : ℝ))
        ≤ T * (C1 * Real.log (2 * (Y:ℝ)) ^ 4) := mul_le_mul_of_nonneg_left (hC1 Y hY1) hT0
      _ = C1 * (T * Real.log (2 * (Y:ℝ)) ^ 4) := by ring
      _ ≤ C1 * (T * (256 * (Real.log T) ^ 4)) := by
          refine mul_le_mul_of_nonneg_left ?_ hC1pos.le
          exact mul_le_mul_of_nonneg_left hpow256 hT0
      _ = 256 * C1 * (T * (Real.log T) ^ 4) := by ring
  have hoff : (∑ K ∈ Finset.Icc 1 Y, ∑ K' ∈ Finset.Icc 1 Y,
        ((Nat.divisors K).card : ℝ) * ((Nat.divisors K').card : ℝ)
          * (2 * max (K : ℝ) (K' : ℝ)
            / (Real.sqrt ((K : ℝ) * (K' : ℝ)) * |(K : ℝ) - (K' : ℝ)|)))
      ≤ 648 * C2 * (T * (Real.log T) ^ 4) := by
    have hrw : (∑ K ∈ Finset.Icc 1 Y, ∑ K' ∈ Finset.Icc 1 Y,
          ((Nat.divisors K).card : ℝ) * ((Nat.divisors K').card : ℝ)
            * (2 * max (K : ℝ) (K' : ℝ)
              / (Real.sqrt ((K : ℝ) * (K' : ℝ)) * |(K : ℝ) - (K' : ℝ)|)))
        = 2 * ∑ K ∈ Finset.Icc 1 Y, ∑ K' ∈ Finset.Icc 1 Y,
            ((Nat.divisors K).card : ℝ) * ((Nat.divisors K').card : ℝ) * max (K : ℝ) (K' : ℝ)
              / (Real.sqrt ((K : ℝ) * (K' : ℝ)) * |(K : ℝ) - (K' : ℝ)|) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun K hK' => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun K' hK'' => ?_)
      ring
    rw [hrw]
    have hb : (∑ K ∈ Finset.Icc 1 Y, ∑ K' ∈ Finset.Icc 1 Y,
            ((Nat.divisors K).card : ℝ) * ((Nat.divisors K').card : ℝ) * max (K : ℝ) (K' : ℝ)
              / (Real.sqrt ((K : ℝ) * (K' : ℝ)) * |(K : ℝ) - (K' : ℝ)|))
        ≤ C2 * (Y:ℝ) * Real.log (Y:ℝ) ^ 4 := hC2 Y hY2
    have hlogYnn : (0:ℝ) ≤ Real.log (Y:ℝ) := Real.log_nonneg (by exact_mod_cast hY1)
    have h162 : (0:ℝ) ≤ 162 * C2 := by linarith [hC2pos]
    have h4T : (0:ℝ) ≤ 4 * T := by linarith
    calc 2 * (∑ K ∈ Finset.Icc 1 Y, ∑ K' ∈ Finset.Icc 1 Y,
            ((Nat.divisors K).card : ℝ) * ((Nat.divisors K').card : ℝ) * max (K : ℝ) (K' : ℝ)
              / (Real.sqrt ((K : ℝ) * (K' : ℝ)) * |(K : ℝ) - (K' : ℝ)|))
        ≤ 2 * (C2 * ((Y:ℝ) * Real.log (Y:ℝ) ^ 4)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          calc (∑ K ∈ Finset.Icc 1 Y, ∑ K' ∈ Finset.Icc 1 Y,
                ((Nat.divisors K).card : ℝ) * ((Nat.divisors K').card : ℝ)
                  * max (K : ℝ) (K' : ℝ)
                  / (Real.sqrt ((K : ℝ) * (K' : ℝ)) * |(K : ℝ) - (K' : ℝ)|))
              ≤ C2 * (Y:ℝ) * Real.log (Y:ℝ) ^ 4 := hb
            _ = C2 * ((Y:ℝ) * Real.log (Y:ℝ) ^ 4) := by ring
      _ ≤ 2 * C2 * ((4 * T) * Real.log (Y:ℝ) ^ 4) := by
          calc 2 * (C2 * ((Y:ℝ) * Real.log (Y:ℝ) ^ 4))
              = 2 * C2 * ((Y:ℝ) * Real.log (Y:ℝ) ^ 4) := by ring
            _ ≤ 2 * C2 * ((4 * T) * Real.log (Y:ℝ) ^ 4) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right hY4T (pow_nonneg hlogYnn 4))
                  (by linarith [hC2pos])
      _ ≤ 2 * C2 * ((4 * T) * (81 * (Real.log T) ^ 4)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow81 h4T)
            (by linarith [hC2pos])
      _ = 648 * C2 * (T * (Real.log T) ^ 4) := by ring
  -- splitting the kernel pointwise
  have hA : (∑ K ∈ Finset.Icc 1 Y, ∑ K' ∈ Finset.Icc 1 Y,
        ((Nat.divisors K).card : ℝ) * ((Nat.divisors K').card : ℝ) * pairKernel T K K')
      ≤ (∑ K ∈ Finset.Icc 1 Y, ∑ K' ∈ Finset.Icc 1 Y,
          ((Nat.divisors K).card : ℝ) * ((Nat.divisors K').card : ℝ)
            * (if K = K' then T / (K : ℝ) else 0))
        + (∑ K ∈ Finset.Icc 1 Y, ∑ K' ∈ Finset.Icc 1 Y,
          ((Nat.divisors K).card : ℝ) * ((Nat.divisors K').card : ℝ)
            * (2 * max (K : ℝ) (K' : ℝ)
              / (Real.sqrt ((K : ℝ) * (K' : ℝ)) * |(K : ℝ) - (K' : ℝ)|))) := by
    calc (∑ K ∈ Finset.Icc 1 Y, ∑ K' ∈ Finset.Icc 1 Y,
          ((Nat.divisors K).card : ℝ) * ((Nat.divisors K').card : ℝ) * pairKernel T K K')
        ≤ ∑ K ∈ Finset.Icc 1 Y, ∑ K' ∈ Finset.Icc 1 Y,
            ((Nat.divisors K).card : ℝ) * ((Nat.divisors K').card : ℝ)
              * ((if K = K' then T / (K : ℝ) else 0)
                + 2 * max (K : ℝ) (K' : ℝ)
                  / (Real.sqrt ((K : ℝ) * (K' : ℝ)) * |(K : ℝ) - (K' : ℝ)|)) :=
          Finset.sum_le_sum (fun K _ => Finset.sum_le_sum (fun K' _ =>
            mul_le_mul_of_nonneg_left (pairKernel_le_split T K K')
              (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))))
      _ = ∑ K ∈ Finset.Icc 1 Y, ∑ K' ∈ Finset.Icc 1 Y,
            (((Nat.divisors K).card : ℝ) * ((Nat.divisors K').card : ℝ)
                * (if K = K' then T / (K : ℝ) else 0)
              + ((Nat.divisors K).card : ℝ) * ((Nat.divisors K').card : ℝ)
                * (2 * max (K : ℝ) (K' : ℝ)
                  / (Real.sqrt ((K : ℝ) * (K' : ℝ)) * |(K : ℝ) - (K' : ℝ)|))) := by
          refine Finset.sum_congr rfl (fun K _ => Finset.sum_congr rfl (fun K' _ => ?_))
          ring
      _ = (∑ K ∈ Finset.Icc 1 Y, ∑ K' ∈ Finset.Icc 1 Y,
          ((Nat.divisors K).card : ℝ) * ((Nat.divisors K').card : ℝ)
            * (if K = K' then T / (K : ℝ) else 0))
        + (∑ K ∈ Finset.Icc 1 Y, ∑ K' ∈ Finset.Icc 1 Y,
          ((Nat.divisors K).card : ℝ) * ((Nat.divisors K').card : ℝ)
            * (2 * max (K : ℝ) (K' : ℝ)
              / (Real.sqrt ((K : ℝ) * (K' : ℝ)) * |(K : ℝ) - (K' : ℝ)|))) := by
          simp only [Finset.sum_add_distrib]
  refine le_trans hA ?_
  refine le_trans (add_le_add hdiag hoff) ?_
  have h4 : (0:ℝ) ≤ (Real.log T) ^ 4 := by positivity
  have hT4 : (0:ℝ) ≤ T * (Real.log T) ^ 4 := mul_nonneg hT0 h4
  calc 256 * C1 * (T * (Real.log T) ^ 4) + 648 * C2 * (T * (Real.log T) ^ 4)
      = (256 * C1 + 648 * C2) * (T * (Real.log T) ^ 4) := by ring
    _ ≤ (256 * C1 + 648 * C2 + 100) * (T * (Real.log T) ^ 4) := by
        nlinarith [hC1pos, hC2pos, hT4]
    _ = (256 * C1 + 648 * C2 + 100) * T * (Real.log T) ^ 4 := by ring

/-- `ζ` is bounded on the initial segment `[0,2]` of the critical line. -/
theorem exists_bound_zeta_small :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Set.Icc (0:ℝ) 2,
      ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
  have hcont : Continuous (fun t : ℝ => ‖riemannZeta ((1/2:ℂ) + (t:ℂ)*Complex.I)‖) := by
    refine Continuous.norm ?_
    refine continuous_iff_continuousAt.mpr (fun t => ?_)
    have hs : ((1/2 : ℂ) + (t:ℂ)*Complex.I) ≠ 1 := by
      intro h
      have h2 := congrArg Complex.re h
      norm_num at h2
    exact ContinuousAt.comp ((differentiableAt_riemannZeta hs).continuousAt) (by fun_prop)
  obtain ⟨x, _hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by norm_num : (0:ℝ) ≤ 2)) hcont.continuousOn
  exact ⟨max ‖riemannZeta ((1/2:ℂ) + (x:ℂ)*Complex.I)‖ 1, by positivity,
    fun t ht => le_trans (hmax ht) (le_max_left _ _)⟩

/-- `(1+x)^4 ≤ 16(1+x^4)` for `x ≥ 0`. -/
lemma one_add_pow_four_le {x : ℝ} (hx : 0 ≤ x) : (1 + x) ^ 4 ≤ 16 * (1 + x ^ 4) := by
  rcases le_total x 1 with h | h
  · have h1 : (1 + x) ^ 4 ≤ 16 := by
      have h2 : 1 + x ≤ 2 := by linarith
      calc (1 + x) ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ (by linarith) h2 4
        _ = 16 := by norm_num
    have h3 : (0:ℝ) ≤ x ^ 4 := by positivity
    linarith
  · have h2 : 1 + x ≤ 2 * x := by linarith
    calc (1 + x) ^ 4 ≤ (2 * x) ^ 4 := pow_le_pow_left₀ (by linarith) h2 4
      _ = 16 * x ^ 4 := by ring
      _ ≤ 16 * (1 + x ^ 4) := by nlinarith [pow_nonneg hx 4]

lemma measurable_stepTerm (n : ℕ) : Measurable (stepTerm n) := by
  unfold stepTerm
  refine Measurable.ite ?_ ?_ measurable_const
  · exact measurableSet_le measurable_const measurable_id
  · fun_prop

lemma measurable_stepPoly (M : ℕ) : Measurable (stepPoly M) := by
  unfold stepPoly
  exact Finset.measurable_sum _ (fun n _ => measurable_stepTerm n)

/-- The `M`-th step polynomial is bounded by `M` pointwise (crudely), hence its fourth power is
interval integrable. -/
lemma norm_stepPoly_le (M : ℕ) (t : ℝ) : ‖stepPoly M t‖ ≤ (M : ℝ) := by
  calc ‖stepPoly M t‖ ≤ ∑ n ∈ Finset.Icc 1 M, ‖stepTerm n t‖ := by
        rw [stepPoly]
        exact norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 M, (1:ℝ) := by
        refine Finset.sum_le_sum (fun n hn => ?_)
        have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
        rw [stepTerm_apply]
        split_ifs with h
        · rw [norm_mul,
            show -(Complex.I * ((t * Real.log (n : ℝ) : ℝ) : ℂ))
              = ((-(t * Real.log (n : ℝ)) : ℝ) : ℂ) * Complex.I by push_cast; ring,
            Complex.norm_exp_ofReal_mul_I, mul_one, ← Complex.ofReal_inv, Complex.norm_real,
            Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
          refine inv_le_one_of_one_le₀ ?_
          rw [← Real.sqrt_one]
          exact Real.sqrt_le_sqrt hn1
        · simp
    _ = (M : ℝ) := by simp

lemma intervalIntegrable_stepPoly_pow_four (M : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => ‖stepPoly M t‖ ^ 4) MeasureTheory.volume a b := by
  refine IntervalIntegrable.mono_fun (f := fun _ : ℝ => (((M : ℝ) ^ 4 : ℝ)))
    (intervalIntegrable_const (c := ((M : ℝ) ^ 4))) ?_ ?_
  · exact ((measurable_stepPoly M).norm.pow_const 4).aestronglyMeasurable
  · filter_upwards with t
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ (M:ℝ) ^ 4)]
    exact le_trans (le_of_eq (abs_of_nonneg (by positivity)))
      (pow_le_pow_left₀ (norm_nonneg _) (norm_stepPoly_le M t) 4)

/-- **Ingham's integral fourth moment bound for `ζ` on the critical line.** -/
theorem zetaFourthMomentIntegral :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (∫ t in (0:ℝ)..T, ‖riemannZeta ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 4)
        ≤ C * T * (Real.log T) ^ 4 := by
  obtain ⟨C0, hC0pos, hAFE⟩ := zetaAfeTruncationSharp
  obtain ⟨C2, hC2pos, hpoly⟩ := stepPoly_fourthMoment
  obtain ⟨C1, hC1pos, hcrude⟩ := exists_bound_zeta_small
  refine ⟨256 * C0 ^ 4 + 16 * C1 ^ 4 + 16 * C0 ^ 4 * C2 + 16, by positivity, ?_⟩
  intro T hT
  set M : ℕ := ⌊Real.sqrt (T / (2 * Real.pi))⌋₊ + 1 with hMdef
  have hT0 : (0:ℝ) ≤ T := by linarith
  have hM1 : 1 ≤ M := by rw [hMdef]; exact Nat.le_add_left _ _
  have hlog2 : (0.5:ℝ) ≤ Real.log T := by
    have h2 : (0.5:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    exact le_trans h2 (Real.log_le_log (by norm_num) hT)
  have hlog4 : (0.0625:ℝ) ≤ (Real.log T) ^ 4 := by
    have h5 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 0.5) hlog2 4
    norm_num at h5 ⊢
    linarith [h5]
  have hTlog : (1/8:ℝ) ≤ T * (Real.log T) ^ 4 := by nlinarith [hT, hlog4]
  have hM4T : (M:ℝ) ^ 2 ≤ 4 * T := by
    have hfloor : ((⌊Real.sqrt (T / (2 * Real.pi))⌋₊ : ℕ) : ℝ)
        ≤ Real.sqrt (T / (2 * Real.pi)) := Nat.floor_le (by positivity)
    have hle : Real.sqrt (T / (2 * Real.pi)) ≤ Real.sqrt T := by
      refine Real.sqrt_le_sqrt ?_
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi)]
      nlinarith [Real.pi_gt_three, hT0]
    have hMl : (M:ℝ) = ((⌊Real.sqrt (T / (2 * Real.pi))⌋₊ : ℕ) : ℝ) + 1 := by
      rw [hMdef]; push_cast; ring
    have hfnn : (0:ℝ) ≤ ((⌊Real.sqrt (T / (2 * Real.pi))⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
    have h1 : (M:ℝ) ≤ Real.sqrt T + 1 := by
      rw [hMl]
      linarith [hfloor, hle]
    have hMnn : (0:ℝ) ≤ (M:ℝ) := by rw [hMl]; linarith
    have hsq : Real.sqrt T ^ 2 = T := Real.sq_sqrt hT0
    have hT1 : (1:ℝ) ≤ T := by linarith
    have hsT : (1:ℝ) ≤ Real.sqrt T := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hT1
    have hsqle : Real.sqrt T ≤ T := by nlinarith [hsq, hsT, Real.sqrt_nonneg T]
    have hsq2 : (M:ℝ) ^ 2 ≤ (Real.sqrt T + 1) ^ 2 := pow_le_pow_left₀ hMnn h1 2
    have hexp : (Real.sqrt T + 1) ^ 2 = T + 2 * Real.sqrt T + 1 := by rw [add_sq, hsq]; ring
    rw [hexp] at hsq2
    nlinarith [hsq2, hsT, hsqle, hT1]
  have hpoint : ∀ t ∈ Set.Icc (2:ℝ) T,
      ‖riemannZeta ((1/2:ℂ) + (t:ℂ)*Complex.I)‖ ^ 4 ≤ 16 * C0 ^ 4 * (1 + ‖stepPoly M t‖ ^ 4) := by
    intro t ht
    have ht1 : (1:ℝ) ≤ t := by linarith [ht.1]
    have hafe := hAFE t ht1
    have hfloor2 : ⌊Real.sqrt (t / (2 * Real.pi))⌋₊ + 1 ≤ M := by
      rw [hMdef]
      refine Nat.add_le_add_right (Nat.floor_mono ?_) 1
      refine Real.sqrt_le_sqrt ?_
      rw [div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < 2 * Real.pi)]
      exact ht.2
    have hsum := stepPoly_eq_dirichletSum M t (by linarith) hfloor2
    have hstep : (1 + ‖∑ n ∈ Finset.Icc 1 (⌊Real.sqrt (t / (2 * Real.pi))⌋₊ + 1),
          (n : ℂ) ^ (-((1 / 2 : ℂ) + (t : ℂ) * Complex.I))‖) = 1 + ‖stepPoly M t‖ := by
      rw [hsum]
    rw [hstep] at hafe
    calc ‖riemannZeta ((1/2:ℂ) + (t:ℂ)*Complex.I)‖ ^ 4
        ≤ (C0 * (1 + ‖stepPoly M t‖)) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hafe 4
      _ = C0 ^ 4 * (1 + ‖stepPoly M t‖) ^ 4 := by ring
      _ ≤ C0 ^ 4 * (16 * (1 + ‖stepPoly M t‖ ^ 4)) :=
          mul_le_mul_of_nonneg_left (one_add_pow_four_le (norm_nonneg _)) (by positivity)
      _ = 16 * C0 ^ 4 * (1 + ‖stepPoly M t‖ ^ 4) := by ring
  have hcontζ : Continuous (fun t : ℝ => ‖riemannZeta ((1/2:ℂ) + (t:ℂ)*Complex.I)‖ ^ 4) := by
    refine Continuous.pow ?_ 4
    refine Continuous.norm ?_
    refine continuous_iff_continuousAt.mpr (fun t => ?_)
    have hs : ((1/2 : ℂ) + (t:ℂ)*Complex.I) ≠ 1 := by
      intro h
      have h2 := congrArg Complex.re h
      norm_num at h2
    exact ContinuousAt.comp ((differentiableAt_riemannZeta hs).continuousAt) (by fun_prop)
  have hsplit : (∫ t in (0:ℝ)..T, ‖riemannZeta ((1/2:ℂ) + (t:ℂ)*Complex.I)‖ ^ 4)
      = (∫ t in (0:ℝ)..2, ‖riemannZeta ((1/2:ℂ) + (t:ℂ)*Complex.I)‖ ^ 4)
        + (∫ t in (2:ℝ)..T, ‖riemannZeta ((1/2:ℂ) + (t:ℂ)*Complex.I)‖ ^ 4) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hcontζ.intervalIntegrable (0:ℝ) 2) (hcontζ.intervalIntegrable (2:ℝ) T)).symm
  have hfirst : (∫ t in (0:ℝ)..2, ‖riemannZeta ((1/2:ℂ) + (t:ℂ)*Complex.I)‖ ^ 4)
      ≤ C1 ^ 4 * 2 := by
    have hmono : (∫ t in (0:ℝ)..2, ‖riemannZeta ((1/2:ℂ) + (t:ℂ)*Complex.I)‖ ^ 4)
        ≤ ∫ _t in (0:ℝ)..2, C1 ^ 4 :=
      intervalIntegral.integral_mono_on (by norm_num)
        (hcontζ.intervalIntegrable (0:ℝ) 2) (intervalIntegrable_const (c := (C1 ^ 4)))
        (fun t ht => pow_le_pow_left₀ (norm_nonneg _) (hcrude t ht) 4)
    calc (∫ t in (0:ℝ)..2, ‖riemannZeta ((1/2:ℂ) + (t:ℂ)*Complex.I)‖ ^ 4)
        ≤ ∫ _t in (0:ℝ)..2, C1 ^ 4 := hmono
      _ = C1 ^ 4 * 2 := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          ring
  have hsecond : (∫ t in (2:ℝ)..T, ‖riemannZeta ((1/2:ℂ) + (t:ℂ)*Complex.I)‖ ^ 4)
      ≤ 16 * C0 ^ 4 * (T + C2 * T * (Real.log T) ^ 4) := by
    have hstep1 : (∫ t in (2:ℝ)..T, ‖riemannZeta ((1/2:ℂ) + (t:ℂ)*Complex.I)‖ ^ 4)
        ≤ ∫ t in (2:ℝ)..T, 16 * C0 ^ 4 * (1 + ‖stepPoly M t‖ ^ 4) := by
      refine intervalIntegral.integral_mono_on (by linarith)
        (hcontζ.intervalIntegrable (2:ℝ) T)
        (((intervalIntegrable_const (c := (1:ℝ))).add
          (intervalIntegrable_stepPoly_pow_four M 2 T)).const_mul (16 * C0 ^ 4)) hpoint
    have hstep2 : (∫ t in (2:ℝ)..T, 16 * C0 ^ 4 * (1 + ‖stepPoly M t‖ ^ 4))
        = 16 * C0 ^ 4 * ∫ t in (2:ℝ)..T, (1 + ‖stepPoly M t‖ ^ 4) :=
      intervalIntegral.integral_const_mul _ _
    have hstep3 : (∫ t in (2:ℝ)..T, (1 + ‖stepPoly M t‖ ^ 4))
        = (T - 2) + ∫ t in (2:ℝ)..T, ‖stepPoly M t‖ ^ 4 := by
      rw [intervalIntegral.integral_add
        (intervalIntegrable_const (c := (1:ℝ))) (intervalIntegrable_stepPoly_pow_four M 2 T),
        intervalIntegral.integral_const]
      norm_num
    have hstep4 : (∫ t in (2:ℝ)..T, ‖stepPoly M t‖ ^ 4)
        ≤ ∫ t in (0:ℝ)..T, ‖stepPoly M t‖ ^ 4 := by
      have hadj : (∫ t in (0:ℝ)..T, ‖stepPoly M t‖ ^ 4)
          = (∫ t in (0:ℝ)..2, ‖stepPoly M t‖ ^ 4)
            + (∫ t in (2:ℝ)..T, ‖stepPoly M t‖ ^ 4) :=
        (intervalIntegral.integral_add_adjacent_intervals
          (intervalIntegrable_stepPoly_pow_four M 0 2)
          (intervalIntegrable_stepPoly_pow_four M 2 T)).symm
      have hnn : 0 ≤ ∫ t in (0:ℝ)..2, ‖stepPoly M t‖ ^ 4 :=
        intervalIntegral.integral_nonneg (by norm_num) (fun t _ => by positivity)
      linarith
    have hstep5 : (∫ t in (0:ℝ)..T, ‖stepPoly M t‖ ^ 4) ≤ C2 * T * (Real.log T) ^ 4 :=
      hpoly T M hM1 hM4T hT
    calc (∫ t in (2:ℝ)..T, ‖riemannZeta ((1/2:ℂ) + (t:ℂ)*Complex.I)‖ ^ 4)
        ≤ ∫ t in (2:ℝ)..T, 16 * C0 ^ 4 * (1 + ‖stepPoly M t‖ ^ 4) := hstep1
      _ = 16 * C0 ^ 4 * ∫ t in (2:ℝ)..T, (1 + ‖stepPoly M t‖ ^ 4) := hstep2
      _ = 16 * C0 ^ 4 * ((T - 2) + ∫ t in (2:ℝ)..T, ‖stepPoly M t‖ ^ 4) := by rw [hstep3]
      _ ≤ 16 * C0 ^ 4 * (T + C2 * T * (Real.log T) ^ 4) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith [hstep4, hstep5]
  rw [hsplit]
  refine le_trans (add_le_add hfirst hsecond) ?_
  have hC0p : (0:ℝ) ≤ C0 ^ 4 := by positivity
  have hC1p : (0:ℝ) ≤ C1 ^ 4 := by positivity
  have hprod : (0:ℝ) ≤ T * ((Real.log T) ^ 4 - 0.0625) :=
    mul_nonneg hT0 (by linarith [hlog4])
  have e1 : C1 ^ 4 * 2 ≤ 16 * C1 ^ 4 * (T * (Real.log T) ^ 4) := by nlinarith [hC1p, hTlog]
  have e2 : 16 * C0 ^ 4 * T ≤ 256 * C0 ^ 4 * (T * (Real.log T) ^ 4) := by nlinarith [hC0p, hprod]
  have e3 : 16 * C0 ^ 4 * (C2 * T * (Real.log T) ^ 4)
      ≤ 16 * C0 ^ 4 * C2 * (T * (Real.log T) ^ 4) := le_of_eq (by ring)
  rw [show (256 * C0 ^ 4 + 16 * C1 ^ 4 + 16 * C0 ^ 4 * C2 + 16) * T * (Real.log T) ^ 4
      = (256 * C0 ^ 4 + 16 * C1 ^ 4 + 16 * C0 ^ 4 * C2 + 16) * (T * (Real.log T) ^ 4) from by
        ring]
  linarith [e1, e2, e3, hC0p, hC1p, hC2pos]

end

end Work.ZeroDensity.Ingham
