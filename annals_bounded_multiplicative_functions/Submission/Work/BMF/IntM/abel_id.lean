import Mathlib
import Submission.Work.BMF.halasz_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Abel summation identity for `Mf` and `Kf`

`Mf f x = Σ_{n ≤ x} f n` and `Kf f x = Σ_{n ≤ x} f n log n`.  The classical identity

  `Mf f x * log x - Kf f x = ∫_1^x Mf f t / t dt`

is the Abel summation (partial summation) formula
`Σ_{n ≤ x} f n log(x/n) = ∫_1^x (Σ_{n ≤ t} f n) dt/t`.
-/

namespace Work.BMF.IntM

open MeasureTheory intervalIntegral Finset

/-- The real integral `∫_1^x 1_{[n,∞)}(t)/t dt = log x - log n` for `1 ≤ n ≤ x`. -/
theorem integral_Ici_indicator_inv (n : ℕ) (x : ℝ) (hn : 1 ≤ n) (hx : (n : ℝ) ≤ x) :
    ∫ t in (1 : ℝ)..x, (Set.Ici ((n : ℝ))).indicator (fun t : ℝ => (1 : ℝ)/t) t
      = Real.log x - Real.log n := by
  have hx1 : (1 : ℝ) ≤ x := le_trans (by exact_mod_cast hn) hx
  have hmem : (n : ℝ) ∈ Set.Icc (1 : ℝ) x := ⟨by exact_mod_cast hn, hx⟩
  have hcont : ContinuousOn (fun t : ℝ => (1 : ℝ)/t) (Set.uIcc (1 : ℝ) x) := by
    rw [Set.uIcc_of_le hx1]
    intro t ht
    exact ContinuousAt.continuousWithinAt
      ((ContinuousAt.inv₀ continuousAt_id
        (ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1))).const_mul 1)
  have hIntC : IntervalIntegrable (fun t : ℝ => (1 : ℝ)/t) volume 1 x :=
    ContinuousOn.intervalIntegrable hcont
  have hIntK :
      IntervalIntegrable ((Set.Iic ((n : ℝ))).indicator (fun t : ℝ => (1 : ℝ)/t)) volume 1 x := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx1]
    refine IntegrableOn.of_bound (C := 1) ?_ ?_ ?_
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    · exact (Measurable.indicator (by fun_prop) measurableSet_Iic).aestronglyMeasurable
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => ?_)
      by_cases ht' : t ≤ (n : ℝ)
      · rw [Set.indicator_of_mem (s := Set.Iic ((n : ℝ))) (by simpa [Set.mem_Iic] using ht')]
        rw [Real.norm_eq_abs, abs_of_pos (div_pos one_pos (by linarith [ht.1]))]
        rw [div_le_one (by linarith [ht.1])]
        linarith [ht.1]
      · rw [Set.indicator_of_notMem (s := Set.Iic ((n : ℝ))) (by simpa [Set.mem_Iic] using ht')]
        simp
  have hpt : ∀ t : ℝ, t ≠ (n : ℝ) →
      (Set.Ici ((n : ℝ))).indicator (fun t : ℝ => (1 : ℝ)/t) t
        = 1/t - (Set.Iic ((n : ℝ))).indicator (fun t : ℝ => (1 : ℝ)/t) t := by
    intro t ht
    rcases lt_or_gt_of_ne ht with hlt | hgt
    · rw [Set.indicator_of_notMem (s := Set.Ici ((n : ℝ)))
            (by simpa [Set.mem_Ici] using not_le.mpr hlt),
          Set.indicator_of_mem (s := Set.Iic ((n : ℝ)))
            (by simpa [Set.mem_Iic] using le_of_lt hlt)]
      ring
    · rw [Set.indicator_of_mem (s := Set.Ici ((n : ℝ)))
            (by simpa [Set.mem_Ici] using le_of_lt hgt),
          Set.indicator_of_notMem (s := Set.Iic ((n : ℝ)))
            (by simpa [Set.mem_Iic] using not_le.mpr hgt)]
      ring
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ (n : ℝ) := by
    rw [MeasureTheory.ae_iff]
    simp [MeasureTheory.measure_singleton]
  rw [integral_congr_ae (hae.mono (fun t ht _ => hpt t ht))]
  rw [intervalIntegral.integral_sub hIntC hIntK]
  rw [integral_one_div_of_pos zero_lt_one (by linarith), ← Set.Iic_def,
      intervalIntegral.integral_indicator hmem,
      integral_one_div_of_pos zero_lt_one (by exact_mod_cast hn)]
  simp

/-- Complex version of the previous computation. -/
theorem integral_Ici_inv_complex (n : ℕ) (x : ℝ) (hn : 1 ≤ n) (hx : (n : ℝ) ≤ x) :
    ∫ t in (1 : ℝ)..x, (if (n : ℝ) ≤ t then (1 : ℂ)/(t : ℂ) else 0)
      = (Real.log x : ℂ) - (Real.log n : ℂ) := by
  have hreal := integral_Ici_indicator_inv n x hn hx
  have key : (∫ t in (1 : ℝ)..x, (if (n : ℝ) ≤ t then (1 : ℂ)/(t : ℂ) else 0))
      = ((∫ t in (1 : ℝ)..x,
            (Set.Ici ((n : ℝ))).indicator (fun t : ℝ => (1 : ℝ)/t) t : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro t _
    beta_reduce
    by_cases h : (n : ℝ) ≤ t
    · rw [ite_eq_left h, Set.indicator_of_mem (s := Set.Ici ((n : ℝ)))
            (by simpa [Set.mem_Ici] using h)]
      simp
    · rw [ite_eq_right h, Set.indicator_of_notMem (s := Set.Ici ((n : ℝ)))
            (by simpa [Set.mem_Ici] using h)]
      simp
  rw [key, hreal, Complex.ofReal_sub]

/-- Writing `Mf f t` as a sum over `n ≤ ⌊x⌋₊` of indicators of `n ≤ t`, divided by `t`. -/
theorem Mf_div_eq_sum (f : ℕ → ℂ) (x t : ℝ) (ht1 : 1 ≤ t) (htx : t ≤ x) :
    Work.BMF.Mf f t / t
      = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n * (if (n : ℝ) ≤ t then (1 : ℂ)/(t : ℂ) else 0) := by
  have hN : ⌊t⌋₊ ≤ ⌊x⌋₊ := Nat.floor_mono htx
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hset : (Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ => (n : ℝ) ≤ t)
      = Finset.Icc 1 ⌊t⌋₊ := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, (Nat.le_floor_iff ht0).mpr h3⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, le_trans h2 hN⟩, (Nat.le_floor_iff ht0).mp h2⟩
  have h1 : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊, f n * (if (n : ℝ) ≤ t then (1 : ℂ)/(t : ℂ) else 0)
      = (if (n : ℝ) ≤ t then f n * ((t : ℂ))⁻¹ else 0) := by
    intro n _; by_cases h : (n : ℝ) ≤ t <;> simp [h, one_div]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_filter, hset, ← Finset.sum_mul,
      Work.BMF.Mf, div_eq_mul_inv]

/-- `t ↦ (if n ≤ t then 1/t else 0)` is interval-integrable on `[1,x]` for `1 ≤ x`. -/
theorem intervalIntegrable_Ici_inv (n : ℕ) (x : ℝ) (hx : (1 : ℝ) ≤ x) :
    IntervalIntegrable (fun t : ℝ => (if (n : ℝ) ≤ t then (1 : ℂ)/(t : ℂ) else 0))
      volume 1 x := by
  have heq : (fun t : ℝ => (if (n : ℝ) ≤ t then (1 : ℂ)/(t : ℂ) else 0))
      = (fun t : ℝ => (Set.Ici ((n : ℝ))).indicator (fun t : ℝ => (1 : ℂ)/(t : ℂ)) t) := by
    funext t
    by_cases h : (n : ℝ) ≤ t
    · rw [ite_eq_left h, Set.indicator_of_mem (s := Set.Ici ((n : ℝ)))
            (by simpa [Set.mem_Ici] using h)]
    · rw [ite_eq_right h, Set.indicator_of_notMem (s := Set.Ici ((n : ℝ)))
            (by simpa [Set.mem_Ici] using h)]
  rw [heq, intervalIntegrable_iff_integrableOn_Ioc_of_le hx]
  refine IntegrableOn.of_bound (C := 1) ?_ ?_ ?_
  · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  · exact (Measurable.indicator (by fun_prop) measurableSet_Ici).aestronglyMeasurable
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => ?_)
    by_cases ht' : (n : ℝ) ≤ t
    · rw [Set.indicator_of_mem (s := Set.Ici ((n : ℝ))) (by simpa [Set.mem_Ici] using ht')]
      rw [norm_div, norm_one, one_div]
      have hnorm : ‖((t : ℂ))‖ = t := by
        rw [show ‖((t : ℂ))‖ = |t| by simp]
        exact abs_of_pos (by linarith [ht.1])
      rw [hnorm]
      exact inv_le_one_of_one_le₀ (le_of_lt ht.1)
    · rw [Set.indicator_of_notMem (s := Set.Ici ((n : ℝ))) (by simpa [Set.mem_Ici] using ht')]
      simp

/-- `t ↦ c * (if n ≤ t then 1/t else 0)` is interval-integrable on `[1,x]` for `1 ≤ x`. -/
theorem intervalIntegrable_const_mul_Ici_inv (c : ℂ) (n : ℕ) (x : ℝ) (hx : (1 : ℝ) ≤ x) :
    IntervalIntegrable
      (fun t : ℝ => c * (if (n : ℝ) ≤ t then (1 : ℂ)/(t : ℂ) else 0)) volume 1 x :=
  (intervalIntegrable_Ici_inv n x hx).const_mul c

theorem abel_id (f : ℕ → ℂ) (x : ℝ) (hx : 1 ≤ x) :
    Work.BMF.Mf f x * Real.log x - Work.BMF.Kf f x = ∫ t in (1:ℝ)..x, Work.BMF.Mf f t / t := by
  have hfloor : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le (by linarith)
  -- Step A: rewrite the left-hand side as a sum of `f n * (log x - log n)`.
  have hA : Work.BMF.Mf f x * (Real.log x : ℂ) - Work.BMF.Kf f x
      = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n * ((Real.log x : ℂ) - (Real.log n : ℂ)) := by
    rw [Work.BMF.Mf, Work.BMF.Kf, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [hA]
  -- Step B: the integrand `Mf f t / t` is the finite sum of the `n`-th indicator terms.
  rw [show (∫ t in (1 : ℝ)..x, Work.BMF.Mf f t / t)
      = ∫ t in (1 : ℝ)..x,
          (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
            f n * (if (n : ℝ) ≤ t then (1 : ℂ)/(t : ℂ) else 0)) from by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hx] at ht
        exact Mf_div_eq_sum f x t ht.1 ht.2]
  -- Step C: swap the finite sum and the integral; evaluate each integral.
  rw [intervalIntegral.integral_finsetSum
        (fun n _ => intervalIntegrable_const_mul_Ici_inv (f n) n x hx)]
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
  rw [intervalIntegral.integral_const_mul,
      integral_Ici_inv_complex n x hn1
        (le_trans (by exact_mod_cast hn2) hfloor)]

end Work.BMF.IntM
