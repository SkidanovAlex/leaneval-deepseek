import Mathlib.Algebra.Group.Ext
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open _root_.MeasureTheory intervalIntegral Set

namespace Commons.MeasureTheory.Integral

/-- Auxiliary recurrence for the interval beta integral.  Integrating the derivative of
`x ↦ -(1-x)^(a+1) x^(b+1)` over `[0,1]` (the boundary terms vanish) yields
`(b+1) ∫₀¹ (1-x)^(a+1) x^b = (a+1) ∫₀¹ (1-x)^a x^(b+1)`. -/
private lemma beta_interval_aux (a b : ℕ) :
    ((b : ℝ) + 1) * (∫ x in (0 : ℝ)..1, (1 - x) ^ (a + 1) * x ^ b) =
      ((a : ℝ) + 1) * (∫ x in (0 : ℝ)..1, (1 - x) ^ a * x ^ (b + 1)) := by
  set F : ℝ → ℝ := fun x => -((1 - x) ^ (a + 1) * x ^ (b + 1)) with hF
  set F' : ℝ → ℝ := fun x => ((a : ℝ) + 1) * ((1 - x) ^ a * x ^ (b + 1)) -
      ((b : ℝ) + 1) * ((1 - x) ^ (a + 1) * x ^ b) with hF'
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt F (F' x) x := by
    intro x _
    rw [hF, hF']
    have h1 : HasDerivAt (fun y : ℝ => (1 - y) ^ (a + 1))
        (-((↑(a + 1) : ℝ) * (1 - x) ^ a)) x := by
      have hsub : HasDerivAt (fun y : ℝ => (1 : ℝ) - y) (-1) x := by
        simpa using (hasDerivAt_id x).const_sub (1 : ℝ)
      have h := (hasDerivAt_pow (a + 1) (1 - x)).comp x hsub
      simpa [Function.comp_def, Nat.add_sub_cancel] using h
    have h2 : HasDerivAt (fun y : ℝ => y ^ (b + 1)) ((↑(b + 1) : ℝ) * x ^ b) x := by
      simpa [Nat.add_sub_cancel] using hasDerivAt_pow (b + 1) x
    have h3 : HasDerivAt (fun y : ℝ => (1 - y) ^ (a + 1) * y ^ (b + 1))
        ((-((↑(a + 1) : ℝ) * (1 - x) ^ a)) * x ^ (b + 1) +
          (1 - x) ^ (a + 1) * ((↑(b + 1) : ℝ) * x ^ b)) x := by
      convert h1.mul h2 using 1
      · ext y; simp
      all_goals try rfl
    have h4 : HasDerivAt (fun y : ℝ => -((1 - y) ^ (a + 1) * y ^ (b + 1)))
        (-((-((↑(a + 1) : ℝ) * (1 - x) ^ a)) * x ^ (b + 1) +
          (1 - x) ^ (a + 1) * ((↑(b + 1) : ℝ) * x ^ b))) x := by
      convert h3.neg using 1
      · ext y; simp
      all_goals try rfl
    have hval : -((-((↑(a + 1) : ℝ) * (1 - x) ^ a)) * x ^ (b + 1) +
        (1 - x) ^ (a + 1) * ((↑(b + 1) : ℝ) * x ^ b)) =
        ((a : ℝ) + 1) * ((1 - x) ^ a * x ^ (b + 1)) -
          ((b : ℝ) + 1) * ((1 - x) ^ (a + 1) * x ^ b) := by
      push_cast; ring
    rw [hval] at h4
    simpa using h4
  have hcont : ContinuousOn F (Icc (0 : ℝ) 1) := by rw [hF]; fun_prop
  have hint : IntervalIntegrable F' volume (0 : ℝ) 1 := by
    apply Continuous.intervalIntegrable; rw [hF']; fun_prop
  have hA : IntervalIntegrable (fun x : ℝ => ((a : ℝ) + 1) * ((1 - x) ^ a * x ^ (b + 1)))
      volume 0 1 := by apply Continuous.intervalIntegrable; fun_prop
  have hB : IntervalIntegrable (fun x : ℝ => ((b : ℝ) + 1) * ((1 - x) ^ (a + 1) * x ^ b))
      volume 0 1 := by apply Continuous.intervalIntegrable; fun_prop
  have hmain := integral_eq_sub_of_hasDerivAt_of_le (a := (0 : ℝ)) (b := 1)
    (by norm_num) hcont hderiv hint
  have hF1 : F 1 = 0 := by rw [hF]; norm_num
  have hF0 : F 0 = 0 := by rw [hF]; norm_num
  rw [hF1, hF0, sub_zero] at hmain
  simp only [hF'] at hmain
  rw [intervalIntegral.integral_sub hA hB, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, sub_eq_zero] at hmain
  exact hmain.symm

/-- The beta integral over the interval `[0,1]`, proved by induction on `a` from
`beta_interval_aux` (integration by parts). -/
private lemma beta_interval (a b : ℕ) :
    ∫ x in (0 : ℝ)..1, (1 - x) ^ a * x ^ b =
      ((a.factorial * b.factorial : ℕ) : ℝ) / ((a + b + 1).factorial : ℝ) := by
  induction a generalizing b with
  | zero =>
    simp only [pow_zero, one_mul]
    rw [integral_pow]
    simp only [one_pow, zero_pow (Nat.succ_ne_zero b), sub_zero, Nat.factorial_zero,
      one_mul, zero_add]
    rw [Nat.factorial_succ]
    push_cast
    have hb : (↑b.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero b
    have hbp : ((b : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  | succ a ih =>
    have hrec := beta_interval_aux a b
    have hih := ih (b + 1)
    have hden : a + (b + 1) + 1 = a + b + 2 := by omega
    rw [hih, hden] at hrec
    have hb1 : ((b : ℝ) + 1) ≠ 0 := by positivity
    apply mul_left_cancel₀ hb1
    rw [hrec]
    have hden2 : a + 1 + b + 1 = a + b + 2 := by omega
    rw [hden2]
    have hfa : ((a.factorial * (b + 1).factorial : ℕ) : ℝ) =
        (a.factorial : ℝ) * ((b : ℝ) + 1) * (b.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hfb : (((a + 1).factorial * b.factorial : ℕ) : ℝ) =
        ((a : ℝ) + 1) * (a.factorial : ℝ) * (b.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [hfa, hfb, ← mul_div_assoc, ← mul_div_assoc]
    have hD : ((a + b + 2).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    rw [div_eq_div_iff hD hD]
    ring

/-- The beta integral `∫₀^1 (1-x)^a x^b dx = a! b! / (a+b+1)!` (Polymath8a Lemma 7.2 in
dimension 1).  Suggested proof: induction on `a`, using that
`deriv (fun x => -(1-x)^(a+1) * x^(b+1) / (b+1)) = (1-x)^a * x^(b+1) · (a+1)/(b+1)` and
`intervalIntegral.integral_deriv_eq_sub`. -/
theorem beta_integral (a b : ℕ) :
    ∫ x : ℝ in Set.Ioo 0 1, (1 - x) ^ a * x ^ b =
      ((a.factorial * b.factorial : ℕ) : ℝ) / ((a + b + 1).factorial : ℝ) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  exact beta_interval a b

end Commons.MeasureTheory.Integral