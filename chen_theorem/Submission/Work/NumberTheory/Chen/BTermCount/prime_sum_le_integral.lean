import Submission.Work.NumberTheory.Chen.BTermCount.primeSumCore

open scoped BigOperators
open MeasureTheory
open intervalIntegral

namespace Work.NumberTheory.Chen.BTermCount

/-- Abel/Mertens partial summation for prime sums: for a `C¹` function `f ≥ 0` which is
monotone (either non-decreasing or non-increasing) on `[A,B]`, the weighted prime sum
`Σ_{A < p ≤ B} f p / p` is at most the corresponding `d log log`-integral
`∫_A^B f t /(t log t) dt` plus the Mertens error, where `E` bounds the error term in the second
Mertens estimate on the relevant range.

Note the strict lower limit `A < p`: with `A ≤ p` the Abel identity would produce an extra
uncontrolled endpoint term `f(A)/A`.

(`L₀` is the Mertens constant; only the *difference* `primeRecips t − log log t − L₀` is used, so
the statement is insensitive to its value.) -/
theorem prime_sum_le_integral
    {A B : ℕ} {f g : ℝ → ℝ} {L₀ E : ℝ}
    (hA : 2 ≤ A) (hAB : A ≤ B)
    (hderiv : ∀ t ∈ Set.uIcc (A : ℝ) (B : ℝ), HasDerivAt f (g t) t)
    (hfint : IntervalIntegrable g volume (A : ℝ) (B : ℝ))
    (hfnn : ∀ t ∈ Set.Icc (A : ℝ) (B : ℝ), 0 ≤ f t)
    (hmono : (∀ t ∈ Set.Icc (A : ℝ) (B : ℝ), 0 ≤ g t) ∨
      (∀ t ∈ Set.Icc (A : ℝ) (B : ℝ), g t ≤ 0))
    (hE : 0 ≤ E)
    (hmer : ∀ t : ℝ, (A : ℝ) ≤ t →
      |(∑ p ∈ (⌊t⌋₊).primesLE, (1 : ℝ) / (p : ℝ)) - Real.log (Real.log t) - L₀| ≤ E) :
    (∑ p ∈ (Finset.Ioc A B).filter Nat.Prime, f (p : ℝ) / (p : ℝ))
      ≤ (∫ t in (A : ℝ)..(B : ℝ), f t / (t * Real.log t)) + 2 * E * (f (A:ℝ) + f (B:ℝ)) := by
  have hAreal : (A:ℝ) ≤ (B:ℝ) := by exact_mod_cast hAB
  -- the second Mertens error, in the form used below
  have hmer' : ∀ t ∈ Set.Icc (A:ℝ) (B:ℝ),
      |primeRecipStep t - (Real.log (Real.log t) + L₀)| ≤ E := by
    intro t ht
    have h := hmer t ht.1
    simpa only [primeRecipStep, primeRecipSum, sub_sub] using h
  -- integrability of the three integrands appearing in the identity
  have hcontP : ContinuousOn (fun t : ℝ => Real.log (Real.log t) + L₀) (Set.uIcc (A:ℝ) (B:ℝ)) :=
    continuousOn_loglog_add_const hA hAB
  have hIntW : IntervalIntegrable (fun t => primeRecipStep t * g t) volume (A:ℝ) (B:ℝ) :=
    intervalIntegrable_primeRecipStep_mul hAreal hfint
  have hIntPg : IntervalIntegrable (fun t => (Real.log (Real.log t) + L₀) * g t)
      volume (A:ℝ) (B:ℝ) :=
    hfint.continuousOn_mul hcontP
  have hIntDg : IntervalIntegrable
      (fun t => (primeRecipStep t - (Real.log (Real.log t) + L₀)) * g t) volume (A:ℝ) (B:ℝ) :=
    IntervalIntegrable.congr
      (f := fun t => primeRecipStep t * g t - (Real.log (Real.log t) + L₀) * g t)
      (fun t _ => by ring) (hIntW.sub hIntPg)
  -- the discrete Abel identity, the step-integral identity and the integration by parts
  have habel := sum_Ioc_primes_div_eq f A B hAB
  have hstep := integral_primeRecipStep_mul_deriv hAB hderiv hfint
  have hibp := integral_loglog_add_const_mul_deriv (f := f) (g := g) (L₀ := L₀) hA hAB hderiv hfint
  have hDg_eq : (∫ t in (A:ℝ)..(B:ℝ), (primeRecipStep t - (Real.log (Real.log t) + L₀)) * g t)
      = (∫ t in (A:ℝ)..(B:ℝ), primeRecipStep t * g t)
        - (∫ t in (A:ℝ)..(B:ℝ), (Real.log (Real.log t) + L₀) * g t) := by
    rw [← intervalIntegral.integral_sub hIntW hIntPg]
    exact intervalIntegral.integral_congr (fun t _ => by ring)
  have hmain : (∑ p ∈ (Finset.Ioc A B).filter Nat.Prime, f (p:ℝ)/(p:ℝ))
      = (∫ t in (A:ℝ)..(B:ℝ), f t / (t * Real.log t))
        + (primeRecipSum B - (Real.log (Real.log (B:ℝ)) + L₀)) * f (B:ℝ)
        - (primeRecipSum A - (Real.log (Real.log (A:ℝ)) + L₀)) * f (A:ℝ)
        - (∫ t in (A:ℝ)..(B:ℝ), (primeRecipStep t - (Real.log (Real.log t) + L₀)) * g t) := by
    rw [habel, ← hstep, hDg_eq, hibp]
    ring
  -- the three error bounds
  have hDB : (primeRecipSum B - (Real.log (Real.log (B:ℝ)) + L₀)) * f (B:ℝ) ≤ E * f (B:ℝ) := by
    have h := hmer' (B:ℝ) ⟨hAreal, le_rfl⟩
    rw [primeRecipStep_natCast] at h
    have hfB : 0 ≤ f (B:ℝ) := hfnn _ ⟨hAreal, le_rfl⟩
    calc (primeRecipSum B - (Real.log (Real.log (B:ℝ)) + L₀)) * f (B:ℝ)
        ≤ |primeRecipSum B - (Real.log (Real.log (B:ℝ)) + L₀)| * f (B:ℝ) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hfB
      _ ≤ E * f (B:ℝ) := mul_le_mul_of_nonneg_right h hfB
  have hDA : -((primeRecipSum A - (Real.log (Real.log (A:ℝ)) + L₀)) * f (A:ℝ)) ≤ E * f (A:ℝ) := by
    have h := hmer' (A:ℝ) ⟨le_rfl, hAreal⟩
    rw [primeRecipStep_natCast] at h
    have hfA : 0 ≤ f (A:ℝ) := hfnn _ ⟨le_rfl, hAreal⟩
    calc -((primeRecipSum A - (Real.log (Real.log (A:ℝ)) + L₀)) * f (A:ℝ))
        ≤ |(primeRecipSum A - (Real.log (Real.log (A:ℝ)) + L₀)) * f (A:ℝ)| := neg_le_abs _
      _ = |primeRecipSum A - (Real.log (Real.log (A:ℝ)) + L₀)| * f (A:ℝ) := by
          rw [abs_mul, abs_of_nonneg hfA]
      _ ≤ E * f (A:ℝ) := mul_le_mul_of_nonneg_right h hfA
  have hDgb : -(∫ t in (A:ℝ)..(B:ℝ), (primeRecipStep t - (Real.log (Real.log t) + L₀)) * g t)
      ≤ E * (f (A:ℝ) + f (B:ℝ)) := by
    have h1 : ‖∫ t in (A:ℝ)..(B:ℝ), (primeRecipStep t - (Real.log (Real.log t) + L₀)) * g t‖
        ≤ E * ∫ t in (A:ℝ)..(B:ℝ), ‖g t‖ :=
      norm_integral_mul_le hAreal hmer' hfint hIntDg
    have h2 : (∫ t in (A:ℝ)..(B:ℝ), ‖g t‖) ≤ f (A:ℝ) + f (B:ℝ) :=
      integral_norm_le_endpoints hAB hderiv hfint hfnn hmono
    calc -(∫ t in (A:ℝ)..(B:ℝ), (primeRecipStep t - (Real.log (Real.log t) + L₀)) * g t)
        ≤ ‖∫ t in (A:ℝ)..(B:ℝ), (primeRecipStep t - (Real.log (Real.log t) + L₀)) * g t‖ :=
          neg_le_abs _
      _ ≤ E * ∫ t in (A:ℝ)..(B:ℝ), ‖g t‖ := h1
      _ ≤ E * (f (A:ℝ) + f (B:ℝ)) := mul_le_mul_of_nonneg_left h2 hE
  rw [hmain]
  have h5 : E * f (B:ℝ) + E * f (A:ℝ) + E * (f (A:ℝ) + f (B:ℝ))
      = 2 * E * (f (A:ℝ) + f (B:ℝ)) := by ring
  linarith [hDB, hDA, hDgb, h5]

end Work.NumberTheory.Chen.BTermCount
