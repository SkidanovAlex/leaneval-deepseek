import Mathlib

namespace Work.ZeroFreeTables

open MeasureTheory intervalIntegral

/-- The truncated Taylor bound `e^u ≤ 1 + u + u²/2 + (2/9)u³` for `0 ≤ u ≤ 1`
(`Real.exp_bound'` with `n = 3`, whose Lagrange remainder is `u³·4/(3!·3) = (2/9)u³`). -/
private lemma triBound_exp_cubic (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Real.exp u ≤ 1 + u + u^2/2 + (2/9)*u^3 := by
  have h := Real.exp_bound' hu0 hu1 (n := 3) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num at h
  linarith

/-- `∫₀¹ (1-t) dt = 1/2`. -/
private lemma triBound_integral_one_sub :
    (∫ t in (0:ℝ)..1, (1 - t)) = 1/2 := by
  have hsub := intervalIntegral.integral_sub (μ := MeasureTheory.volume) (a := (0:ℝ)) (b := 1)
    (f := fun _ : ℝ => (1:ℝ)) (g := fun s : ℝ => s)
    (continuous_const.intervalIntegrable _ _) (continuous_id.intervalIntegrable _ _)
  simp only [intervalIntegral.integral_const, integral_id, smul_eq_mul] at hsub
  rw [hsub]; norm_num

/-- Monomial integral against the triangle:
`∫₀¹ c·tᵏ·(1-t) dt = c·(1/(k+1) - 1/(k+2))`. -/
private lemma triBound_integral_monomial (c : ℝ) (k : ℕ) :
    (∫ t in (0:ℝ)..1, c * t^k * (1-t)) = c * (1/(k+1) - 1/(k+2)) := by
  have h1 : IntervalIntegrable (fun t:ℝ => c * t^(k+1)) volume 0 1 :=
    (by fun_prop : Continuous (fun t:ℝ => c * t^(k+1))).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun t:ℝ => c * t^k) volume 0 1 :=
    (by fun_prop : Continuous (fun t:ℝ => c * t^k)).intervalIntegrable _ _
  have heq : (fun t:ℝ => c * t^k * (1-t)) = fun t => c*t^k - c*t^(k+1) := by
    funext t; ring
  rw [heq, intervalIntegral.integral_sub h2 h1, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_pow, integral_pow]
  simp only [one_pow, zero_pow (Nat.succ_ne_zero k), zero_pow (Nat.succ_ne_zero (k+1))]
  push_cast
  ring

/-- Linear-combination form of the monomial integral against the triangle. -/
private lemma triBound_integral_range_monomial (n : ℕ) (c : ℕ → ℝ) :
    (∫ t in (0:ℝ)..1, ∑ i ∈ Finset.range n, c i * t^i * (1-t))
      = ∑ i ∈ Finset.range n, c i * (1/(i+1) - 1/(i+2)) := by
  have hint : ∀ i ∈ Finset.range n,
      IntervalIntegrable (fun t:ℝ => c i * t^i * (1-t)) volume 0 1 := by
    intro i _
    exact (by fun_prop : Continuous (fun t:ℝ => c i * t^i * (1-t))).intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum hint]
  apply Finset.sum_congr rfl
  intro i _
  exact triBound_integral_monomial (c i) i

/-- Explicit value of the polynomial integral used for the exponential estimate:
`∫₀¹ (1 + λt + (λt)²/2 + (2/9)(λt)³)(1-t)dt = 1/2 + λ/6 + λ²/24 + λ³/90`. -/
private lemma triBound_integral_poly (lam : ℝ) :
    (∫ t in (0:ℝ)..1, (1 + lam*t + (lam*t)^2/2 + (2/9)*(lam*t)^3) * (1-t))
      = 1/2 + lam/6 + lam^2/24 + lam^3/90 := by
  have hrep : (fun t : ℝ => (1 + lam*t + (lam*t)^2/2 + (2/9)*(lam*t)^3) * (1-t))
      = fun t => ∑ i ∈ Finset.range 4,
          (fun i => match i with | 0 => (1:ℝ) | 1 => lam | 2 => lam^2/2 | _ => (2/9)*lam^3) i
            * t^i * (1-t) := by
    funext t
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    ring
  rw [hrep, triBound_integral_range_monomial]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  ring

/-- The triangle test function on `[0,1]`: for every `lam ≤ 2/5`,
`2∫₀¹ e^{lam·t}·max (1-t) 0 dt ≤ 6/5`.  (For `lam ≤ 0` the exponential is `≤ 1` on `[0,1]`,
so the integral is `≤ 1/2`; for `0 ≤ lam ≤ 2/5` use the pointwise cubic Taylor bound
`e^u ≤ 1 + u + u²/2 + (2/9)u³` on `0 ≤ u ≤ 1` (`Real.exp_bound'` with `n = 3`), which gives
`∫₀¹ e^{lam t}(1-t)dt ≤ 1/2 + lam/6 + lam²/24 + lam³/90 ≤ 3/5` at `lam ≤ 2/5`.) -/
theorem t23triBound (lam : ℝ) (hlam : lam ≤ 2 / 5) :
    2 * (∫ t in (0:ℝ)..1, Real.exp (lam * t) * max (1 - t) 0) ≤ 6 / 5 := by
  have hmain : (∫ t in (0:ℝ)..1, Real.exp (lam * t) * max (1 - t) 0) ≤ 3 / 5 := by
    by_cases hle : lam ≤ 0
    · -- Case `lam ≤ 0`: `e^{lam t} ≤ 1`, hence the integrand is `≤ 1 - t`.
      have hpt : ∀ t ∈ Set.Icc (0:ℝ) 1,
          Real.exp (lam * t) * max (1 - t) 0 ≤ (1 - t) := by
        intro t ht
        have ht0 : 0 ≤ t := ht.1
        have ht1 : t ≤ 1 := ht.2
        have hexp1 : Real.exp (lam * t) ≤ 1 := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr
            (by nlinarith [mul_nonpos_of_nonpos_of_nonneg hle ht0])
        have hmaxle : max (1 - t) 0 ≤ 1 - t := max_le (le_refl _) (by linarith)
        have hmax0 : 0 ≤ max (1 - t) 0 := le_max_right _ _
        calc Real.exp (lam * t) * max (1 - t) 0
            ≤ 1 * max (1 - t) 0 := mul_le_mul_of_nonneg_right hexp1 hmax0
          _ = max (1 - t) 0 := one_mul _
          _ ≤ 1 - t := hmaxle
      have hfint : IntervalIntegrable (fun t => Real.exp (lam * t) * max (1 - t) 0)
          volume 0 1 :=
        (by fun_prop : Continuous
          (fun t => Real.exp (lam * t) * max (1 - t) 0)).intervalIntegrable _ _
      have hgint : IntervalIntegrable (fun t : ℝ => (1 - t)) volume 0 1 :=
        (by fun_prop : Continuous (fun t : ℝ => (1 - t))).intervalIntegrable _ _
      have hmono := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1) hfint hgint hpt
      rw [triBound_integral_one_sub] at hmono
      linarith
    · -- Case `0 < lam ≤ 2/5`: cubic Taylor bound, then the explicit polynomial integral.
      have h0 : 0 ≤ lam := le_of_lt (not_le.mp hle)
      have hlam1 : lam ≤ 1 := by linarith
      have hpt : ∀ t ∈ Set.Icc (0:ℝ) 1,
          Real.exp (lam * t) * max (1 - t) 0
            ≤ (1 + lam*t + (lam*t)^2/2 + (2/9)*(lam*t)^3) * (1-t) := by
        intro t ht
        have ht0 : 0 ≤ t := ht.1
        have ht1 : t ≤ 1 := ht.2
        have hmax : max (1 - t) 0 = 1 - t := max_eq_left (by linarith)
        have hlt' : lam * t ≤ lam * 1 := mul_le_mul_of_nonneg_left ht1 h0
        have hlamt1 : lam * t ≤ 1 := by linarith [hlt', hlam1]
        have hlamt0 : 0 ≤ lam * t := mul_nonneg h0 ht0
        have hexp := triBound_exp_cubic (lam*t) hlamt0 hlamt1
        rw [hmax]
        exact mul_le_mul_of_nonneg_right hexp (by linarith)
      have hfint : IntervalIntegrable (fun t => Real.exp (lam * t) * max (1 - t) 0)
          volume 0 1 :=
        (by fun_prop : Continuous
          (fun t => Real.exp (lam * t) * max (1 - t) 0)).intervalIntegrable _ _
      have hgint : IntervalIntegrable
          (fun t => (1 + lam*t + (lam*t)^2/2 + (2/9)*(lam*t)^3) * (1-t)) volume 0 1 :=
        (by fun_prop : Continuous
          (fun t => (1 + lam*t + (lam*t)^2/2 + (2/9)*(lam*t)^3) * (1-t))).intervalIntegrable _ _
      have hmono := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1) hfint hgint hpt
      have hval := triBound_integral_poly lam
      have hnum : 1/2 + lam/6 + lam^2/24 + lam^3/90 ≤ 3/5 := by
        nlinarith [pow_le_pow_left₀ h0 hlam 2, pow_le_pow_left₀ h0 hlam 3]
      linarith [hmono, hval, hnum]
  linarith

end Work.ZeroFreeTables
