import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Commons.Analysis.Asymptotics

theorem summable_sqrt_log_div_pow (A B M : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M) :
    Summable (fun j : ℕ => Real.sqrt ((A + B * Real.log (2 * (2:ℝ) ^ j + 2 * M + 1)) / (2:ℝ) ^ j)) := by
  have hlog2_nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hM3 : (0:ℝ) < 2*M + 3 := by linarith
  have hlogM3 : 0 ≤ Real.log (2*M+3) := Real.log_nonneg (by linarith)
  set P : ℝ := A + B * Real.log (2*M+3) with hPdef
  have hP : 0 ≤ P := by
    rw [hPdef]; exact add_nonneg hA (mul_nonneg hB hlogM3)
  have hPpos : 0 ≤ P + B * Real.log 2 := add_nonneg hP (mul_nonneg hB hlog2_nonneg)
  set r0 : ℝ := Real.sqrt (1/2) with hr0def
  have hr0_nonneg : 0 ≤ r0 := Real.sqrt_nonneg _
  have hr0_lt_one : r0 < 1 := by
    rw [hr0def, Real.sqrt_lt (by norm_num) (by norm_num)]; norm_num
  have hnorm : ‖r0‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0_nonneg]; exact hr0_lt_one
  have hr0sq : r0^2 = 1/2 := by rw [hr0def]; exact Real.sq_sqrt (by norm_num)
  set C : ℝ := Real.sqrt (P + B * Real.log 2) with hCdef
  have hCsq : C^2 = P + B * Real.log 2 := by
    rw [hCdef]; exact Real.sq_sqrt hPpos
  have hC_nonneg : 0 ≤ C := by rw [hCdef]; exact Real.sqrt_nonneg _
  -- summability of the dominating sequence
  have hsum_geom : Summable (fun j : ℕ => r0 ^ j) :=
    summable_geometric_iff_norm_lt_one.mpr hnorm
  have hsum_lin : Summable (fun j : ℕ => (j:ℝ) * r0 ^ j) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm
    simpa using h
  have hsum : Summable (fun j : ℕ => C * ((j:ℝ) + 1) * r0 ^ j) := by
    have h1 : Summable (fun j : ℕ => ((j:ℝ) + 1) * r0 ^ j) := by
      have := hsum_lin.add hsum_geom
      simpa [add_mul, one_mul] using this
    simpa only [mul_assoc] using h1.mul_left C
  -- pointwise bound
  have hbound : ∀ j : ℕ,
      Real.sqrt ((A + B * Real.log (2 * (2:ℝ) ^ j + 2 * M + 1)) / (2:ℝ) ^ j)
        ≤ C * ((j:ℝ) + 1) * r0 ^ j := by
    intro j
    have h2j : (1:ℝ) ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
    have h2jpos : (0:ℝ) < (2:ℝ)^j := by positivity
    have hargpos : (0:ℝ) < 2*(2:ℝ)^j + 2*M + 1 := by
      have : (0:ℝ) ≤ 2*(2:ℝ)^j := by positivity
      linarith
    have hargle : 2*(2:ℝ)^j + 2*M + 1 ≤ (2*M+3)*(2:ℝ)^j := by
      have hprod : (2*M+1) ≤ (2*M+1) * (2:ℝ)^j := by
        calc (2*M+1) = (2*M+1) * 1 := by ring
          _ ≤ (2*M+1) * (2:ℝ)^j := mul_le_mul_of_nonneg_left h2j (by linarith)
      nlinarith [hprod]
    have hlogbounds : Real.log (2*(2:ℝ)^j + 2*M + 1) ≤ Real.log (2*M+3) + (j:ℝ)*Real.log 2 := by
      have h1 := Real.log_le_log hargpos hargle
      rw [Real.log_mul (by linarith : (2*M+3) ≠ 0) (by positivity : (2:ℝ)^j ≠ 0), Real.log_pow] at h1
      simpa using h1
    have hnum : A + B * Real.log (2*(2:ℝ)^j + 2*M + 1) ≤ (P + B*Real.log 2) * ((j:ℝ)+1)^2 := by
      have hb : B * Real.log (2*(2:ℝ)^j + 2*M + 1) ≤ B * (Real.log (2*M+3) + (j:ℝ)*Real.log 2) :=
        mul_le_mul_of_nonneg_left hlogbounds hB
      have step1 : A + B * Real.log (2*(2:ℝ)^j + 2*M + 1) ≤ A + B * (Real.log (2*M+3) + (j:ℝ)*Real.log 2) := by
        linarith
      have heq : A + B * (Real.log (2*M+3) + (j:ℝ)*Real.log 2) = P + B*Real.log 2 * (j:ℝ) := by
        rw [hPdef]; ring
      rw [heq] at step1
      have hjnonneg : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
      have hbc : 0 ≤ B * Real.log 2 := mul_nonneg hB hlog2_nonneg
      have hj1 : (1:ℝ) ≤ (j:ℝ)+1 := by linarith
      have hsq : ((j:ℝ)+1) ≤ ((j:ℝ)+1)^2 := by nlinarith
      have h1 : P + B*Real.log 2 * (j:ℝ) ≤ (P + B*Real.log 2)*((j:ℝ)+1) := by
        nlinarith [hP, hbc, mul_nonneg hP hjnonneg]
      have h2 : (P + B*Real.log 2)*((j:ℝ)+1) ≤ (P + B*Real.log 2)*((j:ℝ)+1)^2 :=
        mul_le_mul_of_nonneg_left hsq hPpos
      linarith
    have hdiv : (A + B * Real.log (2*(2:ℝ)^j + 2*M + 1))/(2:ℝ)^j
        ≤ ((P + B*Real.log 2)*((j:ℝ)+1)^2)/(2:ℝ)^j :=
      div_le_div_of_nonneg_right hnum (le_of_lt h2jpos)
    have hr0j : (r0^j)^2 = (1/2:ℝ)^j := by
      rw [← pow_mul, mul_comm, pow_mul, hr0sq]
    have hhalf : (1/2:ℝ)^j = ((2:ℝ)^j)⁻¹ := by
      rw [one_div, inv_pow]
    have htarget : (C*((j:ℝ)+1)*r0^j)^2 = ((P + B*Real.log 2)*((j:ℝ)+1)^2)/(2:ℝ)^j := by
      rw [mul_pow, mul_pow, hCsq, hr0j, hhalf, div_eq_mul_inv]
    have hsqrtarg : (0:ℝ) ≤ C*((j:ℝ)+1)*r0^j :=
      mul_nonneg (mul_nonneg hC_nonneg (by positivity)) (pow_nonneg hr0_nonneg j)
    calc Real.sqrt ((A + B * Real.log (2*(2:ℝ)^j + 2*M + 1))/(2:ℝ)^j)
        ≤ Real.sqrt (((P + B*Real.log 2)*((j:ℝ)+1)^2)/(2:ℝ)^j) := Real.sqrt_le_sqrt hdiv
      _ = Real.sqrt ((C*((j:ℝ)+1)*r0^j)^2) := by rw [htarget]
      _ = C*((j:ℝ)+1)*r0^j := Real.sqrt_sq hsqrtarg
  exact Summable.of_nonneg_of_le (fun j => Real.sqrt_nonneg _) hbound hsum

end Commons.Analysis.Asymptotics