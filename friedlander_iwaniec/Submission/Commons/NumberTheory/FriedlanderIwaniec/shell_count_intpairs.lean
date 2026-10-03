import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.card_sq_add_pow_four_intpairs_asymptotic

namespace Commons.NumberTheory.FriedlanderIwaniec

open scoped BigOperators

/-- Elementary inequality: for `0 ≤ v ≤ x` (with `x > 0`),
`x ^ (3/4) - v ^ (3/4) ≤ (x - v) * x ^ (-(1/4))`. -/
private lemma rpow_three_quarters_sub_le {x v : ℝ} (hx : 0 < x) (hv : 0 ≤ v) (hveq : v ≤ x) :
    x ^ (3 / 4 : ℝ) - v ^ (3 / 4 : ℝ) ≤ (x - v) * x ^ (-(1 / 4) : ℝ) := by
  have hx0 : 0 ≤ x := le_of_lt hx
  have hsplit : (3 / 4 : ℝ) = 1 + (-(1 / 4)) := by norm_num
  -- `x ^ (3/4) = x * x ^ (-(1/4))`
  have h1 : x ^ (3 / 4 : ℝ) = x * x ^ (-(1 / 4) : ℝ) := by
    rw [hsplit, Real.rpow_add hx, Real.rpow_one]
  -- `v * x ^ (-(1/4)) ≤ v ^ (3/4)`
  have h2 : v * x ^ (-(1 / 4) : ℝ) ≤ v ^ (3 / 4 : ℝ) := by
    rcases eq_or_lt_of_le hv with h | h
    · rw [← h]; simp [Real.zero_rpow (by norm_num : (3 / 4 : ℝ) ≠ 0)]
    · have h3 : v ^ (3 / 4 : ℝ) = v * v ^ (-(1 / 4) : ℝ) := by
        rw [hsplit, Real.rpow_add h, Real.rpow_one]
      rw [h3]
      have h4 : x ^ (-(1 / 4) : ℝ) ≤ v ^ (-(1 / 4) : ℝ) :=
        Real.rpow_le_rpow_of_nonpos h hveq (by norm_num)
      exact mul_le_mul_of_nonneg_left h4 hv
  have h5 : (x - v) * x ^ (-(1 / 4) : ℝ)
      = x * x ^ (-(1 / 4) : ℝ) - v * x ^ (-(1 / 4) : ℝ) := by ring
  rw [h1, h5]
  linarith

theorem shell_count_intpairs :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℕ, 1 ≤ x → y ≤ x / 2 →
      (({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ)}).ncard : ℝ)
        - (({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ ((x - y : ℕ) : ℤ)}).ncard : ℝ)
      ≤ C * ((y : ℝ) * (x : ℝ) ^ (-(1 / 4 : ℝ)) + Real.sqrt x) := by
  obtain ⟨C0, hC0pos, hC0⟩ := card_sq_add_pow_four_intpairs_asymptotic
  set K : ℝ := ∫ u in (0 : ℝ)..1, Real.sqrt (1 - u ^ 4) with hK
  have hKnn : 0 ≤ K := by
    rw [hK]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun u _ => Real.sqrt_nonneg _)
  refine ⟨4 * K + 2 * C0, by linarith, ?_⟩
  intro x y hx hy
  set v : ℕ := x - y with hvdef
  have hvle : v ≤ x := le_of_eq_of_le hvdef (Nat.sub_le x y)
  have hyx : y ≤ x := le_trans hy (Nat.div_le_self x 2)
  have hv1 : 1 ≤ v := by
    have hx2 : x / 2 < x := Nat.div_lt_self (by omega) (by norm_num)
    have : y < x := lt_of_le_of_lt hy hx2
    omega
  have hxR : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hbx := hC0 x hx
  have hbv := hC0 v hv1
  -- upper bound for the larger count
  have hNX : (({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ)}).ncard : ℝ)
      ≤ 4 * K * (x : ℝ) ^ (3 / 4 : ℝ) + C0 * Real.sqrt (x : ℝ) := by
    have h := (abs_le.mp hbx).2
    linarith
  -- lower bound for the smaller count
  have hNV : 4 * K * (v : ℝ) ^ (3 / 4 : ℝ) - C0 * Real.sqrt (v : ℝ)
      ≤ (({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (v : ℤ)}).ncard : ℝ) := by
    have h := (abs_le.mp hbv).1
    linarith
  -- difference bound
  have hdiff : (({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ)}).ncard : ℝ)
      - (({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (v : ℤ)}).ncard : ℝ)
      ≤ 4 * K * ((x : ℝ) ^ (3 / 4 : ℝ) - (v : ℝ) ^ (3 / 4 : ℝ))
        + C0 * Real.sqrt (x : ℝ) + C0 * Real.sqrt (v : ℝ) := by
    linarith
  -- the fourth-root difference estimate
  have hsub : (x : ℝ) ^ (3 / 4 : ℝ) - (v : ℝ) ^ (3 / 4 : ℝ)
      ≤ ((x : ℝ) - (v : ℝ)) * (x : ℝ) ^ (-(1 / 4) : ℝ) :=
    rpow_three_quarters_sub_le hxpos (by positivity) (by exact_mod_cast hvle)
  have hxv : (x : ℝ) - (v : ℝ) = (y : ℝ) := by
    rw [hvdef, Nat.cast_sub hyx]
    ring
  have hsqrtv : Real.sqrt (v : ℝ) ≤ Real.sqrt (x : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hvle)
  calc (({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (x : ℤ)}).ncard : ℝ)
        - (({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 ≤ (v : ℤ)}).ncard : ℝ)
      ≤ 4 * K * ((x : ℝ) ^ (3 / 4 : ℝ) - (v : ℝ) ^ (3 / 4 : ℝ))
          + C0 * Real.sqrt (x : ℝ) + C0 * Real.sqrt (v : ℝ) := hdiff
    _ ≤ 4 * K * (((x : ℝ) - (v : ℝ)) * (x : ℝ) ^ (-(1 / 4) : ℝ))
          + C0 * Real.sqrt (x : ℝ) + C0 * Real.sqrt (v : ℝ) := by
        have := mul_le_mul_of_nonneg_left hsub (by linarith : (0 : ℝ) ≤ 4 * K)
        linarith
    _ = 4 * K * ((y : ℝ) * (x : ℝ) ^ (-(1 / 4) : ℝ))
          + C0 * Real.sqrt (x : ℝ) + C0 * Real.sqrt (v : ℝ) := by rw [hxv]
    _ ≤ 4 * K * ((y : ℝ) * (x : ℝ) ^ (-(1 / 4) : ℝ))
          + 2 * C0 * Real.sqrt (x : ℝ) := by
        have hcv : C0 * Real.sqrt (v : ℝ) ≤ C0 * Real.sqrt (x : ℝ) :=
          mul_le_mul_of_nonneg_left hsqrtv (le_of_lt hC0pos)
        linarith
    _ ≤ (4 * K + 2 * C0) * ((y : ℝ) * (x : ℝ) ^ (-(1 / 4) : ℝ) + Real.sqrt (x : ℝ)) := by
        have h1 : (0 : ℝ) ≤ (y : ℝ) * (x : ℝ) ^ (-(1 / 4) : ℝ) :=
          mul_nonneg (by positivity) (Real.rpow_nonneg (le_of_lt hxpos) _)
        have h2 : (0 : ℝ) ≤ Real.sqrt (x : ℝ) := Real.sqrt_nonneg _
        have e1 : 4 * K * ((y : ℝ) * (x : ℝ) ^ (-(1 / 4) : ℝ))
            ≤ (4 * K + 2 * C0) * ((y : ℝ) * (x : ℝ) ^ (-(1 / 4) : ℝ)) :=
          mul_le_mul_of_nonneg_right (by linarith) h1
        have e2 : 2 * C0 * Real.sqrt (x : ℝ) ≤ (4 * K + 2 * C0) * Real.sqrt (x : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith) h2
        rw [mul_add]
        linarith [e1, e2]

end Commons.NumberTheory.FriedlanderIwaniec
