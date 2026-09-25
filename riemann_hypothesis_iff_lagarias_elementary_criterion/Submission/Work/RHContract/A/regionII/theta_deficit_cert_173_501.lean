import Mathlib
import Submission.Work.RHContract.A.regionII.theta_deficit_small

/-!
# Certified `θ`-deficit bounds on `[173, 501]`

For every integer `m ∈ [173, 501]`,

`(64/100) √m ≤ m − θ(m) ≤ (189/100) √m`.

The content is a *finite* computation.  `thUB m` / `thLB m` (namespace
`Work.RHContract.A.RegionII`, from `theta_deficit_small`) are sums of certified rational
brackets for `10^9 log p` over the primes `p ≤ m`, so

`thLB m / 10^9 ≤ θ(m) ≤ thUB m / 10^9`.

Writing `D = 10^9 m − thUB m ≥ 0` one has `m − θ(m) ≥ D/10^9`, and `D ≥ (64/100)·10^9·√m`
follows from the integer inequality `D^2 ≥ 4096·10^14·m` by squaring, since
`(64/100 · 10^9)^2 = 4096·10^14`.  The upper bound is symmetric using `thLB` and
`(189/100 · 10^9)^2 = 35721·10^14`.  The two integer inequalities, together with
`thUB m, thLB m ≤ 10^9 m`, are verified for the `329` values `m = 173, …, 501` by kernel
evaluation.
-/

set_option maxRecDepth 400000
set_option maxHeartbeats 0

namespace Work.RHContract.A.regionII

open Work.RHContract.A.RegionII

/-! ## The finite arithmetic certificate -/

/-- The integer inequalities behind the statement, for `m ∈ [173, 501]`. -/
theorem theta_cert_key (m : ℕ) (h1 : 173 ≤ m) (h2 : m ≤ 501) :
    (10 ^ 9 * m - thUB m) ^ 2 ≥ 4096 * 10 ^ 14 * m ∧
    (10 ^ 9 * m - thLB m) ^ 2 ≤ 35721 * 10 ^ 14 * m ∧
    thUB m ≤ 10 ^ 9 * m ∧ thLB m ≤ 10 ^ 9 * m := by
  have hall : (List.range 329).all (fun k => decide (
      (10 ^ 9 * (173 + k) - thUB (173 + k)) ^ 2 ≥ 4096 * 10 ^ 14 * (173 + k) ∧
      (10 ^ 9 * (173 + k) - thLB (173 + k)) ^ 2 ≤ 35721 * 10 ^ 14 * (173 + k) ∧
      thUB (173 + k) ≤ 10 ^ 9 * (173 + k) ∧
      thLB (173 + k) ≤ 10 ^ 9 * (173 + k))) = true := by
    decide
  have hk : m - 173 < 329 := by omega
  have hmem : m - 173 ∈ List.range 329 := List.mem_range.mpr hk
  have h := List.all_eq_true.mp hall (m - 173) hmem
  have hm : 173 + (m - 173) = m := by omega
  rw [hm] at h
  simpa using h

/-! ## From a square inequality to a `√` inequality -/

lemma sqrt_le_of_sq_le {c : ℝ} (hc : 0 ≤ c) {m D : ℕ}
    (h : c ^ 2 * (m : ℝ) ≤ ((D : ℝ)) ^ 2) : c * Real.sqrt m ≤ D := by
  have hsqrt := Real.sqrt_le_sqrt h
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc, Real.sqrt_sq (Nat.cast_nonneg D)] at hsqrt
  exact hsqrt

lemma le_sqrt_mul_of_sq_le {c : ℝ} (hc : 0 ≤ c) {m D : ℕ}
    (h : ((D : ℝ)) ^ 2 ≤ c ^ 2 * (m : ℝ)) : (D : ℝ) ≤ c * Real.sqrt m := by
  have hsqrt := Real.sqrt_le_sqrt h
  rw [Real.sqrt_sq (Nat.cast_nonneg D), Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc] at hsqrt
  exact hsqrt

/-! ## The two real bounds -/

/-- Lower bound: an integer certificate at level `10^9`, together with an upper bound `V/10^9`
for `θ m`, gives `(64/100) √m ≤ m − θ m`. -/
lemma deficit_lower (m V : ℕ) (hV : V ≤ 10 ^ 9 * m)
    (h : 4096 * 10 ^ 14 * m ≤ (10 ^ 9 * m - V) ^ 2)
    (hth : Chebyshev.theta (m : ℝ) ≤ (V : ℝ) / 10 ^ 9) :
    (64 / 100 : ℝ) * Real.sqrt m ≤ (m : ℝ) - Chebyshev.theta (m : ℝ) := by
  have hcast : (((10 ^ 9 * m - V : ℕ)) : ℝ) = 10 ^ 9 * (m : ℝ) - (V : ℝ) := by
    rw [Nat.cast_sub hV]; push_cast; ring
  have hsq : ((64 / 100 : ℝ) * 10 ^ 9) ^ 2 * (m : ℝ) ≤ (((10 ^ 9 * m - V : ℕ)) : ℝ) ^ 2 := by
    have h'' : ((4096 : ℝ) * 10 ^ 14) * (m : ℝ) ≤ (((10 ^ 9 * m - V : ℕ)) : ℝ) ^ 2 := by
      rw [← Nat.cast_pow]; push_cast; exact_mod_cast h
    rwa [show ((64 / 100 : ℝ) * 10 ^ 9) ^ 2 = (4096 : ℝ) * 10 ^ 14 by norm_num]
  have hstep := sqrt_le_of_sq_le (c := (64 / 100) * 10 ^ 9) (by norm_num)
    (m := m) (D := 10 ^ 9 * m - V) hsq
  have hdiv : (64 / 100 : ℝ) * Real.sqrt m ≤ (((10 ^ 9 * m - V : ℕ)) : ℝ) / 10 ^ 9 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 9)]
    nlinarith [hstep]
  calc (64 / 100 : ℝ) * Real.sqrt m ≤ (((10 ^ 9 * m - V : ℕ)) : ℝ) / 10 ^ 9 := hdiv
    _ = (m : ℝ) - (V : ℝ) / 10 ^ 9 := by rw [hcast]; ring
    _ ≤ (m : ℝ) - Chebyshev.theta (m : ℝ) := by linarith [hth]

/-- Upper bound: an integer certificate at level `10^9`, together with a lower bound `V/10^9`
for `θ m`, gives `m − θ m ≤ (189/100) √m`. -/
lemma deficit_upper (m V : ℕ) (hV : V ≤ 10 ^ 9 * m)
    (h : (10 ^ 9 * m - V) ^ 2 ≤ 35721 * 10 ^ 14 * m)
    (hth : (V : ℝ) / 10 ^ 9 ≤ Chebyshev.theta (m : ℝ)) :
    (m : ℝ) - Chebyshev.theta (m : ℝ) ≤ (189 / 100 : ℝ) * Real.sqrt m := by
  have hcast : (((10 ^ 9 * m - V : ℕ)) : ℝ) = 10 ^ 9 * (m : ℝ) - (V : ℝ) := by
    rw [Nat.cast_sub hV]; push_cast; ring
  have hsq : (((10 ^ 9 * m - V : ℕ)) : ℝ) ^ 2 ≤ ((189 / 100 : ℝ) * 10 ^ 9) ^ 2 * (m : ℝ) := by
    have h'' : (((10 ^ 9 * m - V : ℕ)) : ℝ) ^ 2 ≤ ((35721 : ℝ) * 10 ^ 14) * (m : ℝ) := by
      rw [← Nat.cast_pow]; push_cast; exact_mod_cast h
    rwa [show ((189 / 100 : ℝ) * 10 ^ 9) ^ 2 = (35721 : ℝ) * 10 ^ 14 by norm_num]
  have hstep := le_sqrt_mul_of_sq_le (c := (189 / 100) * 10 ^ 9) (by norm_num)
    (m := m) (D := 10 ^ 9 * m - V) hsq
  have hdiv : (((10 ^ 9 * m - V : ℕ)) : ℝ) / 10 ^ 9 ≤ (189 / 100 : ℝ) * Real.sqrt m := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 9)]
    nlinarith [hstep]
  calc (m : ℝ) - Chebyshev.theta (m : ℝ) ≤ (m : ℝ) - (V : ℝ) / 10 ^ 9 := by linarith [hth]
    _ = (((10 ^ 9 * m - V : ℕ)) : ℝ) / 10 ^ 9 := by rw [hcast]; ring
    _ ≤ (189 / 100 : ℝ) * Real.sqrt m := hdiv

/-! ## The target -/

theorem theta_deficit_cert_173_501 :
    (∀ m : ℕ, 173 ≤ m → m ≤ 501 →
        (64/100 : ℝ) * Real.sqrt m ≤ (m : ℝ) - Chebyshev.theta (m : ℝ)) ∧
    (∀ m : ℕ, 173 ≤ m → m ≤ 501 →
        (m : ℝ) - Chebyshev.theta (m : ℝ) ≤ (189/100 : ℝ) * Real.sqrt m) := by
  constructor
  · intro m h1 h2
    obtain ⟨hA, -, hC, -⟩ := theta_cert_key m h1 h2
    exact deficit_lower m (thUB m) hC hA (theta_le_thUB m)
  · intro m h1 h2
    obtain ⟨-, hB, -, hD⟩ := theta_cert_key m h1 h2
    exact deficit_upper m (thLB m) hD hB (thLB_div_le_theta m)

end Work.RHContract.A.regionII
