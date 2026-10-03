import Mathlib

namespace Work.A3

/-- Orthogonality of the exponential sum: for `q ≥ 1` and `m : ℤ`,
`∑_{r<q} exp(-2πi·m·r/q) = q` if `q ∣ m` and `0` otherwise. -/
lemma sum_range_exp_neg_int_mul_div (q : ℕ) (hq : 1 ≤ q) (m : ℤ) :
    (∑ r ∈ Finset.range q,
        Complex.exp (-(2 * Real.pi * Complex.I * ((m : ℝ) * (r : ℝ) / ((q : ℕ) : ℝ)))))
      = if (q : ℤ) ∣ m then ((q : ℕ) : ℂ) else 0 := by
  set ζ : ℂ := Complex.exp (-(2 * Real.pi * Complex.I * ((m:ℝ)/((q:ℕ):ℝ)))) with hζ
  -- Each summand is a power of `ζ`.
  have hterm : ∀ r : ℕ,
      Complex.exp (-(2 * Real.pi * Complex.I * ((m:ℝ)*(r:ℝ)/((q:ℕ):ℝ)))) = ζ ^ r := by
    intro r
    rw [hζ, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun r _ => hterm r)]
  -- `ζ` is a `q`-th root of unity.
  have hζq : ζ ^ q = 1 := by
    rw [hζ, ← Complex.exp_nat_mul]
    have hq0 : ((q:ℕ):ℂ) ≠ 0 := by
      exact_mod_cast (Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le Nat.zero_lt_one hq))
    have h : (q:ℂ) * (-(2 * Real.pi * Complex.I * ((m:ℝ)/((q:ℕ):ℝ))))
        = ((-m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast
      field_simp
    rw [h]
    exact Complex.exp_int_mul_two_pi_mul_I (-m)
  -- `ζ = 1` exactly when `q ∣ m`.
  have hfwd : ζ = 1 → (q:ℤ) ∣ m := by
    intro h1
    rw [hζ] at h1
    rw [Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    have hc : (2 * (Real.pi:ℂ) * Complex.I) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero
      exact_mod_cast Real.pi_ne_zero
    have h2 : (-(((m:ℝ)/((q:ℕ):ℝ)))) * (2 * (Real.pi:ℂ) * Complex.I)
        = (↑n : ℂ) * (2 * (Real.pi:ℂ) * Complex.I) := by
      rw [← hn]; ring
    have ht : -(((m:ℝ)/((q:ℕ):ℝ))) = (↑n : ℂ) := mul_right_cancel₀ hc h2
    have ht' : (((m:ℝ)/((q:ℕ):ℝ))) = -(↑n : ℂ) := neg_eq_iff_eq_neg.mp ht
    have ht_eq : (((m:ℝ)/((q:ℕ):ℝ))) = (↑m : ℂ) / (↑q : ℂ) := by push_cast; ring
    have hqq0 : (↑q : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le Nat.zero_lt_one hq))
    have hmc : (↑m : ℂ) = -(↑n : ℂ) * (↑q : ℂ) := by
      rw [ht_eq] at ht'
      exact (div_eq_iff hqq0).mp ht'
    have hmc' : (↑m : ℂ) = (((-n) * (q:ℤ) : ℤ) : ℂ) := by
      rw [hmc]; push_cast; ring
    have hm : m = (-n) * (q:ℤ) := Int.cast_injective hmc'
    exact ⟨-n, by rw [hm]; ring⟩
  have hbwd : (q:ℤ) ∣ m → ζ = 1 := by
    intro h1
    rw [hζ]
    obtain ⟨k, rfl⟩ := h1
    have hq0 : ((q:ℕ):ℂ) ≠ 0 := by
      exact_mod_cast (Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le Nat.zero_lt_one hq))
    have hqk : (((q:ℤ) * k : ℤ) : ℝ) / ((q:ℕ):ℝ) = (k:ℂ) := by
      push_cast
      field_simp
    rw [hqk]
    have hcast : -(2 * Real.pi * Complex.I * (k:ℂ))
        = ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast; ring
    rw [hcast]
    exact Complex.exp_int_mul_two_pi_mul_I (-k)
  by_cases hdvd : (q:ℤ) ∣ m
  · rw [if_pos hdvd]
    have hζ1 : ζ = 1 := hbwd hdvd
    simp [hζ1]
  · rw [if_neg hdvd]
    have hζne : ζ ≠ 1 := fun h => hdvd (hfwd h)
    have hgm := geom_sum_mul ζ q
    have hzero : (∑ r ∈ Finset.range q, ζ ^ r) * (ζ - 1) = 0 := by
      rw [hgm, hζq]; ring
    exact (mul_eq_zero.mp hzero).resolve_right (sub_ne_zero.mpr hζne)

end Work.A3
