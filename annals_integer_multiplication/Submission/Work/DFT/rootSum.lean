import Mathlib

namespace Work.DFT

/-- Sum of the `t`-th roots of unity: rotation of the argument by `c` gives
a full period exactly when `t ∣ c`. -/
theorem rootSum (t : ℕ) (c : ℤ) (ht : 0 < t) :
    (∑ k : Fin t, Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        (((c : ℝ) * (k : ℝ)) / (t : ℝ) : ℝ))) =
      if (t : ℤ) ∣ c then (t : ℂ) else 0 := by
  -- base exponential `W = exp(2πi c/t)`; every summand is `W^k`
  let W : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((c : ℝ) / (t : ℝ) : ℝ)))
  have hWdef : W = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((c : ℝ) / (t : ℝ) : ℝ))) := rfl
  -- the k-th summand is `W^k`
  have hterm : ∀ n : ℕ,
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (((c : ℝ) * (n : ℝ)) / (t : ℝ) : ℝ)) = W ^ n := by
    intro n
    rw [hWdef, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  -- `W^t = exp(2πi c) = 1`
  have hWt : W ^ t = 1 := by
    rw [hWdef, ← Complex.exp_nat_mul]
    have harg : (↑t : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (((c : ℝ) / (t : ℝ) : ℝ)))
        = (↑c : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      have htc : (↑t : ℂ) * (((c : ℝ) / (t : ℝ) : ℝ) : ℂ) = (↑c : ℂ) := by
        have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp ht)
        push_cast
        field_simp
      calc (↑t : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (((c : ℝ) / (t : ℝ) : ℝ)))
          = ((↑t : ℂ) * (((c : ℝ) / (t : ℝ) : ℝ) : ℂ)) * (2 * (Real.pi : ℂ) * Complex.I) := by
            ring
        _ = (↑c : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by rw [htc]
    rw [harg]
    exact Complex.exp_int_mul_two_pi_mul_I c
  -- `W = 1 ↔ t ∣ c`
  have hW1 : W = 1 ↔ (t : ℤ) ∣ c := by
    constructor
    · intro h
      rw [hWdef] at h
      rw [Complex.exp_eq_one_iff] at h
      obtain ⟨n, hn⟩ := h
      have hA : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 := Complex.two_pi_I_ne_zero
      have hn2 : (2 * (Real.pi : ℂ) * Complex.I) * (((c : ℝ) / (t : ℝ) : ℝ) : ℂ)
          = (2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) := by
        rw [hn]; ring
      have hXeq : (((c : ℝ) / (t : ℝ) : ℝ) : ℂ) = (n : ℂ) := mul_left_cancel₀ hA hn2
      have hX : ((c : ℝ) / (t : ℝ) : ℝ) = (n : ℝ) := by
        have h' : ((((c : ℝ) / (t : ℝ) : ℝ)) : ℂ) = (((n : ℝ)) : ℂ) := by simpa using hXeq
        exact Complex.ofReal_inj.mp h'
      have htR : (t : ℝ) ≠ 0 := by positivity
      have hreal : (t : ℝ) * (n : ℝ) = (c : ℝ) := by rw [← hX, mul_div_cancel₀ _ htR]
      have hz : (t : ℤ) * n = c := by exact_mod_cast hreal
      exact ⟨n, hz.symm⟩
    · intro hd
      rw [hWdef]
      obtain ⟨m, hm⟩ := hd
      rw [hm]
      have hXm : (((↑((t : ℤ) * m) : ℤ) : ℝ) / (t : ℝ)) = (m : ℝ) := by
        push_cast
        field_simp
      rw [hXm]
      rw [show 2 * (Real.pi : ℂ) * Complex.I * (((m : ℝ)) : ℂ)
            = (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) from by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I m
  -- geometric sum
  have hgeom : (∑ k ∈ Finset.range t, W ^ k) = if W = 1 then (t : ℂ) else 0 := by
    by_cases hW : W = 1
    · rw [ite_eq_left hW]
      calc ∑ k ∈ Finset.range t, W ^ k = ∑ k ∈ Finset.range t, (1 : ℂ) ^ k :=
            Finset.sum_congr rfl (fun k _ => by rw [hW, one_pow])
        _ = (t : ℂ) := one_geom_sum t
    · rw [ite_eq_right hW]
      have h := geom_sum_mul W t
      rw [hWt] at h
      have : W - 1 ≠ 0 := sub_ne_zero.mpr hW
      exact (mul_eq_zero.mp (by simpa using h)).resolve_right this
  have hsum : (∑ k : Fin t, Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        (((c : ℝ) * (k : ℝ)) / (t : ℝ) : ℝ))) = ∑ k ∈ Finset.range t, W ^ k := by
    rw [show (∑ k : Fin t, Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          (((c : ℝ) * (k : ℝ)) / (t : ℝ) : ℝ))) = ∑ k : Fin t, W ^ (k : ℕ) from
        Finset.sum_congr rfl (fun k _ => hterm (k : ℕ))]
    exact Fin.sum_univ_eq_sum_range (fun n : ℕ => W ^ n) t
  rw [hsum, hgeom]
  by_cases hd : (t : ℤ) ∣ c
  · rw [ite_eq_left hd, ite_eq_left ((hW1).mpr hd)]
  · rw [ite_eq_right hd, ite_eq_right (fun h => hd ((hW1).mp h))]

end Work.DFT
