import Mathlib

namespace Work.ZeroDensity.Ingham

/-- **`K` is bounded whenever the truncation inequality of the Ingham detector forces it small.**

Setting `A = C₁` (the detector constant), `Y ≤ (A T)^2` and `1/2 ≤ σ ≤ 1`, the hypothesis
`T^{1/3} (T+K)^{2/3} Y^{(2-4σ)/3} T^ε < 2T+1` pins down `K`: it forces `K ≤ 6 A^2 T^3`.

The mechanism is that `Y ↦ Y^{(2-4σ)/3}` is *decreasing* in `Y` (the exponent `(2-4σ)/3` lies in
`[-2/3, 0]`), so the left-hand side is at least its value at the maximal admissible
`Y = (A T)^2`, namely `T^{1/3} (T+K)^{2/3} (A T)^{-4/3}`; dropping the harmless factor `T^ε ≥ 1`
and cubing the resulting inequality gives
`T (T+K)^2 < (2T+1)^3 A^4 T^4`, whence `(T+K)^2 < (2T+1)^3 A^4 T^3 ≤ 27 A^4 T^6` and finally
`T + K < 6 A^2 T^3`. -/
theorem KboundOfSmallP : ∃ C : ℝ, 0 < C ∧ ∀ (A ε T K σ Y : ℝ), 6 ≤ A → 0 < ε → 2 ≤ T → 1 ≤ K →
    1 ≤ Y → Y ≤ (A * T) ^ 2 → 1 / 2 ≤ σ → σ ≤ 1 →
      T ^ ((1 : ℝ) / 3) * (T + K) ^ ((2 : ℝ) / 3) * Y ^ ((2 - 4 * σ) / 3) * T ^ ε < 2 * T + 1 →
        K ≤ C * A ^ 2 * T ^ 3 := by
  refine ⟨6, by norm_num, ?_⟩
  intro A ε T K σ Y hA hε hT hK hY1 hY2 hσ1 hσ2 hlt
  -- elementary positivity / size bookkeeping
  have hA0 : (0:ℝ) < A := by linarith
  have hT0 : (0:ℝ) < T := by linarith
  have hT1 : (1:ℝ) ≤ T := by linarith
  have hK0 : (0:ℝ) < K := by linarith
  have hTK0 : (0:ℝ) < T + K := by linarith
  have hY0 : (0:ℝ) < Y := by linarith
  have hW0 : (0:ℝ) < (A*T)^2 := by positivity
  have hW1 : (1:ℝ) ≤ (A*T)^2 := by nlinarith [hA, hT, hA0, hT0]
  -- the exponent `(2-4σ)/3` lies in `[-2/3, 0]`
  have hα1 : (-(2:ℝ)) ≤ 2 - 4*σ := by linarith
  have hα3 : 2 - 4*σ ≤ 0 := by linarith
  -- the worst case `Y = (A T)^2` gives a lower bound for `Y^(2-4σ)`
  have hYlb : ((A*T)^2)^(-(2:ℝ)) ≤ Y^(2-4*σ) := by
    have hYα : ((A*T)^2)^(2-4*σ) ≤ Y^(2-4*σ) := Real.rpow_le_rpow_of_nonpos hY0 hY2 hα3
    have hWexp : ((A*T)^2)^(-(2:ℝ)) ≤ ((A*T)^2)^(2-4*σ) :=
      Real.rpow_le_rpow_of_exponent_le hW1 hα1
    exact le_trans hWexp hYα
  -- `T^ε ≥ 1`
  have hTlb : (1:ℝ) ≤ T^(3*ε) := Real.one_le_rpow hT1 (by nlinarith [hε])
  -- cube the hypothesis
  have hLHS0 : (0:ℝ) ≤ T^(1/3:ℝ) * (T+K)^(2/3:ℝ) * Y^((2-4*σ)/3) * T^ε := by positivity
  have hcube : (T^(1/3:ℝ) * (T+K)^(2/3:ℝ) * Y^((2-4*σ)/3) * T^ε)^(3:ℝ) < (2*T+1)^(3:ℝ) :=
    Real.rpow_lt_rpow hLHS0 hlt (by norm_num)
  rw [show (T^(1/3:ℝ) * (T+K)^(2/3:ℝ) * Y^((2-4*σ)/3) * T^ε)^(3:ℝ)
        = T^(1:ℝ) * (T+K)^(2:ℝ) * Y^(2-4*σ) * T^(3*ε) from by
          rw [Real.mul_rpow (by positivity) (by positivity),
              Real.mul_rpow (by positivity) (by positivity),
              Real.mul_rpow (by positivity) (by positivity),
              ← Real.rpow_mul (le_of_lt hT0),
              ← Real.rpow_mul (le_of_lt hTK0),
              ← Real.rpow_mul (le_of_lt hY0),
              ← Real.rpow_mul (le_of_lt hT0)]
          ring_nf] at hcube
  -- replace `Y^(2-4σ)` by its worst-case lower bound and drop `T^(3ε) ≥ 1`
  have h0 : T^(1:ℝ) * (T+K)^(2:ℝ) * ((A*T)^2)^(-(2:ℝ)) ≤
      T^(1:ℝ) * (T+K)^(2:ℝ) * Y^(2-4*σ) := mul_le_mul_of_nonneg_left hYlb (by positivity)
  have h1 : T^(1:ℝ) * (T+K)^(2:ℝ) * Y^(2-4*σ) ≤
      T^(1:ℝ) * (T+K)^(2:ℝ) * Y^(2-4*σ) * T^(3*ε) := le_mul_of_one_le_right (by positivity) hTlb
  have h2 : T^(1:ℝ) * (T+K)^(2:ℝ) * ((A*T)^2)^(-(2:ℝ)) < (2*T+1)^(3:ℝ) :=
    lt_of_le_of_lt (le_trans h0 h1) hcube
  -- clear the negative power
  have hWmul : ((A*T)^2)^(-(2:ℝ)) * ((A*T)^2)^(2:ℝ) = 1 := by
    rw [← Real.rpow_add hW0]; norm_num
  have hmul := mul_lt_mul_of_pos_right h2 (by positivity : (0:ℝ) < ((A*T)^2)^(2:ℝ))
  rw [mul_assoc] at hmul
  have hmain : T * (T+K)^2 < (2*T+1)^3 * ((A*T)^2)^2 := by
    rw [hWmul, mul_one] at hmul
    simpa using hmul
  have hA4 : ((A*T)^2)^2 = A^4 * T^4 := by ring
  rw [hA4] at hmain
  -- divide by `T`
  have hdiv : (T+K)^2 < (2*T+1)^3 * A^4 * T^3 := by
    have hh : (T+K)^2 * T < ((2*T+1)^3 * A^4 * T^3) * T := by nlinarith [hmain]
    exact lt_of_mul_lt_mul_right hh hT0.le
  -- `(2T+1)^3 ≤ 27 T^3`
  have h27 : (2*T+1)^3 ≤ 27*T^3 := by
    have hle : 2*T+1 ≤ 3*T := by linarith
    have h3 := pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ 2*T+1) hle 3
    rwa [show (3*T)^3 = 27*T^3 by ring] at h3
  have hstep1 : (2*T+1)^3 * A^4 * T^3 ≤ 27 * A^4 * T^6 := by
    have h := mul_le_mul_of_nonneg_right h27 (by positivity : (0:ℝ) ≤ A^4 * T^3)
    nlinarith [h]
  have hstep2 : (27:ℝ) * A^4 * T^6 ≤ (6*A^2*T^3)^2 := by
    have h6sq : (6*A^2*T^3)^2 = 36*A^4*T^6 := by ring
    rw [h6sq]
    nlinarith [show (0:ℝ) ≤ A^4 * T^6 by positivity]
  have hsq : (T+K)^2 < (6*A^2*T^3)^2 := lt_of_lt_of_le (lt_of_lt_of_le hdiv hstep1) hstep2
  have h6 : (0:ℝ) ≤ 6*A^2*T^3 := by positivity
  have hTK : T + K < 6*A^2*T^3 :=
    (pow_lt_pow_iff_left₀ hTK0.le h6 (by norm_num : (2:ℕ) ≠ 0)).mp hsq
  linarith [hTK, hT0, hK0]

end Work.ZeroDensity.Ingham
