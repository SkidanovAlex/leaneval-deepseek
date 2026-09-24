import Mathlib

namespace Work.GM.Affine

/-- Core arithmetic inequality behind `WindowFarCountArith`, in terms of the ratio `r = M₁/M₃`.

For `0 < εc`, `2 εc ≤ ε`, `T ≥ 1`, `B ≥ 2` and `0 < r ≤ T^6`:
```
(T^6 + 2 B r + 2)^{εc} (4 B r + 1) ≤ 20 · 9^{εc} · B^{1+ε} · T^{6ε} · (r+1).
```
The proof: `T^6 + 2Br + 2 ≤ 18 B T^6`, so the power is `≤ 18^{εc} B^{εc} T^{6εc}`;
further `4Br + 1 ≤ 4B(r+1)`, and finally `4·2^{εc} ≤ 20·B^{ε-εc}·T^{6(ε-εc)}`
(using `B^{ε-εc} ≥ 2^{ε-εc} ≥ 2^{εc}` and `T^{6(ε-εc)} ≥ 1`). -/
private lemma core {ε εc T B r : ℝ}
    (hεc : 0 < εc) (hεc2 : 2 * εc ≤ ε) (hT : 1 ≤ T) (hB : 2 ≤ B)
    (hr0 : 0 < r) (hrT : r ≤ T ^ 6) :
    (T ^ 6 + 2 * B * r + 2) ^ εc * (4 * B * r + 1)
      ≤ 20 * 9 ^ εc * B ^ (1 + ε) * T ^ (6 * ε) * (r + 1) := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hBpos : 0 < B := by linarith
  have hT6 : (1:ℝ) ≤ T ^ 6 := one_le_pow₀ hT
  -- A := T^6 + 2 B r + 2 is at most 18 B T^6
  have hA_le : T ^ 6 + 2 * B * r + 2 ≤ 18 * B * T ^ 6 := by
    have hA1 : T ^ 6 + 2 ≤ 16 * B * T ^ 6 := by
      have h31 : (31:ℝ) ≤ 16 * B - 1 := by linarith
      have hmul : (31:ℝ) * 1 ≤ (16 * B - 1) * T ^ 6 :=
        mul_le_mul h31 hT6 (by norm_num) (by linarith)
      nlinarith [hmul]
    have hA2 : 2 * B * r ≤ 2 * B * T ^ 6 := by
      have h := mul_le_mul_of_nonneg_left hrT (show (0:ℝ) ≤ 2 * B by positivity)
      linarith [h]
    linarith
  have hA_nonneg : 0 ≤ T ^ 6 + 2 * B * r + 2 := by positivity
  -- power bound
  have hApow : (T ^ 6 + 2 * B * r + 2) ^ εc ≤ 18 ^ εc * B ^ εc * T ^ (6 * εc) := by
    have h1 : (T ^ 6 + 2 * B * r + 2) ^ εc ≤ (18 * B * T ^ 6) ^ εc :=
      Real.rpow_le_rpow hA_nonneg hA_le (le_of_lt hεc)
    have h2 : (18 * B * T ^ 6) ^ εc = 18 ^ εc * B ^ εc * T ^ (6 * εc) := by
      rw [Real.mul_rpow (x := 18 * B) (y := T ^ 6) (z := εc) (by positivity) (by positivity)]
      rw [Real.mul_rpow (x := 18) (y := B) (z := εc) (by norm_num) (le_of_lt hBpos)]
      rw [show (T ^ 6 : ℝ) = T ^ (6:ℝ) from (Real.rpow_natCast T 6).symm]
      rw [show (T ^ (6:ℝ)) ^ εc = T ^ (6 * εc) from (Real.rpow_mul (le_of_lt hTpos) 6 εc).symm]
    linarith [h1, h2]
  have hlin : 4 * B * r + 1 ≤ 4 * B * (r + 1) := by nlinarith [hB]
  -- scalar bound 4 · 2^εc ≤ 20 · (B^{ε-εc} T^{6(ε-εc)})
  have hσnn : 0 ≤ ε - εc := by linarith
  have hεcσ : εc ≤ ε - εc := by linarith
  have h2σ : (2:ℝ) ^ εc ≤ (2:ℝ) ^ (ε - εc) :=
    Real.rpow_le_rpow_of_exponent_le (x := 2) (y := εc) (z := ε - εc) (by norm_num) hεcσ
  have hBσ : (2:ℝ) ^ (ε - εc) ≤ B ^ (ε - εc) :=
    Real.rpow_le_rpow (x := 2) (y := B) (z := ε - εc) (by norm_num) hB hσnn
  have hTσ : 1 ≤ T ^ (6 * (ε - εc)) := Real.one_le_rpow hT (by positivity)
  have hBσnn : 0 ≤ B ^ (ε - εc) := Real.rpow_nonneg (le_of_lt hBpos) _
  have hprod2 : (2:ℝ) ^ εc ≤ B ^ (ε - εc) * T ^ (6 * (ε - εc)) := by
    have h1 : B ^ (ε - εc) * 1 ≤ B ^ (ε - εc) * T ^ (6 * (ε - εc)) :=
      mul_le_mul_of_nonneg_left hTσ hBσnn
    rw [mul_one] at h1
    linarith
  have hscalar : 4 * (2:ℝ) ^ εc ≤ 20 * (B ^ (ε - εc) * T ^ (6 * (ε - εc))) := by
    have h2c : 4 * (2:ℝ) ^ εc ≤ 20 * (2:ℝ) ^ εc := by
      have h := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) εc
      linarith
    have h3 : 20 * (2:ℝ) ^ εc ≤ 20 * (B ^ (ε - εc) * T ^ (6 * (ε - εc))) :=
      mul_le_mul_of_nonneg_left hprod2 (by norm_num)
    linarith [h2c, h3]
  -- exponent-splitting identities
  have hBb : B ^ (1 + ε) = B ^ (1 + εc) * B ^ (ε - εc) := by
    rw [show (1 + ε : ℝ) = (1 + εc) + (ε - εc) by ring, Real.rpow_add hBpos]
  have hTb : T ^ (6 * ε) = T ^ (6 * εc) * T ^ (6 * (ε - εc)) := by
    rw [show (6 * ε : ℝ) = 6 * εc + 6 * (ε - εc) by ring, Real.rpow_add hTpos]
  have hBa : B ^ εc * B = B ^ (1 + εc) := by
    rw [show (1 + εc : ℝ) = εc + 1 by ring, Real.rpow_add hBpos, Real.rpow_one]
  have h18 : (18:ℝ) ^ εc = (2:ℝ) ^ εc * 9 ^ εc := by
    rw [show (18:ℝ) = 2 * 9 by norm_num, Real.mul_rpow (by norm_num) (by norm_num)]
  have hCnn : 0 ≤ 9 ^ εc * B ^ εc * B * T ^ (6 * εc) * (r + 1) := by
    have := Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 9) εc
    positivity
  have hstep2 : (18 ^ εc * B ^ εc * T ^ (6 * εc)) * (4 * B * (r + 1))
      ≤ 20 * 9 ^ εc * B ^ (1 + ε) * T ^ (6 * ε) * (r + 1) := by
    have hL_eq : (18 ^ εc * B ^ εc * T ^ (6 * εc)) * (4 * B * (r + 1))
        = (4 * (2:ℝ) ^ εc) * (9 ^ εc * B ^ εc * B * T ^ (6 * εc) * (r + 1)) := by
      rw [h18]; ring
    have hR_eq : 20 * 9 ^ εc * B ^ (1 + ε) * T ^ (6 * ε) * (r + 1)
        = (20 * (B ^ (ε - εc) * T ^ (6 * (ε - εc)))) *
            (9 ^ εc * B ^ εc * B * T ^ (6 * εc) * (r + 1)) := by
      rw [hBb, hTb, ← hBa]; ring
    rw [hL_eq, hR_eq]
    exact mul_le_mul_of_nonneg_right hscalar hCnn
  have h1 : (T ^ 6 + 2 * B * r + 2) ^ εc * (4 * B * r + 1)
      ≤ (18 ^ εc * B ^ εc * T ^ (6 * εc)) * (4 * B * (r + 1)) :=
    mul_le_mul hApow hlin (by positivity) (by positivity)
  linarith [h1, hstep2]

/-- The arithmetic bound requested by the `WindowFar_sharp` assembly: for `M₁/M₃ ≤ T^6`,
the "count times constants" expression is dominated by `C·B^{1+ε}T^{6ε}(M₁+M₃)`,
with constant `20·9^{εc}·Cc·Cmid·CW + 1`. -/
theorem WindowFarCountArith {ε εc Cc Cmid CW T B M₁ M₃ : ℝ}
    (hεc : 0 < εc) (hεc2 : 2 * εc ≤ ε) (hCc : 0 < Cc) (hCmid : 0 < Cmid) (hCW : 0 < CW)
    (hT : 1 ≤ T) (hB : 2 ≤ B) (hM₁ : 0 < M₁) (hM₃ : 1 ≤ M₃) (hratio : M₁ / M₃ ≤ T ^ 6) :
    Cc * (T ^ 6 + 2 * B * M₁ / M₃ + 2) ^ εc * (2 * (2 * B * M₁ / M₃) + 1) * Cmid * M₃ * CW
      ≤ (20 * 9 ^ εc * Cc * Cmid * CW + 1) * B ^ (1 + ε) * T ^ (6 * ε) * (M₁ + M₃) := by
  have hM₃pos : 0 < M₃ := lt_of_lt_of_le zero_lt_one hM₃
  have hr0 : 0 < M₁ / M₃ := div_pos hM₁ hM₃pos
  have hdiv : 2 * B * M₁ / M₃ = 2 * B * (M₁ / M₃) := mul_div_assoc (2 * B) M₁ M₃
  have hQ : 2 * (2 * B * (M₁ / M₃)) + 1 = 4 * B * (M₁ / M₃) + 1 := by ring
  have hM : M₁ + M₃ = (M₁ / M₃ + 1) * M₃ := by
    rw [add_mul, one_mul, div_mul_cancel₀ M₁ (ne_of_gt hM₃pos)]
  rw [hdiv, hQ, hM]
  have hcore := core (ε := ε) (εc := εc) (T := T) (B := B) (r := M₁ / M₃)
    hεc hεc2 hT hB hr0 hratio
  have hCnn : 0 ≤ Cmid * M₃ * CW := by positivity
  have hz1 : 0 ≤ B ^ (1 + ε) * T ^ (6 * ε) * ((M₁ / M₃ + 1) * M₃) := by positivity
  calc Cc * (T ^ 6 + 2 * B * (M₁ / M₃) + 2) ^ εc * (4 * B * (M₁ / M₃) + 1) * Cmid * M₃ * CW
      = Cc * (((T ^ 6 + 2 * B * (M₁ / M₃) + 2) ^ εc * (4 * B * (M₁ / M₃) + 1)) *
            (Cmid * M₃ * CW)) := by ring
    _ ≤ Cc * ((20 * 9 ^ εc * B ^ (1 + ε) * T ^ (6 * ε) * (M₁ / M₃ + 1)) *
            (Cmid * M₃ * CW)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcore hCnn) (le_of_lt hCc)
    _ = (20 * 9 ^ εc * Cc * Cmid * CW) * B ^ (1 + ε) * T ^ (6 * ε) *
            ((M₁ / M₃ + 1) * M₃) := by ring
    _ ≤ (20 * 9 ^ εc * Cc * Cmid * CW + 1) * B ^ (1 + ε) * T ^ (6 * ε) *
            ((M₁ / M₃ + 1) * M₃) := by
        rw [show (20 * 9 ^ εc * Cc * Cmid * CW) * B ^ (1 + ε) * T ^ (6 * ε) *
                ((M₁ / M₃ + 1) * M₃)
              = (20 * 9 ^ εc * Cc * Cmid * CW) *
                  (B ^ (1 + ε) * T ^ (6 * ε) * ((M₁ / M₃ + 1) * M₃)) from by ring,
            show (20 * 9 ^ εc * Cc * Cmid * CW + 1) * B ^ (1 + ε) * T ^ (6 * ε) *
                ((M₁ / M₃ + 1) * M₃)
              = (20 * 9 ^ εc * Cc * Cmid * CW + 1) *
                  (B ^ (1 + ε) * T ^ (6 * ε) * ((M₁ / M₃ + 1) * M₃)) from by ring]
        exact mul_le_mul_of_nonneg_right (by linarith) hz1

end Work.GM.Affine
