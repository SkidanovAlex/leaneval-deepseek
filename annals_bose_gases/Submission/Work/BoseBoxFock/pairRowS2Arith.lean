import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

/-- For `0 ≤ pL` and `x ≤ D * pL` one has `√pL * √x ≤ √D * pL` (no sign hypothesis on `D`;
the statement is trivial when `D < 0` because then both square roots of nonpositive numbers
vanish). -/
private lemma sqrt_sqrt_le_D {pL D x : ℝ} (hpL : 0 ≤ pL) (hx : x ≤ D * pL) :
    Real.sqrt pL * Real.sqrt x ≤ Real.sqrt D * pL := by
  have h2 : Real.sqrt pL * Real.sqrt x ≤ Real.sqrt pL * Real.sqrt (D * pL) :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hx) (Real.sqrt_nonneg pL)
  refine h2.trans ?_
  rcases le_or_gt D 0 with hD | hD
  · have hDp : D * pL ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hD hpL
    rw [Real.sqrt_eq_zero_of_nonpos hD, Real.sqrt_eq_zero_of_nonpos hDp]
    simp
  · rw [Real.sqrt_mul (le_of_lt hD)]
    have hs : Real.sqrt pL * Real.sqrt pL = pL := by rw [← pow_two, Real.sq_sqrt hpL]
    calc Real.sqrt pL * (Real.sqrt D * Real.sqrt pL)
        = Real.sqrt D * (Real.sqrt pL * Real.sqrt pL) := by ring
      _ ≤ Real.sqrt D * pL := by rw [hs]

theorem pairRowS2Arith {ℓ μ a Cf Ckap C ε err pDchi pL A2 L2 : ℝ} {n : ℕ}
    (hℓ : 0 < ℓ) (hμ : 0 < μ) (hCf : 0 ≤ Cf) (hCkap : 0 ≤ Ckap) (hC : 0 ≤ C)
    (hε : 0 ≤ ε) (hpL : 0 ≤ pL) (hA2 : 0 ≤ A2) (hL2 : 0 ≤ L2) (herr : 0 ≤ err)
    (hn : (n : ℝ) ≤ 2 * μ * ℓ ^ 3)
    (hL2' : L2 = pL)
    (hpD : pDchi ≤ C * (Ckap * μ ^ 2 * a * ℓ ^ 3 + 2 * μ * ℓ ^ 3) * pL)
    (hA2' : A2 * L2 ≤ pL)
    (hε' : ε ≤ err / (16 * Cf * μ ^ 2
        * (Real.sqrt (C * (Ckap * μ ^ 2 * a * ℓ ^ 3 + 2 * μ * ℓ ^ 3) + 1) + ℓ ^ 3))) :
    2 * (ℓ ^ 3)⁻¹ * ε * Cf * (n : ℝ) ^ 2
        * ((ℓ ^ 3)⁻¹ * Real.sqrt pL * Real.sqrt (pDchi + pL) + A2 * L2)
      ≤ (1 / 2) * err * pL := by
  set D : ℝ := C * (Ckap * μ ^ 2 * a * ℓ ^ 3 + 2 * μ * ℓ ^ 3) + 1 with hDdef
  have hℓ3pos : 0 < ℓ ^ 3 := pow_pos hℓ 3
  have hℓ3ne : ℓ ^ 3 ≠ 0 := ne_of_gt hℓ3pos
  have hli : 0 ≤ (ℓ ^ 3)⁻¹ := inv_nonneg.mpr (le_of_lt hℓ3pos)
  have hlimul : (ℓ ^ 3)⁻¹ * ℓ ^ 3 = 1 := inv_mul_cancel₀ hℓ3ne
  -- the `pDchi` hypothesis gives `pDchi + pL ≤ D * pL`
  have hDpL : pDchi + pL ≤ D * pL := by
    rw [hDdef]; nlinarith [hpD]
  have hsq : Real.sqrt pL * Real.sqrt (pDchi + pL) ≤ Real.sqrt D * pL :=
    sqrt_sqrt_le_D hpL hDpL
  -- bound on the bracket
  have hbr : (ℓ ^ 3)⁻¹ * Real.sqrt pL * Real.sqrt (pDchi + pL) + A2 * L2
      ≤ (ℓ ^ 3)⁻¹ * Real.sqrt D * pL + pL := by
    have h1 : (ℓ ^ 3)⁻¹ * (Real.sqrt pL * Real.sqrt (pDchi + pL))
        ≤ (ℓ ^ 3)⁻¹ * (Real.sqrt D * pL) := mul_le_mul_of_nonneg_left hsq hli
    nlinarith [h1, hA2']
  have hPnn : 0 ≤ 2 * (ℓ ^ 3)⁻¹ * ε * Cf * (n : ℝ) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hli) hε) hCf) (sq_nonneg _)
  have hXnn : 0 ≤ (ℓ ^ 3)⁻¹ * Real.sqrt D * pL + pL := by
    have : 0 ≤ (ℓ ^ 3)⁻¹ * Real.sqrt D * pL :=
      mul_nonneg (mul_nonneg hli (Real.sqrt_nonneg D)) hpL
    linarith
  -- `n` is bounded by `2 μ ℓ³`
  have hn2 : (n : ℝ) ^ 2 ≤ 4 * μ ^ 2 * ℓ ^ 6 :=
    calc (n : ℝ) ^ 2 ≤ (2 * μ * ℓ ^ 3) ^ 2 :=
          pow_le_pow_left₀ (Nat.cast_nonneg n) hn 2
      _ = 4 * μ ^ 2 * ℓ ^ 6 := by ring
  have hPle : 2 * (ℓ ^ 3)⁻¹ * ε * Cf * (n : ℝ) ^ 2 ≤ 8 * ε * Cf * μ ^ 2 * ℓ ^ 3 := by
    have h1 : 2 * (ℓ ^ 3)⁻¹ * ε * Cf * (n : ℝ) ^ 2
        ≤ 2 * (ℓ ^ 3)⁻¹ * ε * Cf * (4 * μ ^ 2 * ℓ ^ 6) :=
      mul_le_mul_of_nonneg_left hn2
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hli) hε) hCf)
    have h2 : 2 * (ℓ ^ 3)⁻¹ * ε * Cf * (4 * μ ^ 2 * ℓ ^ 6) = 8 * ε * Cf * μ ^ 2 * ℓ ^ 3 := by
      rw [show ℓ ^ 6 = ℓ ^ 3 * ℓ ^ 3 by ring]
      rw [show 2 * (ℓ ^ 3)⁻¹ * ε * Cf * (4 * μ ^ 2 * (ℓ ^ 3 * ℓ ^ 3))
          = 8 * ε * Cf * μ ^ 2 * ((ℓ ^ 3)⁻¹ * ℓ ^ 3) * ℓ ^ 3 by ring]
      rw [hlimul]; ring
    linarith [h1, h2]
  have hstep2 : 2 * (ℓ ^ 3)⁻¹ * ε * Cf * (n : ℝ) ^ 2
        * ((ℓ ^ 3)⁻¹ * Real.sqrt pL * Real.sqrt (pDchi + pL) + A2 * L2)
      ≤ 8 * ε * Cf * μ ^ 2 * ℓ ^ 3 * ((ℓ ^ 3)⁻¹ * Real.sqrt D * pL + pL) := by
    have h1 := mul_le_mul_of_nonneg_left hbr hPnn
    have h2 := mul_le_mul_of_nonneg_right hPle hXnn
    linarith [h1, h2]
  have hEq3 : 8 * ε * Cf * μ ^ 2 * ℓ ^ 3 * ((ℓ ^ 3)⁻¹ * Real.sqrt D * pL + pL)
      = 8 * ε * Cf * μ ^ 2 * pL * (Real.sqrt D + ℓ ^ 3) := by
    rw [show 8 * ε * Cf * μ ^ 2 * ℓ ^ 3 * ((ℓ ^ 3)⁻¹ * Real.sqrt D * pL + pL)
        = 8 * ε * Cf * μ ^ 2 * pL * ((ℓ ^ 3)⁻¹ * ℓ ^ 3 * Real.sqrt D)
          + 8 * ε * Cf * μ ^ 2 * ℓ ^ 3 * pL by ring]
    rw [hlimul]; ring
  -- the `ε` hypothesis, cleared of the division
  have hεK : ε * (16 * Cf * μ ^ 2 * (Real.sqrt D + ℓ ^ 3)) ≤ err := by
    by_cases hCf0 : Cf = 0
    · have hK0 : 16 * Cf * μ ^ 2 * (Real.sqrt D + ℓ ^ 3) = 0 := by rw [hCf0]; ring
      rw [hK0, mul_zero]; exact herr
    · have hCfpos : 0 < Cf := lt_of_le_of_ne hCf (Ne.symm hCf0)
      have hKpos : 0 < 16 * Cf * μ ^ 2 * (Real.sqrt D + ℓ ^ 3) := by
        have h1 : (0 : ℝ) < Real.sqrt D + ℓ ^ 3 := by
          have := Real.sqrt_nonneg D; linarith
        exact mul_pos (mul_pos (mul_pos (by norm_num) hCfpos) (pow_pos hμ 2)) h1
      exact (le_div_iff₀ hKpos).mp hε'
  have hstep4 : 8 * ε * Cf * μ ^ 2 * pL * (Real.sqrt D + ℓ ^ 3) ≤ (1 / 2) * err * pL := by
    have h1 := mul_le_mul_of_nonneg_right hεK hpL
    nlinarith [h1]
  calc 2 * (ℓ ^ 3)⁻¹ * ε * Cf * (n : ℝ) ^ 2
        * ((ℓ ^ 3)⁻¹ * Real.sqrt pL * Real.sqrt (pDchi + pL) + A2 * L2)
      ≤ 8 * ε * Cf * μ ^ 2 * ℓ ^ 3 * ((ℓ ^ 3)⁻¹ * Real.sqrt D * pL + pL) := hstep2
    _ = 8 * ε * Cf * μ ^ 2 * pL * (Real.sqrt D + ℓ ^ 3) := hEq3
    _ ≤ (1 / 2) * err * pL := hstep4

end Work.BoseBoxFock
