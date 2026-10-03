import Mathlib

-- The two hypotheses `hC`, `ht` are part of the requested statement; the argument below does not
-- need them.
set_option linter.unusedVariables false

namespace Work.Peluse.LadderA

/-- **Per-`Q` arithmetic of the ladder.**

With `p = 1/2^C` and `M = 2^tbig * 2^C`, the datum
`δ * (1/2)^(2^(tbig - s') - 1) * X^(2^tbig) ≤ Z` gives
`(δ * (1/2)^M * X^(2^tbig))^p ≤ Z^p`, because `2^(tbig - s') - 1 ≤ 2^tbig ≤ M` and `1/2 ≤ 1`
(so `(1/2)^M ≤ (1/2)^(2^(tbig-s')-1)`).  Expanding the left-hand side with `Real.mul_rpow`
and `Real.rpow_mul` (using `M * p = 2^tbig`, `x^(2^tbig) = x^((2^tbig : ℝ))` and
`p = (2^C)⁻¹`) yields exactly the claim. -/
theorem perQArith {C tbig s' : ℕ} (hC : 1 ≤ C) (ht : s' + 1 ≤ tbig) {δ X Z : ℝ}
    (hδ : 0 ≤ δ) (hX : 0 ≤ X) (hZ : δ * ((1 / 2 : ℝ) ^ (2 ^ (tbig - s') - 1)) * X ^ (2 ^ tbig) ≤ Z) :
    δ ^ (1 / (2 : ℝ) ^ C) * ((1 : ℝ) / 2) ^ (2 ^ tbig) * X ^ ((2 : ℝ) ^ tbig / (2 : ℝ) ^ C)
      ≤ Z ^ (1 / (2 : ℝ) ^ C) := by
  set p : ℝ := 1 / (2 : ℝ) ^ C with hp
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  set M : ℕ := 2 ^ tbig * 2 ^ C with hM
  -- the exponent of `(1/2)^·` in the hypothesis is at most `M`
  have hexp : 2 ^ (tbig - s') - 1 ≤ M := by
    rw [hM]
    exact le_trans (Nat.sub_le _ _)
      (le_trans (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _))
        (Nat.le_mul_of_pos_right _ (pow_pos (by norm_num) _)))
  have hhalf : ((1:ℝ)/2)^M ≤ ((1:ℝ)/2)^(2^(tbig - s') - 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hexp
  have hW : δ * ((1:ℝ)/2)^M * X^(2^tbig) ≤ Z :=
    le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhalf hδ) (pow_nonneg hX _)) hZ
  have hpval : p = ((2:ℝ)^C)⁻¹ := by rw [hp]; exact one_div _
  -- the left-hand side of the goal is `(δ * (1/2)^M * X^(2^tbig))^p`
  have hBpow : (δ * ((1:ℝ)/2)^M * X^(2^tbig)) ^ p
      = δ ^ p * ((1:ℝ)/2)^(2^tbig) * X ^ ((2:ℝ)^tbig / (2:ℝ)^C) := by
    rw [Real.mul_rpow (by positivity) (pow_nonneg hX _)]
    rw [Real.mul_rpow hδ (by positivity : (0:ℝ) ≤ ((1:ℝ)/2)^M)]
    have h1p : (((1:ℝ)/2)^M) ^ p = ((1:ℝ)/2)^(2^tbig) := by
      rw [← Real.rpow_natCast ((1:ℝ)/2) M, ← Real.rpow_natCast ((1:ℝ)/2) (2^tbig)]
      rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 1/2)]
      congr 1
      have hcastM : ((M:ℕ):ℝ) = (2:ℝ)^tbig * (2:ℝ)^C := by
        rw [hM]; push_cast; ring
      rw [hcastM, hpval, Nat.cast_pow, mul_assoc,
        mul_inv_cancel₀ (by positivity : ((2:ℝ)^C) ≠ 0), mul_one]
      rfl
    have h2p : (X^(2^tbig)) ^ p = X ^ ((2:ℝ)^tbig/(2:ℝ)^C) := by
      rw [← Real.rpow_natCast X (2^tbig)]
      rw [← Real.rpow_mul hX]
      congr 1
      rw [Nat.cast_pow, hpval, div_eq_mul_inv]
      rfl
    rw [h1p, h2p]
  rw [← hBpow]
  exact Real.rpow_le_rpow (by positivity) hW hp0

end Work.Peluse.LadderA
