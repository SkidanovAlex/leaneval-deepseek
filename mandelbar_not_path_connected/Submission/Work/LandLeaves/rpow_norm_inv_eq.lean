import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

/-- Key algebraic identity for the Mandelbar ray-normalisation: with exponent
`p = -1/n`, the product of the `n`-fold scaled modulus `n‖c‖` (to the power `p`)
and the modulus of the inverse of `n c zⁿ` (to the power `p`) equals `‖z‖`. -/
theorem rpow_norm_inv_eq (n : ℕ) (hn : 0 < n) (c z : ℂ) (hc : c ≠ 0) (hz : z ≠ 0) :
    ‖z‖ = ((n : ℝ) * ‖c‖) ^ (-(1 : ℝ) / (n : ℝ))
        * ‖(1 : ℂ) / ((n : ℂ) * c * z ^ n)‖ ^ (-(1 : ℝ) / (n : ℝ)) := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
  have hcn : (0:ℝ) < ‖c‖ := norm_pos_iff.mpr hc
  have hzn : (0:ℝ) < ‖z‖ := norm_pos_iff.mpr hz
  have hA : 0 < (n:ℝ) * ‖c‖ := mul_pos (by exact_mod_cast hn) hcn
  have hznn : z ^ n ≠ 0 := pow_ne_zero n hz
  have hden : (n:ℂ) * c * z ^ n ≠ 0 := mul_ne_zero (mul_ne_zero hnC hc) hznn
  have hnorm_den : ‖(n : ℂ) * c * z ^ n‖ = (n:ℝ) * ‖c‖ * ‖z‖^n := by
    rw [norm_mul, norm_mul, Complex.norm_natCast, norm_pow]
  have hB : ‖(1 : ℂ) / ((n : ℂ) * c * z ^ n)‖ = 1 / ((n:ℝ) * ‖c‖ * ‖z‖^n) := by
    rw [norm_div, hnorm_den, norm_one]
  have hBnn : 0 ≤ ‖(1 : ℂ) / ((n : ℂ) * c * z ^ n)‖ := norm_nonneg _
  have hAnn : 0 ≤ (n:ℝ) * ‖c‖ := le_of_lt hA
  have hAB : ((n:ℝ) * ‖c‖) * ‖(1 : ℂ) / ((n : ℂ) * c * z ^ n)‖ = 1 / ‖z‖^n := by
    rw [hB]
    field_simp
  rw [← Real.mul_rpow hAnn hBnn]
  rw [hAB]
  rw [← one_div_pow]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by positivity)]
  have hexp : ((n:ℝ)) * (-(1:ℝ)/(n:ℝ)) = -1 := by
    field_simp
  rw [hexp, Real.rpow_neg_one, one_div, inv_inv]

end Work.LandLeaves
