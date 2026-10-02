import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

/-- **Level-band monotonicity.** Passing from the level `t ≤ η ^ ((1/Λ)^m)` to the coarser orbit
level: for `η, Λ, t > 1` and `j ≤ m`, the value `t ^ (Λ ^ (m - j))` is still bounded by `η`.

Indeed, raising the hypothesis to the power `Λ ^ (m - j) ≥ 0` gives
`t ^ (Λ ^ (m - j)) ≤ η ^ (((1/Λ)^m) * Λ ^ (m - j))` and the exponent satisfies
`((1/Λ)^m) * Λ ^ (m - j) = Λ ^ (m - j) / Λ ^ m ≤ 1`, because `m - j ≤ m`. -/
theorem rpow_band {η Λ t : ℝ} {m j : ℕ} (hη : 1 < η) (hΛ : 1 < Λ) (ht : 1 < t) (hj : j ≤ m)
    (hlev : t ≤ η ^ (((1 : ℝ) / Λ) ^ m)) : t ^ (Λ ^ (m - j)) ≤ η := by
  have hη0 : (0 : ℝ) < η := lt_trans zero_lt_one hη
  have hΛ0 : (0 : ℝ) < Λ := lt_trans zero_lt_one hΛ
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  set a : ℝ := Λ ^ (m - j) with ha
  have ha0 : (0 : ℝ) ≤ a := by rw [ha]; positivity
  have hstep : t ^ a ≤ (η ^ (((1 : ℝ) / Λ) ^ m)) ^ a :=
    Real.rpow_le_rpow ht0.le hlev ha0
  have hpow : (η ^ (((1 : ℝ) / Λ) ^ m)) ^ a = η ^ ((((1 : ℝ) / Λ) ^ m) * a) := by
    rw [Real.rpow_mul hη0.le]
  rw [hpow] at hstep
  have hexp : (((1 : ℝ) / Λ) ^ m) * a ≤ 1 := by
    rw [ha]
    have hprod : (((1 : ℝ) / Λ) ^ m) * Λ ^ (m - j) = Λ ^ (m - j) / Λ ^ m := by
      rw [div_pow, one_pow, one_div, inv_mul_eq_div]
    rw [hprod, div_le_one (pow_pos hΛ0 m)]
    exact pow_le_pow_right₀ (le_of_lt hΛ) (Nat.sub_le m j)
  calc t ^ (Λ ^ (m - j)) = t ^ a := by rw [ha]
    _ ≤ η ^ ((((1 : ℝ) / Λ) ^ m) * a) := hstep
    _ ≤ η ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (le_of_lt hη) hexp
    _ = η := Real.rpow_one η

end Work.LandLeaves
