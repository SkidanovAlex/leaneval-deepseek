import Mathlib.Analysis.SpecialFunctions.Pow.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- Every unit of `ℝ` is a sign times a `p`-th power, for `p` prime (in fact for
any `p ≠ 0`): the `p`-th power of a nonnegative real can be inverted using
`Real.rpow` with exponent `1/p`. -/
theorem exists_sign_mul_pow_eq_real (p : ℕ) [Fact p.Prime] (x : ℝˣ) :
    ∃ (s y : ℝˣ), (s = 1 ∨ s = -1) ∧ s * y ^ p = x := by
  have hp : p ≠ 0 := (Fact.out (p := p.Prime)).ne_zero
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp
  -- the `p`-th root of a nonnegative real, as a natural power
  have key : ∀ a : ℝ, 0 ≤ a → (a ^ ((1:ℝ)/(p:ℝ))) ^ p = a := by
    intro a ha
    have h := Real.rpow_mul ha ((1:ℝ)/(p:ℝ)) (p:ℝ)
    rw [div_mul_cancel₀ (1:ℝ) hpR, Real.rpow_one, Real.rpow_natCast] at h
    exact h.symm
  rcases lt_or_gt_of_ne x.ne_zero with hneg | hpos
  · -- negative case: `x = -1 * (-x)^(1/p) ^ p`
    refine ⟨-1, Units.mk0 ((-(x:ℝ)) ^ ((1:ℝ)/(p:ℝ)))
      (ne_of_gt (Real.rpow_pos_of_pos (by linarith) _)), Or.inr rfl, ?_⟩
    rw [Units.ext_iff]
    simp only [Units.val_mul, Units.val_neg, Units.val_one, Units.val_pow_eq_pow_val,
      Units.val_mk0]
    rw [key (-(x:ℝ)) (by linarith)]
    ring
  · -- positive case: `x = 1 * x^(1/p) ^ p`
    refine ⟨1, Units.mk0 ((x:ℝ) ^ ((1:ℝ)/(p:ℝ)))
      (ne_of_gt (Real.rpow_pos_of_pos hpos _)), Or.inl rfl, ?_⟩
    rw [Units.ext_iff]
    simp only [one_mul, Units.val_pow_eq_pow_val, Units.val_mk0]
    exact key (x:ℝ) (le_of_lt hpos)

end Work.SSGRoute
