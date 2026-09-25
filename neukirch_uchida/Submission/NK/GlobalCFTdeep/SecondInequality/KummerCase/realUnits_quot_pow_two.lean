import Mathlib

namespace NK.GlobalCFTdeep.SecondInequality.KummerCase

/-- The squares of the units of `ℝ` are exactly the positive units: every positive real
has a real square root, and a square of a nonzero real is positive. -/
lemma range_powMonoidHom_two_realUnits :
    (powMonoidHom 2 : ℝˣ →* ℝˣ).range = Units.posSubgroup ℝ := by
  apply Subgroup.ext
  intro u
  rw [MonoidHom.mem_range, Units.mem_posSubgroup]
  constructor
  · rintro ⟨v, rfl⟩
    simpa [powMonoidHom, Units.val_pow_eq_pow_val] using sq_pos_of_ne_zero v.ne_zero
  · intro hu
    refine ⟨Units.mk0 (Real.sqrt (u : ℝ)) (ne_of_gt (Real.sqrt_pos_of_pos hu)), ?_⟩
    ext
    simp [powMonoidHom, Units.val_pow_eq_pow_val, Real.sq_sqrt hu.le]

/-- The quotient of `ℝˣ` by its subgroup of squares has two elements, the two cosets of
`1` and `-1`: `ℝˣ ⧸ (ℝˣ)² ≅ {±1}`. -/
theorem realUnits_quot_pow_two :
    Nat.card (ℝˣ ⧸ (powMonoidHom 2 : ℝˣ →* ℝˣ).range) = 2 := by
  rw [range_powMonoidHom_two_realUnits,
    ← Subgroup.index_eq_card (Units.posSubgroup ℝ)]
  exact Units.index_posSubgroup ℝ

end NK.GlobalCFTdeep.SecondInequality.KummerCase
