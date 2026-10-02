import Mathlib
import Submission.Work.Top.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Top

/-- The exponential `exp (2πi x)` depends on `x : ℝ` only through its class modulo `1`:
replacing `x` by its representative in `[0,1)` does not change the value. -/
theorem exp_two_pi_mul_toIcoMod_one (x : ℝ) :
    Complex.exp (2 * (Real.pi : ℂ) * (x : ℂ) * Complex.I) =
      Complex.exp (2 * (Real.pi : ℂ) * ((toIcoMod (p := (1 : ℝ)) one_pos 0 x : ℝ) : ℂ) * Complex.I) := by
  have h1 : x - (toIcoMod (p := (1 : ℝ)) one_pos 0 x) =
      ((toIcoDiv (p := (1 : ℝ)) one_pos 0 x : ℤ) : ℝ) := by
    rw [self_sub_toIcoMod (p := (1 : ℝ)) one_pos (a := 0) x]
    simp
  have h2 : (x : ℂ) = ((toIcoMod (p := (1 : ℝ)) one_pos 0 x : ℝ) : ℂ) +
      ((toIcoDiv (p := (1 : ℝ)) one_pos 0 x : ℤ) : ℂ) := by
    have hc : (x : ℂ) - ((toIcoMod (p := (1 : ℝ)) one_pos 0 x : ℝ) : ℂ) =
        (((toIcoDiv (p := (1 : ℝ)) one_pos 0 x : ℤ)) : ℂ) := by exact_mod_cast h1
    linear_combination hc
  refine Complex.exp_eq_exp_iff_exists_int.mpr ⟨toIcoDiv (p := (1 : ℝ)) one_pos 0 x, ?_⟩
  conv_lhs => rw [h2]
  ring

theorem Phi_eq_norm_mul_exp_extAngle {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : Work.Top.NakaneData Mb Φ) {c : ℂ}
    (hc : Φ c ≠ 0) :
    Φ c = ↑‖Φ c‖ * Complex.exp (2 * (Real.pi : ℂ) * (Work.Top.NakaneData.extAngle Φ c : ℂ) * Complex.I) := by
  rw [Work.Top.NakaneData.extAngle]
  rw [← exp_two_pi_mul_toIcoMod_one (Complex.arg (Φ c) / (2 * Real.pi))]
  rw [show 2 * (Real.pi : ℂ) * ((Complex.arg (Φ c) / (2 * Real.pi) : ℝ) : ℂ) = (Complex.arg (Φ c) : ℂ) from by
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp]
  exact (Complex.norm_mul_exp_arg_mul_I (Φ c)).symm

end Work.Top
