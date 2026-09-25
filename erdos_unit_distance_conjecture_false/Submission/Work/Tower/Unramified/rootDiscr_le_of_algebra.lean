import Mathlib
import Submission.Work.Tower.Unramified.Discriminant

/-!
# Monotonicity of the root discriminant in towers

For a finite extension `L/F` of number fields, the root discriminant is monotone:
`rootDiscr F ≤ rootDiscr L`.  This follows from the tower formula for absolute
discriminants,
`|discr L| = N(𝔡_{L/F}) · |discr F| ^ [L : F]`,
and the fact that the absolute norm of the (nonzero) relative different `𝔡_{L/F}` is a
positive integer, so `|discr L| ≥ |discr F| ^ [L : F]`.  Taking `[L : ℚ]`-th roots and using
`[L : ℚ] = [L : F] · [F : ℚ]` gives the claim.

## Main result

* `Work.Tower.Unramified.rootDiscr_le_of_algebra`.
-/

open NumberField
open scoped Classical nonZeroDivisors

namespace Work.Tower.Unramified

/-- **Monotonicity of the root discriminant.**  If `L/F` is a finite extension of number
fields, then `rootDiscr F ≤ rootDiscr L`. -/
theorem rootDiscr_le_of_algebra
    (F L : Type*) [Field F] [NumberField F] [Field L] [NumberField L]
    [Algebra F L] [FiniteDimensional F L] :
    NumberField.rootDiscr F ≤ NumberField.rootDiscr L := by
  -- Step 1: the tower inequality on absolute discriminants,
  -- `|discr F| ^ [L : F] ≤ |discr L|`, from the different tower formula.
  have hmain := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) L (𝓞 L)
  have hdL : (discr L).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (discr_ne_zero L)
  have hNpos : 0 < Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 L)) := by
    rcases Nat.eq_zero_or_pos (Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 L))) with h | h
    · exfalso; rw [hmain, h, zero_mul] at hdL; exact hdL rfl
    · exact h
  have hineq : (discr F).natAbs ^ Module.finrank F L ≤ (discr L).natAbs := by
    rw [hmain]; exact Nat.le_mul_of_pos_left _ hNpos
  -- Step 2: the real version of the inequality, in terms of `|discr ·|`.
  have haF : (0 : ℝ) ≤ ((|discr F| : ℤ) : ℝ) := by positivity
  have hreal : ((|discr F| : ℤ) : ℝ) ^ Module.finrank F L ≤ ((|discr L| : ℤ) : ℝ) := by
    have h1 : ((|discr F| : ℤ) : ℝ) = ((discr F).natAbs : ℝ) := by
      rw [← Int.natCast_natAbs (discr F), Int.cast_natCast]
    have h2 : ((|discr L| : ℤ) : ℝ) = ((discr L).natAbs : ℝ) := by
      rw [← Int.natCast_natAbs (discr L), Int.cast_natCast]
    rw [h1, h2, ← Nat.cast_pow]
    exact_mod_cast hineq
  -- Step 3: exponent bookkeeping, `[L : ℚ] = [L : F] · [F : ℚ]`.
  have hfinNat : Module.finrank ℚ L = Module.finrank F L * Module.finrank ℚ F := by
    rw [← Module.finrank_mul_finrank ℚ F L, mul_comm]
  have hfin : (Module.finrank ℚ L : ℝ) =
      (Module.finrank F L : ℝ) * (Module.finrank ℚ F : ℝ) := by
    rw [hfinNat, Nat.cast_mul]
  have hn : (Module.finrank F L : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have hexp : (Module.finrank F L : ℝ) *
      ((Module.finrank F L : ℝ) * (Module.finrank ℚ F : ℝ))⁻¹ =
        ((Module.finrank ℚ F : ℝ))⁻¹ := by
    rw [mul_inv]; field_simp
  -- Step 4: assemble, taking `[L : ℚ]`-th roots.
  rw [rootDiscr_def, rootDiscr_def]
  calc ((|discr F| : ℤ) : ℝ) ^ ((Module.finrank ℚ F : ℝ))⁻¹
      = (((|discr F| : ℤ) : ℝ) ^ (Module.finrank F L : ℝ)) ^
          (((Module.finrank F L : ℝ)) * (Module.finrank ℚ F : ℝ))⁻¹ := by
        rw [← Real.rpow_mul haF, hexp]
    _ = (((|discr F| : ℤ) : ℝ) ^ Module.finrank F L) ^
          (((Module.finrank F L : ℝ)) * (Module.finrank ℚ F : ℝ))⁻¹ := by
        rw [Real.rpow_natCast]
    _ ≤ ((|discr L| : ℤ) : ℝ) ^
          (((Module.finrank F L : ℝ)) * (Module.finrank ℚ F : ℝ))⁻¹ :=
        Real.rpow_le_rpow (pow_nonneg haF _) hreal (by positivity)
    _ = ((|discr L| : ℤ) : ℝ) ^ (Module.finrank ℚ L : ℝ)⁻¹ := by
        rw [← hfin]

end Work.Tower.Unramified
