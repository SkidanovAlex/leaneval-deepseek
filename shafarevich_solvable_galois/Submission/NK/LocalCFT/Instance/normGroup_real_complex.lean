import Mathlib
import Submission.NK.LocalCFT.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The norm group of `ℂ / ℝ`

The image of the norm map `ℂˣ → ℝˣ` is exactly the group of positive real units:
`Algebra.norm ℝ` is `Complex.normSq` on `ℂ`, which is a sum of two squares, hence
positive on nonzero elements and surjective onto `(0, ∞)` (every positive real is a
square).  This is the archimedean place of `ℚ`: local class field theory for
`ℝ ⊆ ℂ` reduces to `ℝˣ ⧸ N ℂˣ ≅ ℤ/2`.
-/

namespace NK.LocalCFT.Instance

theorem normGroup_real_complex :
    NK.LocalReciprocity.normGroup ℝ ℂ = Units.posSubgroup ℝ := by
  ext x
  rw [NK.LocalReciprocity.normGroup_eq_range, MonoidHom.mem_range, Units.mem_posSubgroup]
  constructor
  · rintro ⟨y, rfl⟩
    rw [Units.coe_map, Algebra.norm_complex_apply]
    exact Complex.normSq_pos.mpr (Units.ne_zero y)
  · intro hx
    refine ⟨Units.mk0 (↑(Real.sqrt (x : ℝ)) : ℂ) ?_, ?_⟩
    · rw [Complex.ofReal_ne_zero]
      exact ne_of_gt (Real.sqrt_pos.mpr hx)
    · ext
      rw [Units.coe_map, Units.val_mk0, Algebra.norm_complex_apply, Complex.normSq_ofReal, ← sq,
        Real.sq_sqrt (le_of_lt hx)]

end NK.LocalCFT.Instance
