import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFTdeep.SecondInequality.KummerCase

/-- The norm of a natural number `p` inside the completion of a number field `K` at an infinite
place `w` is `p`.

Indeed, the place `w` is defined by a complex embedding `w.embedding : K →+* ℂ`, and an infinite
completion is isometric either to `ℝ` (`w` real) or to `ℂ` (`w` complex). In both cases the norm
of `(p : K)` (whose image in `ℂ` is the natural number `p`) is `|p| = p`. -/
theorem norm_algebraMap_natCast_infinitePlace {K : Type} [Field K] [NumberField K]
    (w : NumberField.InfinitePlace K) (p : ℕ) :
    ‖algebraMap K w.Completion (p : K)‖ = (p : ℝ) := by
  rw [NumberField.InfinitePlace.Completion.algebraMap_apply]
  rw [NumberField.InfinitePlace.Completion.norm_coe]
  rw [WithAbs.equiv_apply, WithAbs.ofAbs_toAbs]
  rw [← NumberField.InfinitePlace.norm_embedding_eq w (p : K)]
  simp

end NK.GlobalCFTdeep.SecondInequality.KummerCase
