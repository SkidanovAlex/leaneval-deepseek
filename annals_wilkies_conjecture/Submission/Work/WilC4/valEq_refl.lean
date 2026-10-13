import Mathlib
import Submission.Work.WilC4.Defs

namespace Work.WilC4

/-- `ValEq` is reflexive: every element is comparable with itself.  The witness is `N = 1`,
since `1⁻¹ * |x| = |x| ≤ 1 * |x|`. -/
theorem valEq_refl {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] (x : M) : ValEq x x :=
  ⟨1, Nat.one_pos, by simp, by simp⟩

end Work.WilC4
