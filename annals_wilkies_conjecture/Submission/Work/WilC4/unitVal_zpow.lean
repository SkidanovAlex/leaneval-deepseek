import Mathlib
import Submission.Work.WilC4.Defs
import Submission.Work.WilC4.valEq_zpow
import Submission.Work.WilC4.valEq_one_iff_unitVal

namespace Work.WilC4

/-- The class of units (value `0`) is closed under integer powers.

`hx` says `x` lies in the Archimedean class of `1` (`ValEq 1 x`, by `valEq_one_iff_unitVal`),
and `ValEq` is preserved by integer powers (`valEq_zpow`); since `1 ^ n = 1` the element `x ^ n`
again lies in the class of `1`. -/
theorem unitVal_zpow {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] {x : M} (hx : WilkiesDesign.CG.IsUnitVal x) (n : ℤ) : WilkiesDesign.CG.IsUnitVal (x ^ n) := by
  rw [← valEq_one_iff_unitVal] at hx ⊢
  simpa using valEq_zpow hx n

end Work.WilC4
