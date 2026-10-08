import Mathlib
import Submission.Work.ZASS.Defs
import Submission.Work.Zassenhaus.Basic

namespace Work.ZASS

/-- **Z3 (blueprint §ZASS).** The elementwise identity `h u h⁻¹ • 0 = h • (u • 0)` for
`h ∈ G_{∞0}`, i.e. the equivariance of `u ↦ u • 0` under the conjugation action of `H` on
`U`.  Immediate since `h` fixes `0`, so `h⁻¹ • 0 = 0`. -/
theorem conjBy_smul_zero {G X : Type} [Group G] [MulAction G X] {inf zero : X} {h u : G}
    (hh : h ∈ Work.Zassenhaus.pairStab G inf zero) :
    Work.ZASS.conjBy h u • zero = h • (u • zero) := by
  have h0 : h • zero = zero := (Work.Zassenhaus.mem_pairStab_iff.mp hh).1
  have h0' : h⁻¹ • zero = zero := inv_smul_eq_iff.mpr h0.symm
  rw [conjBy, mul_smul, mul_smul, h0']

end Work.ZASS
