import Mathlib
import Submission.Work.ShafarevichKoch.GenusConj

namespace Work.ShafarevichKoch

open Work.ClassFieldTower

/-- `Kc = ℚ(√-30030)` is quadratic, so for `z ∈ 𝓞 Kc` the product with its conjugate is the
(integer) norm: `z * conjR z = Algebra.norm ℤ z` (as elements of `𝓞 Kc`).  Hints: `conjR` is the
restriction of the nontrivial `ℚ`-automorphism `conjK` of `Kc` (`conjR_apply_coe`); use
`conjK_mul_self : w * conjK w = algebraMap ℚ Kc (Algebra.norm ℚ w)` from `GenusConj.lean`,
`Algebra.coe_norm_int`, and injectivity of the coercion `𝓞 Kc → Kc`. -/
theorem conjR_mul_self (z : NumberField.RingOfIntegers Work.ClassFieldTower.Kc) :
    z * Work.ShafarevichKoch.conjR z
      = (Algebra.norm ℤ z : NumberField.RingOfIntegers Work.ClassFieldTower.Kc) := by
  apply NumberField.RingOfIntegers.coe_injective
  push_cast
  change (↑z : Kc) * conjK (↑z) = (((Algebra.norm ℤ z : ℤ) : Kc))
  rw [conjK_mul_self]
  rw [← map_intCast (algebraMap ℚ Kc) (Algebra.norm ℤ z), Algebra.coe_norm_int z]

end Work.ShafarevichKoch
