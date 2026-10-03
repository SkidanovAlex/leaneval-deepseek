/-
# `Submission.Work.FIArea1.Defs` — vocabulary for the divisor sum of *FI* §5

Two objects:

* `Nsol d`, the number of solutions `(r,s) ∈ (Z/d)²` of `r² + s² ≡ 0`, i.e.
  the number of residue classes modulo `d` in which a lattice point `z` with
  `d ∣ |z|²` can lie (`N(d)` of the route book for `sum_tau_gnorm`);
* `boxZ n`, the integer box `[-n,n]²`, the coordinate model of `Work.FIPlan.gBox`.
-/
import Mathlib
import Submission.Work.FIArea1.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.FIArea1

open Set

noncomputable section

/-- The number of solutions `(r,s)` of `r² + s² = 0` in `ZMod d`; the `N(d)` of
the divisor-sum route (*FI* §5): `{z : d ∣ |z|²}` is a union of `N(d)` cosets of `dℤ²`. -/
def Nsol (d : ℕ) : ℕ := ({z : ZMod d × ZMod d | z.1 ^ 2 + z.2 ^ 2 = 0}).ncard

/-- The integer box `[-n,n] × [-n,n]`, coordinate model of `Work.FIPlan.gBox`. -/
def boxZ (n : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(n : ℤ)) (n : ℤ)).product (Finset.Icc (-(n : ℤ)) (n : ℤ))

end

end Work.FIArea1
