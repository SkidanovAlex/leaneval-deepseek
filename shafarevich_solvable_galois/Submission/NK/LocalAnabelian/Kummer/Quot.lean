import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.GroupTheory.Coset.Defs
import Submission.NK.LocalAnabelian.Kummer.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open IntermediateField

namespace NK.LocalAnabelian

noncomputable section

variable {k K' : Type*} [Field k] [Field K'] [Algebra k K']

/-- The Kummer field `k(a^{1/p})`, as a function on the class group `kˣ/(kˣ)^p`.

It is defined by choosing a representative of the class (which is harmless: the
field is independent of the choice, see
`kummerFieldQuot_mk`). -/
noncomputable def kummerFieldQuot (p : ℕ) (x : KummerGroup p k) : IntermediateField k K' :=
  kummerField (K' := K') p (Quotient.out x)

end

end NK.LocalAnabelian
