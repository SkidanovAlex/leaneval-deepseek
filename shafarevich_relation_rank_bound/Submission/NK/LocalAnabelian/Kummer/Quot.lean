/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Kummer field as a function on the class group `kˣ/(kˣ)^p`

The Kummer field of an element `a` of `kˣ` depends only on the class of `a` in
`kˣ/(kˣ)^p`.  This file introduces the resulting function on the class group;
the well-definedness proof is `NK.LocalAnabelian.kummerField_eq_of_div_mem_powSubgroup`
and is imported in `Submission.NK.LocalAnabelian.Kummer.QuotAPI`.
-/
import Submission.NK.LocalAnabelian.Kummer.Defs

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
