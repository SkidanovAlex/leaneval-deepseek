/-
# The character expansion of `zmodAvg`

This module proves `Work.KMTPlan.A6.zmodAvgCharExpansion`: the bilinear averaging operator
`zmodAvg P Q` is diagonalised by the characters `zmChar Q a` of `ZMod Q`, with the arithmetic
coefficient `zmLambda P Q a b`:

`A_{ZMod Q}(ξ_a, ξ_b) = ξ_{a+b} · Λ_P(a,b)`.

The two structural facts used are the multiplicativity of `zmChar` in each variable,
`ξ_c(x+y) = ξ_c(x)ξ_c(y)` and `ξ_{a+b}(x) = ξ_a(x)ξ_b(x)`, which follow from the identification
`ξ_c(x) = ZMod.stdAddChar (c * x)` and the additivity of `ZMod.stdAddChar`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlAdelicDefs

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.KMTPlan.A6

open Finset
open scoped BigOperators

/-- The product of two finite sums as a double sum. -/
private lemma finset_sum_mul_sum {ι κ R : Type*} [NonUnitalNonAssocSemiring R]
    (s : Finset ι) (t : Finset κ) (f : ι → R) (g : κ → R) :
    (∑ a ∈ s, f a) * (∑ b ∈ t, g b) = ∑ a ∈ s, ∑ b ∈ t, f a * g b := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun a _ => Finset.mul_sum t g (f a))

end Work.KMTPlan.A6
