/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The `ℚ_p` case: consistency of the power class exponent

The local inputs of `NK.LocalAnabelian.PadicGaloisInputs` include the structure theory
of `κˣ` in the form `|κˣ/(κˣ)^p| = p^{d+1+δ}`.  For `κ = ℚ_p` (`d = 1`, and `δ = 0`
because `ζ_p ∉ ℚ_p`) this reads `p²`, and that case is already available in the shared
commons as
`Commons.NumberTheory.NumberField.Completion.natCard_powerQuotient_adicCompletion_rat_units`.
This file records the translation into the vocabulary of this chapter, so that the
exponent `d + 1 + δ` is not merely asserted but anchored in a proved arithmetic
statement.
-/
import Submission.NK.LocalAnabelian.PadicField.Defs
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_powerQuotient_adicCompletion_rat_units
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open IsDedekindDomain.HeightOneSpectrum

namespace NK.LocalAnabelian

noncomputable section

/-- The `p`-th power class group of `ℚ_p` has order `p^2 = p^{d+1+δ}` with
`d = 1`, `δ = 0` — the arithmetic input of the local theory, in the `ℚ_p` case. -/
theorem natCard_KummerGroup_rat_adic {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (hres : Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) = p) :
    Nat.card (KummerGroup p (v.adicCompletion ℚ)) = p ^ (1 + 1 + 0) := by
  simpa [KummerGroup, powSubgroup] using
    Commons.NumberTheory.NumberField.Completion.natCard_powerQuotient_adicCompletion_rat_units
      hp hodd v hres

end

end NK.LocalAnabelian
