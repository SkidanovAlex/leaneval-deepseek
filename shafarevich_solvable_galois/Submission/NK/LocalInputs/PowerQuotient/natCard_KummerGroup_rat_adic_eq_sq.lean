/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Sanity check: the power-class count for `ℚ_p` reproduces `p²`

This file is the end-to-end validation of the arithmetic input of this area in the base case
`K = ℚ`.  Feeding

* the discharged arithmetic input `NK.LocalInputs.Zeta.localFieldInputs_rat`
  (`LocalFieldInputs ℚ 𝔭 p`, proved there from the commons),
* `localDegree ℚ 𝔭 = 1` (`NK.LocalInputs.Degree.localDegree_rat`) and
* `ζ_p ∉ ℚ_p` (`NK.LocalInputs.Zeta.not_exists_isPrimitiveRoot_rat_adic`)

into the main power-class count `NK.LocalInputs.natCard_KummerGroup_adicCompletion_eq_pow`
gives

  `|ℚ_pˣ / (ℚ_pˣ)^p| = p ^ ([ℚ_p : ℚ_p] + 1 + 0) = p²`,

which is exactly the value established *independently* in the commons as
`Commons.NumberTheory.NumberField.Completion.natCard_powerQuotient_adicCompletion_rat_units`
(for `p` odd).  This checks that the input structure `LocalFieldInputs` is satisfiable and that
the derivation of `|κˣ/(κˣ)^p| = p^{d+1+δ}` from it is consistent with the classical arithmetic:
for `κ = ℚ_p` the "missing case" `ζ_p ∉ κ` with `p` the residue characteristic occurs, and the
formula returns `p^{1+1+0} = p²`.
-/
import Submission.NK.LocalInputs.Instantiation
import Submission.NK.LocalInputs.ResidueChar.residueCard_eq_primesEquiv
import Submission.NK.LocalInputs.Zeta.localFieldInputs_rat
import Submission.NK.LocalInputs.Zeta.not_exists_isPrimitiveRoot_rat_adic
import Submission.NK.LocalInputs.Degree.localDegree_rat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open IsDedekindDomain.HeightOneSpectrum

namespace NK.LocalInputs

noncomputable section

/-- **The power-class count of `ℚ_p` from the local inputs**: `|ℚ_pˣ/(ℚ_pˣ)^p| = p²` for `p` odd.

This agrees with the independent commons computation
`Commons.NumberTheory.NumberField.Completion.natCard_powerQuotient_adicCompletion_rat_units`. -/
theorem natCard_KummerGroup_rat_adic_eq_sq
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) {p : ℕ}
    (hp : p.Prime) (hodd : p ≠ 2)
    (hprim : (Rat.HeightOneSpectrum.primesEquiv 𝔭).1 = p) :
    Nat.card (NK.LocalAnabelian.KummerGroup p (𝔭.adicCompletion ℚ)) = p ^ 2 := by
  rw [natCard_KummerGroup_adicCompletion_eq_pow 𝔭
    (NK.LocalInputs.Zeta.localFieldInputs_rat 𝔭 hp hodd hprim),
    NK.LocalInputs.Degree.localDegree_rat,
    (zetaIndicator_eq_zero_iff p (𝔭.adicCompletion ℚ)).mpr
      (NK.LocalInputs.Zeta.not_exists_isPrimitiveRoot_rat_adic 𝔭 hp hodd hprim)]

/-- **The commons' independent computation of the same count.**  This is
`Commons.NumberTheory.NumberField.Completion.natCard_powerQuotient_adicCompletion_rat_units`
restated in the vocabulary of `NK.LocalAnabelian.KummerGroup`; together with
`natCard_KummerGroup_rat_adic_eq_sq` it shows that the derivation of this area from the input
structure `LocalFieldInputs` reproduces the classical value for `ℚ_p`.

The two hypotheses `hres` (a residue-field cardinality) and `hprim` (a `primesEquiv` value) are
equivalent by `NK.LocalInputs.ResidueChar.residueCard_eq_primesEquiv`. -/
theorem natCard_KummerGroup_rat_adic_eq_sq_of_commons
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) {p : ℕ}
    (hp : p.Prime) (hodd : p ≠ 2)
    (hres : Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers ℚ)) = p) :
    Nat.card (NK.LocalAnabelian.KummerGroup p (𝔭.adicCompletion ℚ)) = p ^ 2 := by
  simpa [NK.LocalAnabelian.KummerGroup, NK.LocalAnabelian.powSubgroup] using
    Commons.NumberTheory.NumberField.Completion.natCard_powerQuotient_adicCompletion_rat_units
      hp hodd 𝔭 hres

end

end NK.LocalInputs
