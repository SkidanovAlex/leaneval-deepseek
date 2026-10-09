/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The exact sequence of ramification theory and the Frobenius

For a finite Galois extension `L/K` of number fields and a prime `w` of `L` with `v` the prime of
`K` below it, this file provides

* `ramificationExactSequence`: the canonical isomorphism
  `D_w ⧸ I_w ≃* Gal(κ_w / κ_v)`;
* `residueFrobenius`: the Frobenius of the residue field extension `κ_w/κ_v`, i.e. the `q`-power
  map with `q = #κ_v`;
* `frobenius`: an element of `D_w` lifting `residueFrobenius`, i.e. a Frobenius at `w`
  (well defined modulo `I_w`).

## Main definitions

* `Work.LocalFields.ramificationExactSequence`
* `Work.LocalFields.residueFrobenius`, `Work.LocalFields.residueFrobenius_apply`
* `Work.LocalFields.frobeniusClass`, `Work.LocalFields.frobenius`
-/
import Submission.Work.LocalFields.Decomposition
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocalFields

open scoped NumberField Pointwise Valued WithZero

variable {K : Type*} [Field K] {L : Type*} [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- **The exact sequence of ramification theory.**  The quotient of the decomposition group `D_w`
by the inertia subgroup `I_w` is canonically the Galois group of the residue field extension
`κ_w/κ_v`. -/
noncomputable def ramificationExactSequence (v : FinitePrime K) (w : FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal] :
    decompositionGroup K w ⧸ inertiaSubgroup K w ≃*
      (𝓞 L ⧸ w.asIdeal) ≃ₐ[𝓞 K ⧸ v.asIdeal] (𝓞 L ⧸ w.asIdeal) :=
  (QuotientGroup.quotientMulEquivOfEq
      (inertiaSubgroup_eq_inertia_stabilizer (K := K) (w := w))).trans
    (Ideal.Quotient.stabilizerQuotientInertiaEquiv Gal(L/K) v.asIdeal w.asIdeal)

/-- The Frobenius of the residue field extension `κ_w/κ_v`: the `#κ_v`-power map. -/
noncomputable def residueFrobenius (v : FinitePrime K) (w : FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal] :
    (𝓞 L ⧸ w.asIdeal) ≃ₐ[𝓞 K ⧸ v.asIdeal] (𝓞 L ⧸ w.asIdeal) := by
  letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  letI : Field (𝓞 L ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
  exact FiniteField.frobeniusAlgEquivOfAlgebraic (𝓞 K ⧸ v.asIdeal) (𝓞 L ⧸ w.asIdeal)

/-- The Frobenius of the residue field extension is the `#κ_v`-power map. -/
theorem residueFrobenius_apply (v : FinitePrime K) (w : FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal] (x : 𝓞 L ⧸ w.asIdeal) :
    residueFrobenius v w x = x ^ Nat.card (𝓞 K ⧸ v.asIdeal) := by
  rw [residueFrobenius]
  simp only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
  rw [Nat.card_eq_fintype_card]

/-- The class of the Frobenius in `D_w ⧸ I_w`. -/
noncomputable def frobeniusClass (v : FinitePrime K) (w : FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal] :
    decompositionGroup K w ⧸ inertiaSubgroup K w :=
  (ramificationExactSequence v w).symm (residueFrobenius v w)

/-- A **Frobenius** at `w`: an element of the decomposition group whose class in `D_w ⧸ I_w` is
the Frobenius of the residue field extension. -/
noncomputable def frobenius (v : FinitePrime K) (w : FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal] : decompositionGroup K w :=
  Quotient.out (frobeniusClass v w)

/-- **For an unramified prime, the decomposition group is the Galois group of the residue field
extension.**  This is the exact sequence of ramification theory in the case `I_w = 1`. -/
noncomputable def unramifiedDecompositionEquiv (v : FinitePrime K) (w : FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal] (hunr : IsUnramifiedAt K w) :
    decompositionGroup K w ≃*
      (𝓞 L ⧸ w.asIdeal) ≃ₐ[𝓞 K ⧸ v.asIdeal] (𝓞 L ⧸ w.asIdeal) :=
  QuotientGroup.quotientBot.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hunr.symm).trans (ramificationExactSequence v w))

end Work.LocalFields
