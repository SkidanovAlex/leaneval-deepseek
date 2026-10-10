import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFTdeep.Inequalities
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The vanishing of `H¹(Gal(L/K), C_L)`

Milne, *Class Field Theory*, Theorem 5.1(b): for a finite Galois extension `L/K` of number fields
one has `H¹(Gal(L/K), C_L) = 0`.  Together with the `H⁰`-computation this is one half of the
class-formation axioms (`NK.GlobalCFT.CohomologicalFieldAxiom`).

The proof here is the classical equivalence (a) ⟺ (b) of Milne's Lemma 5.2 in the form in which
the chapter can state it: **the Herbrand-quotient computation `h(G, C_L) = [L : K]` and the index
computation `[C_K : N_{L/K}C_L] = [L : K]` together force `|Ĥ¹(G, C_L)| = 1`**, because
`|Ĥ⁰(G,C_L)| = [C_K : N_{L/K}C_L]` (`NK.GlobalCFT.H0Computation.index_eq_natCard`) and
`|Ĥ⁰(G,C_L)| = [L:K]·|Ĥ¹(G,C_L)|` (`NK.GlobalCFT.HerbrandQuotient.herbrand`).

The index computation is available for abelian `L/K` from the two inequalities
(`index_eq_finrank_of_secondInequality`), so for abelian `L/K` the vanishing of `H¹` is proved here
from the two named inputs `HerbrandQuotient` and `SecondInequality`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain
open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep

open NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **The Herbrand-quotient computation and the index computation force `Ĥ¹(G, C_L)` to vanish.**

Since `|Ĥ⁰(G, C_L)| = [C_K : N_{L/K}C_L]` (the `H⁰`-computation) and
`|Ĥ⁰(G, C_L)| = [L : K]·|Ĥ¹(G, C_L)|` (the Herbrand-quotient computation), the equality
`[C_K : N_{L/K}C_L] = [L : K]` gives `[L:K]·|Ĥ¹| = [L:K]`, hence `|Ĥ¹| = 1`. -/
theorem subsingleton_tateCohomology_one_of_index_eq (hh : HerbrandQuotient K L)
    (hidx : (Idele.normClassSubgroup K L).index = Module.finrank K L) :
    Subsingleton (tateCohomology (IdeleClassGroup.rep K L) 1) := by
  have hcard : Nat.card (tateCohomology (IdeleClassGroup.rep K L) 0) = Module.finrank K L := by
    rw [← H0Computation.index_eq_natCard (globalCFT_H0Computation (K := K) (L := L)), hidx]
  have h1c : Nat.card (tateCohomology (IdeleClassGroup.rep K L) 1) = 1 := by
    have h := hh.herbrand
    rw [hcard] at h
    have h' : Module.finrank K L * Nat.card (tateCohomology (IdeleClassGroup.rep K L) 1)
        = Module.finrank K L := h.symm
    refine Nat.mul_left_cancel (Module.finrank_pos (R := K) (M := L)) ?_
    rw [h', mul_one]
  exact (Nat.card_eq_one_iff_unique.mp h1c).1

/-- **Vanishing of `H¹(Gal(L/K), C_L)`.**  The group cohomology `H¹` agrees with the Tate group
`Ĥ¹` in positive degrees (`TateCohomology.isoGroupCohomology`). -/
theorem subsingleton_groupCohomology_one_of_index_eq (hh : HerbrandQuotient K L)
    (hidx : (Idele.normClassSubgroup K L).index = Module.finrank K L) :
    Subsingleton (groupCohomology (IdeleClassGroup.rep K L) 1) := by
  haveI : Subsingleton (tateCohomology (IdeleClassGroup.rep K L) 1) :=
    subsingleton_tateCohomology_one_of_index_eq hh hidx
  exact ((TateCohomology.isoGroupCohomology (R := ℤ) (G := L ≃ₐ[K] L) 1).app
    (IdeleClassGroup.rep K L)).toLinearEquiv.symm.injective.subsingleton

/-- **Vanishing of `Ĥ¹(Gal(L/K), C_L)` for abelian `L/K`**, from the second inequality and the
Herbrand-quotient computation (Milne, *CFT*, Theorem 5.1(b) with Lemma 5.2). -/
theorem subsingleton_tateCohomology_one_of_secondInequality [IsMulCommutative (L ≃ₐ[K] L)]
    (hh : HerbrandQuotient K L) (h2 : SecondInequality) :
    Subsingleton (tateCohomology (IdeleClassGroup.rep K L) 1) :=
  subsingleton_tateCohomology_one_of_index_eq hh (index_eq_finrank_of_secondInequality hh h2)

/-- **Vanishing of `H¹(Gal(L/K), C_L)` for abelian `L/K`.** -/
theorem subsingleton_groupCohomology_one_of_secondInequality [IsMulCommutative (L ≃ₐ[K] L)]
    (hh : HerbrandQuotient K L) (h2 : SecondInequality) :
    Subsingleton (groupCohomology (IdeleClassGroup.rep K L) 1) :=
  subsingleton_groupCohomology_one_of_index_eq hh (index_eq_finrank_of_secondInequality hh h2)

end NK.GlobalCFTdeep
