/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.NK.GlobalCFTdeep.CoCore.H1
import Submission.Commons.RepresentationTheory.GroupCohomology.natCard_groupCohomology_two_eq_natCard_tateCohomology_zero_of_cyclic

/-!
# Cyclic periodicity: `|H²(Gal(L/K), C_L)| = [L : K]`

For a **cyclic** finite Galois extension the cohomology of the Galois group is two-periodic, so
`H²(G, C_L) ≅ Ĥ⁰(G, C_L)`; combined with the `H⁰`-computation this computes the order of `H²`:

  `|H²(Gal(L/K), C_L)| = |Ĥ⁰(Gal(L/K), C_L)| = [C_K : N_{L/K} C_L]`.

With the index computation `[C_K : N_{L/K}C_L] = [L:K]` (the two inequalities) this is
Milne, *CFT*, Remark 5.5, in the cyclic case.  The periodicity statement in the form used here is
`Commons.RepresentationTheory.GroupCohomology.natCard_groupCohomology_two_eq_natCard_tateCohomology_zero_of_cyclic`.
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

/-- **Two-periodicity computes the order of `H²`**: for a cyclic extension,
`|H²(Gal(L/K), C_L)| = |Ĥ⁰(Gal(L/K), C_L)|`. -/
theorem natCard_groupCohomology_two_eq_natCard_tateCohomology_zero [IsCyclic (L ≃ₐ[K] L)] :
    Nat.card (groupCohomology (IdeleClassGroup.rep K L) 2) =
      Nat.card (tateCohomology (IdeleClassGroup.rep K L) 0) := by
  letI : CommGroup (L ≃ₐ[K] L) := IsCyclic.commGroup
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  exact Commons.RepresentationTheory.GroupCohomology.natCard_groupCohomology_two_eq_natCard_tateCohomology_zero_of_cyclic
    g hg (IdeleClassGroup.rep K L)

/-- **The order of `H²(Gal(L/K), C_L)` is the degree** for a cyclic extension, given the index
computation `[C_K : N_{L/K}C_L] = [L:K]` (which for a cyclic extension follows from the two
inequalities). -/
theorem natCard_groupCohomology_two_eq_finrank_of_index_eq [IsCyclic (L ≃ₐ[K] L)]
    (hidx : (Idele.normClassSubgroup K L).index = Module.finrank K L) :
    Nat.card (groupCohomology (IdeleClassGroup.rep K L) 2) = Module.finrank K L := by
  rw [natCard_groupCohomology_two_eq_natCard_tateCohomology_zero (K := K) (L := L),
    ← H0Computation.index_eq_natCard (globalCFT_H0Computation (K := K) (L := L)), hidx]

/-- **The order of `H²(Gal(L/K), C_L)` is the degree** for a cyclic extension, from the second
inequality and the Herbrand-quotient computation. -/
theorem natCard_groupCohomology_two_eq_finrank_of_secondInequality [IsCyclic (L ≃ₐ[K] L)]
    (hh : HerbrandQuotient K L) (h2 : SecondInequality) :
    Nat.card (groupCohomology (IdeleClassGroup.rep K L) 2) = Module.finrank K L := by
  haveI : IsMulCommutative (L ≃ₐ[K] L) := IsMulCommutative.of_comm fun a b => mul_comm a b
  exact natCard_groupCohomology_two_eq_finrank_of_index_eq
    (index_eq_finrank_of_secondInequality hh h2)

end NK.GlobalCFTdeep
