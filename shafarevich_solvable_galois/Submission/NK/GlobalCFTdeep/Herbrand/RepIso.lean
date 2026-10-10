import Mathlib.RepresentationTheory.Coinduced
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFTdeep.Herbrand.CoindHerbrand
import Submission.NK.GlobalCFTdeep.Herbrand.fiberIdelesRep_iso_coind
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Herbrand quotient of the fibre, from Shapiro's lemma

With the orbit identification `∏_{w | v} L_wˣ ≅ Coind_{D_w}^{G} L_wˣ`
(`NK.GlobalCFTdeep.Herbrand.fiberIdelesRep_iso_coind`, i.e. Milne's Proposition 2.7 at the level
of modules), Shapiro's lemma gives the Herbrand quotient of the fibre directly:

  `h(∏_{w | v} L_wˣ) = h(D_w, L_wˣ)`.

This file records that reduction (`herbrandEq_fiberIdeles_iff`), together with the elementary fact
that the Herbrand quotient is invariant under isomorphism of representations
(`herbrandEq_of_repIso`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain
open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep

open NK.GlobalCFT

/-- The Herbrand quotient is invariant under isomorphism of `ℤ[G]`-modules. -/
theorem herbrandEq_of_repIso {G : Type} [Group G] [Fintype G] {M N : Rep ℤ G} (e : M ≅ N)
    (m : ℕ) : HerbrandEq M m ↔ HerbrandEq N m := by
  have h0 : Nat.card (tateCohomology M 0) = Nat.card (tateCohomology N 0) :=
    Nat.card_congr
      ((tateCohomologyFunctor (R := ℤ) (G := G) 0).mapIso e).toLinearEquiv.toEquiv
  have h1 : Nat.card (tateCohomology M 1) = Nat.card (tateCohomology N 1) :=
    Nat.card_congr
      ((tateCohomologyFunctor (R := ℤ) (G := G) 1).mapIso e).toLinearEquiv.toEquiv
  rw [HerbrandEq, HerbrandEq, show hZero M = hZero N from h0, show hOne M = hOne N from h1]

/-- **Shapiro for the fibre** (Milne, *CFT*, Proposition 2.7, module level): the Herbrand quotient
of the places above `v` is that of the local units at a single `w | v`, with the action of the
decomposition group `D_w`. -/
theorem herbrandEq_fiberIdeles_iff {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : Place K) (w : Place L) (hw : Place.LiesOver w v)
    [Fintype (decompositionSubgroup (K := K) (L := L) w)] (m : ℕ) :
    HerbrandEq (fiberIdelesRep (K := K) (L := L) v) m ↔
      HerbrandEq (localUnitsRep (K := K) (L := L) w) m := by
  obtain ⟨e⟩ := Herbrand.fiberIdelesRep_iso_coind (K := K) (L := L) v w hw
  exact (herbrandEq_of_repIso e m).trans
    (herbrandEq_coind_iff (decompositionSubgroup (K := K) (L := L) w)
      (localUnitsRep (K := K) (L := L) w) m)

end NK.GlobalCFTdeep
