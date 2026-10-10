import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFTdeep.Herbrand.Prop27
import Submission.NK.GlobalCFTdeep.Herbrand.hZero_hOne_unitIdelesOutsideRep_eq_one
import Submission.NK.GlobalCFTdeep.Herbrand.hposSup_supportedIdelesRep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Milne's Proposition 2.7 with the two side conditions discharged

`herbrandEq_tIdelesRep_of_outsideTrivial` (`Herbrand/Prop27.lean`) proves
`h(𝕀_{L,T}) = ∏_{v∈S}|D_{w_v}|` from the triviality of the cohomology of the units outside `T` and
the positivity of `Ĥ¹` of the idèles supported on `T`.  This file supplies those two side
conditions:

* `hposSup_supportedIdelesRep`: `Ĥ¹` of the idèles supported on `T` is trivial, because `Ĥ¹` of
  each fibre is trivial (Hilbert 90 at every place, `hOne_fiberIdelesRep_eq_one`);
* `hZero_hOne_unitIdelesOutsideRep_eq_one`: the cohomology of `∏_{v∉S}∏_{w|v}U_w` is trivial,
  under the hypothesis that no place outside `S` ramifies — which is exactly the hypothesis under
  which Milne applies Proposition 2.7 (`S` contains all ramified primes).

The resulting theorem `herbrandEq_tIdelesRep_of_fibreTrivial` has a single remaining hypothesis, the
per-place triviality `Ĥ⁰(fiberUnitsRep v) = Ĥ¹(fiberUnitsRep v) = 1` for `v ∉ S`; that hypothesis is
turned into the ramification condition in `Herbrand/Prop27Unramified.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain
open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep.Herbrand

open NK.GlobalCFT
open NK.GlobalCFTdeep

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **Milne, *CFT*, Proposition 2.7, with the side conditions discharged.**  For a cyclic extension
`L/K`, a finite set `S` of places of `K` containing the archimedean places, `T` the places of `L`
above `S`, and a choice `w v` of a place above each `v ∈ S`, the Herbrand quotient of the
`T`-idèles is the product of the local degrees; the single hypothesis is that at every `v ∉ S` the
block of local units `∏_{w|v}U_w` has trivial cohomology, i.e. that `v` is unramified in `L`. -/
theorem herbrandEq_tIdelesRep_of_fibreTrivial [IsCyclic (L ≃ₐ[K] L)]
    (S : Finset (Place K)) (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (hTS : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v)
    (hSinf : ∀ a : NumberField.InfinitePlace K, Place.ofInfinite a ∈ S)
    (w : (v : Place K) → v ∈ S → Place L)
    (hw : ∀ (v : Place K) (hv : v ∈ S), Place.LiesOver (w v hv) v)
    (hfib : ∀ v : Place K, v ∉ S →
      Nat.card (tateCohomology (fiberUnitsRep (K := K) (L := L) v) 0) = 1 ∧
        Nat.card (tateCohomology (fiberUnitsRep (K := K) (L := L) v) 1) = 1) :
    HerbrandEq (tIdelesRep (L := L) T hT)
      (Finset.prod S.attach (fun v => Nat.card
        (decompositionSubgroup (K := K) (L := L) (w v.1 v.2)))) := by
  obtain ⟨hOut0, hOut1⟩ :=
    hZero_hOne_unitIdelesOutsideRep_eq_one (K := K) (L := L) S T hT hTS hSinf hfib
  exact herbrandEq_tIdelesRep_of_outsideTrivial (K := K) (L := L) S T hT hTS hSinf w hw
    hOut0 hOut1 (hposSup_supportedIdelesRep (K := K) (L := L) S T hT hTS)

end NK.GlobalCFTdeep.Herbrand
