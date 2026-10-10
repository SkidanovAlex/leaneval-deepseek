import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFTdeep.Audit.index_normClassSubgroup_self
import Submission.NK.GlobalCFTdeep.Corollaries.HasseInput
import Submission.NK.GlobalCFTdeep.Herbrand.Assembly
import Submission.NK.GlobalCFTdeep.Herbrand.FiberAll
import Submission.NK.GlobalCFTdeep.Herbrand.exists_finset_TIdeles_surjective
import Submission.NK.GlobalCFTdeep.Herbrand.fiberUnitsRep_iso_coind
import Submission.NK.GlobalCFTdeep.Herbrand.herbrandEq_iff_of_finite_quotient
import Submission.NK.GlobalCFTdeep.Herbrand.herbrandEq_ind_iff
import Submission.NK.GlobalCFTdeep.Herbrand.herbrandEq_localUnitSubRep_ofFinite
import Submission.NK.GlobalCFTdeep.Herbrand.natCard_tIdeles_mul_eq_unitIdeles
import Submission.NK.GlobalCFTdeep.Herbrand.natCard_tateCohomology_supportedIdelesRep
import Submission.NK.GlobalCFTdeep.Herbrand.natCard_tateCohomology_unitIdelesOutsideRep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Milne's Proposition 2.7: `h(𝕀_{L,T}) = ∏_{v ∈ S} [L_w : K_v]`

Milne, *Class Field Theory*, Proposition 2.7: for a finite Galois extension `L / K` of number
fields (cyclic, in the form used here), a finite set `S` of places of `K` and `T` the set of
places of `L` above `S`,

  `h(𝕀_{L,T}) = ∏_{v ∈ S} [L_w : K_v]`,  `n_v = [L_w : K_v]`.

Everything that is *local* about this statement is proved elsewhere in this chapter:

* the per-place value `h(∏_{w|v} L_wˣ) = |D_w|` at every place `v` — `herbrandEq_fiberIdeles`;
* the product decomposition `𝕀_{L,T} = ∏_{v∈S}∏_{w|v}L_wˣ × ∏_{v∉S}∏_{w|v}U_w` in the
  cohomological form
  `|Ĥ⁰(𝕀_{L,T})| |Ĥ¹(outside)| |Ĥ¹(supported)| = |Ĥ⁰(outside)| |Ĥ⁰(supported)| |Ĥ¹(𝕀_{L,T})|`
  — `natCard_tIdeles_mul_eq_unitIdeles`;
* the identification of the cohomology of the supported idèles with the product of the fibres —
  `natCard_tateCohomology_supportedIdelesRep`.

This file carries out the arithmetic assembly, with the one genuinely arithmetic input left as an
explicit hypothesis: the *outside* factor `∏_{v∉S}∏_{w|v}U_w` has trivial cohomology, which holds
exactly when no place outside `S` ramifies (`hZero_hOne_unitIdelesOutsideRep_eq_one`, Milne III.2.5
plus the fact that for unramified `w` the norm on local units is onto).  Positivity of `Ĥ¹` of the
supported idèles is the second hypothesis; it follows from the per-place computation
`hOne_fiberIdelesRep_eq_one` and is discharged in the companion file
`Herbrand/Prop27Unconditional.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain
open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep.Herbrand

open NK.GlobalCFT
open NK.GlobalCFTdeep

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **Milne, *CFT*, Proposition 2.7, assembled.**  For a cyclic extension `L / K`, a finite set `S`
of places of `K` containing the archimedean ones, `T` the places of `L` above `S`, and a choice
`w v` of a place above each `v ∈ S`:

  `h(𝕀_{L,T}) = ∏_{v ∈ S} |D_{w_v}| = ∏_{v ∈ S} [L_{w_v} : K_v]`.

The two hypotheses are the triviality of the cohomology of the idèles which are units at every
place outside `T` — Milne III.2.5, holding when nothing outside `S` ramifies — and the positivity of
`Ĥ¹` of the idèles supported on `T`, which is the finiteness of that group. -/
theorem herbrandEq_tIdelesRep_of_outsideTrivial [IsCyclic (L ≃ₐ[K] L)]
    (S : Finset (Place K)) (T : Set (Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (hTS : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v)
    (hSinf : ∀ a : NumberField.InfinitePlace K, Place.ofInfinite a ∈ S)
    (w : (v : Place K) → v ∈ S → Place L)
    (hw : ∀ (v : Place K) (hv : v ∈ S), Place.LiesOver (w v hv) v)
    (hOut0 : hZero (unitIdelesOutsideRep (L := L) T hT) = 1)
    (hOut1 : hOne (unitIdelesOutsideRep (L := L) T hT) = 1)
    (hposSup : 0 < hOne (supportedIdelesRep (L := L) T hT)) :
    HerbrandEq (tIdelesRep (L := L) T hT)
      (Finset.prod S.attach (fun v => Nat.card
        (decompositionSubgroup (K := K) (L := L) (w v.1 v.2)))) := by
  classical
  -- ## The per-place values of Milne's Proposition 2.7
  have hval : ∀ (v : Place K) (hv : v ∈ S),
      HerbrandEq (fiberIdelesRep (K := K) (L := L) v)
        (Nat.card (decompositionSubgroup (K := K) (L := L) (w v hv))) :=
    fun v hv => herbrandEq_fiberIdeles (K := K) (L := L) v (w v hv) (hw v hv)
      (fun a b => mul_comm a b)
  -- ## The Herbrand quotient of the idèles supported on `T`
  have hS0 := natCard_tateCohomology_supportedIdelesRep (K := K) (L := L) S T hT hTS 0
  have hS1 := natCard_tateCohomology_supportedIdelesRep (K := K) (L := L) S T hT hTS 1
  have hSup : hZero (supportedIdelesRep (L := L) T hT)
      = (Finset.prod S.attach (fun v => Nat.card
          (decompositionSubgroup (K := K) (L := L) (w v.1 v.2))))
        * hOne (supportedIdelesRep (L := L) T hT) := by
    rw [hZero_def, hOne_def, hS0, hS1]
    have e : Nat.card ((v : ↥S) → tateCohomology
          (fiberIdelesRep (K := K) (L := L) (v : Place K)) 0)
        = (Finset.prod S.attach (fun v => Nat.card
            (decompositionSubgroup (K := K) (L := L) (w v.1 v.2))))
          * Nat.card ((v : ↥S) → tateCohomology
              (fiberIdelesRep (K := K) (L := L) (v : Place K)) 1) := by
      rw [Nat.card_pi, Nat.card_pi]
      rw [Finset.prod_congr (Finset.univ_eq_attach S).symm (fun _ _ => rfl)]
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun v _ => by
        simpa [HerbrandEq, hZero, hOne] using hval v.1 v.2)
    simpa only [Finset.univ_eq_attach] using e
  -- ## The multiplicativity identity along `0 → ∏_{w ∉ T} U_w → 𝕀_{L,T} → ∏_{w ∈ T} L_wˣ → 0`
  have hSES := natCard_tIdeles_mul_eq_unitIdeles (K := K) (L := L) S T hT hTS
  -- ## The arithmetic
  have hkey : hZero (tIdelesRep (L := L) T hT) * hOne (supportedIdelesRep (L := L) T hT)
      = ((Finset.prod S.attach (fun v => Nat.card
            (decompositionSubgroup (K := K) (L := L) (w v.1 v.2))))
          * hOne (tIdelesRep (L := L) T hT))
        * hOne (supportedIdelesRep (L := L) T hT) := by
    have h1 : hZero (tIdelesRep (L := L) T hT) * hOne (unitIdelesOutsideRep (L := L) T hT) *
        hOne (supportedIdelesRep (L := L) T hT)
        = hZero (unitIdelesOutsideRep (L := L) T hT) *
          hZero (supportedIdelesRep (L := L) T hT) * hOne (tIdelesRep (L := L) T hT) := by
      simpa only [hZero_def, hOne_def] using hSES
    rw [hOut0, hOut1, hSup] at h1
    rw [mul_one, one_mul] at h1
    rw [h1]
    ring
  have hfin := Nat.eq_of_mul_eq_mul_right hposSup hkey
  rw [HerbrandEq, hZero_def, hOne_def]
  exact hfin

end NK.GlobalCFTdeep.Herbrand
