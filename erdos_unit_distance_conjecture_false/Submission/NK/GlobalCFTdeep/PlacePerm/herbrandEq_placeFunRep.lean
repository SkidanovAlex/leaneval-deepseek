import Mathlib
import Submission.NK.GlobalCFTdeep.PlacePerm.Defs
import Submission.NK.GlobalCFTdeep.PlacePerm.fibreRep_iso_coind
import Submission.NK.GlobalCFTdeep.PlacePerm.placeFunRep_piRep_iso
import Submission.NK.GlobalCFTdeep.Herbrand.LogDefs
import Submission.NK.GlobalCFTdeep.Herbrand.Fiber
import Submission.NK.GlobalCFTdeep.Shared
import Submission.NK.GlobalCFTdeep.Herbrand.Mul
import Submission.NK.GlobalCFTdeep.Herbrand.CoindHerbrand
import Submission.NK.GlobalCFTdeep.Herbrand.tateCohomology_piRep

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep.PlacePerm

open NK.GlobalCFT
open NK.GlobalCFTdeep
open NK.GlobalCFTdeep.PlacePerm

/-- **Milne, *CFT*, the `ℤ[T]` side of Proposition 3.1.**  For a finite `Gal(L/K)`-stable set `T`
of places of `L` which is the set of places above a finite set `S` of places of `K`, the
permutation module `Hom(T, ℤ) = ∏_{w ∈ T} ℤ` (`NK.GlobalCFTdeep.placeFunRep`) has Herbrand
quotient the product of the local degrees:

  `|Ĥ⁰(G, ℤ[T])| = (∏_{v ∈ S} |D_{w v}|) · |Ĥ¹(G, ℤ[T])|`.

## Proof sketch

* `hTS` says that `T` is the disjoint union of the fibres `Fib v = {w ∈ T | LiesOver w v}`,
  `v ∈ S` (uniqueness of the place below a place is `NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique`).
* By transitivity of the `Gal(L/K)`-action on the places above a fixed place
  (`NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver`), each fibre is the orbit of
  `w v hv`, whose stabiliser is `decompositionSubgroup (w v hv)`.
* Hence `↥T → ℤ ≅ ∏_{v ∈ S} (Fib v → ℤ)` as `ℤ[Gal(L/K)]`-modules (a function on the disjoint
  union is a tuple of functions on the parts), and `Fib v → ℤ` is the permutation module on
  `G ⧸ D_v`, i.e. `Rep.coind (D_v).subtype (Rep.trivial ℤ D_v ℤ)` (functions on the coset space,
  equivalently `D_v`-invariant functions on `G`).
* `NK.GlobalCFTdeep.Herbrand.herbrandEq_coind_iff` (Shapiro) together with
  `hZero_trivial`/`hOne_trivial` gives `HerbrandEq (Coind_{D_v}^G ℤ) (Nat.card D_v)`.
* The product over the finitely many `v ∈ S` is assembled with the Herbrand multiplicativity
  `NK.GlobalCFTdeep.Herbrand.herbrandEq_of_mult` (or `herbrandEq_of_shortExact`) applied to the
  exact sequences `0 → (functions on the part of `T` above the already-handled places) →
  (functions on `T`) → (functions on `Fib v`) → 0` for one `v` at a time; the finiteness
  hypotheses are discharged by
  `NK.GlobalCFTdeep.Herbrand.finite_tateCohomology_of_moduleFinite` (all the modules occurring
  are finitely generated over `ℤ`, because `T` is finite). -/
theorem herbrandEq_placeFunRep {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (S : Finset (NK.GlobalCFT.Place K)) (T : Set (NK.GlobalCFT.Place L)) [Finite T]
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : NK.GlobalCFT.Place L⦄, w ∈ T → σ • w ∈ T)
    (hTS : ∀ w : NK.GlobalCFT.Place L, w ∈ T ↔ ∃ v ∈ S, NK.GlobalCFT.Place.LiesOver w v)
    (w : (v : NK.GlobalCFT.Place K) → v ∈ S → NK.GlobalCFT.Place L)
    (hw : ∀ (v : NK.GlobalCFT.Place K) (hv : v ∈ S),
      NK.GlobalCFT.Place.LiesOver (w v hv) v) :
    NK.GlobalCFTdeep.HerbrandEq (NK.GlobalCFTdeep.placeFunRep (L := L) T hT)
      (Finset.prod S.attach (fun v => Nat.card
        (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L) (w v.1 v.2)))) := by
  classical
  -- The family of fibre modules indexed by `↥S`.
  set F : ↥S → Rep ℤ (L ≃ₐ[K] L) :=
    fun v => fibreRep (K := K) (L := L) T hT (v : Place K) with hF
  -- `T` is the disjoint union of its fibres, so `ℤ[T]` is the product of the fibre modules.
  obtain ⟨e⟩ := placeFunRep_piRep_iso (K := K) (L := L) S T hT hTS
  have eF : placeFunRep (K := K) (L := L) T hT ≅
      NK.RepresentationTheory.GroupCohomology.piRep F := e
  -- ## `Ĥ⁰` and `Ĥ¹` of the permutation module are the products over the fibres of `Ĥ⁰`, `Ĥ¹`
  have hstep : ∀ n : ℤ, Nat.card (tateCohomology (placeFunRep (K := K) (L := L) T hT) n)
      = ∏ v : ↥S, Nat.card (tateCohomology (F v) n) := by
    intro n
    calc Nat.card (tateCohomology (placeFunRep (K := K) (L := L) T hT) n)
        = Nat.card (tateCohomology (NK.RepresentationTheory.GroupCohomology.piRep F) n) :=
          Nat.card_congr (Iso.toLinearEquiv
            ((tateCohomologyFunctor (R := ℤ) (G := L ≃ₐ[K] L) n).mapIso eF)).toEquiv
      _ = Nat.card ((v : ↥S) → tateCohomology (F v) n) := Herbrand.tateCohomology_piRep F n
      _ = ∏ v : ↥S, Nat.card (tateCohomology (F v) n) := Nat.card_pi
  -- ## Shapiro's lemma on a single fibre: the value `|D_{w v}|`
  have hfib : ∀ v : ↥S, Nat.card (tateCohomology (F v) 0)
      = Nat.card (decompositionSubgroup (K := K) (L := L) (w v.1 v.2))
        * Nat.card (tateCohomology (F v) 1) := by
    intro v
    haveI : Fintype ↥(decompositionSubgroup (K := K) (L := L) (w v.1 v.2)) := Fintype.ofFinite _
    obtain ⟨ev⟩ := fibreRep_iso_coind (K := K) (L := L) S T hT hTS w hw v.1 v.2
    have h := herbrandEq_of_iso ev
      (herbrandEq_coind_trivial (decompositionSubgroup (K := K) (L := L) (w v.1 v.2)))
    simpa only [HerbrandEq, hZero_def, hOne_def] using h
  -- ## The arithmetic assembly
  rw [HerbrandEq, hZero_def, hOne_def, hstep 0, hstep 1]
  have hp : (Finset.prod S.attach (fun v => Nat.card
        (decompositionSubgroup (K := K) (L := L) (w v.1 v.2))))
      = ∏ v : ↥S, Nat.card (decompositionSubgroup (K := K) (L := L) (w v.1 v.2)) := by
    rw [Finset.univ_eq_attach]
  rw [hp, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun v _ => hfib v)

end NK.GlobalCFTdeep.PlacePerm
