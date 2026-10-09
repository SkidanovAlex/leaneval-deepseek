/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.NK.GlobalCFTdeep.Shared
import Submission.NK.GlobalCFTdeep.Herbrand.Prop27Unramified
import Submission.NK.GlobalCFTdeep.Herbrand.exists_T_unramifiedOutside_surjective
import Submission.NK.GlobalCFTdeep.Herbrand.finite_tateCohomology_of_moduleFinite
import Submission.NK.GlobalCFTdeep.Herbrand.finrank_tUnits
import Submission.NK.GlobalCFTdeep.Herbrand.finite_T_of_liesOver_finset
import Submission.NK.GlobalCFTdeep.Herbrand.isInfinite_mem_of_liesOver_finset
import Submission.NK.GlobalCFTdeep.Herbrand.natCard_tateCohomology_one_tIdelesRep_eq_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Milne's Theorem 4.3, with Proposition 2.7 (and Lemma 4.2) discharged

Milne's proof of `h(Gal(L/K), C_L) = [L : K]` (*Class Field Theory*, Theorem 4.3) has three
numerical inputs:

1. **Lemma 4.2**: `𝕀_L = Lˣ · 𝕀_{L,T}` for a suitable finite `Gal(L/K)`-stable `T`
   (`Herbrand/milneFourTwoExact_nonempty.lean`, proved);
2. **Proposition 2.7**: `h(𝕀_{L,T}) = ∏_{v ∈ S}[L_w : K_v]` — proved in this chapter for a good
   `T` (`Herbrand/Prop27Unramified.lean`, with the existence of a good `T` in
   `Herbrand/exists_T_unramifiedOutside_surjective.lean`);
3. **Proposition 3.1**: `[L:K]·h(U(T)) = ∏_{v ∈ S}[L_w : K_v]` — the `S`-unit computation, still
   an input (see `README.md` §5).

This file states the arithmetic assembly of Theorem 4.3 with `hJ` (Proposition 2.7) supplied by
this chapter, so that only Proposition 3.1 and finiteness side conditions remain as hypotheses.

* `exists_good_T_herbrandEq_tIdelesRep`: there is a finite `S ∋ S_∞` with `T` the places above
  `S`, containing all ramified primes, such that `𝕀_L = Lˣ·𝕀_{L,T}` *and*
  `h(𝕀_{L,T}) = ∏_{v∈S}|D_{w_v}|` for every choice of `w_v | v` — Propositions 2.7 and Lemma 4.2
  together, with no hypothesis.
* `herbrandQuotient_of_prop31`: Milne's Theorem 4.3 from Proposition 3.1 and the finiteness of the
  cohomology groups involved.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1200000

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain
open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep.Herbrand

open NK.GlobalCFT
open NK.GlobalCFTdeep

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **Milne's Propositions 2.7 and Lemma 4.2 together, for a suitable `T`.**  For a cyclic
extension `L/K` there is a finite set `S` of places of `K` containing the archimedean places and
every ramified prime, such that, writing `T` for the set of places of `L` above `S`,

* `T` is Galois-stable and characterised by `S` (so that `𝕀_{L,T}` is defined);
* `𝕀_L = Lˣ·𝕀_{L,T}` (Milne's Lemma 4.2, in the form of the complement condition);
* for every choice of a place `w_v | v` (`v ∈ S`), `h(𝕀_{L,T}) = ∏_{v∈S}|D_{w_v}|` (Milne's
  Proposition 2.7). -/
theorem exists_good_T_herbrandEq_tIdelesRep [IsCyclic (L ≃ₐ[K] L)] :
    ∃ (S : Finset (Place K)) (T : Set (Place L))
      (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
      (hTS : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v)
      (hTfin : T.Finite) (hTinf : ∀ w : Place L, w.IsInfinite → w ∈ T),
      (∀ a : NumberField.InfinitePlace K, Place.ofInfinite a ∈ S) ∧
      (∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
        (∀ v ∈ S, ¬ Place.LiesOver (Place.ofFinite q) v) →
          q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) ∧
      ((⊤ : Subgroup (Idele L)) = Idele.principalSubgroup L ⊔ TIdeles T) ∧
      (∀ (w : (v : Place K) → v ∈ S → Place L)
        (hw : ∀ (v : Place K) (hv : v ∈ S), Place.LiesOver (w v hv) v),
        HerbrandEq (tIdelesRep (L := L) T hT)
          (Finset.prod S.attach (fun v => Nat.card
            (decompositionSubgroup (K := K) (L := L) (w v.1 v.2))))) := by
  obtain ⟨S, T, hT, hTS, hSinf, hunr, hgen⟩ := exists_T_unramifiedOutside_surjective (K := K) (L := L)
  exact ⟨S, T, hT, hTS, finite_T_of_liesOver_finset (K := K) (L := L) S T hTS,
    isInfinite_mem_of_liesOver_finset (K := K) (L := L) S T hTS hSinf, hSinf, hunr, hgen, fun w hw =>
    herbrandEq_tIdelesRep_of_unramifiedOutside (K := K) (L := L) S T hT hTS hSinf hunr w hw⟩

/-- **Milne, *CFT*, Theorem 4.3, from Proposition 3.1.**  The product `P = ∏_{v∈S}|D_{w_v}|` of
the local degrees is positive, and with the `S`-unit computation of Milne's Proposition 3.1
(`hU`) together with the finiteness of the cohomology groups involved, the Herbrand quotient of
`C_L` is `[L : K]`.

The finiteness side conditions are exactly the ones of `herbrandQuotient_of_milneFourTwo`:
`Ĥ⁰`, `Ĥ¹` of the `T`-units (finite because `U(T)` is finitely generated — Dirichlet's `S`-unit
theorem), of the `T`-idèles (finite by the product decomposition and Proposition 2.7), and of
`C_L`. -/
theorem herbrandQuotient_of_prop31 [IsCyclic (L ≃ₐ[K] L)]
    (S : Finset (Place K)) (T : Set (Place L)) [Finite T]
    (hTinf : ∀ w : Place L, w.IsInfinite → w ∈ T)
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : Place L⦄, w ∈ T → σ • w ∈ T)
    (hTS : ∀ w : Place L, w ∈ T ↔ ∃ v ∈ S, Place.LiesOver w v)
    (hSinf : ∀ a : NumberField.InfinitePlace K, Place.ofInfinite a ∈ S)
    (hunr : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
      (∀ v ∈ S, ¬ Place.LiesOver (Place.ofFinite q) v) →
        q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1)
    (hgen : (⊤ : Subgroup (Idele L)) = Idele.principalSubgroup L ⊔ TIdeles T)
    (w : (v : Place K) → v ∈ S → Place L)
    (hw : ∀ (v : Place K) (hv : v ∈ S), Place.LiesOver (w v hv) v)
    (hU : Nat.card (L ≃ₐ[K] L) * hZero (tUnitsRep (L := L) T hT)
      = (Finset.prod S.attach (fun v => Nat.card
          (decompositionSubgroup (K := K) (L := L) (w v.1 v.2))))
        * hOne (tUnitsRep (L := L) T hT))
    [Finite ↥(tateCohomology (IdeleClassGroup.rep K L) 0)]
    [Finite ↥(tateCohomology (IdeleClassGroup.rep K L) 1)] :
    HerbrandQuotient K L := by
  -- the product of the local degrees is positive
  have hP : 0 < Finset.prod S.attach (fun v => Nat.card
      (decompositionSubgroup (K := K) (L := L) (w v.1 v.2))) := by
    refine Finset.prod_pos fun v _ => ?_
    haveI : Fintype (decompositionSubgroup (K := K) (L := L) (w v.1 v.2)) :=
      Fintype.ofFinite _
    exact Nat.card_pos
  -- the `T`-units are finitely generated (Dirichlet's `S`-unit theorem), hence their cohomology
  -- is finite and `Ĥ¹(U(T))` is positive
  haveI hfg : Module.Finite ℤ (tUnitsRep (L := L) T hT).V :=
    (finrank_tUnits (L := L) T hTinf).1
  haveI hfinU0 : Finite ↥(tateCohomology (tUnitsRep (L := L) T hT) 0) :=
    (finite_tateCohomology_of_moduleFinite (tUnitsRep (L := L) T hT)).1
  haveI hfinU1 : Finite ↥(tateCohomology (tUnitsRep (L := L) T hT) 1) :=
    (finite_tateCohomology_of_moduleFinite (tUnitsRep (L := L) T hT)).2
  have hU1 : 0 < hOne (tUnitsRep (L := L) T hT) := by
    haveI : Nonempty ↥(tateCohomology (tUnitsRep (L := L) T hT) 1) := ⟨0⟩
    rw [hOne_def]
    exact Nat.card_pos
  -- Proposition 2.7, and the vanishing of `Ĥ¹` of the `T`-idèles
  have hJ := herbrandEq_tIdelesRep_of_unramifiedOutside (K := K) (L := L) S T hT hTS hSinf hunr w hw
  have h1I : Nat.card (tateCohomology (tIdelesRep (L := L) T hT) 1) = 1 :=
    natCard_tateCohomology_one_tIdelesRep_eq_one (K := K) (L := L) S T hT hTS hSinf hunr
  haveI hfinI1 : Finite ↥(tateCohomology (tIdelesRep (L := L) T hT) 1) :=
    (Nat.card_ne_zero.mp (by rw [h1I]; exact one_ne_zero)).2
  have h0I : Nat.card (tateCohomology (tIdelesRep (L := L) T hT) 0)
      = Finset.prod S.attach (fun v => Nat.card
          (decompositionSubgroup (K := K) (L := L) (w v.1 v.2))) := by
    rw [← hZero_def, hJ, hOne_def, h1I, mul_one]
  haveI hfinI0 : Finite ↥(tateCohomology (tIdelesRep (L := L) T hT) 0) :=
    (Nat.card_ne_zero.mp (by rw [h0I]; exact ne_of_gt hP)).2
  have hJ1 : 0 < hOne (tIdelesRep (L := L) T hT) := by
    rw [hOne_def, h1I]
    exact one_pos
  exact herbrandQuotient_of_milneFourTwo (K := K) (L := L) T hT hgen _ hJ hU hP hJ1 hU1

end NK.GlobalCFTdeep.Herbrand
