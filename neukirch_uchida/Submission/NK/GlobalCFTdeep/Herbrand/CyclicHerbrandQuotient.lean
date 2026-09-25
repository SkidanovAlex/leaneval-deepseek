/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.NK.GlobalCFTdeep.Shared
import Submission.NK.GlobalCFTdeep.Herbrand.Prop27Unramified
import Submission.NK.GlobalCFTdeep.Herbrand.Milne43ModuloProp31
import Submission.NK.GlobalCFTdeep.Herbrand.prop31
import Submission.NK.GlobalCFTdeep.Herbrand.finrank_tUnits
import Submission.NK.GlobalCFTdeep.Herbrand.finite_tateCohomology_of_moduleFinite
import Submission.NK.GlobalCFTdeep.Herbrand.natCard_tateCohomology_one_tIdelesRep_eq_one
import Submission.NK.GlobalCFTdeep.finiteTate_three_of_shortComplex

/-!
# Milne's Theorem 4.3: `h(Gal(L/K), C_L) = [L : K]` for cyclic `L/K`, unconditionally

This file closes the Herbrand-quotient computation of global class field theory.  All the inputs
are now proved in this chapter:

* **Lemma 4.2** — `𝕀_L = Lˣ·𝕀_{L,T}` for a good `T`
  (`Herbrand/milneFourTwoExact_nonempty.lean`, `Herbrand/exists_T_unramifiedOutside_surjective.lean`);
* **Proposition 2.7** — `h(𝕀_{L,T}) = ∏_{v∈S}|D_{w_v}|`
  (`Herbrand/Prop27Unramified.lean`, `herbrandEq_tIdelesRep_of_unramifiedOutside`);
* **Proposition 3.1** — `[L:K]·h(U(T)) = ∏_{v∈S}|D_{w_v}|` (`Herbrand/prop31.lean`, `prop31`),
  whose arithmetic half is Dirichlet's `S`-unit theorem (`Herbrand/finrank_tUnits.lean`).

`herbrandQuotient_of_goodT_selfContained` assembles them for arbitrary good `T` data, and
`cyclicHerbrandQuotient` produces the universal statement `CyclicHerbrandQuotient` of
`Inequalities.lean`.  The first inequality then follows unconditionally
(`first_inequality_unconditional`).
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

/-- **Milne, *CFT*, Theorem 4.3 from the good-`T` data**, with Propositions 2.7 and 3.1 supplied by
this chapter and only the finiteness of `Ĥ⁰`, `Ĥ¹` of `C_L` left as hypotheses. -/
theorem herbrandQuotient_of_goodT [IsCyclic (L ≃ₐ[K] L)]
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
    [Finite ↥(tateCohomology (IdeleClassGroup.rep K L) 0)]
    [Finite ↥(tateCohomology (IdeleClassGroup.rep K L) 1)] :
    HerbrandQuotient K L :=
  herbrandQuotient_of_prop31 (K := K) (L := L) S T hTinf hT hTS hSinf hunr hgen w hw
    (prop31 (K := K) (L := L) S T hTinf hT hTS w hw)

/-- **Milne, *CFT*, Theorem 4.3 from the good-`T` data, self-contained**: the finiteness of `Ĥ⁰`
and `Ĥ¹` of `C_L` is derived from that of the `T`-units (Dirichlet's `S`-unit theorem together
with Milne II.3.9) and of the `T`-idèles (Proposition 2.7 with `Ĥ¹ = 0`), through the long exact
sequence of Lemma 4.2. -/
theorem herbrandQuotient_of_goodT_selfContained [IsCyclic (L ≃ₐ[K] L)]
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
    (hw : ∀ (v : Place K) (hv : v ∈ S), Place.LiesOver (w v hv) v) :
    HerbrandQuotient K L := by
  classical
  -- positivity of the product of the local degrees
  have hP : 0 < Finset.prod S.attach (fun v => Nat.card
      (decompositionSubgroup (K := K) (L := L) (w v.1 v.2))) := by
    refine Finset.prod_pos fun v _ => ?_
    haveI : Fintype (decompositionSubgroup (K := K) (L := L) (w v.1 v.2)) := Fintype.ofFinite _
    exact Nat.card_pos
  -- the `T`-units are finitely generated, hence have finite cohomology
  haveI hfg : Module.Finite ℤ (tUnitsRep (L := L) T hT).V :=
    (finrank_tUnits (L := L) T hTinf).1
  have hUfin : FiniteTate (tUnitsRep (L := L) T hT) :=
    ⟨(finite_tateCohomology_of_moduleFinite (tUnitsRep (L := L) T hT)).1,
      (finite_tateCohomology_of_moduleFinite (tUnitsRep (L := L) T hT)).2⟩
  -- the `T`-idèles: Proposition 2.7 and the vanishing of `Ĥ¹`
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
  have hIfin : FiniteTate (tIdelesRep (L := L) T hT) := ⟨‹Finite _›, ‹Finite _›⟩
  -- the finiteness of `C_L` follows from Lemma 4.2's exact sequence
  obtain ⟨E⟩ := Herbrand.milneFourTwoExact_nonempty (K := K) (L := L) T hT hgen
  have hCfin : FiniteTate (IdeleClassGroup.rep K L) :=
    finiteTate_three_of_shortComplex (ShortComplex.mk E.i E.p E.w) E.shortExact hUfin hIfin
  haveI : Finite ↥(tateCohomology (IdeleClassGroup.rep K L) 0) := hCfin.zero
  haveI : Finite ↥(tateCohomology (IdeleClassGroup.rep K L) 1) := hCfin.one
  exact herbrandQuotient_of_goodT (K := K) (L := L) S T hTinf hT hTS hSinf hunr hgen w hw

end NK.GlobalCFTdeep.Herbrand

namespace NK.GlobalCFTdeep

open NK.GlobalCFT

/-- **Milne, *CFT*, Theorem 4.3, unconditional.**  For every finite cyclic extension `L/K` of number
fields, `h(Gal(L/K), C_L) = [L : K]`; this is the universal statement `CyclicHerbrandQuotient` of
`Inequalities.lean`, formerly an input of this chapter. -/
theorem cyclicHerbrandQuotient : CyclicHerbrandQuotient where
  herbrand := fun {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
      [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] => by
    obtain ⟨S, T, hT, hTS, hTfin, hTinf, hSinf, hunr, hgen, _hJ⟩ :=
      Herbrand.exists_good_T_herbrandEq_tIdelesRep (K := K) (L := L)
    haveI : Fintype T := hTfin.fintype
    have hk : ∀ v : Place K, ∃ w : Place L, Place.LiesOver w v := by
      intro v
      rcases v with a | Q
      · obtain ⟨w', hw'⟩ : ∃ w' : InfinitePlace L, w'.comap (algebraMap K L) = a :=
          InfinitePlace.comap_surjective (k := K) (K := L) a
        exact ⟨Place.ofInfinite w',
          Place.liesOver_ofInfinite (hw' ▸ NK.GlobalCFT.Norm.liesOver_comap_self w')⟩
      · obtain ⟨q, hq⟩ := Herbrand.exists_heightOneSpectrum_liesOver (K := K) (L := L) Q
        exact ⟨Place.ofFinite q, hq⟩
    let w : (v : Place K) → v ∈ S → Place L := fun v _ => Classical.choose (hk v)
    have hw : ∀ (v : Place K) (hv : v ∈ S), Place.LiesOver (w v hv) v :=
      fun v _ => Classical.choose_spec (hk v)
    exact Herbrand.herbrandQuotient_of_goodT_selfContained (K := K) (L := L) S T
      hTinf hT hTS hSinf hunr hgen w hw

/-- **The first inequality of global class field theory, unconditional**: for a cyclic extension
`L/K` of number fields, `[L : K] ≤ [C_K : N_{L/K} C_L]`.  (The inequality holds for all finite
Galois `L/K`; it is stated here at cyclic levels, where `CyclicHerbrandQuotient` applies, and is
obtained from the delivered `first_inequality_of_herbrandQuotient`.) -/
theorem first_inequality_unconditional {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] :
    Module.finrank K L ≤ (Idele.normClassSubgroup K L).index :=
  first_inequality_of_herbrandQuotient (globalCFT_H0Computation (K := K) (L := L))
    (cyclicHerbrandQuotient.herbrand (K := K) (L := L))

end NK.GlobalCFTdeep
