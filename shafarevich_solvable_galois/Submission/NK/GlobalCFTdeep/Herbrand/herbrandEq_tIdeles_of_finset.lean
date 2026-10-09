import Mathlib
import Submission.NK.GlobalCFTdeep.Herbrand.herbrandEq_supportedIdeles_of_insert
import Submission.NK.GlobalCFTdeep.Herbrand.FiberValue
import Submission.NK.GlobalCFTdeep.Herbrand.FiniteIndex
import Submission.NK.GlobalCFTdeep.Herbrand.UnitIdelesDefs
import Submission.NK.GlobalCFTdeep.Herbrand.tateCohomology_mul_eq_of_shortExact_noFin
import Submission.NK.GlobalCFTdeep.Herbrand.herbrandEq_fiberUnitsRep
import Submission.NK.GlobalCFTdeep.Herbrand.natCard_tateCohomology_supportedIdelesRep
import Submission.NK.GlobalCFTdeep.Herbrand.natCard_tateCohomology_unitIdelesOutsideRep
import Submission.NK.GlobalCFTdeep.Herbrand.natCard_pi_congr
import Submission.NK.GlobalCFTdeep.Herbrand.natCard_tIdeles_mul_eq_unitIdeles
import Submission.NK.GlobalCFTdeep.Herbrand.finite_tateCohomology_one_unitIdelesOutsideRep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

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

/-- A finite place of `K` has a place of `L` above it. -/
theorem exists_liesOver_of_isFinite {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] (v : Place K) (hv : v.IsFinite) :
    ∃ w : Place L, Place.LiesOver w v := by
  obtain ⟨Q, hQ⟩ := Place.isFinite_iff.mp hv
  rw [hQ]
  obtain ⟨P₀⟩ := (Ideal.nonempty_primesOver Q.asIdeal :
    Nonempty (Q.asIdeal.primesOver (NumberField.RingOfIntegers L)))
  exact ⟨Place.ofFinite
    { asIdeal := P₀.1
      isPrime := P₀.2.1
      ne_bot := Ideal.ne_bot_of_mem_primesOver Q.ne_bot P₀.2 },
    Place.liesOver_ofFinite P₀.2.2⟩

theorem herbrandEq_tIdeles_of_finset {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)]
    (S : Finset (NK.GlobalCFT.Place K)) (T : Set (NK.GlobalCFT.Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : NK.GlobalCFT.Place L⦄, w ∈ T → σ • w ∈ T)
    (hTS : ∀ w : NK.GlobalCFT.Place L, w ∈ T ↔ ∃ v ∈ S, NK.GlobalCFT.Place.LiesOver w v)
    (hSinf : ∀ a : NumberField.InfinitePlace K, NK.GlobalCFT.Place.ofInfinite a ∈ S)
    (w : (v : NK.GlobalCFT.Place K) → v ∈ S → NK.GlobalCFT.Place L)
    (hw : ∀ v hv, NK.GlobalCFT.Place.LiesOver (w v hv) v)
    (hcomm : ∀ v hv, ∀ a b : NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L) (w v hv),
      a * b = b * a)
    (hval : ∀ v (hv : v ∈ S), NK.GlobalCFTdeep.HerbrandEq
      (NK.GlobalCFTdeep.fiberIdelesRep (K := K) (L := L) v)
      (Nat.card (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L) (w v hv))))
    (hfinf : ∀ v : NK.GlobalCFT.Place K,
      NK.GlobalCFTdeep.FiniteTate (NK.GlobalCFTdeep.fiberIdelesRep (K := K) (L := L) v))
    (hfinT : ∀ (S' : Finset (NK.GlobalCFT.Place K)) (T' : Set (NK.GlobalCFT.Place L))
      (hT' : ∀ (σ : L ≃ₐ[K] L) ⦃u : NK.GlobalCFT.Place L⦄, u ∈ T' → σ • u ∈ T')
      (hTS' : ∀ u : NK.GlobalCFT.Place L, u ∈ T' ↔ ∃ v ∈ S', NK.GlobalCFT.Place.LiesOver u v),
        NK.GlobalCFTdeep.FiniteTate (NK.GlobalCFTdeep.tIdelesRep (K := K) (L := L) T' hT')) :
    NK.GlobalCFTdeep.HerbrandEq (NK.GlobalCFTdeep.tIdelesRep (K := K) (L := L) T hT)
      (Finset.prod S.attach (fun v => Nat.card
        (NK.GlobalCFTdeep.decompositionSubgroup (K := K) (L := L) (w v.1 v.2)))) := by
  classical
  -- ## The Herbrand quotient of the unit idèles outside `T` is `1`
  have hcard : ∀ v : {v : Place K // v ∉ S},
      Nat.card (tateCohomology (fiberUnitsRep (K := K) (L := L) v.1) 0)
        = Nat.card (tateCohomology (fiberUnitsRep (K := K) (L := L) v.1) 1) := by
    intro v
    have hv : v.1.IsFinite := by
      rw [Place.isFinite_iff_not_isInfinite]
      intro hv'
      obtain ⟨a, ha⟩ := Place.isInfinite_iff.mp hv'
      exact v.2 (ha ▸ hSinf a)
    obtain ⟨w', hw'⟩ := exists_liesOver_of_isFinite (K := K) (L := L) v.1 hv
    haveI : Fintype (decompositionSubgroup (K := K) (L := L) w') := Fintype.ofFinite _
    have h := herbrandEq_fiberUnitsRep (K := K) (L := L) v.1 hv w' hw'
    simpa [HerbrandEq, hZero, hOne, one_mul] using h
  have hK0 := natCard_tateCohomology_unitIdelesOutsideRep (K := K) (L := L) S T hT hTS hSinf 0
  have hK1 := natCard_tateCohomology_unitIdelesOutsideRep (K := K) (L := L) S T hT hTS hSinf 1
  have hK : hZero (unitIdelesOutsideRep (L := L) T hT)
      = hOne (unitIdelesOutsideRep (L := L) T hT) := by
    rw [hZero_def, hOne_def, hK0, hK1]
    exact natCard_pi_congr _ _ hcard
  -- ## The Herbrand quotient of the idèles supported on `T`
  have hS0 := natCard_tateCohomology_supportedIdelesRep (K := K) (L := L) S T hT hTS 0
  have hS1 := natCard_tateCohomology_supportedIdelesRep (K := K) (L := L) S T hT hTS 1
  haveI hFin0 : ∀ (v : Place K),
      Finite ↥(tateCohomology (fiberIdelesRep (K := K) (L := L) v) 0) :=
    fun v => (hfinf v).zero
  haveI hFin1 : ∀ (v : Place K),
      Finite ↥(tateCohomology (fiberIdelesRep (K := K) (L := L) v) 1) :=
    fun v => (hfinf v).one
  haveI hF0 : ∀ (v : Place K),
      Fintype ↥(tateCohomology (fiberIdelesRep (K := K) (L := L) v) 0) :=
    fun v => Fintype.ofFinite _
  haveI hF1 : ∀ (v : Place K),
      Fintype ↥(tateCohomology (fiberIdelesRep (K := K) (L := L) v) 1) :=
    fun v => Fintype.ofFinite _
  have hfac : ∀ v : ↥S,
      Nat.card (tateCohomology (fiberIdelesRep (K := K) (L := L) (v : Place K)) 0)
        = Nat.card (decompositionSubgroup (K := K) (L := L) (w v.1 v.2))
          * Nat.card (tateCohomology (fiberIdelesRep (K := K) (L := L) (v : Place K)) 1) := by
    intro v
    simpa [HerbrandEq, hZero, hOne] using hval v.1 v.2
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
      exact Finset.prod_congr rfl (fun v _ => hfac v)
    exact e
  -- ## The multiplicativity identity along `0 → ∏_{w ∉ T} U_w → 𝕀_{L,T} → ∏_{w ∈ T} L_wˣ → 0`
  have hSES : hZero (tIdelesRep (L := L) T hT)
        * hOne (unitIdelesOutsideRep (L := L) T hT)
        * hOne (supportedIdelesRep (L := L) T hT)
      = hZero (unitIdelesOutsideRep (L := L) T hT)
        * hZero (supportedIdelesRep (L := L) T hT)
        * hOne (tIdelesRep (L := L) T hT) := by
    simpa [hZero_def, hOne_def] using
      natCard_tIdeles_mul_eq_unitIdeles (K := K) (L := L) S T hT hTS
  -- ## The arithmetic
  have hposSup : 0 < hOne (supportedIdelesRep (L := L) T hT) := by
    rw [hOne_def, hS1]
    haveI : Nonempty ((v : ↥S) → tateCohomology
        (fiberIdelesRep (K := K) (L := L) (v : Place K)) 1) := ⟨fun _ => 0⟩
    exact Nat.card_pos
  have hposK : 0 < hOne (unitIdelesOutsideRep (L := L) T hT) := by
    haveI hfin := finite_tateCohomology_one_unitIdelesOutsideRep (K := K) (L := L) S T hT hTS hSinf
      hfinf hfinT
    haveI : Nonempty ↥(tateCohomology (unitIdelesOutsideRep (L := L) T hT) 1) := ⟨0⟩
    rw [hOne_def]
    exact Nat.card_pos
  have hpos : 0 < hOne (unitIdelesOutsideRep (L := L) T hT)
      * hOne (supportedIdelesRep (L := L) T hT) :=
    Nat.mul_pos hposK hposSup
  have hkey : hZero (tIdelesRep (L := L) T hT)
        * (hOne (unitIdelesOutsideRep (L := L) T hT)
            * hOne (supportedIdelesRep (L := L) T hT))
      = ((Finset.prod S.attach (fun v => Nat.card
            (decompositionSubgroup (K := K) (L := L) (w v.1 v.2))))
          * hOne (tIdelesRep (L := L) T hT))
        * (hOne (unitIdelesOutsideRep (L := L) T hT)
            * hOne (supportedIdelesRep (L := L) T hT)) := by
    have h1 := hSES
    rw [hK, hSup] at h1
    have h2 : hZero (tIdelesRep (L := L) T hT)
          * hOne (unitIdelesOutsideRep (L := L) T hT)
          * hOne (supportedIdelesRep (L := L) T hT)
        = hZero (tIdelesRep (L := L) T hT)
          * (hOne (unitIdelesOutsideRep (L := L) T hT)
              * hOne (supportedIdelesRep (L := L) T hT)) := by ring
    rw [← h2, h1]
    ring
  have hfin := Nat.eq_of_mul_eq_mul_right hpos hkey
  rw [HerbrandEq, hZero_def, hOne_def]
  exact hfin

end NK.GlobalCFTdeep.Herbrand
