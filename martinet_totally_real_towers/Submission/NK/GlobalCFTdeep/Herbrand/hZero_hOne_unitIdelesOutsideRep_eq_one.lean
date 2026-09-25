import Mathlib
import Submission.NK.GlobalCFTdeep.Shared

/-!
# `h⁰` and `h¹` of the unit idèles outside `T` vanish

Milne, *Arithmetic Duality Theorems* III.2.5 (and its generalisation to an arbitrary finite set
`S ⊇ S_∞` of places of `K`): the Herbrand quotient of the group `∏_{w ∉ T, w finite} U_w` of
unit idèles outside `T` is `1`.  The vanishing of both `|Ĥ⁰|` and `|Ĥ¹|` is what is needed for
the class formation computation.

The group `unitIdelesOutside T` splits as the direct product, over the places `v ∉ S` of `K`, of
the unit parts `fiberUnits v` of the fibres (`unitIdelesOutsideRep_iso_piRep`, hence
`natCard_tateCohomology_unitIdelesOutsideRep`), so the statement reduces to the vanishing of
`|Ĥ⁰|` and `|Ĥ¹|` of *each* fibre.  That local input is exactly hypothesis `hfib`; here we only
perform the reduction, so that the local computation can be proved where it belongs.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace NK.GlobalCFTdeep.Herbrand

open NK.GlobalCFT

theorem hZero_hOne_unitIdelesOutsideRep_eq_one {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)]
    (S : Finset (NK.GlobalCFT.Place K)) (T : Set (NK.GlobalCFT.Place L))
    (hT : ∀ (σ : L ≃ₐ[K] L) ⦃w : NK.GlobalCFT.Place L⦄, w ∈ T → σ • w ∈ T)
    (hTS : ∀ w : NK.GlobalCFT.Place L, w ∈ T ↔ ∃ v ∈ S, NK.GlobalCFT.Place.LiesOver w v)
    (hSinf : ∀ a : NumberField.InfinitePlace K, NK.GlobalCFT.Place.ofInfinite a ∈ S)
    (hfib : ∀ v : NK.GlobalCFT.Place K, v ∉ S →
      Nat.card (tateCohomology (NK.GlobalCFTdeep.fiberUnitsRep (K := K) (L := L) v) 0) = 1 ∧
        Nat.card (tateCohomology (NK.GlobalCFTdeep.fiberUnitsRep (K := K) (L := L) v) 1) = 1) :
    NK.GlobalCFTdeep.hZero (NK.GlobalCFTdeep.unitIdelesOutsideRep (L := L) T hT) = 1 ∧
      NK.GlobalCFTdeep.hOne (NK.GlobalCFTdeep.unitIdelesOutsideRep (L := L) T hT) = 1 := by
  -- The `Nat.card` of a product all of whose fibres are singletons is `1`.
  have key : ∀ (n : ℤ), (n = 0 ∨ n = 1) →
      Nat.card (tateCohomology (NK.GlobalCFTdeep.unitIdelesOutsideRep (L := L) T hT) n)
        = 1 := by
    intro n hn
    rw [natCard_tateCohomology_unitIdelesOutsideRep (K := K) (L := L) S T hT hTS hSinf n]
    have hfac : ∀ v : {v : NK.GlobalCFT.Place K // v ∉ S},
        Nat.card (tateCohomology (NK.GlobalCFTdeep.fiberUnitsRep (K := K) (L := L)
          (v : NK.GlobalCFT.Place K)) n) = 1 := by
      intro v
      rcases hn with rfl | rfl
      · exact (hfib v.1 v.2).1
      · exact (hfib v.1 v.2).2
    haveI : ∀ v : {v : NK.GlobalCFT.Place K // v ∉ S},
        Subsingleton (tateCohomology (NK.GlobalCFTdeep.fiberUnitsRep (K := K) (L := L)
          (v : NK.GlobalCFT.Place K)) n) :=
      fun v => (Nat.card_eq_one_iff_unique.mp (hfac v)).1
    haveI : ∀ v : {v : NK.GlobalCFT.Place K // v ∉ S},
        Nonempty (tateCohomology (NK.GlobalCFTdeep.fiberUnitsRep (K := K) (L := L)
          (v : NK.GlobalCFT.Place K)) n) :=
      fun v => (Nat.card_eq_one_iff_unique.mp (hfac v)).2
    exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
  exact ⟨by simpa [NK.GlobalCFTdeep.hZero_def] using key 0 (Or.inl rfl),
    by simpa [NK.GlobalCFTdeep.hOne_def] using key 1 (Or.inr rfl)⟩

end NK.GlobalCFTdeep.Herbrand
