import Mathlib
import Submission.Work.SSGRoute.PT.wc_orbit_injective
import Submission.Work.SSGRoute.PT.glue_helpers
import Submission.Work.SSGRoute.PT.finHalfData
import Submission.Work.SSGRoute.PT.glue_realiser_abstract
import Submission.Work.SSGRoute.PT.vf_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

/-- **A transversal of *all* places of `K` containing the finite places of `R` and the linked
infinite places `wc c` (`c ∈ C`).**

`R` is a pairwise non-conjugate set of finite places of `Ω` (one per conjugacy class, as produced
by `PT.exists_transversal_finPlaces`), and each `wc c` is the infinite place of `K` attached to the
seam embedding `φc c`.  The prescribed set
`{ofFinite (finQ K v) | v ∈ R} ∪ {wc c | c ∈ C}` is pairwise non-conjugate:
* two finite places are not conjugate (exactly `hRnc`),
* a finite place is never conjugate to an infinite one (`Place.IsFinite` is `smul`-invariant:
  `Work.SSGRoute.PT.isFinite_smul_iff`, `Place.isFinite_iff`, `NK.GlobalCFT.Place.ofInfinite_ne_ofFinite`),
* `σ • wc c = wc c'` implies `c` and `c'` are conjugate (`wc_orbit_injective`, with the seam
  properties from `hseam`), hence `c = c'` by `hCdisj`.

`exists_transversal_containing_set` (`PT/glue_helpers`) then produces the transversal. -/
theorem exists_transversal_places_wc (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K]
    (R : Set (ValuationSubring Ω)) (hRfin : ∀ v ∈ R, SSGRoute.IsFinPlace k v)
    (hRnc : ∀ v ∈ R, ∀ w ∈ R, SSGRoute.IsConjPlace k v w → v = w)
    (wc : (Ω ≃ₐ[k] Ω) → NK.GlobalCFT.Place ↥K) (φc : (Ω ≃ₐ[k] Ω) → (Ω →+* ℂ))
    (hseam : ∀ c : (Ω ≃ₐ[k] Ω), c ^ 2 = 1 → c ≠ 1 →
      (∀ x : Ω, φc c (c x) = starRingEnd ℂ (φc c x)) ∧
      wc c = NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk ((φc c).comp (algebraMap (↥K) Ω))))
    (C : Finset (Ω ≃ₐ[k] Ω)) (hCinv : ∀ c ∈ C, c ^ 2 = 1) (hC1 : ∀ c ∈ C, c ≠ 1)
    (hCdisj : ∀ c ∈ C, ∀ c' ∈ C, (∃ σ : Ω ≃ₐ[k] Ω, c' = σ * c * σ⁻¹) → c = c') :
    ∃ RK : Set (NK.GlobalCFT.Place ↥K),
      (∀ (v : ValuationSubring Ω) (hv : v ∈ R),
        NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K v (hRfin v hv)) ∈ RK) ∧
      (∀ c ∈ C, wc c ∈ RK) ∧
      (∀ w : NK.GlobalCFT.Place ↥K, ∃! w' : ↥RK, ∃ σ : ↥K ≃ₐ[k] ↥K, σ • w = w'.1) := by
  classical
  -- The prescribed set: the finite places below `R` together with the linked infinite places.
  let S : Set (NK.GlobalCFT.Place ↥K) :=
    Set.range (fun v : ↥R =>
      NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K v.1 (hRfin v.1 v.2)))
      ∪ Set.range (fun c : ↥C => wc c.1)
  -- `S` is pairwise non-conjugate.
  have hS : ∀ a ∈ S, ∀ b ∈ S, (∃ σ : ↥K ≃ₐ[k] ↥K, σ • a = b) → a = b := by
    rintro a (⟨v, rfl⟩ | ⟨c, rfl⟩) b (⟨w, rfl⟩ | ⟨c', rfl⟩) ⟨σ, hσ⟩
    · -- two finite places: reduce to `hRnc` via `isConjPlace_of_finQ_conj`
      have hconj : ∃ σ : ↥K ≃ₐ[k] ↥K,
          σ • NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K v.1 (hRfin v.1 v.2)) =
            NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K w.1 (hRfin w.1 w.2)) :=
        ⟨σ, hσ⟩
      have hvw : v.1 = w.1 :=
        hRnc v.1 v.2 w.1 w.2
          (isConjPlace_of_finQ_conj k Ω K v.1 w.1 (hRfin v.1 v.2) (hRfin w.1 w.2) hconj)
      rw [Subtype.ext hvw]
    · -- a finite place is never conjugate to an infinite one
      exfalso
      have hfin : (NK.GlobalCFT.Place.ofFinite
          (Work.SSGRoute.PT.finQ K v.1 (hRfin v.1 v.2))).IsFinite :=
        NK.GlobalCFT.Place.isFinite_ofFinite _
      have hσred : σ • (NK.GlobalCFT.Place.ofFinite
          (Work.SSGRoute.PT.finQ K v.1 (hRfin v.1 v.2))) = wc c'.1 := hσ
      have hfin' : (wc c'.1).IsFinite := by
        rw [← hσred]
        exact (isFinite_smul_iff K σ _).mpr hfin
      rw [show wc c'.1 = NK.GlobalCFT.Place.ofInfinite
            (NumberField.InfinitePlace.mk ((φc c'.1).comp (algebraMap (↥K) Ω))) from
          (hseam c'.1 (hCinv c'.1 c'.2) (hC1 c'.1 c'.2)).2] at hfin'
      exact absurd hfin' (NK.GlobalCFT.Place.not_isFinite_ofInfinite _)
    · -- an infinite place is never conjugate to a finite one
      exfalso
      have hfin : (NK.GlobalCFT.Place.ofFinite
          (Work.SSGRoute.PT.finQ K w.1 (hRfin w.1 w.2))).IsFinite :=
        NK.GlobalCFT.Place.isFinite_ofFinite _
      have hσred : σ • wc c.1 = (NK.GlobalCFT.Place.ofFinite
          (Work.SSGRoute.PT.finQ K w.1 (hRfin w.1 w.2))) := hσ
      have hfin' : (wc c.1).IsFinite :=
        (isFinite_smul_iff K σ (wc c.1)).mp (by rw [hσred]; exact hfin)
      rw [show wc c.1 = NK.GlobalCFT.Place.ofInfinite
            (NumberField.InfinitePlace.mk ((φc c.1).comp (algebraMap (↥K) Ω))) from
          (hseam c.1 (hCinv c.1 c.2) (hC1 c.1 c.2)).2] at hfin'
      exact absurd hfin' (NK.GlobalCFT.Place.not_isFinite_ofInfinite _)
    · -- two infinite places: conjugacy of the places forces conjugacy of the involutions
      change wc c.1 = wc c'.1
      have hσ' : σ • NK.GlobalCFT.Place.ofInfinite
            (NumberField.InfinitePlace.mk ((φc c.1).comp (algebraMap (↥K) Ω))) =
          NK.GlobalCFT.Place.ofInfinite
            (NumberField.InfinitePlace.mk ((φc c'.1).comp (algebraMap (↥K) Ω))) := by
        rw [← (hseam c.1 (hCinv c.1 c.2) (hC1 c.1 c.2)).2,
            ← (hseam c'.1 (hCinv c'.1 c'.2) (hC1 c'.1 c'.2)).2]
        exact hσ
      obtain ⟨τ, hτ⟩ := wc_orbit_injective k Ω K c.1 c'.1
        (hCinv c.1 c.2) (hC1 c.1 c.2) (hCinv c'.1 c'.2) (hC1 c'.1 c'.2)
        (φc c.1) (φc c'.1)
        (hseam c.1 (hCinv c.1 c.2) (hC1 c.1 c.2)).1
        (hseam c'.1 (hCinv c'.1 c'.2) (hC1 c'.1 c'.2)).1 σ hσ'
      rw [hCdisj c.1 c.2 c'.1 c'.2 ⟨τ, hτ⟩]
  -- Produce the transversal containing `S`.
  obtain ⟨RK, hSRK, htrans⟩ :=
    exists_transversal_containing_set (G := ↥K ≃ₐ[k] ↥K)
      (α := NK.GlobalCFT.Place ↥K) S hS
  exact ⟨RK, fun v hv => hSRK (Or.inl ⟨⟨v, hv⟩, rfl⟩),
    fun c hc => hSRK (Or.inr ⟨⟨c, hc⟩, rfl⟩), htrans⟩

end Work.SSGRoute.PT
