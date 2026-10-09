import Mathlib
import Submission.NK.GlobalCFTdeep.Herbrand.SIdeles
import Submission.NK.GlobalCFTdeep.Herbrand.exists_finset_TIdeles_surjective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFTdeep.SecondInequality

open NK.GlobalCFT

/-- The `T`-idèles shrink as `T` grows: if `T ⊆ S` then every idèle which is a local unit
outside `T` is also a local unit outside `S`. -/
theorem TIdeles_mono {K : Type} [Field K] [NumberField K]
    {T S : Set (NK.GlobalCFT.Place K)} (hTS : T ⊆ S) :
    NK.GlobalCFTdeep.TIdeles (L := K) T ≤ NK.GlobalCFTdeep.TIdeles (L := K) S := by
  intro x hx
  rw [NK.GlobalCFTdeep.mem_TIdeles] at hx ⊢
  exact fun w hw => hx w fun hT => hw (hTS hT)

/-- There is a finite set `S` of places of a number field `K`, containing all the archimedean
ones, such that the `S`-idèles surject onto the ideal class group of `K`: every ideal class is
represented by an idèle which is a local unit outside `S`. -/
theorem exists_finset_place_idealClassMap {K : Type} [Field K] [NumberField K] :
    ∃ S : Finset (NK.GlobalCFT.Place K),
      (∀ w : NK.GlobalCFT.Place K, w.IsInfinite → w ∈ S) ∧
      (∀ c : ClassGroup (NumberField.RingOfIntegers K),
        ∃ u ∈ NK.GlobalCFTdeep.TIdeles (L := K) (S : Set (NK.GlobalCFT.Place K)),
          NK.GlobalCFT.IdeleClassGroup.idealClassMap K u = c) := by
  classical
  -- a finite set of places whose `T`-idèles already surject onto the class group
  obtain ⟨T, hT⟩ := NK.GlobalCFTdeep.Herbrand.exists_finset_TIdeles_surjective (L := K)
  -- enlarge it by the (finitely many) archimedean places
  refine ⟨T ∪ (Finset.univ.image Place.ofInfinite), ?_, ?_⟩
  · intro w hw
    rw [Finset.mem_union]
    right
    rw [Place.isInfinite_iff] at hw
    obtain ⟨w', rfl⟩ := hw
    exact Finset.mem_image.mpr ⟨w', Finset.mem_univ _, rfl⟩
  · intro c
    obtain ⟨u, hu, huc⟩ := hT c
    refine ⟨u, ?_, huc⟩
    -- enlarging `T` only weakens the membership condition
    rw [NK.GlobalCFTdeep.mem_TIdeles] at hu ⊢
    intro w hw
    exact hu w fun h => hw (Finset.mem_union_left _ h)

end NK.GlobalCFTdeep.SecondInequality
