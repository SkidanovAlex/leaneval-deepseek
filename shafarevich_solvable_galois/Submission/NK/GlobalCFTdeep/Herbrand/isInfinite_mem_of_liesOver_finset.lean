import Mathlib
import Submission.NK.GlobalCFT.Place
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFTdeep.Herbrand

/-- Every archimedean place of `L` lies over an archimedean place of `K`, namely the restriction
`w.comap (algebraMap K L)`; since `S` contains all archimedean places of `K`, an archimedean place
of `L` lies over some member of `S`, and hence belongs to `T`. -/
theorem isInfinite_mem_of_liesOver_finset {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (S : Finset (NK.GlobalCFT.Place K)) (T : Set (NK.GlobalCFT.Place L))
    (hTS : ∀ w : NK.GlobalCFT.Place L, w ∈ T ↔ ∃ v ∈ S, NK.GlobalCFT.Place.LiesOver w v)
    (hSinf : ∀ a : NumberField.InfinitePlace K, NK.GlobalCFT.Place.ofInfinite a ∈ S) :
    ∀ w : NK.GlobalCFT.Place L, w.IsInfinite → w ∈ T := by
  intro w hw
  obtain ⟨w', rfl⟩ := NK.GlobalCFT.Place.isInfinite_iff.mp hw
  rw [hTS]
  refine ⟨NK.GlobalCFT.Place.ofInfinite (w'.comap (algebraMap K L)), hSinf _, ?_⟩
  exact NK.GlobalCFT.Place.liesOver_ofInfinite
    (show NumberField.InfinitePlace.LiesOver w' (w'.comap (algebraMap K L)) from ⟨rfl⟩)

end NK.GlobalCFTdeep.Herbrand
