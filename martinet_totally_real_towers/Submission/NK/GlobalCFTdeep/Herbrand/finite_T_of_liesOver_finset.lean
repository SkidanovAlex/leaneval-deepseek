import Mathlib
import Submission.NK.GlobalCFT.Place

namespace NK.GlobalCFTdeep.Herbrand

/-- If `S` is a finite set of places of `K` and `T` is the set of places of `L` lying over some
place in `S`, then `T` is finite: the archimedean places of `L` are finite in number and only
finitely many primes of `𝓞 L` lie over each prime of `𝓞 K` occurring in `S`. -/
theorem finite_T_of_liesOver_finset {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (S : Finset (NK.GlobalCFT.Place K)) (T : Set (NK.GlobalCFT.Place L))
    (hTS : ∀ w : NK.GlobalCFT.Place L, w ∈ T ↔ ∃ v ∈ S, NK.GlobalCFT.Place.LiesOver w v) :
    T.Finite := by
  classical
  -- An explicit finite set of places of `L` containing `T`: all archimedean places of `L`,
  -- together with the primes of `𝓞 L` lying over the finite places in `S`.
  let F : Finset (NK.GlobalCFT.Place L) :=
    (Finset.univ.image NK.GlobalCFT.Place.ofInfinite) ∪
      S.biUnion (fun v => v.elim (fun _ => ∅)
        (fun Q => (NK.GlobalCFT.Place.primesOverFinite Q).image NK.GlobalCFT.Place.ofFinite))
  have hsub : T ⊆ (F : Set (NK.GlobalCFT.Place L)) := by
    intro w hw
    rw [hTS w] at hw
    obtain ⟨v, hvS, hLies⟩ := hw
    rcases hLies with ⟨w', v', rfl, rfl, h⟩ | ⟨q, Q, rfl, rfl, h⟩
    · -- an archimedean place of `L`
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ w'))
    · -- a nonarchimedean place of `L`, over the finite place `ofFinite Q ∈ S`
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨NK.GlobalCFT.Place.ofFinite Q, hvS,
          Finset.mem_image_of_mem _
            (NK.GlobalCFT.Place.mem_primesOverFinite.mpr h)⟩)
  exact (Finset.finite_toSet F).subset hsub

end NK.GlobalCFTdeep.Herbrand
