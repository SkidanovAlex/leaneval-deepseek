import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

namespace Commons.NumberTheory.NumberField

/-- **Unramifiedness at infinite places from "real places stay real".**

If every real infinite place of `F` extends only to real places of `L`, then the extension `L/F` is
unramified at all infinite places.

Proof: `NumberField.InfinitePlace.isRamified_iff` says `w` is ramified over `F` iff `w` is complex
and `w.comap (algebraMap F L)` is real; the hypothesis excludes this (the comap would be real, so
`w` would be real, contradicting `w` being complex), and
`NumberField.InfinitePlace.isUnramified_or_isRamified` splits the cases. -/
theorem isUnramifiedAtInfinitePlaces_of_forall_comap_isReal (F L : Type*) [Field F] [NumberField F]
    [Field L] [NumberField L] [Algebra F L]
    (h : ∀ w : NumberField.InfinitePlace F, w.IsReal →
      ∀ w' : NumberField.InfinitePlace L, w'.comap (algebraMap F L) = w → w'.IsReal) :
    IsUnramifiedAtInfinitePlaces F L := by
  refine ⟨fun w => ?_⟩
  rw [NumberField.InfinitePlace.isUnramified_iff]
  by_cases hw : w.IsReal
  · exact Or.inl hw
  · refine Or.inr ?_
    by_contra hc
    rw [NumberField.InfinitePlace.not_isComplex_iff_isReal] at hc
    exact hw (h (w.comap (algebraMap F L)) hc w rfl)

end Commons.NumberTheory.NumberField