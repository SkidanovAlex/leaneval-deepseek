import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

namespace Commons.NumberTheory.NumberField

theorem totallyReal_of_unramifiedAtInfinitePlaces (k K : Type*) [Field k] [Field K]
    [Algebra k K] (hK : NumberField.IsTotallyReal k)
    [IsUnramifiedAtInfinitePlaces k K] :
    NumberField.IsTotallyReal K := by
  refine NumberField.IsTotallyReal.mk ?_
  intro w
  have hcomp_real : (w.comap (algebraMap k K)).IsReal := hK.isReal _
  exact (NumberField.InfinitePlace.isUnramified_iff.mp
    (NumberField.InfinitePlace.isUnramified k w)).resolve_right
      (NumberField.InfinitePlace.not_isComplex_iff_isReal.mpr hcomp_real)

end Commons.NumberTheory.NumberField