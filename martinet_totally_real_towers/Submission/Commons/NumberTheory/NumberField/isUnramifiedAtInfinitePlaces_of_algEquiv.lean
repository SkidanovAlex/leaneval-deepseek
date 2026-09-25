import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

namespace NumberField.InfinitePlace

/-- The multiplicity of an infinite place is invariant under `comap` along a ring isomorphism:
a real place pulls back to a real place, and a complex place to a complex place. -/
lemma mult_comap_ringEquiv {k K : Type*} [Field k] [Field K]
    (f : k ≃+* K) (w : InfinitePlace K) : mult (w.comap (f : k →+* K)) = mult w := by
  by_cases hw : IsReal w
  · rw [IsReal.mult_eq_one hw, IsReal.mult_eq_one ((isReal_comap_iff f).2 hw)]
  · rw [IsComplex.mult_eq_two (not_isReal_iff_isComplex.1 hw),
      IsComplex.mult_eq_two (not_isReal_iff_isComplex.1 (mt (isReal_comap_iff f).1 hw))]

end NumberField.InfinitePlace

namespace Commons.NumberTheory.NumberField

/-- Unramifiedness at all infinite places is invariant under `F`-algebra isomorphisms of the
top field. -/
theorem isUnramifiedAtInfinitePlaces_of_algEquiv {F L L' : Type*} [Field F] [NumberField F]
    [Field L] [NumberField L] [Field L'] [NumberField L'] [Algebra F L] [Algebra F L']
    (e : L ≃ₐ[F] L') (h : IsUnramifiedAtInfinitePlaces F L) : IsUnramifiedAtInfinitePlaces F L' := by
  refine ⟨fun w' => ?_⟩
  have hw : NumberField.InfinitePlace.IsUnramified F (w'.comap (e : L →+* L')) :=
    h.isUnramified _
  have hcomp : (w'.comap (e : L →+* L')).comap (algebraMap F L)
      = w'.comap (algebraMap F L') := by
    rw [← NumberField.InfinitePlace.comap_comp]
    congr 1
    exact AlgHom.comp_algebraMap (e : L →ₐ[F] L')
  rw [NumberField.InfinitePlace.IsUnramified]
  calc NumberField.InfinitePlace.mult (w'.comap (algebraMap F L'))
      = NumberField.InfinitePlace.mult ((w'.comap (e : L →+* L')).comap (algebraMap F L)) := by
        rw [hcomp]
    _ = NumberField.InfinitePlace.mult (w'.comap (e : L →+* L')) := hw
    _ = NumberField.InfinitePlace.mult w' :=
        NumberField.InfinitePlace.mult_comap_ringEquiv (e : L ≃+* L') w'

end Commons.NumberTheory.NumberField
