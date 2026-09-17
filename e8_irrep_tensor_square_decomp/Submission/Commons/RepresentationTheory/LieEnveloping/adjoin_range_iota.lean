import Mathlib.Algebra.Lie.UniversalEnveloping

namespace Commons.RepresentationTheory.LieEnveloping

/-- The image of the canonical map `ι R : L → U(L)` generates the universal enveloping algebra
as an `R`-algebra.  (Proof sketch: `UniversalEnvelopingAlgebra.mkAlgHom R L` is surjective,
`AlgHom.map_adjoin` transports generation from the tensor algebra, and
`TensorAlgebra.adjoin_range_ι` says the tensor-algebra generators generate.) -/
theorem adjoin_range_iota {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] :
    Algebra.adjoin R (Set.range (UniversalEnvelopingAlgebra.ι R : L → UniversalEnvelopingAlgebra R L)) = ⊤ := by
  have hrange : Set.range (UniversalEnvelopingAlgebra.ι R : L → UniversalEnvelopingAlgebra R L)
      = (UniversalEnvelopingAlgebra.mkAlgHom R L) ''
          (Set.range (TensorAlgebra.ι R : L → TensorAlgebra R L)) := by
    ext x
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨TensorAlgebra.ι R l, ⟨l, rfl⟩, by rw [UniversalEnvelopingAlgebra.ι_apply]⟩
    · rintro ⟨t, ⟨l, rfl⟩, rfl⟩
      exact ⟨l, by rw [UniversalEnvelopingAlgebra.ι_apply]⟩
  rw [hrange, ← AlgHom.map_adjoin, TensorAlgebra.adjoin_range_ι, Algebra.map_top]
  exact (AlgHom.range_eq_top _).mpr (RingCon.mkₐ_surjective _)

end Commons.RepresentationTheory.LieEnveloping