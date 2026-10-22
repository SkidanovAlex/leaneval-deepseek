/-
AREA RESOL — the reduced atom cover (`HasAtomicCover₀`).

The cover of `RESOL/AtomicCover.lean` is indexed by *all* sections of `M` over the skeleton
elements, so it does not preserve zero morphisms: the zero section gives a summand mapping
identically onto the corresponding summand of `F 0`.  The double complex of degreewise resolutions
needs `F 0 = 0` (to get `R (d) ≫ R (d) = R (d ≫ d) = R 0 = 0`), so the construction of B6 uses
the *reduced* cover indexed by the **nonzero** sections, which is built in
`RESOL/ReducedCover.lean`.
-/
import Submission.Work.RESOL.Basic
import Submission.Work.RESOL.exists_atomSkeleton
import Submission.Work.RESOL.ReducedCover

noncomputable section

namespace Work.RESOL

/-- **The reduced atom cover exists.**  There is a functor `F : LightCondAb ⥤ LightCondAb`
preserving zero morphisms and a natural epimorphism `F ⟶ 𝟭`, whose value at every light condensed
abelian group is a small coproduct of free objects `ℤ[S]` on light profinite sets. -/
theorem hasAtomicCoverZero : HasAtomicCover₀ := by
  obtain ⟨ι, S, h⟩ := exists_atomSkeleton
  exact ⟨redCoverFunctor S, redCoverNat S, redCoverFunctor_preservesZeroMorphisms S,
    fun M => epi_redCoverMap S h M, fun M => isAtomicSum_redCover S M⟩

end Work.RESOL
