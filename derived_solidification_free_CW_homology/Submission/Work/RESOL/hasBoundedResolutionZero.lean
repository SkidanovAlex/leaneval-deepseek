import Mathlib
import Submission.Work.RESOL.Basic
import Submission.Work.RESOL.Instances
import Submission.Work.RESOL.ReducedCover
import Submission.Work.RESOL.AtomicCoverZero
import Submission.Work.RESOL.ZeroFilter
import Submission.Work.RESOL.zHasAtomicTermsTotFull
import Submission.Work.RESOL.zIsBoundedAboveTotFull

namespace Work.RESOL

/--
**B6, degreewise.**  From a functorial atom cover `(F, π)` whose functor preserves zero
morphisms -- that is, from `HasAtomicCover₀` -- one gets a functorial resolution by complexes of
atoms of every cochain complex, with a natural augmentation which is a quasi-isomorphism and
solid-cofibrant on every bounded-above complex.

The resolution functor is `Zero.R F π hπ`, the total complex of the column-wise resolutions
`Rco.obj (B.X q)` (`RESOL/ZeroRes.lean`), and the augmentation is `Zero.eps F π hπ`.  Its
filtration by the columns (`RESOL/ZeroFilter.lean`) gives the quasi-isomorphism property on
bounded-above complexes, while the atomicity of the terms and the boundedness of the resolution
of a bounded-above complex are `zHasAtomicTermsTotFull` and `zIsBoundedAboveTotFull`; the
solid-cofibrancy then follows from `hB5`. -/
theorem hasBoundedResolutionZero (hcover : Work.RESOL.HasAtomicCover₀) (hC : Work.RESOL.CofibrantClosure)
    (hB5 : ∀ (K : Work.RESOL.Cpx), Work.RESOL.IsBoundedAbove K → Work.RESOL.HasAtomicTerms K →
      Submission.Blueprint.SolidCofibrant K) :
    ∃ (R : CategoryTheory.Functor Work.RESOL.Cpx Work.RESOL.Cpx)
      (ε : R ⟶ CategoryTheory.Functor.id Work.RESOL.Cpx),
      (∀ B : Work.RESOL.Cpx, Work.RESOL.HasAtomicTerms (R.obj B)) ∧
      (∀ B : Work.RESOL.Cpx, Work.RESOL.IsBoundedAbove B → QuasiIso (ε.app B)) ∧
      (∀ B : Work.RESOL.Cpx, Work.RESOL.IsBoundedAbove B →
        Submission.Blueprint.SolidCofibrant (R.obj B)) := by
  obtain ⟨F, π, hF0, hπ, hFat⟩ := hcover
  haveI : F.PreservesZeroMorphisms := hF0
  refine ⟨Zero.R F π hπ, Zero.eps F π hπ, ?_, ?_, ?_⟩
  · intro B
    exact zHasAtomicTermsTotFull F π hπ hFat B
  · intro B hB
    exact Zero.quasiIso_eps_of_boundedAbove F π hπ B hB
  · intro B hB
    exact hB5 (Zero.totFull F π hπ B) (zIsBoundedAboveTotFull F π hπ B hB)
      (zHasAtomicTermsTotFull F π hπ hFat B)

end Work.RESOL
