import Mathlib
import Submission.Work.RESOL.ZeroTotal
import Submission.Work.RESOL.zAtomicTermsRco
import Submission.Work.RESOL.hasAtomicTerms_R

namespace Work.RESOL

theorem zHasAtomicTermsTotFull (F : CategoryTheory.Functor LightCondAb LightCondAb)
    [F.PreservesZeroMorphisms] (π : F ⟶ CategoryTheory.Functor.id LightCondAb)
    (hπ : ∀ M : LightCondAb, CategoryTheory.Epi (π.app M))
    (hF : ∀ M : LightCondAb, Work.RESOL.IsAtomicSum (F.obj M)) (B : Work.RESOL.Cpx) :
    Work.RESOL.HasAtomicTerms (Work.RESOL.Zero.totFull F π hπ B) := by
  -- The `n`-th term of the total complex is the small coproduct, over the index set
  -- `TotIdx topP n = {(q, p) | p + q = n}`, of the terms `(Rco.obj (B.X q)).X p`, each of which
  -- is a small atomic sum by `zAtomicTermsRco`.  A small coproduct of small atomic sums is a
  -- small atomic sum by `isAtomicSum_sigma`.
  intro n
  show Work.RESOL.IsAtomicSum (∐ (Work.RESOL.Zero.totFam F π hπ Work.RESOL.Zero.topP B n))
  exact Work.RESOL.isAtomicSum_sigma _
    (fun y => Work.RESOL.zAtomicTermsRco F π hπ hF (B.X y.1.1) y.1.2)

end Work.RESOL
