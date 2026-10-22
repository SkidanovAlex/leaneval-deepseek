/-
AREA RESOL — the degreewise inclusion of the columns `≥ k` into all the columns is an
isomorphism as soon as no column `< k` can contribute in that degree.

The total complex `totFull B` has degree `n` given by the coproduct over the pairs `(q, p)` with
`p + q = n` of the summand `((Rco).obj (B.X q)).X p`.  The resolution functor `Rco` is
concentrated in cochain degrees `≤ 0`, so a summand with `p > 0` is the zero object.  In degree
`n ≥ k` every index with `q < k` has `p = n - q > 0`, hence contributes nothing: the summands of
`(totCut k B).X n` are exactly the nonzero summands of `(totFull B).X n`, and the inclusion
`Zero.cutInclTopFam` is an isomorphism.

This is the general statement `isIso_sigmaDesc_of_zero_complement` applied to the injection of
index sets `TotIdx (geP k) n ↪ TotIdx topP n`.

This is the input `Zero.quasiIsoAt_cutInclTop` (the inclusion is a quasi-isomorphism in degrees
`≥ k+1`) needs; it is stated separately because the chain-map level statement lives in
`ZeroTruncSES.lean`.
-/
import Mathlib
import Submission.Work.RESOL.ZeroTruncSES
import Submission.Work.RESOL.isIso_sigmaDesc_of_zero_complement

open CategoryTheory Limits LightProfinite LightCondensed
open _root_.LightCondensed

noncomputable section

namespace Work.RESOL

theorem zIsIsoCutInclTopFam (F : CategoryTheory.Functor LightCondAb LightCondAb)
    [F.PreservesZeroMorphisms] (π : F ⟶ CategoryTheory.Functor.id LightCondAb)
    (hπ : ∀ M : LightCondAb, CategoryTheory.Epi (π.app M)) (k : ℤ) (B : Work.RESOL.Cpx)
    (n : ℤ) (hn : k ≤ n) :
    CategoryTheory.IsIso (Work.RESOL.Zero.cutInclTopFam F π hπ k B n) := by
  -- `cutInclTopFam` is the coproduct inclusion induced by `TotIdx (geP k) n ↪ TotIdx topP n`.
  show CategoryTheory.IsIso (Sigma.desc (fun x : Zero.TotIdx (Zero.geP k) n =>
      Sigma.ι (Zero.totFam F π hπ Zero.topP B n) ⟨x.1, ⟨x.2.1, trivial⟩⟩))
  refine isIso_sigmaDesc_of_zero_complement
    (Y := Zero.totFam F π hπ Zero.topP B n)
    (fun x : Zero.TotIdx (Zero.geP k) n => ⟨x.1, ⟨x.2.1, trivial⟩⟩) ?_ ?_
  · -- the index map is injective
    intro x y hxy
    have h : (x.1 : ℤ × ℤ) = y.1 := by
      simpa using congrArg (fun z : Zero.TotIdx Zero.topP n => z.1) hxy
    exact Subtype.ext h
  · -- an index outside the image has column `< k`, hence resolution degree `> 0`, hence a zero
    -- summand
    intro j hj
    have hq : ¬ (Zero.geP k j.1.1) := by
      intro h
      exact hj ⟨(j.1.1, j.1.2), ⟨j.2.1, h⟩⟩ (Subtype.ext rfl)
    have hp : 0 < j.1.2 := by
      have := j.2.1
      omega
    exact CochainComplex.isZero_of_isStrictlyLE ((Zero.Rco F π hπ).obj (B.X j.1.1)) 0 j.1.2 hp

end Work.RESOL

end
