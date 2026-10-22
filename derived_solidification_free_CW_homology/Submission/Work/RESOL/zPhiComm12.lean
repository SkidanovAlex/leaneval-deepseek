/-
AREA RESOL — the naturality of the cut augmentation in the filtration step.

For a cochain complex `B` of light condensed abelian groups and `j : ℤ`:

* `Zero.totCut j B` is the total complex of the columns `q ≥ j` of the resolution bicomplex,
  `Zero.cutJ j B : totCut j B ⟶ totCut (j-1) B` is the inclusion of the columns `q ≥ j`
  (component formula `Zero.cutJ_ι`);
* `Zero.epsCutFam j B n : (totCut j B).X n ⟶ (trunc j B).X n` is the degree `n` part of the
  augmentation of the cut onto the brutal truncation (component formula `Zero.epsCutFam_ι`);
* `truncIncl B j : trunc j B ⟶ trunc (j-1) B` is the canonical inclusion of the brutal
  truncation (`solidCofibrant_trunc.lean`, component formula `truncIncl_f_of_le`).

The lemma says that these two inclusions are compatible with the augmentations:

`epsCutFam j B n ≫ (truncIncl B j).f n = cutJ j B n ≫ epsCutFam (j-1) B n`.

Both sides are morphisms out of the coproduct `∐ (totFam (geP j) B n)`, so it suffices to test
the identity on the summands `Sigma.ι x` (`Sigma.hom_ext`).  For an index
`x = (q, p)` (column `q ≥ j`, resolution degree `p = n - q`):

* on the left, `Zero.epsCutFam_ι` gives `0` unless `p = 0` and otherwise the component
  `aug0 ≫ (transport to (trunc j B).X n)`, and `truncIncl` is the identity on the common terms
  (`truncIncl_f_of_le` when `j ≤ n`, which holds since `p = 0` gives `q = n`);
* on the right, `Zero.cutJ_ι` moves the summand to the index `cutJIdx x` (with the same column
  and resolution degree, seen in `totCut (j-1) B`), and `Zero.epsCutFam_ι` again gives `0` unless
  `p = 0` and otherwise the same `aug0` followed by the transport to `(trunc (j-1) B).X n`.

In the case `p = 0` both sides are therefore `aug0` followed by transports given by `eqToHom`s
between the same objects; `eqToHom_trans` merges the two transports on the left, and the two
sides then agree by definitional equality of the index (the proof component of `cutJIdx` is
irrelevant).  In the case `p ≠ 0` both sides are `0`.
-/
import Mathlib
import Submission.Work.RESOL.ZeroCutJ
import Submission.Work.RESOL.ZeroTruncSES
import Submission.Work.RESOL.solidCofibrant_trunc

open CategoryTheory Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.RESOL

theorem zPhiComm12 (F : CategoryTheory.Functor LightCondAb LightCondAb)
    [F.PreservesZeroMorphisms] (π : F ⟶ CategoryTheory.Functor.id LightCondAb)
    (hπ : ∀ M : LightCondAb, CategoryTheory.Epi (π.app M)) (j : ℤ) (B : Work.RESOL.Cpx)
    (n : ℤ) :
    CategoryTheory.CategoryStruct.comp (Work.RESOL.Zero.epsCutFam F π hπ j B n)
        ((Work.RESOL.truncIncl B j).f n)
      = CategoryTheory.CategoryStruct.comp (Work.RESOL.Zero.cutJ F π hπ j B n)
          (Work.RESOL.Zero.epsCutFam F π hπ (j - 1) B n) := by
  apply Sigma.hom_ext
  intro x
  rw [← Category.assoc, ← Category.assoc]
  rw [Zero.epsCutFam_ι, Zero.cutJ_ι, Zero.epsCutFam_ι]
  -- unfold the index re-indexing `cutJIdx` so that both sides are written in terms of `x`
  simp only [Zero.cutJIdx]
  by_cases hp : x.1.2 = 0
  · -- resolution degree `0`: both sides are `aug0` followed by a transport
    rw [dite_eq_left hp, dite_eq_left hp]
    rw [truncIncl_f_of_le B j (by have h1 := x.2.1; have h2 := x.2.2; omega)]
    simp only [HomologicalComplex.XIsoOfEq, eqToIso.hom, Category.assoc, eqToHom_trans]
  · -- positive resolution degree: both sides vanish
    rw [dite_eq_right hp, dite_eq_right hp]
    simp

end Work.RESOL

end
