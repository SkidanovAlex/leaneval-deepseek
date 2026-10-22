/-
AREA RESOL — comparison of the augmentation `totFull B ⟶ B` with the truncated augmentation
`totCut k B ⟶ trunc k B`.

For a cochain complex `B` of light condensed abelian groups and `k : ℤ`:

* `Zero.totCut k B` is the total complex of the columns `q ≥ k` of the resolution bicomplex
  (`Zero.totCpx` with the predicate `Zero.geP k`), `Zero.totFull B` is the total complex of
  *all* the columns;
* `Zero.cutInclTopFam k B n : (totCut k B).X n ⟶ (totFull B).X n` is the degree `n` part of the
  inclusion of the columns `q ≥ k` into all the columns (`Zero.cutInclTopFam_ι`);
* `Zero.epsFam B n : (totFull B).X n ⟶ B.X n` is the degree `n` part of the augmentation
  `ε : R B ⟶ B` (it augments the summands of resolution degree `0` and kills all others);
* `Zero.epsCutFam k B n : (totCut k B).X n ⟶ (trunc k B).X n` is the degree `n` part of the
  augmentation of the cut, with values in the *brutal truncation* `trunc k B`;
* `Work.RESOL.loT k B n : (trunc k B).X n ⟶ B.X n` is the (inclusion of the) stupid truncation
  at level `k` in degree `n`.

The lemma proved here is the degreewise compatibility of the two augmentations:

`cutInclTopFam ≫ epsFam = epsCutFam ≫ loT`  in degree `n`.

Both sides are morphisms `(totCut k B).X n ⟶ B.X n`, i.e. morphisms out of the coproduct
`∐ (totFam (geP k) B n)`, so it suffices to test the identity on the summands `Sigma.ι x`
(`Sigma.hom_ext`).  For an index `x = (q, p)` (column `q ≥ k`, resolution degree `p = n - q`):

* `cutInclTopFam` sends the summand to the summand of `totFull B` with the same index, where the
  component of `epsFam` is `0` unless `p = 0` (`Zero.zEpsFam_ι`);
* the component of `epsCutFam` is `0` unless `p = 0` (`Zero.epsCutFam_ι`), and if `p = 0` it is
  `aug0` followed by the transport `B.X q ⟶ (trunc k B).X n`, while `loT k B n` is the inverse
  transport `(trunc k B).X n ⟶ B.X n` (`loT_eq_trunc` below; it is available because `k ≤ q = n`
  when `p = 0`).

In the case `p = 0` both sides are therefore `aug0` followed by a transport from `B.X q` to
`B.X n` given by an `eqToHom`, and `simp` merges the transports (`eqToHom_trans`) and identifies
them (`HomologicalComplex.XIsoOfEq` unfolds to `eqToHom`; the remaining proof arguments are
irrelevant).  In the case `p ≠ 0` both sides are `0`.
-/
import Mathlib
import Submission.Work.RESOL.ZeroTruncSES
import Submission.Work.RESOL.exists_windowTower

open CategoryTheory Limits LightProfinite LightCondensed
open _root_.LightCondensed

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Work.RESOL

/-- The stupid truncation inclusion `loT k B n : (trunc k B).X n ⟶ B.X n` in the `eqToHom`
form.  This is the form in which it is compared with the transport appearing in
`Zero.epsCutFam` (the two are the same transport, written with the two different descriptions
`(trunc k B).X n = B.X n` of the equation). -/
lemma loT_eq_trunc (k : ℤ) (B : Cpx) {n : ℤ} (h : k ≤ n) :
    loT k B n = eqToHom (trunc_X_of_le B k h) := by
  rw [loT_eq k B n h]

/-- **Comparison of the augmentation with its truncated version.**  The augmentation of the total
complex of all the columns, restricted to the columns `q ≥ k`, agrees with the augmentation of
the cut composed with the inclusion of the truncation `trunc k B` into `B`. -/
theorem zCutEpsComm (F : CategoryTheory.Functor LightCondAb LightCondAb)
    [F.PreservesZeroMorphisms] (π : F ⟶ CategoryTheory.Functor.id LightCondAb)
    (hπ : ∀ M : LightCondAb, CategoryTheory.Epi (π.app M)) (k : ℤ) (B : Work.RESOL.Cpx)
    (n : ℤ) :
    CategoryTheory.CategoryStruct.comp (Work.RESOL.Zero.cutInclTopFam F π hπ k B n)
        (Work.RESOL.Zero.epsFam F π hπ B n)
      = CategoryTheory.CategoryStruct.comp (Work.RESOL.Zero.epsCutFam F π hπ k B n)
          (Work.RESOL.loT k B n) := by
  apply Sigma.hom_ext
  intro x
  rw [← Category.assoc, Zero.cutInclTopFam_ι]
  rw [Zero.zEpsFam_ι]
  rw [← Category.assoc, Zero.epsCutFam_ι]
  by_cases hp : x.1.2 = 0
  · -- resolution degree `0`: both sides are `aug0` followed by a transport `B.X q ⟶ B.X n`
    rw [dite_eq_left hp, dite_eq_left hp]
    have hkn : k ≤ n := by have h1 := x.2.1; have h2 := x.2.2; omega
    rw [loT_eq_trunc k B hkn]
    simp only [HomologicalComplex.XIsoOfEq, eqToIso.hom, Category.assoc, eqToHom_trans]
  · -- positive resolution degree: both sides vanish
    rw [dite_eq_right hp, dite_eq_right hp, zero_comp]

end Work.RESOL

end
