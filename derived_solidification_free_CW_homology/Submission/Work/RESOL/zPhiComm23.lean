/-
AREA RESOL — the second face of the commutation of the column filtration with the target-side
truncation, `zPhiComm23`.

For `j n : ℤ` and a complex `B`, the degree `n` component of the augmentation of the columns
`q ≥ j-1` onto the truncation `trunc (j-1) B`, followed by the projection onto the new top term
`B.X (j-1)` of that truncation, equals the projection onto the `(j-1)`-st column followed by the
augmentation of that column.  Both sides are morphisms

`(totCut (j-1) B).X n ⟶ ((single (j-1)).obj (B.X (j-1))).X n`

and both are computed on the coproduct summands of the total complex:

* the second composite keeps the summands with `q = j-1` (`colProjFam`) and then augments them,
  which is non-zero only in the total degree `n = j-1`, where it augments the resolution degree
  `0` part of the resolution of `B.X (j-1)`;
* the first composite augments the summands of resolution degree `0` (`epsCutFam`) and then
  projects onto the top term `B.X (j-1)` of the truncation, which again is non-zero only in degree
  `n = j-1` and only for the column `q = j-1`.

The proof is the computation with the coproduct summands: after splitting on `n = j-1` and on
whether the summand is the one of column `(j-1)` with resolution degree `0` (the only case in
which the two sides do not vanish), the index is substituted by the explicit element
`zPhiComm23Idx j = (j-1, (j-1)-(j-1))`, at which the index arithmetic of the resolution agrees
definitionally with the index arithmetic of the total complex.  There the two sides differ only in
the way the terms are transported along the (definitionally equal) indices, so they agree by
`eqToHom_trans` and proof irrelevance.
-/
import Mathlib
import Submission.Work.RESOL.ZeroCutJ
import Submission.Work.RESOL.ZeroTruncSES
import Submission.Work.RESOL.solidCofibrant_trunc

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open CategoryTheory Limits LightProfinite LightCondensed
open _root_.LightCondensed

noncomputable section

namespace Work.RESOL

/-- The `hom` of the re-indexing isomorphism of a homological complex is the transport
`eqToHom` of the corresponding equality of the terms. -/
lemma zPhiComm23_XIsoOfEq_hom_eq (K : Cpx) {n m : ℤ} (h : n = m) :
    (K.XIsoOfEq h).hom = eqToHom (congrArg (fun t => K.X t) h) := rfl

/-- The index of the `(j-1)`-st column in total degree `j-1`, with the components written as
`j-1` and `(j-1)-(j-1)`: this is the index at which the index arithmetic of the `(j-1)`-st
column of the total complex is definitionally the index arithmetic of the resolution
(`Zero.totFam` at this index is definitionally the `(j-1)`-st column of the total complex). -/
abbrev zPhiComm23Idx (j : ℤ) : Zero.TotIdx (Zero.geP (j - 1)) (j - 1) :=
  ⟨(j - 1, (j - 1) - (j - 1)), ⟨sub_add_cancel _ _, le_refl _⟩⟩

theorem zPhiComm23 (F : CategoryTheory.Functor LightCondAb LightCondAb)
    [F.PreservesZeroMorphisms] (π : F ⟶ CategoryTheory.Functor.id LightCondAb)
    (hπ : ∀ M : LightCondAb, CategoryTheory.Epi (π.app M)) (j : ℤ) (B : Work.RESOL.Cpx)
    (n : ℤ) :
    CategoryTheory.CategoryStruct.comp (Work.RESOL.Zero.epsCutFam F π hπ (j - 1) B n)
        ((Work.RESOL.truncProj B j).f n)
      = CategoryTheory.CategoryStruct.comp (Work.RESOL.Zero.colProjFam F π hπ (j - 1) B n)
          (Work.RESOL.Zero.colAugFam F π hπ (j - 1) B n) := by
  apply CategoryTheory.Limits.Sigma.hom_ext
  intro x
  rw [← Category.assoc, ← Category.assoc]
  rw [Zero.epsCutFam_ι, Zero.colProjFam_ι]
  by_cases hn : n = j - 1
  · subst hn
    rw [Work.RESOL.truncProj_f_eq B j rfl]
    unfold Zero.colAugFam
    rw [dite_eq_left rfl]
    by_cases hp : x.1.2 = 0
    · -- the summand with resolution degree `0` of the column `j-1`: both sides transport the
      -- resolution degree `0` part of `Rco.obj (B.X (j-1))` into the single complex
      have hq : x.1.1 = j - 1 := by have := x.2.1; omega
      have hy : x = zPhiComm23Idx j :=
        Subtype.ext (Prod.ext hq (hp.trans (sub_self (j - 1)).symm))
      subst hy
      rw [dite_eq_left (sub_self (j - 1)), dite_eq_left rfl]
      conv_lhs => rw [zPhiComm23_XIsoOfEq_hom_eq]
      conv_rhs => rw [zPhiComm23_XIsoOfEq_hom_eq]
      simp only [Category.assoc, eqToHom_trans]
      rfl
    · -- otherwise both sides vanish
      have hq : ¬ x.1.1 = j - 1 := by intro h; have := x.2.1; omega
      rw [dite_eq_right hp, dite_eq_right hq, zero_comp, zero_comp]
  · -- in degrees `≠ j - 1` both sides vanish
    rw [Work.RESOL.truncProj_f_of_ne B j hn, comp_zero]
    have hca : Zero.colAugFam F π hπ (j - 1) B n = 0 := by
      unfold Zero.colAugFam
      rw [dite_eq_right hn]
    rw [hca, comp_zero]

end Work.RESOL
