import Mathlib
import Submission.Work.DSF1.Cech.CoaugSheaf
import Submission.Work.DSF1.Sheaf.cechSheafPresheaf_homology_vanishing
import Submission.Work.DSEQ0.AugMain

/-!
# The coaugmentation of the sheaf-level Čech complex is a quasi-isomorphism

For a scheme `X`, a family of opens `U : ι → X.Opens` covering `X` and

`P := Work.DSF1.Sheaf.cechSheafPresheaf X : (X.Opens)ᵒᵖ ⥤ X.Modules`,
`K := (cechComplexFunctor U).obj P : CochainComplex X.Modules ℕ`,

the coaugmentation `Work.DSF1.Cech.cechSheafCoaug U : (single₀ X.Modules).obj (P(⊤)) ⟶ K`
is a quasi-isomorphism: the sheaf-level Čech complex of the structure sheaf along a covering
family is a resolution of the structure sheaf.

The mathematical content -- the vanishing of the positive-degree homology together with the
exactness in degree `0` (the sheaf condition for the cover) -- is developed in the area
`Work.DSEQ0` (`Submission/Work/DSEQ0/AugMain.lean`), under the name
`Work.DSEQ0.C.quasiIso_augN`, for the private copies `Work.DSEQ0.C.aug0`, `C.cechSh`,
`C.augN` of the very same objects.  Those copies are *definitionally* equal to `cechSheafCoaug`
and to the complex `(cechComplexFunctor U).obj (cechSheafPresheaf X)` (see the `example`s in
`Submission/Work/DSEQ0/AugBasic.lean` and the lemma `augN_eq_cechSheafCoaug` below), so the
result transports by `rfl`, with no reindexing and no additional mathematics.
-/

namespace Work.DSF1.Cech

open CategoryTheory AlgebraicGeometry Opposite Limits

universe u

/-- The `ℕ`-indexed coaugmentation `cechSheafCoaug` is the augmentation `Work.DSEQ0.C.augN`
of the `DSEQ0` development: the two complexes and the two degree-`0` maps are the same up to
definitional equality (the private functor `Work.DSEQ0.C.cechShPresheaf` has the same object and
morphism data as `Work.DSF1.Sheaf.cechSheafPresheaf`, and `isTerminalTop.from` and
`homOfLE le_top` are the two names of the unique morphism into `⊤` in `X.Opens`). -/
lemma augN_eq_cechSheafCoaug {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens)
    (h : Work.DSEQ0.C.aug0 X U ≫ (Work.DSEQ0.C.cechSh X U).d 0 1 = 0) :
    Work.DSEQ0.C.augN X U h = Work.DSF1.Cech.cechSheafCoaug U := rfl

theorem cechSheafCoaug_quasiIso {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (hcov : sSup (Set.range U) = ⊤) :
    QuasiIso (Work.DSF1.Cech.cechSheafCoaug U) := by
  -- `sSup (Set.range U) = iSup U`
  have hcov' : iSup U = ⊤ := by rw [← sSup_range]; exact hcov
  -- the degree-`0` component of the coaugmentation is killed by the first Čech differential
  have h : Work.DSEQ0.C.aug0 X U ≫ (Work.DSEQ0.C.cechSh X U).d 0 1 = 0 :=
    Work.DSEQ0.C.aug0_comp_d X U
  -- the augmentation of the sheaf-level Čech complex is a quasi-isomorphism (`DSEQ0`)
  have hqi : QuasiIso (Work.DSEQ0.C.augN X U h) :=
    Work.DSEQ0.C.quasiIso_augN X U hcov' h (Work.DSEQ0.C.localCoaug X U)
  rwa [augN_eq_cechSheafCoaug U h] at hqi

end Work.DSF1.Cech
