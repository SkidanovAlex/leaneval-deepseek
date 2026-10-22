import Mathlib
import Submission.Work.RESOL.ZeroCut

open CategoryTheory Limits LightProfinite LightCondensed
open _root_.LightCondensed

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.RESOL

namespace Zero

variable (F : LightCondAb ⥤ LightCondAb) [F.PreservesZeroMorphisms] (π : F ⟶ 𝟭 LightCondAb)
  (hπ : ∀ M, Epi (π.app M)) (B : Cpx) (k : ℤ)

/-- The vertical part of the differential of `totCut k B` agrees with the vertical part of the
differential of `totCut (k+1) B` after the inclusion of the columns `≥ k+1` into the columns
`≥ k`: on the column `q ≥ k+1` and resolution degree `p` both are the differential of the
resolution `Rco.obj (B.X q)`. -/
lemma zcut_V (i : ℤ) (x : TotIdx (geP (k + 1)) i) :
    totVpart F π hπ (geP (k + 1)) B i x ≫ cutIncFam F π hπ k B (i + 1)
      = totVpart F π hπ (geP k) B i (cutIdx x) := by
  rw [totVpart, totVpart, Category.assoc, cutIncFam_ι]
  rfl

/-- The horizontal part of the differential of `totCut k B` agrees with the horizontal part of
the differential of `totCut (k+1) B` after the inclusion of the columns `≥ k+1` into the columns
`≥ k`: on the column `q ≥ k+1` and resolution degree `p` both are the differential of `B`
followed by the re-indexing, with the sign `(-1)^p`. -/
lemma zcut_H (i : ℤ) (x : TotIdx (geP (k + 1)) i) :
    totHpart F π hπ (geP (k + 1)) (geP_step (k + 1)) B i x ≫ cutIncFam F π hπ k B (i + 1)
      = totHpart F π hπ (geP k) (geP_step k) B i (cutIdx x) := by
  rw [totHpart, totHpart, Linear.units_smul_comp, Category.assoc, cutIncFam_ι]
  rfl

/-- The inclusion `totCut (k+1) B ⟶ totCut k B` of the columns `≥ k+1` into the columns `≥ k`
is a chain map for the canonical differentials `totDc`. -/
lemma zcut_Dc (i : ℤ) :
    cutIncFam F π hπ k B i ≫ totDc F π hπ (geP k) (geP_step k) B i
      = totDc F π hπ (geP (k + 1)) (geP_step (k + 1)) B i
          ≫ cutIncFam F π hπ k B (i + 1) := by
  apply Sigma.hom_ext
  intro x
  conv_lhs => rw [← Category.assoc, cutIncFam_ι, totDc_apply]
  conv_rhs => rw [← Category.assoc, totDc_apply, Preadditive.add_comp]
  rw [zcut_V, zcut_H]

end Zero

theorem zCutIncComm (F : CategoryTheory.Functor LightCondAb LightCondAb)
    [F.PreservesZeroMorphisms] (π : F ⟶ CategoryTheory.Functor.id LightCondAb)
    (hπ : ∀ M, CategoryTheory.Epi (π.app M)) (k : ℤ) (B : Work.RESOL.Cpx) :
    ∀ (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j),
      CategoryTheory.CategoryStruct.comp (Work.RESOL.Zero.cutIncFam F π hπ k B i)
          ((Work.RESOL.Zero.totCut F π hπ k B).d i j)
        = CategoryTheory.CategoryStruct.comp ((Work.RESOL.Zero.totCut F π hπ (k + 1) B).d i j)
            (Work.RESOL.Zero.cutIncFam F π hπ k B j) := by
  intro i j hij
  have hj : i + 1 = j := (ComplexShape.up_Rel ℤ i j).mp hij
  subst hj
  rw [Zero.totCut_d_eq, Zero.totCut_d_eq]
  exact Zero.zcut_Dc F π hπ B k i

end Work.RESOL
