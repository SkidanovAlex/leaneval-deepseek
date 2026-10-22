/-
AREA RESOL — the degreewise splitting data of the column filtration step

`0 ⟶ totCut (k+1) B ⟶ totCut k B ⟶ colCpx k B ⟶ 0`.

All four statements are computed from the component formulas `cutIncFam_ι`, `cutRetrFam_ι`,
`colProjFam_ι` of `RESOL/ZeroCut.lean`, using `Sigma.hom_ext` to test a morphism out of a
coproduct on the coproduct inclusions.
-/
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
  (hπ : ∀ M, Epi (π.app M)) (k : ℤ) (B : Cpx) (n : ℤ)

/-- The inclusion of the columns `≥ k+1` followed by the retraction which kills the
`k`-th column is the identity of `totCut (k+1) B`. -/
theorem cutIncFam_comp_cutRetrFam :
    CategoryTheory.CategoryStruct.comp (cutIncFam F π hπ k B n) (cutRetrFam F π hπ k B n)
      = CategoryTheory.CategoryStruct.id ((totCut F π hπ (k + 1) B).X n) := by
  apply Sigma.hom_ext
  intro x
  have hx : k < x.1.1 := by have := x.2.2; omega
  simp only [← Category.assoc, cutIncFam_ι, cutRetrFam_ι, cutIdx, cutRetrIdx, dif_pos hx]
  rfl

/-- The section of the `k`-th column followed by the projection onto it is the identity of
`colCpx k B`. -/
theorem colSectFam_comp_colProjFam :
    CategoryTheory.CategoryStruct.comp (colSectFam F π hπ k B n) (colProjFam F π hπ k B n)
      = CategoryTheory.CategoryStruct.id ((colCpx F π hπ k B).X n) := by
  simp only [colSectFam, colProjFam_ι, colSectIdx, dif_pos]
  rfl

/-- The projection onto the columns `> k` followed by their inclusion, plus the projection onto
the `k`-th column followed by its section, is the identity of `totCut k B`. -/
theorem cutRetrFam_comp_cutIncFam_add :
    CategoryTheory.CategoryStruct.comp (cutRetrFam F π hπ k B n) (cutIncFam F π hπ k B n)
      + CategoryTheory.CategoryStruct.comp (colProjFam F π hπ k B n) (colSectFam F π hπ k B n)
      = CategoryTheory.CategoryStruct.id ((totCut F π hπ k B).X n) := by
  apply Sigma.hom_ext
  intro x
  by_cases h : k < x.1.1
  · have hk : ¬ (x.1.1 = k) := by omega
    simp only [Preadditive.comp_add, ← Category.assoc, cutRetrFam_ι, cutIncFam_ι, colProjFam_ι,
      dif_pos h, dif_neg hk, cutIdx, cutRetrIdx, zero_comp, add_zero]
    rfl
  · have hq : x.1.1 = k := by omega
    have hp : x.1.2 = n - k := by have := x.2.1; omega
    have hx : x = colSectIdx k n := by
      apply Subtype.ext
      exact Prod.ext hq hp
    subst hx
    simp only [Preadditive.comp_add, ← Category.assoc, cutRetrFam_ι, colProjFam_ι, colSectFam,
      colSectIdx, cutRetrIdx, dif_neg (by omega : ¬ k < k), dif_pos trivial, zero_comp, zero_add,
      Category.id_comp, Category.comp_id]
    rfl

/-- The inclusion of the columns `≥ k+1` followed by the projection onto the `k`-th column
vanishes. -/
theorem cutIncFam_comp_colProjFam :
    CategoryTheory.CategoryStruct.comp (cutIncFam F π hπ k B n) (colProjFam F π hπ k B n) = 0 := by
  apply Sigma.hom_ext
  intro x
  rw [← Category.assoc, cutIncFam_ι, colProjFam_ι]
  rw [dif_neg]
  · rw [comp_zero]
  · intro h
    have hx := x.2.2
    have hv : (cutIdx x).1.1 = x.1.1 := rfl
    omega

end Zero

theorem zCutSplittingData (F : CategoryTheory.Functor LightCondAb LightCondAb)
    [F.PreservesZeroMorphisms] (π : F ⟶ CategoryTheory.Functor.id LightCondAb)
    (hπ : ∀ M, CategoryTheory.Epi (π.app M)) (k : ℤ) (B : Work.RESOL.Cpx) (n : ℤ) :
    (CategoryTheory.CategoryStruct.comp (Work.RESOL.Zero.cutIncFam F π hπ k B n)
        (Work.RESOL.Zero.cutRetrFam F π hπ k B n)
        = CategoryTheory.CategoryStruct.id ((Work.RESOL.Zero.totCut F π hπ (k + 1) B).X n)) ∧
    (CategoryTheory.CategoryStruct.comp (Work.RESOL.Zero.colSectFam F π hπ k B n)
        (Work.RESOL.Zero.colProjFam F π hπ k B n)
        = CategoryTheory.CategoryStruct.id ((Work.RESOL.Zero.colCpx F π hπ k B).X n)) ∧
    (CategoryTheory.CategoryStruct.comp (Work.RESOL.Zero.cutRetrFam F π hπ k B n)
          (Work.RESOL.Zero.cutIncFam F π hπ k B n)
        + CategoryTheory.CategoryStruct.comp (Work.RESOL.Zero.colProjFam F π hπ k B n)
          (Work.RESOL.Zero.colSectFam F π hπ k B n)
        = CategoryTheory.CategoryStruct.id ((Work.RESOL.Zero.totCut F π hπ k B).X n)) ∧
    (CategoryTheory.CategoryStruct.comp (Work.RESOL.Zero.cutIncFam F π hπ k B n)
        (Work.RESOL.Zero.colProjFam F π hπ k B n) = 0) :=
  ⟨Zero.cutIncFam_comp_cutRetrFam F π hπ k B n,
    Zero.colSectFam_comp_colProjFam F π hπ k B n,
    Zero.cutRetrFam_comp_cutIncFam_add F π hπ k B n,
    Zero.cutIncFam_comp_colProjFam F π hπ k B n⟩

end Work.RESOL
