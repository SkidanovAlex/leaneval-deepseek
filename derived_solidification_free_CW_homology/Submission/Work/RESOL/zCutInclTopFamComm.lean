/-
AREA RESOL — the inclusion of the columns `q ≥ k` of the total resolution complex into all the
columns is a chain map.

The two complexes are `Zero.totCut k B` (columns `q ≥ k`, `Zero.totCpx` with the predicate
`Zero.geP k`) and `Zero.totFull B` (all the columns, predicate `Zero.topP`).  The degreewise
components of the inclusion are `Zero.cutInclTopFam k B n`, which on the summand indexed by
`x : TotIdx (geP k) n` is the canonical inclusion of the coproduct summand in the larger
coproduct (`Zero.cutInclTopFam_ι`).

The proof is the exact analogue of `zCutIncComm.lean` (the inclusion `totCut (k+1) ⟶ totCut k`),
with `topP` in place of `geP (k+1)`:

* `zcit_V` / `zcit_H` compare the vertical and the horizontal parts of the two differentials
  after the inclusion, componentwise (both are the same resolution differential / the same
  differential of `B` with the sign `(-1)^p`, followed by the inclusion of the index);
* `zCutInclTopFamComm` then follows by coproduct extensionality (`Sigma.hom_ext`) and
  `Zero.totDc_apply` (the differential `totDc` is `totVpart + totHpart`).
-/
import Mathlib
import Submission.Work.RESOL.ZeroTruncSES

open CategoryTheory Limits LightProfinite LightCondensed
open _root_.LightCondensed

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Work.RESOL

namespace Zero

variable (F : LightCondAb ⥤ LightCondAb) [F.PreservesZeroMorphisms] (π : F ⟶ 𝟭 LightCondAb)
  (hπ : ∀ M, Epi (π.app M)) (B : Cpx) (k : ℤ)

/-- The vertical part of the differential of `totCut k B` agrees with the vertical part of the
differential of `totFull B` after the inclusion of the columns `≥ k` into all the columns: on a
column `q ≥ k` and resolution degree `p` both are the differential of the resolution
`Rco.obj (B.X q)`, followed by the inclusion of the summand `(q, p+1)`. -/
lemma zcit_V (i : ℤ) (x : TotIdx (geP k) i) :
    totVpart F π hπ (geP k) B i x ≫ cutInclTopFam F π hπ k B (i + 1)
      = totVpart F π hπ topP B i ⟨x.1, ⟨x.2.1, trivial⟩⟩ := by
  rw [totVpart, totVpart, Category.assoc, cutInclTopFam_ι]
  rfl

/-- The horizontal part of the differential of `totCut k B` agrees with the horizontal part of the
differential of `totFull B` after the inclusion of the columns `≥ k` into all the columns: both
are the differential of `B` (with the sign `(-1)^p`), followed by the inclusion of the summand
`(q+1, p)`. -/
lemma zcit_H (i : ℤ) (x : TotIdx (geP k) i) :
    totHpart F π hπ (geP k) (geP_step k) B i x ≫ cutInclTopFam F π hπ k B (i + 1)
      = totHpart F π hπ topP topP_step B i ⟨x.1, ⟨x.2.1, trivial⟩⟩ := by
  rw [totHpart, totHpart, Linear.units_smul_comp, Category.assoc, cutInclTopFam_ι]
  rfl

end Zero

/-- The inclusion `cutInclTopFam` of the columns `≥ k` into all the columns of the total complex
is a chain map (degreewise component identity).

NOTE: proved from scratch (the earlier placeholder twin in `ZeroTruncSES.lean` has been removed).
Useful facts: `Zero.cutInclTopFam_ι`, `Zero.totCut_d_eq`,
`Zero.totFull_d_eq`, `Zero.totDc_apply`, `Zero.totVpart`, `Zero.totHpart` and the template proof
in `zTotMapFam.lean`. -/
theorem zCutInclTopFamComm (F : CategoryTheory.Functor LightCondAb LightCondAb)
    [F.PreservesZeroMorphisms] (π : F ⟶ CategoryTheory.Functor.id LightCondAb)
    (hπ : ∀ M, CategoryTheory.Epi (π.app M)) (k : ℤ) (B : Work.RESOL.Cpx) {i j : ℤ}
    (hij : (ComplexShape.up ℤ).Rel i j) :
    CategoryTheory.CategoryStruct.comp (Work.RESOL.Zero.cutInclTopFam F π hπ k B i)
        ((Work.RESOL.Zero.totFull F π hπ B).d i j)
      = CategoryTheory.CategoryStruct.comp ((Work.RESOL.Zero.totCut F π hπ k B).d i j)
          (Work.RESOL.Zero.cutInclTopFam F π hπ k B j) := by
  have hj : i + 1 = j := (ComplexShape.up_Rel ℤ i j).mp hij
  subst hj
  rw [Work.RESOL.Zero.totFull_d_eq, Work.RESOL.Zero.totCut_d_eq]
  apply Sigma.hom_ext
  intro x
  conv_lhs => rw [← Category.assoc, Work.RESOL.Zero.cutInclTopFam_ι,
    Work.RESOL.Zero.totDc_apply]
  conv_rhs => rw [← Category.assoc, Work.RESOL.Zero.totDc_apply, Preadditive.add_comp]
  rw [Work.RESOL.Zero.zcit_V F π hπ B k i x, Work.RESOL.Zero.zcit_H F π hπ B k i x]

end Work.RESOL
