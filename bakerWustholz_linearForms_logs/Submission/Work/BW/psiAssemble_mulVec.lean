import Mathlib
import Submission.Work.BW.sieg2_PhiE_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Classical

namespace Work.BW

noncomputable section

/-- `PhiMat a` is the matrix of the mixed-space linear map `Phi a` in the orthonormal basis
`mixedEmbedding.euclidean.stdOrthonormalBasis F`: conjugating `Phi a` by the coordinate
isomorphisms `psiAssemble` gives `Matrix.mulVec` by `PhiMat a`.

This is the coordinate form of the definition `PhiMat a (i,c) (j,c') =
⟪e_c, mulK (a i j) e_{c'}⟫`. -/
theorem psiAssembleInv_Phi_eq_mulVec {F : Type*} [Field F] [NumberField F] {M N : ℕ}
    (a : Fin M → Fin N → F) :
    (psiAssembleInv (F := F) M).comp ((Phi a).comp (psiAssemble (F := F) N))
      = (PhiMat a).toLin' := by
  classical
  refine (Pi.basisFun ℝ (Fin N × NumberField.mixedEmbedding.index F)).ext ?_
  intro q
  obtain ⟨j, c'⟩ := q
  simp only [LinearMap.comp_apply, Pi.basisFun_apply]
  rw [psiAssemble_single]
  have h1 : (Phi a) (Pi.single j
        ((NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F) c'))
      = fun i : Fin M =>
          mulK (a i j) ((NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F) c') := by
    funext i
    exact Phi_single a j _ i
  rw [h1, Matrix.toLin'_apply, Matrix.mulVec_single_one]
  funext p
  obtain ⟨i, c⟩ := p
  rw [Matrix.col_apply, psiAssembleInv_apply, OrthonormalBasis.repr_apply_apply,
    PhiMat_apply_coe]

theorem psiAssemble_mulVec {F : Type*} [Field F] [NumberField F] {M N : ℕ}
    (a : Fin M → Fin N → F) (x : Fin N × NumberField.mixedEmbedding.index F → ℝ) :
    psiAssemble (F := F) M ((PhiMat a).mulVec x) = Phi a (psiAssemble (F := F) N x) := by
  have h := LinearMap.congr_fun (psiAssembleInv_Phi_eq_mulVec (F := F) a) x
  rw [Matrix.toLin'_apply] at h
  rw [← h]
  exact psiAssemble_psiAssembleInv M (Phi a (psiAssemble (F := F) N x))

end

end Work.BW
