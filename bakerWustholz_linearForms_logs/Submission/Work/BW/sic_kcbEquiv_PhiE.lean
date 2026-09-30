import Mathlib
import Submission.Work.BW.kcb_lat_defs
import Submission.Work.BW.sieg2KernelDefs
import Submission.Work.BW.sieg2_PhiE_aux
import Submission.Work.BW.PhiE_ofLp_mulVec

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `kcbEquiv` intertwines `PhiE` and `Phi`

`kcbEquiv F N` is the `ℝ`-linear coordinate equivalence between the Euclidean coordinate model
`kcbE F N = EuclideanSpace ℝ (Fin N × index F)` and the product model `Fin N → KE F`, given by
expanding the coordinates in the orthonormal basis `stdOrthonormalBasis F` of the mixed space.

`PhiE a` is the matrix model (`PhiMat a`, the matrix of `Phi a` in that orthonormal basis) of the
mixed-space map `Phi a` given by the rows `a i`.  This file proves that the two are intertwined:
`kcbEquiv F M ∘ PhiE a = Phi a ∘ kcbEquiv F N`.
-/

open NumberField

namespace Work.BW

variable {F : Type*} [Field F] [NumberField F]

/-- Coordinates of `kcbEquiv F N x` in the orthonormal basis of the mixed space. -/
theorem kcbEquiv_apply {N : ℕ} (x : kcbE F N) (i : Fin N) :
    kcbEquiv F N x i =
      ∑ k, x.ofLp (i, k) • NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis F k := by
  rw [kcbEquiv]
  simp only [LinearEquiv.trans_apply, LinearEquiv.piCongrRight_apply,
    WithLp.coe_linearEquiv, WithLp.coe_symm_linearEquiv, LinearIsometryEquiv.coe_toLinearEquiv]
  rw [← OrthonormalBasis.sum_repr_symm]
  simp

/-- `kcbEquiv` is the expansion of the coordinates in the orthonormal basis. -/
theorem kcbEquiv_eq_psiAssemble {N : ℕ} (x : kcbE F N) :
    kcbEquiv F N x = psiAssemble (F := F) N x.ofLp := by
  ext i
  rw [kcbEquiv_apply, psiAssemble_apply]

/-- Coordinate form of `kcbEquiv F M ∘ PhiE a = Phi a ∘ kcbEquiv F N`:  the coordinates of both
sides agree. -/
theorem kcbEquiv_PhiE_coord {M N : ℕ} (a : Fin M → Fin N → F) (z : kcbE F N) (p : Fin M)
    (c : NumberField.mixedEmbedding.index F) :
    (PhiMat a).mulVec z.ofLp (p, c) =
      psiAssembleInv (F := F) M (Phi a (psiAssemble (F := F) N z.ofLp)) (p, c) := by
  rw [psiAssembleInv_apply, OrthonormalBasis.repr_apply_apply, Phi_apply]
  rw [inner_sum]
  simp only [psiAssemble_apply, map_sum, map_smul, inner_sum, inner_smul_right,
    Matrix.mulVec_apply, dotProduct, Matrix.row_apply, ← PhiMat_apply_coe]
  rw [← Fintype.sum_prod_type (fun q : Fin N × NumberField.mixedEmbedding.index F =>
        z.ofLp q * PhiMat a (p, c) q)]
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- The coordinate equivalence `kcbEquiv` intertwines the matrix model `PhiE` of the row map with
the mixed-space model `Phi`. -/
theorem sic_kcbEquiv_PhiE {F : Type*} [Field F] [NumberField F] {M N : ℕ}
    (a : Fin M → Fin N → F) (z : Work.BW.kcbE F N) :
    Work.BW.kcbEquiv F M (Work.BW.PhiE a z) = Work.BW.Phi a (Work.BW.kcbEquiv F N z) := by
  rw [kcbEquiv_eq_psiAssemble, kcbEquiv_eq_psiAssemble, PhiE_ofLp_mulVec]
  rw [← psiAssemble_psiAssembleInv M (Phi a (psiAssemble (F := F) N z.ofLp))]
  congr 1
  funext q
  obtain ⟨p, c⟩ := q
  exact kcbEquiv_PhiE_coord a z p c

end Work.BW
