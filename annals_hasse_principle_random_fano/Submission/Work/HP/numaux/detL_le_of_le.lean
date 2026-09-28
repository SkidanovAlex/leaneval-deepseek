import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.numaux.Defs
import Submission.Work.HP.Lat.detL_basis_gram
import Submission.Work.HP.HPgram
import Submission.Work.HP.Lat.detL_ge_one

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

noncomputable section

open Matrix

namespace Work.HP.numaux

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Expansion of the basis `bM` of a sublattice `M ≤ L` in the basis `bL` of `L`. -/
lemma toMatrix_basis_expand {M L : Submodule ℤ (ι → ℤ)} (hML : M ≤ L) {r : ℕ}
    (bL : Module.Basis (Fin r) ℤ L) (bM : Module.Basis (Fin r) ℤ M) (j : Fin r) :
    (bM j : ι → ℤ)
      = ∑ i, (LinearMap.toMatrix bM bL (Submodule.inclusion hML)) i j • (bL i : ι → ℤ) := by
  have hsum : Submodule.inclusion hML (bM j)
      = ∑ i, (LinearMap.toMatrix bM bL (Submodule.inclusion hML)) i j • bL i := by
    rw [← bL.sum_repr (Submodule.inclusion hML (bM j))]
    exact Finset.sum_congr rfl (fun i _ => by rw [LinearMap.toMatrix_apply])
  have hcoe := congrArg (fun y : L => L.subtype y) hsum
  simp only [map_sum, map_smul] at hcoe
  simpa using hcoe

/-- The coordinate matrix of `bM` is `TRᵀ * coordMat` where `TR` is the transition matrix. -/
lemma coordMat_eq {M L : Submodule ℤ (ι → ℤ)} (hML : M ≤ L) {r : ℕ}
    (bL : Module.Basis (Fin r) ℤ L) (bM : Module.Basis (Fin r) ℤ M) :
    Work.HP.coordMat r M bM
      = ((LinearMap.toMatrix bM bL (Submodule.inclusion hML)).map (fun z : ℤ => (z : ℝ)))ᵀ
          * Work.HP.coordMat r L bL := by
  ext j x
  simp only [Work.HP.coordMat, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply]
  rw [toMatrix_basis_expand hML bL bM j]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul]

/-- For a sublattice `M ≤ L`, the Gram determinant of a basis of `L` is at most that of a basis
of `M`. -/
theorem gramMat_det_le {M L : Submodule ℤ (ι → ℤ)} (h : M ≤ L) {r : ℕ}
    (bL : Module.Basis (Fin r) ℤ L) (bM : Module.Basis (Fin r) ℤ M) :
    (Work.HP.gramMat r L bL).det ≤ (Work.HP.gramMat r M bM).det := by
  classical
  set TR : Matrix (Fin r) (Fin r) ℝ :=
    (LinearMap.toMatrix bM bL (Submodule.inclusion h)).map (fun z : ℤ => (z : ℝ)) with hTR
  have hcoord := coordMat_eq h bL bM
  have hgram : Work.HP.gramMat r M bM = TRᵀ * Work.HP.gramMat r L bL * TR := by
    have h1 : Work.HP.gramMat r M bM
        = (TRᵀ * Work.HP.coordMat r L bL) * (TRᵀ * Work.HP.coordMat r L bL)ᵀ := by
      rw [Work.HP.gramMat_eq_mul_transpose, hcoord]
    rw [h1, Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [Work.HP.gramMat_eq_mul_transpose]
    simp only [Matrix.mul_assoc]
  have hGMdet : (Work.HP.gramMat r M bM).det
      = (TR.det)^2 * (Work.HP.gramMat r L bL).det := by
    rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    ring
  have hposL : 0 < (Work.HP.gramMat r L bL).det := Work.HP.Lat.gramMat_det_pos r L bL
  have hposM : 0 < (Work.HP.gramMat r M bM).det := Work.HP.Lat.gramMat_det_pos r M bM
  set c : ℤ := (LinearMap.toMatrix bM bL (Submodule.inclusion h)).det with hc
  have hTRdet : TR.det = ((c : ℤ) : ℝ) := by
    rw [hTR, hc]
    exact (Int.cast_det _).symm
  have hc2pos : 0 < ((c : ℤ) : ℝ)^2 := by
    have h : 0 < (TR.det)^2 * (Work.HP.gramMat r L bL).det := by
      rw [← hGMdet]; exact hposM
    have h2 : 0 < (TR.det)^2 := pos_of_mul_pos_left h (le_of_lt hposL)
    rwa [hTRdet] at h2
  have hc_ne : c ≠ 0 := by
    intro h0
    rw [h0] at hc2pos
    norm_num at hc2pos
  have hc2ge : (1 : ℝ) ≤ ((c : ℤ) : ℝ)^2 := by
    have h1 : (1 : ℤ) ≤ c^2 := by
      have hp : 0 < c^2 := sq_pos_of_ne_zero hc_ne
      omega
    calc (1 : ℝ) ≤ ((c^2 : ℤ) : ℝ) := by exact_mod_cast h1
      _ = ((c : ℤ) : ℝ)^2 := by push_cast; ring
  rw [hGMdet, hTRdet]
  nlinarith [hposL, hc2ge]

theorem detL_le_of_le {ι : Type} [Fintype ι] [DecidableEq ι] {M L : Submodule ℤ (ι → ℤ)}
    (h : M ≤ L) (hr : rk M = rk L) : detL L ≤ detL M := by
  classical
  obtain ⟨nL, bL⟩ := Submodule.basisOfPid (Pi.basisFun ℤ ι) L
  obtain ⟨nM, bM0⟩ := Submodule.basisOfPid (Pi.basisFun ℤ ι) M
  have hnL : rk L = nL := by
    have := Module.finrank_eq_card_basis bL
    simpa [rk] using this
  have hnM : rk M = nM := by
    have := Module.finrank_eq_card_basis bM0
    simpa [rk] using this
  have hn : nL = nM := by rw [← hnL, ← hr, hnM]
  let bM : Module.Basis (Fin nL) ℤ M := bM0.reindex (finCongr hn).symm
  have hle : (Work.HP.gramMat nL L bL).det ≤ (Work.HP.gramMat nL M bM).det :=
    gramMat_det_le h bL bM
  have hL : detL L = Real.sqrt (Work.HP.gramMat nL L bL).det :=
    Work.HP.Lat.detL_basis_gram L bL
  have hM : detL M = Real.sqrt (Work.HP.gramMat nL M bM).det :=
    Work.HP.Lat.detL_basis_gram M bM
  rw [hL, hM]
  exact Real.sqrt_le_sqrt hle

end Work.HP.numaux
