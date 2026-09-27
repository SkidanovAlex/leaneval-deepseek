import Mathlib
import Submission.Work.KT.Idx.PenDefs
import Submission.Work.Idx.WPenAppendDefs
import Submission.Work.Idx.matPenProj_eval
import Submission.Work.Idx.wPen_append_penProj_split
import Submission.Work.Idx.penProj_idem
import Submission.Work.Idx.wPen_append_reindex

/-!
# `Work.Idx.wPenAppendAnalytic` — reindexing and block-diagonal additivity of `penProjMat`

Two analytical facts about the pencil projection `penProjMat X A B = (2πi)⁻¹ ∮ (zA+B)⁻¹ A dz`
on matrices over `C(X, ℂ)` with the `L∞` operator norm:

* `penProjMat_reindex_append` — `penProjMat` commutes with `Matrix.reindex e e`;
* `penProjMat_fromBlocks_append` — the projection of a block-diagonal pencil is the block
  diagonal of the projections.

Both are proved by exhibiting the relevant inclusion of matrices as a *continuous* linear map
(bound `1` for the `L∞` norm) and using `circleIntegral_map_clm`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.Idx

open Matrix MeasureTheory intervalIntegral
open scoped Topology Interval
open Work.KT.Idx

noncomputable section

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-! ## Transfer lemmas for `Matrix.reindex` -/

lemma reindex_add_app {A : Type*} [Add A] {ι ι' : Type*} (e : ι ≃ ι') (M N : Matrix ι ι A) :
    Matrix.reindex e e (M + N) = Matrix.reindex e e M + Matrix.reindex e e N := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.submatrix_apply]

lemma reindex_smul_app {A : Type*} [SMul ℂ A] {ι ι' : Type*} (e : ι ≃ ι') (c : ℂ)
    (M : Matrix ι ι A) :
    Matrix.reindex e e (c • M) = c • Matrix.reindex e e M := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.submatrix_apply]

lemma ringInverse_reindex_app {R : Type*} [Ring R] {ι ι' : Type*} [Fintype ι] [Fintype ι']
    [DecidableEq ι] [DecidableEq ι'] (e : ι ≃ ι') {M : Matrix ι ι R} (hM : IsUnit M) :
    Ring.inverse (Matrix.reindex e e M) = Matrix.reindex e e (Ring.inverse M) := by
  have h : Matrix.reindex e e (Ring.inverse M) = Ring.inverse (Matrix.reindex e e M) := by
    have h1 : (Matrix.reindexRingEquiv R e) (Ring.inverse M)
        = Ring.inverse ((Matrix.reindexRingEquiv R e) M) :=
      ringHom_map_ringInverse (Matrix.reindexRingEquiv R e).toRingHom hM
    rwa [Matrix.coe_reindexRingEquiv] at h1
  exact h.symm

/-! ## `Ring.inverse` of a block-diagonal matrix, and the block-diagonal unit -/

lemma fromBlocks_diag_inv_mul_app {R : Type*} [Ring R] {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (M : Matrix ι ι R) (N : Matrix κ κ R) :
    Matrix.fromBlocks M 0 0 N * Matrix.fromBlocks (Ring.inverse M) 0 0 (Ring.inverse N)
      = Matrix.fromBlocks (M * Ring.inverse M) 0 0 (N * Ring.inverse N) := by
  rw [Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp

lemma fromBlocks_inv_diag_mul_app {R : Type*} [Ring R] {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (M : Matrix ι ι R) (N : Matrix κ κ R) :
    Matrix.fromBlocks (Ring.inverse M) 0 0 (Ring.inverse N) * Matrix.fromBlocks M 0 0 N
      = Matrix.fromBlocks (Ring.inverse M * M) 0 0 (Ring.inverse N * N) := by
  rw [Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp

lemma ringInverse_fromBlocks_app {R : Type*} [Ring R] {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (M : Matrix ι ι R) (N : Matrix κ κ R)
    (hM : IsUnit M) (hN : IsUnit N) :
    Ring.inverse (Matrix.fromBlocks M 0 0 N)
      = Matrix.fromBlocks (Ring.inverse M) 0 0 (Ring.inverse N) := by
  have hprod := fromBlocks_diag_inv_mul_app M N
  rw [Ring.mul_inverse_cancel M hM, Ring.mul_inverse_cancel N hN] at hprod
  have hprod' := fromBlocks_inv_diag_mul_app M N
  rw [Ring.inverse_mul_cancel M hM, Ring.inverse_mul_cancel N hN] at hprod'
  rw [Matrix.fromBlocks_one] at hprod hprod'
  let u : (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ :=
    { val := Matrix.fromBlocks M 0 0 N
      inv := Matrix.fromBlocks (Ring.inverse M) 0 0 (Ring.inverse N)
      val_inv := hprod
      inv_val := hprod' }
  calc Ring.inverse (Matrix.fromBlocks M 0 0 N)
      = Ring.inverse (u : Matrix (ι ⊕ κ) (ι ⊕ κ) R) := rfl
    _ = (↑u⁻¹ : Matrix (ι ⊕ κ) (ι ⊕ κ) R) := Ring.inverse_unit u
    _ = Matrix.fromBlocks (Ring.inverse M) 0 0 (Ring.inverse N) := rfl

lemma isUnit_fromBlocks_app {R : Type*} [Ring R] {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (M : Matrix ι ι R) (N : Matrix κ κ R)
    (hM : IsUnit M) (hN : IsUnit N) : IsUnit (Matrix.fromBlocks M 0 0 N) := by
  have hprod := fromBlocks_diag_inv_mul_app M N
  rw [Ring.mul_inverse_cancel M hM, Ring.mul_inverse_cancel N hN] at hprod
  have hprod' := fromBlocks_inv_diag_mul_app M N
  rw [Ring.inverse_mul_cancel M hM, Ring.inverse_mul_cancel N hN] at hprod'
  rw [Matrix.fromBlocks_one] at hprod hprod'
  exact ⟨⟨_, _, hprod, hprod'⟩, rfl⟩

/-! ## Reindexing commutes with the pencil projection -/

theorem penProjMat_reindex_append {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι']
    [DecidableEq ι'] (e : ι ≃ ι') (A B : Matrix ι ι C(X, ℂ))
    (h : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • A + B)) :
    penProjMat X (Matrix.reindex e e A) (Matrix.reindex e e B)
      = Matrix.reindex e e (penProjMat X A B) := by
  letI : NormedRing (Matrix ι ι C(X, ℂ)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix ι ι C(X, ℂ)) := Matrix.linftyOpNormedAlgebra
  letI : NormedRing (Matrix ι' ι' C(X, ℂ)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix ι' ι' C(X, ℂ)) := Matrix.linftyOpNormedAlgebra
  have hcomp₁ : CompleteSpace (Matrix ι ι C(X, ℂ)) := Matrix.instCompleteSpace _ _ _
  have hcomp₂ : CompleteSpace (Matrix ι' ι' C(X, ℂ)) := Matrix.instCompleteSpace _ _ _
  have hb : ∀ M : Matrix ι ι C(X, ℂ), ‖Matrix.reindex e e M‖ ≤ 1 * ‖M‖ := by
    intro M
    have hsum : ∀ i : ι', (∑ j : ι', ‖Matrix.reindex e e M i j‖₊)
        = ∑ j : ι, ‖M (e.symm i) j‖₊ := by
      intro i
      refine (Finset.sum_congr rfl (fun j _ => ?_)).trans (Equiv.sum_comp e.symm _)
      simp [Matrix.reindex_apply, Matrix.submatrix_apply]
    have hnn : ‖Matrix.reindex e e M‖₊ ≤ ‖M‖₊ := by
      rw [Matrix.linfty_opNNNorm_def, Matrix.linfty_opNNNorm_def]
      refine Finset.sup_le (fun i _ => ?_)
      rw [hsum i]
      exact Finset.le_sup (f := fun i : ι => ∑ j : ι, ‖M i j‖₊) (Finset.mem_univ (e.symm i))
    have h' : ((‖Matrix.reindex e e M‖₊ : NNReal) : ℝ) ≤ ((‖M‖₊ : NNReal) : ℝ) :=
      NNReal.coe_le_coe.mpr hnn
    simpa using h'
  let L : Matrix ι ι C(X, ℂ) →L[ℂ] Matrix ι' ι' C(X, ℂ) :=
    LinearMap.mkContinuous
      { toFun := fun M => Matrix.reindex e e M
        map_add' := fun M N => reindex_add_app e M N
        map_smul' := fun c M => reindex_smul_app e c M }
      1 hb
  have hL : ∀ M : Matrix ι ι C(X, ℂ), L M = Matrix.reindex e e M := fun M => rfl
  have hcont : ContinuousOn (fun z : ℂ => pResA A B z) (Metric.sphere (0 : ℂ) 1) :=
    @continuousOn_pResA_one (Matrix ι ι C(X, ℂ)) Matrix.linftyOpNormedRing
      Matrix.linftyOpNormedAlgebra hcomp₁ A B h
  have hf : CircleIntegrable (fun z : ℂ => pResA A B z) 0 1 :=
    hcont.circleIntegrable (by norm_num)
  have hfL : CircleIntegrable (fun z : ℂ => L (pResA A B z)) 0 1 :=
    (L.continuous.comp_continuousOn hcont).circleIntegrable (by norm_num)
  have hmap : L (∮ z in C(0, 1), pResA A B z) = ∮ z in C(0, 1), L (pResA A B z) :=
    @circleIntegral_map_clm (Matrix ι ι C(X, ℂ)) _ _ (Matrix ι' ι' C(X, ℂ)) _ _
      hcomp₁ hcomp₂ L (fun z : ℂ => pResA A B z) 0 1 hf
  have hpoint : ∀ z : ℂ, ‖z‖ = 1 →
      L (pResA A B z) = pResA (Matrix.reindex e e A) (Matrix.reindex e e B) z := by
    intro z hz
    have hz' : z • Matrix.reindex e e A + Matrix.reindex e e B
        = Matrix.reindex e e (z • A + B) := by
      rw [reindex_add_app, reindex_smul_app]
    rw [hL]
    simp only [Work.KT.Idx.pResA, Work.KT.Idx.pRes]
    rw [hz', ringInverse_reindex_app e (h z hz), reindexMul']
  calc penProjMat X (Matrix.reindex e e A) (Matrix.reindex e e B)
      = (2 * Real.pi * Complex.I)⁻¹ •
          (∮ z in C(0, 1), pResA (Matrix.reindex e e A) (Matrix.reindex e e B) z) := rfl
    _ = (2 * Real.pi * Complex.I)⁻¹ • (∮ z in C(0, 1), L (pResA A B z)) := by
        congr 1
        exact circleIntegral.integral_congr (by norm_num) (fun z hz => (hpoint z (by
          simpa [Metric.mem_sphere, dist_eq_norm, sub_zero] using hz)).symm)
    _ = (2 * Real.pi * Complex.I)⁻¹ • (L (∮ z in C(0, 1), pResA A B z)) := by
        congr 1
        exact hmap.symm
    _ = L ((2 * Real.pi * Complex.I)⁻¹ • (∮ z in C(0, 1), pResA A B z)) := by
        rw [map_smul]
    _ = Matrix.reindex e e (penProjMat X A B) := by rw [hL]; rfl

/-! ## The projection of a block-diagonal pencil -/

theorem penProjMat_fromBlocks_append {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (A₁ B₁ : Matrix ι ι C(X, ℂ)) (A₂ B₂ : Matrix κ κ C(X, ℂ))
    (h₁ : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • A₁ + B₁))
    (h₂ : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • A₂ + B₂)) :
    penProjMat X (Matrix.fromBlocks A₁ 0 0 A₂) (Matrix.fromBlocks B₁ 0 0 B₂)
      = Matrix.fromBlocks (penProjMat X A₁ B₁) 0 0 (penProjMat X A₂ B₂) := by
  letI : NormedRing (Matrix ι ι C(X, ℂ)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix ι ι C(X, ℂ)) := Matrix.linftyOpNormedAlgebra
  letI : NormedRing (Matrix κ κ C(X, ℂ)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix κ κ C(X, ℂ)) := Matrix.linftyOpNormedAlgebra
  letI : NormedRing (Matrix (ι ⊕ κ) (ι ⊕ κ) C(X, ℂ)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (ι ⊕ κ) (ι ⊕ κ) C(X, ℂ)) := Matrix.linftyOpNormedAlgebra
  have hcomp₁ : CompleteSpace (Matrix ι ι C(X, ℂ)) := Matrix.instCompleteSpace _ _ _
  have hcomp₂ : CompleteSpace (Matrix κ κ C(X, ℂ)) := Matrix.instCompleteSpace _ _ _
  have hcomp₃ : CompleteSpace (Matrix (ι ⊕ κ) (ι ⊕ κ) C(X, ℂ)) :=
    Matrix.instCompleteSpace _ _ _
  have hb₁ : ∀ M : Matrix ι ι C(X, ℂ),
      ‖Matrix.fromBlocks M 0 0 (0 : Matrix κ κ C(X, ℂ))‖ ≤ 1 * ‖M‖ := by
    intro M
    have hnn : ‖Matrix.fromBlocks M 0 0 (0 : Matrix κ κ C(X, ℂ))‖₊ ≤ ‖M‖₊ := by
      rw [Matrix.linfty_opNNNorm_def, Matrix.linfty_opNNNorm_def]
      refine Finset.sup_le (fun p _ => ?_)
      rcases p with i | k
      · rw [Fintype.sum_sum_type]
        simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply,
          nnnorm_zero, Finset.sum_const_zero, add_zero]
        exact Finset.le_sup (f := fun i : ι => ∑ j : ι, ‖M i j‖₊) (Finset.mem_univ i)
      · rw [Fintype.sum_sum_type]
        simp
    have h' : ((‖Matrix.fromBlocks M 0 0 (0 : Matrix κ κ C(X, ℂ))‖₊ : NNReal) : ℝ) ≤
        ((‖M‖₊ : NNReal) : ℝ) := NNReal.coe_le_coe.mpr hnn
    simpa using h'
  have hb₂ : ∀ N : Matrix κ κ C(X, ℂ),
      ‖Matrix.fromBlocks (0 : Matrix ι ι C(X, ℂ)) 0 0 N‖ ≤ 1 * ‖N‖ := by
    intro N
    have hnn : ‖Matrix.fromBlocks (0 : Matrix ι ι C(X, ℂ)) 0 0 N‖₊ ≤ ‖N‖₊ := by
      rw [Matrix.linfty_opNNNorm_def, Matrix.linfty_opNNNorm_def]
      refine Finset.sup_le (fun p _ => ?_)
      rcases p with i | k
      · rw [Fintype.sum_sum_type]
        simp
      · rw [Fintype.sum_sum_type]
        simp only [Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
          nnnorm_zero, Finset.sum_const_zero, zero_add]
        exact Finset.le_sup (f := fun k : κ => ∑ l : κ, ‖N k l‖₊) (Finset.mem_univ k)
    have h' : ((‖Matrix.fromBlocks (0 : Matrix ι ι C(X, ℂ)) 0 0 N‖₊ : NNReal) : ℝ) ≤
        ((‖N‖₊ : NNReal) : ℝ) := NNReal.coe_le_coe.mpr hnn
    simpa using h'
  let L₁ : Matrix ι ι C(X, ℂ) →L[ℂ] Matrix (ι ⊕ κ) (ι ⊕ κ) C(X, ℂ) :=
    LinearMap.mkContinuous
      { toFun := fun M => Matrix.fromBlocks M 0 0 (0 : Matrix κ κ C(X, ℂ))
        map_add' := by intro M N; rw [Matrix.fromBlocks_add]; simp
        map_smul' := by intro c M; rw [Matrix.fromBlocks_smul]; simp }
      1 hb₁
  let L₂ : Matrix κ κ C(X, ℂ) →L[ℂ] Matrix (ι ⊕ κ) (ι ⊕ κ) C(X, ℂ) :=
    LinearMap.mkContinuous
      { toFun := fun N => Matrix.fromBlocks (0 : Matrix ι ι C(X, ℂ)) 0 0 N
        map_add' := by intro M N; rw [Matrix.fromBlocks_add]; simp
        map_smul' := by intro c M; rw [Matrix.fromBlocks_smul]; simp }
      1 hb₂
  have hL₁ : ∀ M : Matrix ι ι C(X, ℂ), L₁ M = Matrix.fromBlocks M 0 0 0 := fun M => rfl
  have hL₂ : ∀ N : Matrix κ κ C(X, ℂ), L₂ N = Matrix.fromBlocks 0 0 0 N := fun N => rfl
  have hbigU : ∀ z : ℂ, ‖z‖ = 1 →
      IsUnit (z • Matrix.fromBlocks A₁ 0 0 A₂ + Matrix.fromBlocks B₁ 0 0 B₂) := by
    intro z hz
    have hblk : z • Matrix.fromBlocks A₁ 0 0 A₂ + Matrix.fromBlocks B₁ 0 0 B₂
        = Matrix.fromBlocks (z • A₁ + B₁) 0 0 (z • A₂ + B₂) := by
      rw [Matrix.fromBlocks_smul, Matrix.fromBlocks_add]
      simp
    rw [hblk]
    exact isUnit_fromBlocks_app _ _ (h₁ z hz) (h₂ z hz)
  have hcont₁ : ContinuousOn (fun z : ℂ => pResA A₁ B₁ z) (Metric.sphere (0 : ℂ) 1) :=
    @continuousOn_pResA_one (Matrix ι ι C(X, ℂ)) Matrix.linftyOpNormedRing
      Matrix.linftyOpNormedAlgebra hcomp₁ A₁ B₁ h₁
  have hcont₂ : ContinuousOn (fun z : ℂ => pResA A₂ B₂ z) (Metric.sphere (0 : ℂ) 1) :=
    @continuousOn_pResA_one (Matrix κ κ C(X, ℂ)) Matrix.linftyOpNormedRing
      Matrix.linftyOpNormedAlgebra hcomp₂ A₂ B₂ h₂
  have hf₁ : CircleIntegrable (fun z : ℂ => pResA A₁ B₁ z) 0 1 :=
    hcont₁.circleIntegrable (by norm_num)
  have hf₂ : CircleIntegrable (fun z : ℂ => pResA A₂ B₂ z) 0 1 :=
    hcont₂.circleIntegrable (by norm_num)
  have hfL₁ : CircleIntegrable (fun z : ℂ => L₁ (pResA A₁ B₁ z)) 0 1 :=
    (L₁.continuous.comp_continuousOn hcont₁).circleIntegrable (by norm_num)
  have hfL₂ : CircleIntegrable (fun z : ℂ => L₂ (pResA A₂ B₂ z)) 0 1 :=
    (L₂.continuous.comp_continuousOn hcont₂).circleIntegrable (by norm_num)
  have hmap₁ : L₁ (∮ z in C(0, 1), pResA A₁ B₁ z) = ∮ z in C(0, 1), L₁ (pResA A₁ B₁ z) :=
    @circleIntegral_map_clm (Matrix ι ι C(X, ℂ)) _ _ (Matrix (ι ⊕ κ) (ι ⊕ κ) C(X, ℂ)) _ _
      hcomp₁ hcomp₃ L₁ (fun z : ℂ => pResA A₁ B₁ z) 0 1 hf₁
  have hmap₂ : L₂ (∮ z in C(0, 1), pResA A₂ B₂ z) = ∮ z in C(0, 1), L₂ (pResA A₂ B₂ z) :=
    @circleIntegral_map_clm (Matrix κ κ C(X, ℂ)) _ _ (Matrix (ι ⊕ κ) (ι ⊕ κ) C(X, ℂ)) _ _
      hcomp₂ hcomp₃ L₂ (fun z : ℂ => pResA A₂ B₂ z) 0 1 hf₂
  have hpoint : ∀ z : ℂ, ‖z‖ = 1 →
      pResA (Matrix.fromBlocks A₁ 0 0 A₂) (Matrix.fromBlocks B₁ 0 0 B₂) z
        = L₁ (pResA A₁ B₁ z) + L₂ (pResA A₂ B₂ z) := by
    intro z hz
    have hblk : z • Matrix.fromBlocks A₁ 0 0 A₂ + Matrix.fromBlocks B₁ 0 0 B₂
        = Matrix.fromBlocks (z • A₁ + B₁) 0 0 (z • A₂ + B₂) := by
      rw [Matrix.fromBlocks_smul, Matrix.fromBlocks_add]
      simp
    rw [hL₁, hL₂]
    simp only [Work.KT.Idx.pResA, Work.KT.Idx.pRes]
    rw [hblk, ringInverse_fromBlocks_app _ _ (h₁ z hz) (h₂ z hz), Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_add]
    simp [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  calc penProjMat X (Matrix.fromBlocks A₁ 0 0 A₂) (Matrix.fromBlocks B₁ 0 0 B₂)
      = (2 * Real.pi * Complex.I)⁻¹ •
          (∮ z in C(0, 1),
            pResA (Matrix.fromBlocks A₁ 0 0 A₂) (Matrix.fromBlocks B₁ 0 0 B₂) z) := rfl
    _ = (2 * Real.pi * Complex.I)⁻¹ •
          (∮ z in C(0, 1), (L₁ (pResA A₁ B₁ z) + L₂ (pResA A₂ B₂ z))) := by
        congr 1
        exact circleIntegral.integral_congr (by norm_num) (fun z hz => hpoint z (by
          simpa [Metric.mem_sphere, dist_eq_norm, sub_zero] using hz))
    _ = (2 * Real.pi * Complex.I)⁻¹ •
          ((∮ z in C(0, 1), L₁ (pResA A₁ B₁ z))
            + (∮ z in C(0, 1), L₂ (pResA A₂ B₂ z))) := by
        rw [circleIntegral.integral_add hfL₁ hfL₂]
    _ = (2 * Real.pi * Complex.I)⁻¹ •
          (L₁ (∮ z in C(0, 1), pResA A₁ B₁ z)
            + L₂ (∮ z in C(0, 1), pResA A₂ B₂ z)) := by
        congr 1
        rw [← hmap₁, ← hmap₂]
    _ = L₁ ((2 * Real.pi * Complex.I)⁻¹ • (∮ z in C(0, 1), pResA A₁ B₁ z))
          + L₂ ((2 * Real.pi * Complex.I)⁻¹ • (∮ z in C(0, 1), pResA A₂ B₂ z)) := by
        rw [map_smul, map_smul, smul_add]
    _ = Matrix.fromBlocks (penProjMat X A₁ B₁) 0 0 (penProjMat X A₂ B₂) := by
        rw [hL₁, hL₂, Matrix.fromBlocks_add]
        simp only [add_zero, zero_add]
        rfl

/-! ## Auxiliary lemmas for the append comparison -/

lemma reindex_symm_reindex_app {A : Type*} {ι ι' : Type*} (e : ι ≃ ι') (M : Matrix ι ι A) :
    Matrix.reindex e.symm e.symm (Matrix.reindex e e M) = M := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.submatrix_apply]

lemma isUnit_reindex_iff_app {R : Type*} [Ring R] {ι ι' : Type*} [Fintype ι] [Fintype ι']
    [DecidableEq ι] [DecidableEq ι'] (e : ι ≃ ι') (M : Matrix ι ι R) :
    IsUnit (Matrix.reindex e e M) ↔ IsUnit M := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := h
    refine ⟨Units.map (Matrix.reindexRingEquiv R e.symm).toMonoidHom u, ?_⟩
    show ((Matrix.reindexRingEquiv R e.symm) ((u : Matrix ι' ι' R))) = M
    rw [hu, Matrix.coe_reindexRingEquiv]
    exact reindex_symm_reindex_app e M
  · intro h
    obtain ⟨u, hu⟩ := h
    refine ⟨Units.map (Matrix.reindexRingEquiv R e).toMonoidHom u, ?_⟩
    show ((Matrix.reindexRingEquiv R e) ((u : Matrix ι ι R))) = Matrix.reindex e e M
    rw [hu, Matrix.coe_reindexRingEquiv]

lemma reindex_refl_app {A : Type*} {ι : Type*} (M : Matrix ι ι A) :
    Matrix.reindex (Equiv.refl ι) (Equiv.refl ι) M = M :=
  reindex_symm_reindex_app (Equiv.refl ι) M

lemma isUnit_neg_one_matrix_app {R : Type*} [Ring R] {κ : Type*} [Fintype κ] [DecidableEq κ] :
    IsUnit (-1 : Matrix κ κ R) :=
  ⟨⟨-1, -1, by simp, by simp⟩, rfl⟩

theorem penProjMat_zero_neg_one_app (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {m : ℕ} : penProjMat X (0 : Matrix (Fin m) (Fin m) C(X, ℂ)) (-1) = 0 := by
  letI : NormedRing (Matrix (Fin m) (Fin m) C(X, ℂ)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin m) (Fin m) C(X, ℂ)) := Matrix.linftyOpNormedAlgebra
  letI : CompleteSpace (Matrix (Fin m) (Fin m) C(X, ℂ)) := Matrix.instCompleteSpace _ _ _
  show Work.KT.Idx.penProj (0 : Matrix (Fin m) (Fin m) C(X, ℂ)) (-1) = 0
  simp [Work.KT.Idx.penProj, Work.KT.Idx.pCirc, Work.KT.Idx.pResA, Work.KT.Idx.pRes, circleIntegral]

theorem penProjMat_idem_app (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι C(X, ℂ))
    (h : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • A + B)) :
    penProjMat X A B * penProjMat X A B = penProjMat X A B := by
  obtain ⟨e⟩ : Nonempty (ι ≃ Fin (Fintype.card ι)) := ⟨Fintype.equivFin ι⟩
  have h' : ∀ z : ℂ, ‖z‖ = 1 →
      IsUnit (z • Matrix.reindex e e A + Matrix.reindex e e B) := by
    intro z hz
    rw [← reindex_smul_app e z A, ← reindex_add_app e (z • A) B]
    exact (isUnit_reindex_iff_app e (z • A + B)).mpr (h z hz)
  have hbase : penProjMat X (Matrix.reindex e e A) (Matrix.reindex e e B) *
      penProjMat X (Matrix.reindex e e A) (Matrix.reindex e e B) =
      penProjMat X (Matrix.reindex e e A) (Matrix.reindex e e B) :=
    penProj_idem X (Matrix.reindex e e A) (Matrix.reindex e e B) h'
  have hbridge : penProjMat X (Matrix.reindex e e A) (Matrix.reindex e e B) =
      Matrix.reindex e e (penProjMat X A B) := penProjMat_reindex_append X e A B h
  rw [hbridge] at hbase
  have h2 : Matrix.reindex e e (penProjMat X A B * penProjMat X A B) =
      Matrix.reindex e e (penProjMat X A B) := by
    rw [← reindexMul' e e e (penProjMat X A B) (penProjMat X A B), hbase]
  exact (Matrix.reindex e e).injective h2

lemma reindex_eb_Ablk_app (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n d : ℕ) :
    Matrix.reindex (eb n d) (eb n d) (Ablk X n d) = wPenA X n (d + 1) :=
  (wPen_append_reindex X n d (fun _ => (0 : Matrix (Fin n) (Fin n) C(X, ℂ)))).1

lemma reindex_eb_Bblk_app (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n d : ℕ) (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix.reindex (eb n d) (eb n d) (Bblk X n d b)
      = wPenB X n (d + 1) (appSeq X b) :=
  (wPen_append_reindex X n d b).2

end

end Work.Idx
