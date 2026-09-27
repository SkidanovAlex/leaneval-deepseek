import Mathlib
import Submission.Work.KT.FP.PencilDefs
import Submission.Work.KT.FP.PadDefs
import Submission.Work.KT.FP.pencil_proj_data
import Submission.Work.KT.FP.pCirc_mul_pCirc_iterated
import Submission.Work.KT.FP.prepend_admissible
import Submission.Work.KT.FP.prepend_proj_blocks
import Submission.Work.KT.FP.append_proj_blocks
import Submission.Work.Idx.WPenAppendDefs
import Submission.Work.Idx.MvNGen_fromBlocks
import Submission.Work.Idx.WPenBlk
import Submission.Work.Idx.matPenProj_eval
import Submission.Work.KT.Basic

namespace Work.KT.FP

open Matrix MeasureTheory intervalIntegral
open scoped Topology Interval BigOperators

noncomputable section

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-! ## The pencil projection on an arbitrary finite index type -/

/-- The pencil projection of a matrix pencil over an arbitrary finite index type, with the `L∞`
operator norm on the matrix algebra. -/
def lindPadProj {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι C(X, ℂ)) :
    Matrix ι ι C(X, ℂ) :=
  letI : NormedRing (Matrix ι ι C(X, ℂ)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix ι ι C(X, ℂ)) := Matrix.linftyOpNormedAlgebra
  letI : CompleteSpace (Matrix ι ι C(X, ℂ)) := Matrix.instCompleteSpace _ _ _
  pProj A B 1

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Reindexing is a contraction for the `L∞` operator norm. -/
lemma reindex_norm_le (e : ι ≃ κ) (M : Matrix ι ι C(X,ℂ)) :
    letI : NormedRing (Matrix ι ι C(X,ℂ)) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℂ (Matrix ι ι C(X,ℂ)) := Matrix.linftyOpNormedAlgebra
    letI : NormedRing (Matrix κ κ C(X,ℂ)) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℂ (Matrix κ κ C(X,ℂ)) := Matrix.linftyOpNormedAlgebra
    ‖Matrix.reindex e e M‖ ≤ ‖M‖ := by
  rw [Matrix.reindex_apply]
  rw [Matrix.linfty_opNorm_def, Matrix.linfty_opNorm_def]
  rw [NNReal.coe_le_coe]
  refine Finset.sup_le fun i _ => ?_
  simp only [Matrix.submatrix_apply]
  have h : ∑ j : κ, ‖M (e.symm i) (e.symm j)‖₊ = ∑ j : ι, ‖M (e.symm i) j‖₊ :=
    Finset.sum_bij (fun j _ => e.symm j) (by intro a _; simp)
      (by intro a _ b _ h; simpa using e.symm.injective h)
      (by intro b _; exact ⟨e b, by simp, by simp⟩) (by intro a _; simp)
  rw [h]
  exact Finset.le_sup (f := fun p : ι => ∑ q : ι, ‖M p q‖₊) (Finset.mem_univ (e.symm i))

/-- Naturality of the pencil projection under a reindexing. -/
theorem padProj_reindex (e : ι ≃ κ) (A B : Matrix ι ι C(X,ℂ))
    (hunit : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • A + B)) :
    lindPadProj X (Matrix.reindex e e A) (Matrix.reindex e e B) = Matrix.reindex e e (lindPadProj X A B) := by
  letI : NormedRing (Matrix ι ι C(X,ℂ)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix ι ι C(X,ℂ)) := Matrix.linftyOpNormedAlgebra
  letI : NormedRing (Matrix κ κ C(X,ℂ)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix κ κ C(X,ℂ)) := Matrix.linftyOpNormedAlgebra
  letI : CompleteSpace (Matrix ι ι C(X,ℂ)) := Matrix.instCompleteSpace ι ι C(X,ℂ)
  letI : CompleteSpace (Matrix κ κ C(X,ℂ)) := Matrix.instCompleteSpace κ κ C(X,ℂ)
  have hCι : CompleteSpace (Matrix ι ι C(X,ℂ)) := inferInstance
  have hCκ : CompleteSpace (Matrix κ κ C(X,ℂ)) := inferInstance
  change pProj (Matrix.reindex e e A) (Matrix.reindex e e B) 1 = Matrix.reindex e e (pProj A B 1)
  let Lm : Matrix ι ι C(X,ℂ) →ₗ[ℂ] Matrix κ κ C(X,ℂ) :=
    { toFun := Matrix.reindex e e
      map_add' := by intro M N; ext i j; simp [Matrix.reindex_apply, Matrix.submatrix_apply]
      map_smul' := by intro c M; ext i j; simp [Matrix.reindex_apply, Matrix.submatrix_apply] }
  have hLmCL : ∀ M : Matrix ι ι C(X,ℂ), ‖Lm M‖ ≤ 1 * ‖M‖ := by
    intro M
    change ‖Matrix.reindex e e M‖ ≤ 1 * ‖M‖
    rw [one_mul]
    exact reindex_norm_le X e M
  let L : Matrix ι ι C(X,ℂ) →L[ℂ] Matrix κ κ C(X,ℂ) := Lm.mkContinuous 1 hLmCL
  have hL : ∀ M, L M = Matrix.reindex e e M := fun M => rfl
  have hcont : ContinuousOn (fun z : ℂ => pResA A B z) (Metric.sphere (0:ℂ) 1) :=
    @Work.KT.FP.pResA_continuousOn_sphere (Matrix ι ι C(X,ℂ)) Matrix.linftyOpNormedRing
      Matrix.linftyOpNormedAlgebra hCι A B 1 (fun z hz => hunit z hz)
  have hint : CircleIntegrable (fun z : ℂ => pResA A B z) 0 1 :=
    hcont.circleIntegrable (by norm_num)
  have hkey := @Work.Idx.circleIntegral_map_clm (Matrix ι ι C(X,ℂ)) (inferInstance) (inferInstance)
    (Matrix κ κ C(X,ℂ)) (inferInstance) (inferInstance) hCι hCκ L
    (fun z : ℂ => pResA A B z) 0 1 hint
  have hpoint : ∀ z : ℂ, ‖z‖ = 1 →
      L (pResA A B z) = pResA (Matrix.reindex e e A) (Matrix.reindex e e B) z := by
    intro z hz
    rw [hL]
    have hφ : Matrix.reindex e e (Ring.inverse (z • A + B))
        = Ring.inverse (z • Matrix.reindex e e A + Matrix.reindex e e B) := by
      have h1 := Work.Idx.ringHom_map_ringInverse
        (Matrix.reindexAlgEquiv ℂ (C(X,ℂ)) e).toRingEquiv.toRingHom (hunit z hz)
      have h2 : (Matrix.reindexAlgEquiv ℂ (C(X,ℂ)) e).toRingEquiv.toRingHom (z • A + B)
          = z • Matrix.reindex e e A + Matrix.reindex e e B := by
        change Matrix.reindex e e (z • A + B) = _
        ext i j
        simp [Matrix.reindex_apply, Matrix.submatrix_apply]
      rwa [h2] at h1
    have hmul : Matrix.reindex e e (Ring.inverse (z • A + B) * A)
        = Matrix.reindex e e (Ring.inverse (z • A + B)) * Matrix.reindex e e A :=
      (Work.Idx.reindexMul' e e e (Ring.inverse (z • A + B)) A).symm
    show Matrix.reindex e e (Ring.inverse (z • A + B) * A)
        = Ring.inverse (z • Matrix.reindex e e A + Matrix.reindex e e B) * Matrix.reindex e e A
    rw [hmul, hφ]
  have hkey2 : L (pProj A B 1) = pProj (Matrix.reindex e e A) (Matrix.reindex e e B) 1 := by
    change L ((2 * Real.pi * Complex.I)⁻¹ • (∮ z in C(0,1), pResA A B z))
      = (2 * Real.pi * Complex.I)⁻¹ •
          (∮ z in C(0,1), pResA (Matrix.reindex e e A) (Matrix.reindex e e B) z)
    rw [map_smul]
    congr 1
    calc L (∮ z in C(0,1), pResA A B z)
        = ∮ z in C(0,1), L (pResA A B z) := hkey
      _ = ∮ z in C(0,1), pResA (Matrix.reindex e e A) (Matrix.reindex e e B) z :=
          circleIntegral.integral_congr (by norm_num : (0:ℝ) ≤ 1) (fun z hz =>
            hpoint z (by simpa [Metric.mem_sphere, dist_eq_norm] using hz))
  rw [← hkey2]
  exact hL (pProj A B 1)

/-! ## The block-index projection and its class -/

/-- The unit-circle projection of the degree-`d` W linearisation of a coefficient sequence. -/
def padBP (n d : ℕ) (c : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (BIdx n d) (BIdx n d) C(X, ℂ) :=
  lindPadProj X (Work.KT.Idx.wPenA X n d) (Work.KT.Idx.wPenB X n d c)

/-- The flat projection as an element of the matrix model of `K₀`. -/
def padCls (n d : ℕ) (c : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Work.KT.Mat C(X, ℂ) :=
  ⟨(d + 1) * n, Matrix.reindex finProdFinEquiv finProdFinEquiv (padBP X n d c)⟩

/-- `padBP` is idempotent. -/
theorem padBP_idem (n d : ℕ) (c : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ))
    (h : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • Work.KT.Idx.wPenA X n d + Work.KT.Idx.wPenB X n d c)) :
    padBP X n d c * padBP X n d c = padBP X n d c := by
  letI : NormedRing (Matrix (BIdx n d) (BIdx n d) C(X,ℂ)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (BIdx n d) (BIdx n d) C(X,ℂ)) := Matrix.linftyOpNormedAlgebra
  letI : CompleteSpace (Matrix (BIdx n d) (BIdx n d) C(X,ℂ)) := Matrix.instCompleteSpace _ _ _
  have hC : CompleteSpace (Matrix (BIdx n d) (BIdx n d) C(X,ℂ)) := inferInstance
  have hunit : ∀ z : ℂ, (1:ℝ) ≤ ‖z‖ → ‖z‖ ≤ 1 →
      IsUnit (z • Work.KT.Idx.wPenA X n d + Work.KT.Idx.wPenB X n d c) :=
    fun z h1 h2 => h z (le_antisymm h2 h1)
  have hh := (@Work.KT.FP.pencil_proj_data (Matrix (BIdx n d) (BIdx n d) C(X,ℂ))
    Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra hC
    (Work.KT.Idx.wPenA X n d) (Work.KT.Idx.wPenB X n d c)).1 (by norm_num) le_rfl hunit
  simpa only [padBP, lindPadProj] using hh

/-- `padBP` is the block-index pencil projection of the coefficient sequence. -/
theorem padBP_eq_penProjMat (n d : ℕ) (c : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) :
    padBP X n d c = Work.Idx.penProjMat X (Work.KT.Idx.wPenA X n d) (Work.KT.Idx.wPenB X n d c) := rfl

/-- The flat projection at radius `1` is the reindexing of `padBP`. -/
theorem matPProj_eq_reindex_pad (n d : ℕ) (c : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ))
    (h : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • Work.KT.Idx.wPenA X n d + Work.KT.Idx.wPenB X n d c)) :
    matPProj X ((d + 1) * n) (wPenAf X n d) (wPenBf X n d c) 1
      = Matrix.reindex finProdFinEquiv finProdFinEquiv (padBP X n d c) := by
  have h1 : matPProj X ((d + 1) * n) (wPenAf X n d) (wPenBf X n d c) 1
      = lindPadProj X (wPenAf X n d) (wPenBf X n d c) := rfl
  rw [h1]
  have h2 : wPenAf X n d
      = Matrix.reindex finProdFinEquiv finProdFinEquiv (Work.KT.Idx.wPenA X n d) := rfl
  have h3 : wPenBf X n d c
      = Matrix.reindex finProdFinEquiv finProdFinEquiv (Work.KT.Idx.wPenB X n d c) := rfl
  rw [h2, h3,
    padProj_reindex X finProdFinEquiv (Work.KT.Idx.wPenA X n d) (Work.KT.Idx.wPenB X n d c) h]
  rfl

/-! ## Two glue lemmas -/

/-- The class of a reindexed matrix, upgraded from `MvNGen`. -/
theorem padCls_eq_of_mvNGen {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] {N M : ℕ}
    {p : Matrix ι₁ ι₁ C(X, ℂ)} {q : Matrix ι₂ ι₂ C(X, ℂ)}
    (e₁ : ι₁ ≃ Fin N) (e₂ : ι₂ ≃ Fin M)
    (hp : p * p = p) (hq : q * q = q) (h : Work.Idx.MvNGen p q) :
    Work.KT.cls (⟨N, Matrix.reindex e₁ e₁ p⟩ : Work.KT.Mat C(X, ℂ)) =
      Work.KT.cls (⟨M, Matrix.reindex e₂ e₂ q⟩ : Work.KT.Mat C(X, ℂ)) :=
  Work.KT.cls_eq_of_mvN (Work.Idx.isIdem_reindex e₁ hp) (Work.Idx.isIdem_reindex e₂ hq)
    (Work.Idx.MvNGen.toMat e₁ e₂ h)

/-- Reindexing a block matrix along a sum-congruence acts blockwise. -/
theorem fromBlocks_reindex_sumCongr {R : Type*} [Zero R] {ι₁ ι₁' ι₂ ι₂' : Type*}
    (e₁ : ι₁ ≃ ι₁') (e₂ : ι₂ ≃ ι₂')
    (A : Matrix ι₁ ι₁ R) (B : Matrix ι₁ ι₂ R) (C : Matrix ι₂ ι₁ R) (D : Matrix ι₂ ι₂ R) :
    Matrix.reindex (Equiv.sumCongr e₁ e₂) (Equiv.sumCongr e₁ e₂) (Matrix.fromBlocks A B C D) =
      Matrix.fromBlocks (Matrix.reindex e₁ e₁ A) (Matrix.reindex e₁ e₂ B)
        (Matrix.reindex e₂ e₁ C) (Matrix.reindex e₂ e₂ D) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.reindex_apply, Matrix.submatrix_apply]

/-! ## The two padding relations (Hatcher (1) and (2)) -/

/-- Reindexing of square matrices is injective. -/
lemma reindex_inj {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) :
    Function.Injective (Matrix.reindex e e : Matrix ι ι C(X,ℂ) → Matrix κ κ C(X,ℂ)) := by
  intro M N h
  have h' := congrArg (Matrix.reindex e.symm e.symm) h
  simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using h'

/-- Reindexing along an equivalence, then along its inverse, is the identity. -/
lemma reindex_symm_reindex' {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (M : Matrix κ κ C(X,ℂ)) :
    Matrix.reindex e e (Matrix.reindex e.symm e.symm M) = M := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.submatrix_apply]

/-- Reindexing a diagonal block matrix along a sum-congruence. -/
lemma fromBlocks_reindex_sumCongr' {ι₁ ι₁' ι₂ ι₂' : Type*} [Fintype ι₁] [Fintype ι₁']
    [Fintype ι₂] [Fintype ι₂'] (e₁ : ι₁ ≃ ι₁') (e₂ : ι₂ ≃ ι₂')
    (A : Matrix ι₁ ι₁ C(X,ℂ)) (D : Matrix ι₂ ι₂ C(X,ℂ)) :
    Matrix.reindex (Equiv.sumCongr e₁ e₂) (Equiv.sumCongr e₁ e₂)
        (Matrix.fromBlocks A 0 0 D) =
      Matrix.fromBlocks (Matrix.reindex e₁ e₁ A) 0 0 (Matrix.reindex e₂ e₂ D) := by
  rw [fromBlocks_reindex_sumCongr]
  refine Matrix.fromBlocks_inj.mpr ⟨rfl, by simp [Matrix.reindex_apply, Matrix.submatrix_apply],
    by simp [Matrix.reindex_apply, Matrix.submatrix_apply], rfl⟩

/-- The identity matrix is idempotent, as a `Work.KT.Mat`. -/
lemma matOne_isIdem (n : ℕ) : (Work.KT.Mat.one C(X,ℂ) n).IsIdem := by
  rw [Work.KT.Mat.IsIdem, Work.KT.Mat.one]
  exact mul_one 1

/-- Reindexing a matrix along the identity equivalence. -/
@[simp] lemma reindex_refl_id {ι : Type*} (M : Matrix ι ι C(X,ℂ)) :
    Matrix.reindex (Equiv.refl ι) (Equiv.refl ι) M = M := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.submatrix_apply]

theorem padCls_append (n d : ℕ) (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ))
    (h : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • Work.KT.Idx.wPenA X n d + Work.KT.Idx.wPenB X n d b))
    (h' : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • Work.KT.Idx.wPenA X n (d + 1)
        + Work.KT.Idx.wPenB X n (d + 1) (Work.KT.Idx.appSeq X b))) :
    Work.KT.cls (padCls X n (d + 1) (Work.KT.Idx.appSeq X b)) = Work.KT.cls (padCls X n d b) := by
  obtain ⟨h00, h01, h11⟩ := append_proj_blocks X n d b h h'
  let Z : Matrix (Fin n) (BIdx n d) C(X, ℂ) :=
    fun a i => padBP X n (d + 1) (Work.KT.Idx.appSeq X b) (eApp n d (Sum.inr a)) (eApp n d (Sum.inl i))
  have hblocks : Matrix.reindex (eApp n d).symm (eApp n d).symm
        (padBP X n (d + 1) (Work.KT.Idx.appSeq X b))
      = Work.Idx.fromBlocks20 (padBP X n d b) Z := by
    apply Matrix.ext
    intro p q
    rcases p with i | a
    · rcases q with i' | a'
      · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
          Work.Idx.fromBlocks20_apply_inl_inl, padBP_eq_penProjMat]
        exact h00 i i'
      · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
          Work.Idx.fromBlocks20_apply_inl_inr, padBP_eq_penProjMat]
        exact h01 i a'
    · rcases q with i' | a'
      · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
          Work.Idx.fromBlocks20_apply_inr_inl, padBP_eq_penProjMat]
        rfl
      · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
          Work.Idx.fromBlocks20_apply_inr_inr, padBP_eq_penProjMat]
        exact h11 a a'
  have hbig : padBP X n (d + 1) (Work.KT.Idx.appSeq X b)
      = Matrix.reindex (eApp n d) (eApp n d) (Work.Idx.fromBlocks20 (padBP X n d b) Z) := by
    rw [← hblocks]
    exact (reindex_symm_reindex' X (eApp n d) _).symm
  have hP : padBP X n d b * padBP X n d b = padBP X n d b := padBP_idem X n d b h
  have hX : Work.Idx.fromBlocks20 (padBP X n d b) Z * Work.Idx.fromBlocks20 (padBP X n d b) Z
      = Work.Idx.fromBlocks20 (padBP X n d b) Z := by
    apply reindex_inj X (eApp n d)
    rw [← Work.Idx.reindexMul' (eApp n d) (eApp n d) (eApp n d)
      (Work.Idx.fromBlocks20 (padBP X n d b) Z) (Work.Idx.fromBlocks20 (padBP X n d b) Z)]
    rw [← hbig]
    exact padBP_idem X n (d + 1) (Work.KT.Idx.appSeq X b) h'
  have hmvn := Work.Idx.MvNGen_fromBlocks (padBP X n d b) Z hP hX
  have hmvn' : Work.Idx.MvNGen (padBP X n (d + 1) (Work.KT.Idx.appSeq X b)) (padBP X n d b) := by
    rw [hbig]
    exact (Work.Idx.MvNGen_reindex (eApp n d) (Equiv.refl (BIdx n d))
      (Work.Idx.fromBlocks20 (padBP X n d b) Z) (padBP X n d b)).mpr hmvn
  change Work.KT.cls (⟨(d + 2) * n, Matrix.reindex finProdFinEquiv finProdFinEquiv
      (padBP X n (d + 1) (Work.KT.Idx.appSeq X b))⟩ : Work.KT.Mat C(X, ℂ))
    = Work.KT.cls (⟨(d + 1) * n, Matrix.reindex finProdFinEquiv finProdFinEquiv
        (padBP X n d b)⟩ : Work.KT.Mat C(X, ℂ))
  exact Work.KT.cls_eq_of_mvN
    (Work.Idx.isIdem_reindex (finProdFinEquiv : BIdx n (d+1) ≃ Fin ((d+2)*n))
      (padBP_idem X n (d + 1) (Work.KT.Idx.appSeq X b) h'))
    (Work.Idx.isIdem_reindex (finProdFinEquiv : BIdx n d ≃ Fin ((d+1)*n)) hP)
    (Work.Idx.MvNGen.toMat (finProdFinEquiv : BIdx n (d+1) ≃ Fin ((d+2)*n))
      (finProdFinEquiv : BIdx n d ≃ Fin ((d+1)*n)) hmvn')

theorem padCls_prepend (n d : ℕ) (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ))
    (h : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • Work.KT.Idx.wPenA X n d + Work.KT.Idx.wPenB X n d b))
    (h' : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • Work.KT.Idx.wPenA X n (d + 1)
        + Work.KT.Idx.wPenB X n (d + 1) (Work.KT.Idx.preSeq X b))) :
    Work.KT.cls (padCls X n (d + 1) (Work.KT.Idx.preSeq X b))
      = Work.KT.cls (padCls X n d b) + Work.KT.cls (Work.KT.Mat.one C(X, ℂ) n) := by
  obtain ⟨h00, h10, h11⟩ := prepend_proj_blocks X n d b h h'
  let Cb : Matrix (Fin n) (BIdx n d) C(X, ℂ) :=
    fun a i => padBP X n (d + 1) (Work.KT.Idx.preSeq X b) (ePre n d (Sum.inl a)) (ePre n d (Sum.inr i))
  let E : Matrix (Fin n ⊕ BIdx n d) (Fin n ⊕ BIdx n d) C(X, ℂ) :=
    Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) Cb 0 (padBP X n d b)
  have hblocks : Matrix.reindex (ePre n d).symm (ePre n d).symm
        (padBP X n (d + 1) (Work.KT.Idx.preSeq X b)) = E := by
    apply Matrix.ext
    intro p q
    rcases p with a | i
    · rcases q with a' | i'
      · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
          E, Matrix.fromBlocks_apply₁₁, padBP_eq_penProjMat]
        exact h00 a a'
      · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
          E, Matrix.fromBlocks_apply₁₂]
        rfl
    · rcases q with a' | i'
      · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
          E, Matrix.fromBlocks_apply₂₁, padBP_eq_penProjMat]
        exact h10 i a'
      · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
          E, Matrix.fromBlocks_apply₂₂, padBP_eq_penProjMat]
        exact h11 i i'
  have hbig : padBP X n (d + 1) (Work.KT.Idx.preSeq X b)
      = Matrix.reindex (ePre n d) (ePre n d) E := by
    rw [← hblocks]
    exact (reindex_symm_reindex' X (ePre n d) _).symm
  have hP : padBP X n d b * padBP X n d b = padBP X n d b := padBP_idem X n d b h
  have hE : E * E = E := by
    apply reindex_inj X (ePre n d)
    rw [← Work.Idx.reindexMul' (ePre n d) (ePre n d) (ePre n d) E E]
    rw [← hbig]
    exact padBP_idem X n (d + 1) (Work.KT.Idx.preSeq X b) h'
  have hCP : Cb * padBP X n d b = 0 := by
    have h2 : Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) Cb 0 (padBP X n d b)
        * Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) Cb 0 (padBP X n d b)
        = Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) Cb 0 (padBP X n d b) := hE
    rw [Matrix.fromBlocks_multiply] at h2
    obtain ⟨-, h01, -, -⟩ := Matrix.fromBlocks_inj.mp h2
    rw [Matrix.one_mul] at h01
    exact add_left_cancel (show Cb + Cb * padBP X n d b = Cb + 0 by rw [add_zero]; exact h01)
  have hmvn : Work.Idx.MvNGen
      (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) Cb 0 (padBP X n d b))
      (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) 0 0 (padBP X n d b)) := by
    refine ⟨Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) Cb 0 (padBP X n d b),
      Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) 0 0 (padBP X n d b), ?_, ?_⟩
    · rw [Matrix.fromBlocks_multiply]
      exact Matrix.fromBlocks_inj.mpr ⟨by simp, by simp, by simp, by simp [hP]⟩
    · rw [Matrix.fromBlocks_multiply]
      exact Matrix.fromBlocks_inj.mpr ⟨by simp, by simp [hCP], by simp, by simp [hP]⟩
  have hmvn' : Work.Idx.MvNGen (padBP X n (d + 1) (Work.KT.Idx.preSeq X b))
      (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) 0 0 (padBP X n d b)) := by
    rw [hbig]
    exact (Work.Idx.MvNGen_reindex (ePre n d) (Equiv.refl (Fin n ⊕ BIdx n d))
      (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) Cb 0 (padBP X n d b))
      (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) 0 0 (padBP X n d b))).mpr hmvn
  have hdiag : Work.KT.Mat.MvN
      (⟨(d + 2) * n, Matrix.reindex finProdFinEquiv finProdFinEquiv
        (padBP X n (d + 1) (Work.KT.Idx.preSeq X b))⟩ : Work.KT.Mat C(X, ℂ))
      ((Work.KT.Mat.one C(X, ℂ) n).sum
        ⟨(d + 1) * n, Matrix.reindex finProdFinEquiv finProdFinEquiv (padBP X n d b)⟩) := by
    have hQ : Work.Idx.MvNGen (padBP X n (d + 1) (Work.KT.Idx.preSeq X b))
        (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) 0 0
          (Matrix.reindex finProdFinEquiv finProdFinEquiv (padBP X n d b))) := by
      have h2 := (Work.Idx.MvNGen_reindex (Equiv.refl (BIdx n (d + 1)))
        (Equiv.sumCongr (Equiv.refl (Fin n)) (finProdFinEquiv : BIdx n d ≃ Fin ((d+1)*n)))
        (padBP X n (d + 1) (Work.KT.Idx.preSeq X b))
        (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) 0 0 (padBP X n d b))).mpr hmvn'
      rw [reindex_refl_id,
        fromBlocks_reindex_sumCongr' (e₁ := Equiv.refl (Fin n))
          (e₂ := (finProdFinEquiv : BIdx n d ≃ Fin ((d+1)*n)))
          (A := (1 : Matrix (Fin n) (Fin n) C(X, ℂ))) (D := padBP X n d b)] at h2
      exact h2
    exact Work.Idx.MvNGen.toMat (finProdFinEquiv : BIdx n (d+1) ≃ Fin ((d+2)*n))
      finSumFinEquiv hQ
  have h1 : Work.KT.cls (⟨(d + 2) * n, Matrix.reindex finProdFinEquiv finProdFinEquiv
        (padBP X n (d + 1) (Work.KT.Idx.preSeq X b))⟩ : Work.KT.Mat C(X, ℂ))
      = Work.KT.cls ((Work.KT.Mat.one C(X, ℂ) n).sum
        ⟨(d + 1) * n, Matrix.reindex finProdFinEquiv finProdFinEquiv (padBP X n d b)⟩) :=
    Work.KT.cls_eq_of_mvN
      (Work.Idx.isIdem_reindex (finProdFinEquiv : BIdx n (d+1) ≃ Fin ((d+2)*n))
        (padBP_idem X n (d + 1) (Work.KT.Idx.preSeq X b) h'))
      (Work.KT.Mat.sum_idem (matOne_isIdem X n)
        (Work.Idx.isIdem_reindex (finProdFinEquiv : BIdx n d ≃ Fin ((d+1)*n)) hP)) hdiag
  change Work.KT.cls (⟨(d + 2) * n, Matrix.reindex finProdFinEquiv finProdFinEquiv
      (padBP X n (d + 1) (Work.KT.Idx.preSeq X b))⟩ : Work.KT.Mat C(X, ℂ))
    = Work.KT.cls (⟨(d + 1) * n, Matrix.reindex finProdFinEquiv finProdFinEquiv
        (padBP X n d b)⟩ : Work.KT.Mat C(X, ℂ)) + Work.KT.cls (Work.KT.Mat.one C(X, ℂ) n)
  rw [h1, Work.KT.cls_sum (p := Work.KT.Mat.one C(X, ℂ) n) (q := ⟨(d + 1) * n, Matrix.reindex finProdFinEquiv finProdFinEquiv (padBP X n d b)⟩) (matOne_isIdem X n)
      (Work.Idx.isIdem_reindex (finProdFinEquiv : BIdx n d ≃ Fin ((d+1)*n)) hP), add_comm]

/-! ## The final assembly -/

/-- The padded coefficient sequence is `appSeq` of `preSeq`. -/
lemma coeffSeq_pad (n m : ℕ) (P : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ)))
    (hb : ∀ (i j : Fin n) (k : ℤ), (m : ℤ) < k ∨ k < -(m : ℤ) → (P i j).coeff k = 0) :
    coeffSeq X n (m + 1) P
      = Work.KT.Idx.appSeq X (Work.KT.Idx.preSeq X (coeffSeq X n m P)) := by
  funext j
  apply Matrix.ext
  intro a c
  simp only [coeffSeq, Work.KT.Idx.appSeq, Work.KT.Idx.preSeq]
  split_ifs with h1 h2
  · congr 1
    simp only [Fin.val_mk]
    omega
  · rw [hb a c _ (Or.inr (by push_cast; omega))]
    rfl
  · rw [hb a c _ (Or.inl (by push_cast; omega))]
    rfl

/-- The projection at radius `σ` is the projection at radius `1`. -/
lemma matPProj_radius_eq (n d : ℕ) (c : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) {σ : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hadm : ∀ z : ℂ, σ ≤ ‖z‖ → ‖z‖ ≤ 1 →
      IsUnit (z • wPenAf X n d + wPenBf X n d c)) :
    matPProj X ((d + 1) * n) (wPenAf X n d) (wPenBf X n d c) σ
      = matPProj X ((d + 1) * n) (wPenAf X n d) (wPenBf X n d c) 1 := by
  rcases lt_or_eq_of_le hσ1 with hlt | heq
  · letI : NormedRing (Matrix (Fin ((d + 1) * n)) (Fin ((d + 1) * n)) C(X,ℂ)) :=
      Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℂ (Matrix (Fin ((d + 1) * n)) (Fin ((d + 1) * n)) C(X,ℂ)) :=
      Matrix.linftyOpNormedAlgebra
    letI : CompleteSpace (Matrix (Fin ((d + 1) * n)) (Fin ((d + 1) * n)) C(X,ℂ)) :=
      Matrix.instCompleteSpace _ _ _
    have hC : CompleteSpace (Matrix (Fin ((d + 1) * n)) (Fin ((d + 1) * n)) C(X,ℂ)) := inferInstance
    have h := (@Work.KT.FP.pencil_proj_data (Matrix (Fin ((d + 1) * n)) (Fin ((d + 1) * n)) C(X,ℂ))
      Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra hC
      (wPenAf X n d) (wPenBf X n d c)).2 hσ0 hlt le_rfl hadm
    simpa only [matPProj] using h
  · rw [heq]

/-- Reindexing twice with an equivalence and its inverse. -/
lemma reindex_symm_reindex'' {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (M : Matrix ι ι C(X,ℂ)) :
    Matrix.reindex e.symm e.symm (Matrix.reindex e e M) = M := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.submatrix_apply]

/-- Unit-ness is invariant under reindexing. -/
lemma isUnit_reindex_iff {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (M : Matrix ι ι C(X,ℂ)) :
    IsUnit (Matrix.reindex e e M) ↔ IsUnit M :=
  ⟨fun h => by
      have h' : IsUnit (Matrix.reindex e.symm e.symm (Matrix.reindex e e M)) :=
        IsUnit.map (Matrix.reindexRingEquiv C(X, ℂ) e.symm).toRingHom h
      rwa [reindex_symm_reindex'' X e M] at h',
    fun h => h.map (Matrix.reindexRingEquiv C(X, ℂ) e).toRingHom⟩

/-- The flat (reindexed) W pencil is the reindexed block pencil. -/
lemma smul_wPenAf_add_wPenBf_eq (n d : ℕ)
    (c : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) (z : ℂ) :
    z • wPenAf X n d + wPenBf X n d c
      = Matrix.reindex finProdFinEquiv finProdFinEquiv
          (z • Work.KT.Idx.wPenA X n d + Work.KT.Idx.wPenB X n d c) := by
  simp only [wPenAf, wPenBf, Matrix.reindex_apply, Matrix.submatrix_add, Matrix.submatrix_smul,
    Pi.add_apply, Pi.smul_apply]
  rfl

/-- The `Work.KT.FP` and `Work.KT.Idx` copies of the W pencil agree definitionally. -/
lemma wPenA_fp_eq_idx (n d : ℕ) : wPenA X n d = Work.KT.Idx.wPenA X n d := rfl

lemma wPenB_fp_eq_idx (n d : ℕ) (c : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) :
    wPenB X n d c = Work.KT.Idx.wPenB X n d c := rfl

lemma wPenAf_fp_eq_idx (n d : ℕ) : wPenAf X n d = Work.KT.Idx.wPenAf X n d := rfl

lemma wPenBf_fp_eq_idx (n d : ℕ) (c : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) :
    wPenBf X n d c = Work.KT.Idx.wPenBf X n d c := rfl

theorem lindAt_pad (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n m : ℕ) (P : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ)))
    (hb : ∀ (i j : Fin n) (k : ℤ), (m : ℤ) < k ∨ k < -(m : ℤ) → (P i j).coeff k = 0)
    {ρ ρ' : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hρ'0 : 0 < ρ') (hρ'1 : ρ' ≤ 1)
    (hadm : ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 → IsUnit (z • linAf X n m + linBf X n m P))
    (hadm' : ∀ z : ℂ, ρ' ≤ ‖z‖ → ‖z‖ ≤ 1 →
      IsUnit (z • linAf X n (m + 1) + linBf X n (m + 1) P)) :
    lindAt X n (m + 1) P ρ' = lindAt X n m P ρ := by
  have hbk := coeffSeq_pad X n m P hb
  have hadmB : ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 →
      IsUnit (z • Work.KT.Idx.wPenA X n (2 * m)
        + Work.KT.Idx.wPenB X n (2 * m) (coeffSeq X n m P)) := by
    intro z h1 h2
    have h := hadm z h1 h2
    simp only [linAf, linBf] at h
    rw [smul_wPenAf_add_wPenBf_eq X n (2 * m) (coeffSeq X n m P) z] at h
    rwa [isUnit_reindex_iff X finProdFinEquiv] at h
  have hadm'B : ∀ z : ℂ, ρ' ≤ ‖z‖ → ‖z‖ ≤ 1 →
      IsUnit (z • Work.KT.Idx.wPenA X n (2 * (m + 1))
        + Work.KT.Idx.wPenB X n (2 * (m + 1)) (coeffSeq X n (m + 1) P)) := by
    intro z h1 h2
    have h := hadm' z h1 h2
    simp only [linAf, linBf] at h
    rw [smul_wPenAf_add_wPenBf_eq X n (2 * (m + 1)) (coeffSeq X n (m + 1) P) z] at h
    rwa [isUnit_reindex_iff X finProdFinEquiv] at h
  have hmidB := prepend_admissible X n (2 * m) (coeffSeq X n m P) hρ0 hρ1 hadmB
  have hsmall : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • Work.KT.Idx.wPenA X n (2 * m)
      + Work.KT.Idx.wPenB X n (2 * m) (coeffSeq X n m P)) :=
    fun z hz => hadmB z (by rw [hz]; exact hρ1) (le_of_eq hz)
  have hmid : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • Work.KT.Idx.wPenA X n (2 * m + 1)
      + Work.KT.Idx.wPenB X n (2 * m + 1) (Work.KT.Idx.preSeq X (coeffSeq X n m P))) :=
    fun z hz => hmidB z (by rw [hz]; exact hρ1) (le_of_eq hz)
  have hval : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • Work.KT.Idx.wPenA X n (2 * m + 1 + 1)
      + Work.KT.Idx.wPenB X n (2 * m + 1 + 1)
        (Work.KT.Idx.appSeq X (Work.KT.Idx.preSeq X (coeffSeq X n m P)))) := by
    intro z hz
    rw [← hbk]
    exact hadm'B z (by rw [hz]; exact hρ'1) (le_of_eq hz)
  have hunit : ∀ (d : ℕ) (c : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) {σ : ℝ},
      0 < σ → σ ≤ 1 →
      (∀ z : ℂ, σ ≤ ‖z‖ → ‖z‖ ≤ 1 →
        IsUnit (z • wPenAf X n d + wPenBf X n d c)) →
      Work.KT.cls (⟨(d + 1) * n, matPProj X ((d + 1) * n) (wPenAf X n d)
          (wPenBf X n d c) σ⟩ : Work.KT.Mat C(X, ℂ))
        = Work.KT.cls (padCls X n d c) := by
    intro d c σ hσ0 hσ1 hadmσ
    have hblk : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • Work.KT.Idx.wPenA X n d + Work.KT.Idx.wPenB X n d c) := by
      intro z hz
      have h := hadmσ z (by rw [hz]; exact hσ1) (le_of_eq hz)
      rw [show (z : ℂ) • wPenAf X n d + wPenBf X n d c
          = Matrix.reindex finProdFinEquiv finProdFinEquiv
              (z • Work.KT.Idx.wPenA X n d + Work.KT.Idx.wPenB X n d c) from
        smul_wPenAf_add_wPenBf_eq X n d c z] at h
      rwa [isUnit_reindex_iff X finProdFinEquiv] at h
    rw [matPProj_radius_eq X n d c hσ0 hσ1 hadmσ]
    rw [matPProj_eq_reindex_pad X n d c hblk]
    rfl
  have h1 : lindAt X n m P ρ
      = Work.KT.cls (padCls X n (2 * m) (coeffSeq X n m P))
        - m • Work.KT.cls (Work.KT.Mat.one C(X, ℂ) n) := by
    simp only [lindAt, linAf, linBf]
    rw [hunit (2 * m) (coeffSeq X n m P) hρ0 hρ1 hadm]
  have h2 : lindAt X n (m + 1) P ρ'
      = Work.KT.cls (padCls X n (2 * (m + 1)) (coeffSeq X n (m + 1) P))
        - (m + 1) • Work.KT.cls (Work.KT.Mat.one C(X, ℂ) n) := by
    simp only [lindAt, linAf, linBf]
    rw [hunit (2 * (m + 1)) (coeffSeq X n (m + 1) P) hρ'0 hρ'1 hadm']
  have hchain : Work.KT.cls (padCls X n (2 * (m + 1)) (coeffSeq X n (m + 1) P))
      = Work.KT.cls (padCls X n (2 * m) (coeffSeq X n m P))
        + Work.KT.cls (Work.KT.Mat.one C(X, ℂ) n) := by
    rw [hbk]
    change Work.KT.cls (padCls X n (2 * m + 1 + 1)
        (Work.KT.Idx.appSeq X (Work.KT.Idx.preSeq X (coeffSeq X n m P))))
      = Work.KT.cls (padCls X n (2 * m) (coeffSeq X n m P))
        + Work.KT.cls (Work.KT.Mat.one C(X, ℂ) n)
    rw [padCls_append X n (2 * m + 1) (Work.KT.Idx.preSeq X (coeffSeq X n m P)) hmid hval]
    rw [padCls_prepend X n (2 * m) (coeffSeq X n m P) hsmall hmid]
  rw [h1, h2, hchain]
  have hsmul : (m + 1) • (Work.KT.cls (Work.KT.Mat.one C(X, ℂ) n))
      = m • Work.KT.cls (Work.KT.Mat.one C(X, ℂ) n)
        + Work.KT.cls (Work.KT.Mat.one C(X, ℂ) n) := by
    rw [add_smul, one_smul]
  rw [hsmul]
  abel

end

end Work.KT.FP
