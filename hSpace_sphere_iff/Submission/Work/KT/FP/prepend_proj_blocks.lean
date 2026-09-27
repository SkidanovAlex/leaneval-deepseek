import Mathlib
import Submission.Work.KT.FP.PadDefs
import Submission.Work.KT.Idx.PenDefs
import Submission.Work.Idx.WPenBlk
import Submission.Work.Idx.WPenAppendDefs
import Submission.Work.Idx.matPenProj_eval
import Submission.Work.Idx.circleIntegral_const
import Submission.Work.Idx.WPenPsi
import Submission.Work.Idx.wPsi_preSeq

open Matrix MeasureTheory intervalIntegral
open scoped Topology Interval
open scoped Matrix.Norms.Operator

namespace Work.KT.FP

noncomputable section


variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

def ppb_matEntryCLM (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {ι : Type*} [Fintype ι] (i j : ι) : Matrix ι ι C(X, ℂ) →L[ℂ] C(X, ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun M => M i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun M => by
      rw [one_mul]
      have h1 : ‖M i j‖₊ ≤ ∑ l : ι, ‖M i l‖₊ :=
        Finset.single_le_sum (f := fun l => ‖M i l‖₊) (fun _ _ => zero_le) (Finset.mem_univ j)
      have h2 : (∑ l : ι, ‖M i l‖₊) ≤ Finset.univ.sup (fun k : ι => ∑ l : ι, ‖M k l‖₊) :=
        Finset.le_sup (f := fun k => ∑ l, ‖M k l‖₊) (Finset.mem_univ i)
      have h3 : ‖M i j‖₊ ≤ ‖M‖₊ := by
        rw [Matrix.linfty_opNNNorm_def]
        exact h1.trans h2
      exact NNReal.coe_le_coe.mp (by simpa using h3))

theorem ppb_circleIntegral_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ℂ → Matrix ι ι C(X, ℂ)) (c : ℂ) (R : ℝ) (i j : ι) (hf : CircleIntegrable f c R) :
    (∮ z in C(c, R), f z) i j = ∮ z in C(c, R), f z i j := by
  have hcomp : CompleteSpace (Matrix ι ι C(X, ℂ)) := Matrix.instCompleteSpace ι ι C(X, ℂ)
  have h := @Work.Idx.circleIntegral_map_clm (Matrix ι ι C(X, ℂ)) _ _ (C(X, ℂ)) _ _ hcomp _
    (ppb_matEntryCLM X i j) f c R hf
  exact h

theorem ppb_penProjMat_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι C(X, ℂ)) (i j : ι)
    (hf : CircleIntegrable (fun z => Work.KT.Idx.pResA A B z) 0 1) :
    (Work.Idx.penProjMat X A B) i j
      = (2 * Real.pi * Complex.I)⁻¹ • (∮ z in C(0, 1), Work.KT.Idx.pResA A B z i j) := by
  rw [Work.Idx.penProjMat, Work.KT.Idx.penProj, Work.KT.Idx.pCirc, Matrix.smul_apply]
  congr 1
  exact ppb_circleIntegral_apply X (fun z => Work.KT.Idx.pResA A B z) 0 1 i j hf

theorem ppb_ringInverse_fromBlocks_upper {R : Type*} [Ring R]
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (P : Matrix ι ι R) (Q : Matrix ι κ R) (Rn : Matrix κ κ R)
    (hP : IsUnit P) (hR : IsUnit Rn) :
    Ring.inverse (Matrix.fromBlocks P Q 0 Rn)
      = Matrix.fromBlocks (Ring.inverse P) (-(Ring.inverse P * Q * Ring.inverse Rn)) 0
          (Ring.inverse Rn) := by
  have hmain : P * (-(Ring.inverse P * Q * Ring.inverse Rn)) + Q * Ring.inverse Rn = 0 := by
    have h1 : P * (Ring.inverse P * Q * Ring.inverse Rn) = Q * Ring.inverse Rn := by
      rw [Matrix.mul_assoc (Ring.inverse P) Q (Ring.inverse Rn),
        ← Matrix.mul_assoc P (Ring.inverse P) (Q * Ring.inverse Rn),
        Ring.mul_inverse_cancel P hP, Matrix.one_mul]
    rw [Matrix.mul_neg, h1, neg_add_cancel]
  have h1 : Matrix.fromBlocks P Q 0 Rn *
      Matrix.fromBlocks (Ring.inverse P) (-(Ring.inverse P * Q * Ring.inverse Rn)) 0
        (Ring.inverse Rn) = 1 := by
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    rw [hmain, Ring.mul_inverse_cancel P hP, Ring.mul_inverse_cancel Rn hR,
      Matrix.fromBlocks_one]
  have h2 : Matrix.fromBlocks (Ring.inverse P) (-(Ring.inverse P * Q * Ring.inverse Rn)) 0
      (Ring.inverse Rn) * Matrix.fromBlocks P Q 0 Rn = 1 := by
    have hmain' : Ring.inverse P * Q + (-(Ring.inverse P * Q * Ring.inverse Rn)) * Rn = 0 := by
      have h3 : (Ring.inverse P * Q * Ring.inverse Rn) * Rn = Ring.inverse P * Q := by
        rw [Matrix.mul_assoc (Ring.inverse P * Q) (Ring.inverse Rn) Rn,
          Ring.inverse_mul_cancel Rn hR, Matrix.mul_one]
      rw [Matrix.neg_mul, h3, add_neg_cancel]
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    rw [hmain', Ring.inverse_mul_cancel P hP, Ring.inverse_mul_cancel Rn hR,
      Matrix.fromBlocks_one]
  let u : (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ :=
    { val := Matrix.fromBlocks P Q 0 Rn
      inv := Matrix.fromBlocks (Ring.inverse P) (-(Ring.inverse P * Q * Ring.inverse Rn)) 0
        (Ring.inverse Rn)
      val_inv := h1
      inv_val := h2 }
  calc Ring.inverse (Matrix.fromBlocks P Q 0 Rn)
      = Ring.inverse (u : Matrix (ι ⊕ κ) (ι ⊕ κ) R) := rfl
    _ = (↑u⁻¹ : Matrix (ι ⊕ κ) (ι ⊕ κ) R) := Ring.inverse_unit u
    _ = Matrix.fromBlocks (Ring.inverse P) (-(Ring.inverse P * Q * Ring.inverse Rn)) 0
          (Ring.inverse Rn) := rfl

theorem ppb_ringInverse_smul_one {R : Type*} [Ring R] [Algebra ℂ R] (z : ℂ) :
    Ring.inverse (z • (1 : R)) = z⁻¹ • (1 : R) := by
  rw [Work.Idx.ringInverse_smul z (1 : R), Ring.inverse_one R]

theorem ppb_circleIntegral_inv_smul_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (c : E) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ • (∮ z in C(0, 1), z⁻¹ • c) = c := by
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero
    exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [circleIntegral.integral_smul_const (fun z : ℂ => z⁻¹) c 0 1]
  have h : (∮ z in C(0, 1), (fun z : ℂ => z⁻¹) z) = (2 * Real.pi * Complex.I : ℂ) := by
    have h2 := Work.Idx.circleIntegral_zpow (-1)
    simpa using h2
  rw [h, smul_smul, inv_mul_cancel₀ hne, one_smul]

theorem ppb_reindex_pencil_eq {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (A B : Matrix ι ι C(X, ℂ)) (z : ℂ) :
    (Matrix.reindexAlgEquiv ℂ (C(X, ℂ)) e).toRingEquiv.toRingHom (z • A + B)
      = z • Matrix.reindex e e A + Matrix.reindex e e B := by
  have hTalg : ∀ c : ℂ,
      (Matrix.reindexAlgEquiv ℂ (C(X, ℂ)) e).toRingEquiv.toRingHom
          (algebraMap ℂ (Matrix ι ι C(X, ℂ)) c)
        = algebraMap ℂ (Matrix κ κ C(X, ℂ)) c := by
    intro c
    exact (Matrix.reindexAlgEquiv ℂ (C(X, ℂ)) e).commutes c
  have hTs : ∀ (c : ℂ) (x : Matrix ι ι C(X, ℂ)),
      (Matrix.reindexAlgEquiv ℂ (C(X, ℂ)) e).toRingEquiv.toRingHom (c • x)
        = c • (Matrix.reindexAlgEquiv ℂ (C(X, ℂ)) e).toRingEquiv.toRingHom x := by
    intro c x
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hTalg]
  rw [map_add, hTs]
  rfl

theorem ppb_pResA_reindex {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (A B : Matrix ι ι C(X, ℂ)) (z : ℂ) (hz : IsUnit (z • A + B)) :
    Work.KT.Idx.pResA (Matrix.reindex e e A) (Matrix.reindex e e B) z
      = Matrix.reindex e e (Work.KT.Idx.pResA A B z) := by
  have hT : ∀ M : Matrix ι ι C(X, ℂ),
      (Matrix.reindexAlgEquiv ℂ (C(X, ℂ)) e).toRingEquiv.toRingHom M = Matrix.reindex e e M :=
    fun M => rfl
  have hmain : (Matrix.reindexAlgEquiv ℂ (C(X, ℂ)) e).toRingEquiv.toRingHom
        (Work.KT.Idx.pResA A B z)
      = Work.KT.Idx.pResA (Matrix.reindex e e A) (Matrix.reindex e e B) z := by
    show (Matrix.reindexAlgEquiv ℂ (C(X, ℂ)) e).toRingEquiv.toRingHom
          (Ring.inverse (z • A + B) * A)
        = Ring.inverse (z • Matrix.reindex e e A + Matrix.reindex e e B) * Matrix.reindex e e A
    rw [map_mul, Work.Idx.ringHom_map_ringInverse _ hz,
      ppb_reindex_pencil_eq X e A B z, hT A]
  rw [← hmain]
  exact (hT (Work.KT.Idx.pResA A B z)).symm

theorem ppb_penProjMat_entry_reindex {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) (A B : Matrix ι ι C(X, ℂ))
    (hunit : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • A + B)) (x y : κ) :
    Work.Idx.penProjMat X (Matrix.reindex e e A) (Matrix.reindex e e B) x y
      = Work.Idx.penProjMat X A B (e.symm x) (e.symm y) := by
  have hnorm : ∀ z ∈ Metric.sphere (0 : ℂ) 1, ‖z‖ = 1 := fun z hz => by
    simpa [Metric.mem_sphere, dist_eq_norm] using hz
  have hunit₂ : ∀ z : ℂ, ‖z‖ = 1 →
      IsUnit (z • Matrix.reindex e e A + Matrix.reindex e e B) := by
    intro z hz
    have h := (hunit z hz).map ((Matrix.reindexAlgEquiv ℂ (C(X, ℂ)) e).toRingEquiv.toRingHom)
    rwa [ppb_reindex_pencil_eq X e A B z] at h
  have hcont₂ : ContinuousOn (fun z => Work.KT.Idx.pResA (Matrix.reindex e e A)
      (Matrix.reindex e e B) z) (Metric.sphere (0 : ℂ) 1) :=
    @Work.Idx.continuousOn_res (Matrix κ κ C(X, ℂ)) Matrix.linftyOpNormedRing
      Matrix.linftyOpNormedAlgebra (Matrix.instCompleteSpace κ κ C(X, ℂ)) _ _ hunit₂
  have hcont₁ : ContinuousOn (fun z => Work.KT.Idx.pResA A B z) (Metric.sphere (0 : ℂ) 1) :=
    @Work.Idx.continuousOn_res (Matrix ι ι C(X, ℂ)) Matrix.linftyOpNormedRing
      Matrix.linftyOpNormedAlgebra (Matrix.instCompleteSpace ι ι C(X, ℂ)) _ _ hunit
  have hint₂ : CircleIntegrable (fun z => Work.KT.Idx.pResA (Matrix.reindex e e A)
      (Matrix.reindex e e B) z) 0 1 := hcont₂.circleIntegrable (by norm_num)
  have hint₁ : CircleIntegrable (fun z => Work.KT.Idx.pResA A B z) 0 1 :=
    hcont₁.circleIntegrable (by norm_num)
  rw [ppb_penProjMat_apply X (Matrix.reindex e e A) (Matrix.reindex e e B) x y hint₂,
      ppb_penProjMat_apply X A B (e.symm x) (e.symm y) hint₁]
  congr 1
  refine circleIntegral.integral_congr (by norm_num) fun z hz => ?_
  rw [ppb_pResA_reindex X e A B z (hunit z (hnorm z hz)), Matrix.reindex_apply,
    Matrix.submatrix_apply]

/-! ## the prepend block matrices -/

def ppbCoup (X : Type) [TopologicalSpace X] (n d : ℕ) :
    Matrix (Fin n) (BIdx n d) C(X, ℂ) :=
  fun a p => if (p.1 : ℕ) = 0 then (-(1 : Matrix (Fin n) (Fin n) C(X, ℂ))) a p.2 else 0

def ppbA (X : Type) [TopologicalSpace X] (n d : ℕ) :
    Matrix (Fin n ⊕ BIdx n d) (Fin n ⊕ BIdx n d) C(X, ℂ) :=
  Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) 0 0 (Work.KT.Idx.wPenA X n d)

def ppbB (X : Type) [TopologicalSpace X] (n d : ℕ)
    (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix (Fin n ⊕ BIdx n d) (Fin n ⊕ BIdx n d) C(X, ℂ) :=
  Matrix.fromBlocks 0 (ppbCoup X n d) 0 (Work.KT.Idx.wPenB X n d b)

theorem ppb_preSeq_zero (n d : ℕ) (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Work.KT.Idx.preSeq X b (0 : Fin (d + 2)) = 0 := by
  rw [Work.KT.Idx.preSeq_apply, dif_neg (by simp)]

theorem ppb_preSeq_succ (n d : ℕ) (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ))
    (l : Fin (d + 1)) : Work.KT.Idx.preSeq X b (Fin.succ l) = b l := by
  rw [Work.KT.Idx.preSeq_apply, dif_pos (by simp)]
  congr 1

theorem ppbCoup_apply (n d : ℕ) (a : Fin n) (k : Fin (d + 1)) (y : Fin n) :
    ppbCoup X n d a (k, y)
      = (if (k : ℕ) = 0 then (-(1 : Matrix (Fin n) (Fin n) C(X, ℂ))) a y else 0) := rfl

theorem ppb_wPenA_apply {D n : ℕ} (i j : Fin (D + 1) × Fin n) :
    Work.KT.Idx.wPenA X n D i j
      = if i.1 = j.1 ∧ (i.1 : ℕ) ≠ D then (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) i.2 j.2
        else 0 := rfl

theorem ppb_wPenB_apply {D n : ℕ} (c : Fin (D + 1) → Matrix (Fin n) (Fin n) C(X, ℂ))
    (i j : Fin (D + 1) × Fin n) :
    Work.KT.Idx.wPenB X n D c i j
      = (if (i.1 : ℕ) + 1 = (j.1 : ℕ) then
          (if (i.1 : ℕ) = D then c j.1 i.2 j.2
            else -(1 : Matrix (Fin n) (Fin n) C(X, ℂ)) i.2 j.2)
          else if (i.1 : ℕ) = D then c j.1 i.2 j.2 else 0) := rfl

theorem ppb_reindex_wPenA (n d : ℕ) :
    Matrix.reindex ((ePre n d).symm) ((ePre n d).symm) (Work.KT.Idx.wPenA X n (d + 1))
      = ppbA X n d := by
  rw [ppbA, Matrix.reindex_apply]
  apply Matrix.ext
  intro i j
  rw [Matrix.submatrix_apply]
  rcases i with a | ⟨k, y⟩ <;> rcases j with a' | ⟨l, y'⟩
  · change Work.KT.Idx.wPenA X n (d + 1) (0, a) (0, a')
      = Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) 0 0 (Work.KT.Idx.wPenA X n d)
          (Sum.inl a) (Sum.inl a')
    rw [Matrix.fromBlocks_apply₁₁, ppb_wPenA_apply]
    split_ifs with h
    · rfl
    · exact absurd ⟨rfl, by simp only [Fin.val_zero]; omega⟩ h
  · change Work.KT.Idx.wPenA X n (d + 1) (0, a) (Fin.succ l, y')
      = Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) 0 0 (Work.KT.Idx.wPenA X n d)
          (Sum.inl a) (Sum.inr (l, y'))
    rw [Matrix.fromBlocks_apply₁₂, ppb_wPenA_apply]
    split_ifs with h
    · exact absurd (congrArg (fun p : Fin (d + 2) => (p : ℕ)) h.1) (by simp)
    · rfl
  · change Work.KT.Idx.wPenA X n (d + 1) (Fin.succ k, y) (0, a')
      = Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) 0 0 (Work.KT.Idx.wPenA X n d)
          (Sum.inr (k, y)) (Sum.inl a')
    rw [Matrix.fromBlocks_apply₂₁, ppb_wPenA_apply]
    split_ifs with h
    · exact absurd (congrArg (fun p : Fin (d + 2) => (p : ℕ)) h.1) (by simp)
    · rfl
  · change Work.KT.Idx.wPenA X n (d + 1) (Fin.succ k, y) (Fin.succ l, y')
      = Work.KT.Idx.wPenA X n d (k, y) (l, y')
    rw [ppb_wPenA_apply, ppb_wPenA_apply]
    split_ifs with h1 h2
    all_goals (simp only [Fin.val_succ, Fin.succ_inj] at *)
    all_goals first | omega | rfl

theorem ppb_reindex_wPenB (n d : ℕ)
    (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Matrix.reindex ((ePre n d).symm) ((ePre n d).symm)
        (Work.KT.Idx.wPenB X n (d + 1) (Work.KT.Idx.preSeq X b))
      = ppbB X n d b := by
  rw [ppbB, Matrix.reindex_apply]
  apply Matrix.ext
  intro i j
  rw [Matrix.submatrix_apply]
  rcases i with a | ⟨k, y⟩ <;> rcases j with a' | ⟨l, y'⟩
  · change Work.KT.Idx.wPenB X n (d + 1) (Work.KT.Idx.preSeq X b) (0, a) (0, a')
      = Matrix.fromBlocks 0 (ppbCoup X n d) 0 (Work.KT.Idx.wPenB X n d b)
          (Sum.inl a) (Sum.inl a')
    rw [Matrix.fromBlocks_apply₁₁, ppb_wPenB_apply]
    split_ifs with h1 h2
    all_goals (simp only [Fin.val_zero] at *)
    all_goals try omega
    all_goals try rfl
  · change Work.KT.Idx.wPenB X n (d + 1) (Work.KT.Idx.preSeq X b) (0, a) (Fin.succ l, y')
      = Matrix.fromBlocks 0 (ppbCoup X n d) 0 (Work.KT.Idx.wPenB X n d b)
          (Sum.inl a) (Sum.inr (l, y'))
    rw [Matrix.fromBlocks_apply₁₂, ppb_wPenB_apply, ppbCoup_apply]
    split_ifs with h1 h2 h3
    all_goals (simp only [Fin.val_zero, Fin.val_succ] at *)
    all_goals try omega
    all_goals try rfl
  · change Work.KT.Idx.wPenB X n (d + 1) (Work.KT.Idx.preSeq X b) (Fin.succ k, y) (0, a')
      = Matrix.fromBlocks 0 (ppbCoup X n d) 0 (Work.KT.Idx.wPenB X n d b)
          (Sum.inr (k, y)) (Sum.inl a')
    rw [Matrix.fromBlocks_apply₂₁, ppb_wPenB_apply]
    split_ifs with h1 h2
    all_goals (simp only [Fin.val_zero, Fin.val_succ] at *)
    all_goals try omega
    all_goals try rw [ppb_preSeq_zero (n := n) (d := d) (b := b)]
    all_goals try rfl
  · change Work.KT.Idx.wPenB X n (d + 1) (Work.KT.Idx.preSeq X b) (Fin.succ k, y) (Fin.succ l, y')
      = Work.KT.Idx.wPenB X n d b (k, y) (l, y')
    rw [ppb_wPenB_apply, ppb_wPenB_apply]
    split_ifs with h1 h2 h3 h4
    all_goals (simp only [Fin.val_succ, Fin.succ_inj] at *)
    all_goals try omega
    all_goals try rw [ppb_preSeq_succ (n := n) (d := d) (b := b)]
    all_goals try rfl

theorem ppb_penProjMat_entry_ePre (n d : ℕ)
    (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ))
    (h' : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • Work.KT.Idx.wPenA X n (d + 1)
        + Work.KT.Idx.wPenB X n (d + 1) (Work.KT.Idx.preSeq X b)))
    (x y : Fin n ⊕ BIdx n d) :
    Work.Idx.penProjMat X (Matrix.reindex ((ePre n d).symm) ((ePre n d).symm)
        (Work.KT.Idx.wPenA X n (d + 1)))
      (Matrix.reindex ((ePre n d).symm) ((ePre n d).symm)
        (Work.KT.Idx.wPenB X n (d + 1) (Work.KT.Idx.preSeq X b))) x y
      = Work.Idx.penProjMat X (Work.KT.Idx.wPenA X n (d + 1))
          (Work.KT.Idx.wPenB X n (d + 1) (Work.KT.Idx.preSeq X b))
          (ePre n d x) (ePre n d y) := by
  have h := ppb_penProjMat_entry_reindex X (ePre n d).symm (Work.KT.Idx.wPenA X n (d + 1))
    (Work.KT.Idx.wPenB X n (d + 1) (Work.KT.Idx.preSeq X b)) h' x y
  simpa only [Equiv.symm_symm] using h

theorem ppb_pResA_prep (n d : ℕ) (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) (z : ℂ)
    (hz : z ≠ 0)
    (hR : IsUnit (z • Work.KT.Idx.wPenA X n d + Work.KT.Idx.wPenB X n d b)) :
    Work.KT.Idx.pResA (ppbA X n d) (ppbB X n d b) z
      = Matrix.fromBlocks (Ring.inverse (z • (1 : Matrix (Fin n) (Fin n) C(X, ℂ))))
          ((-(Ring.inverse (z • (1 : Matrix (Fin n) (Fin n) C(X, ℂ))) * ppbCoup X n d
              * Ring.inverse (z • Work.KT.Idx.wPenA X n d + Work.KT.Idx.wPenB X n d b)))
            * Work.KT.Idx.wPenA X n d)
          0 (Ring.inverse (z • Work.KT.Idx.wPenA X n d + Work.KT.Idx.wPenB X n d b)
              * Work.KT.Idx.wPenA X n d) := by
  have hP : IsUnit (z • (1 : Matrix (Fin n) (Fin n) C(X, ℂ))) := by
    have h := (isUnit_iff_ne_zero.mpr hz).map (algebraMap ℂ (Matrix (Fin n) (Fin n) C(X, ℂ)))
    rwa [Algebra.algebraMap_eq_smul_one] at h
  have hM : z • ppbA X n d + ppbB X n d b
      = Matrix.fromBlocks (z • (1 : Matrix (Fin n) (Fin n) C(X, ℂ))) (ppbCoup X n d) 0
          (z • Work.KT.Idx.wPenA X n d + Work.KT.Idx.wPenB X n d b) := by
    rw [ppbA, ppbB, Matrix.fromBlocks_smul, Matrix.fromBlocks_add]
    simp only [smul_zero, zero_add, add_zero]
  rw [Work.KT.Idx.pResA, Work.KT.Idx.pRes, hM,
    ppb_ringInverse_fromBlocks_upper _ _ _ hP hR, ppbA, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one]

/-! ## assembly -/

theorem prepend_proj_blocks (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n d : ℕ) (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ))
    (h : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • Work.KT.Idx.wPenA X n d + Work.KT.Idx.wPenB X n d b))
    (h' : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • Work.KT.Idx.wPenA X n (d + 1)
        + Work.KT.Idx.wPenB X n (d + 1) (Work.KT.Idx.preSeq X b))) :
    (∀ (a a' : Fin n), Work.Idx.penProjMat X (Work.KT.Idx.wPenA X n (d + 1))
        (Work.KT.Idx.wPenB X n (d + 1) (Work.KT.Idx.preSeq X b))
        (ePre n d (Sum.inl a)) (ePre n d (Sum.inl a')) =
        (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) a a')
    ∧ (∀ (i : BIdx n d) (a : Fin n), Work.Idx.penProjMat X (Work.KT.Idx.wPenA X n (d + 1))
        (Work.KT.Idx.wPenB X n (d + 1) (Work.KT.Idx.preSeq X b))
        (ePre n d (Sum.inr i)) (ePre n d (Sum.inl a)) = 0)
    ∧ (∀ (i i' : BIdx n d), Work.Idx.penProjMat X (Work.KT.Idx.wPenA X n (d + 1))
        (Work.KT.Idx.wPenB X n (d + 1) (Work.KT.Idx.preSeq X b))
        (ePre n d (Sum.inr i)) (ePre n d (Sum.inr i'))
        = Work.Idx.penProjMat X (Work.KT.Idx.wPenA X n d) (Work.KT.Idx.wPenB X n d b) i i') := by
  have hnorm : ∀ z ∈ Metric.sphere (0 : ℂ) 1, ‖z‖ = 1 := fun z hz => by
    simpa [Metric.mem_sphere, dist_eq_norm] using hz
  have hz0_of : ∀ z : ℂ, ‖z‖ = 1 → z ≠ 0 := by
    intro z hz1 h0
    rw [h0, norm_zero] at hz1
    exact one_ne_zero hz1.symm
  have hunit₂ : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (z • ppbA X n d + ppbB X n d b) := by
    intro z hz
    have hh := (h' z hz).map
      ((Matrix.reindexAlgEquiv ℂ (C(X, ℂ)) (ePre n d).symm).toRingEquiv.toRingHom)
    rw [ppb_reindex_pencil_eq X (ePre n d).symm (Work.KT.Idx.wPenA X n (d + 1))
        (Work.KT.Idx.wPenB X n (d + 1) (Work.KT.Idx.preSeq X b)) z,
      ppb_reindex_wPenA X n d, ppb_reindex_wPenB X n d b] at hh
    exact hh
  have hcont₂ : ContinuousOn (fun z => Work.KT.Idx.pResA (ppbA X n d) (ppbB X n d b) z)
      (Metric.sphere (0 : ℂ) 1) :=
    @Work.Idx.continuousOn_res (Matrix (Fin n ⊕ BIdx n d) (Fin n ⊕ BIdx n d) C(X, ℂ))
      Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
      (Matrix.instCompleteSpace _ _ _) _ _ hunit₂
  have hint₂ : CircleIntegrable
      (fun z => Work.KT.Idx.pResA (ppbA X n d) (ppbB X n d b) z) 0 1 :=
    hcont₂.circleIntegrable (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · intro a a'
    rw [← ppb_penProjMat_entry_ePre X n d b h' (Sum.inl a) (Sum.inl a')]
    rw [ppb_reindex_wPenA X n d, ppb_reindex_wPenB X n d b]
    rw [ppb_penProjMat_apply X (ppbA X n d) (ppbB X n d b) (Sum.inl a) (Sum.inl a') hint₂]
    have hcongr : (∮ z in C(0, 1), Work.KT.Idx.pResA (ppbA X n d) (ppbB X n d b) z
          (Sum.inl a) (Sum.inl a'))
        = (∮ z in C(0, 1), z⁻¹ • (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) a a') := by
      refine circleIntegral.integral_congr (by norm_num) fun z hz => ?_
      rw [ppb_pResA_prep X n d b z (hz0_of z (hnorm z hz)) (h z (hnorm z hz)),
        Matrix.fromBlocks_apply₁₁, ppb_ringInverse_smul_one, Matrix.smul_apply]
    rw [hcongr, ppb_circleIntegral_inv_smul_const]
  · intro i a
    rw [← ppb_penProjMat_entry_ePre X n d b h' (Sum.inr i) (Sum.inl a)]
    rw [ppb_reindex_wPenA X n d, ppb_reindex_wPenB X n d b]
    rw [ppb_penProjMat_apply X (ppbA X n d) (ppbB X n d b) (Sum.inr i) (Sum.inl a) hint₂]
    have hcongr : (∮ z in C(0, 1), Work.KT.Idx.pResA (ppbA X n d) (ppbB X n d b) z
          (Sum.inr i) (Sum.inl a)) = (∮ z in C(0, 1), (0 : C(X, ℂ))) := by
      refine circleIntegral.integral_congr (by norm_num) fun z hz => ?_
      rw [ppb_pResA_prep X n d b z (hz0_of z (hnorm z hz)) (h z (hnorm z hz)),
        Matrix.fromBlocks_apply₂₁]
      rfl
    rw [hcongr, Work.Idx.circleIntegral_const, smul_zero]
  · intro i i'
    rw [← ppb_penProjMat_entry_ePre X n d b h' (Sum.inr i) (Sum.inr i')]
    rw [ppb_reindex_wPenA X n d, ppb_reindex_wPenB X n d b]
    have hcont₁ : ContinuousOn (fun z => Work.KT.Idx.pResA (Work.KT.Idx.wPenA X n d)
        (Work.KT.Idx.wPenB X n d b) z) (Metric.sphere (0 : ℂ) 1) :=
      @Work.Idx.continuousOn_res (Matrix (BIdx n d) (BIdx n d) C(X, ℂ))
        Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
        (Matrix.instCompleteSpace _ _ _) _ _ h
    have hint₁ : CircleIntegrable (fun z => Work.KT.Idx.pResA (Work.KT.Idx.wPenA X n d)
        (Work.KT.Idx.wPenB X n d b) z) 0 1 := hcont₁.circleIntegrable (by norm_num)
    rw [ppb_penProjMat_apply X (ppbA X n d) (ppbB X n d b) (Sum.inr i) (Sum.inr i') hint₂,
        ppb_penProjMat_apply X (Work.KT.Idx.wPenA X n d) (Work.KT.Idx.wPenB X n d b) i i' hint₁]
    congr 1
    refine circleIntegral.integral_congr (by norm_num) fun z hz => ?_
    rw [ppb_pResA_prep X n d b z (hz0_of z (hnorm z hz)) (h z (hnorm z hz)),
      Matrix.fromBlocks_apply₂₂]
    rfl

end

end Work.KT.FP
