import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.K0Shim
import Submission.Work.KT.K0_prod_defs
import Submission.Work.KT.K0prod.mvN_zero_sum
import Submission.Work.KT.K0prod.mvN_prod

namespace Work.KT

open _root_.Matrix

open Classical

noncomputable section


/-! ### The pair embeddings of matrices -/

/-- A matrix over `A`, viewed over `A × B` with zero second component. -/
def pairMat {A B : Type} [Zero B] {m n : Type} (X : Matrix m n A) : Matrix m n (A × B) :=
  fun i j => (X i j, 0)

/-- A matrix over `B`, viewed over `A × B` with zero first component. -/
def pairMatB {A B : Type} [Zero A] {m n : Type} (Y : Matrix m n B) : Matrix m n (A × B) :=
  fun i j => (0, Y i j)

@[simp] lemma pairMat_apply {A B : Type} [Zero B] {m n : Type} (X : Matrix m n A)
    (i : m) (j : n) : pairMat (B := B) X i j = (X i j, 0) := rfl

@[simp] lemma pairMatB_apply {A B : Type} [Zero A] {m n : Type} (Y : Matrix m n B)
    (i : m) (j : n) : pairMatB (A := A) Y i j = (0, Y i j) := rfl

lemma pairMat_map_fst {A B : Type} [Ring A] [Ring B] {m n : Type} (X : Matrix m n A) :
    (pairMat (B := B) X).map (RingHom.fst A B) = X := by ext i j; rfl

lemma pairMat_map_snd {A B : Type} [Ring A] [Ring B] {m n : Type} (X : Matrix m n A) :
    (pairMat (B := B) X).map (RingHom.snd A B) = 0 := by ext i j; rfl

lemma pairMatB_map_fst {A B : Type} [Ring A] [Ring B] {m n : Type} (Y : Matrix m n B) :
    (pairMatB (A := A) Y).map (RingHom.fst A B) = 0 := by ext i j; rfl

lemma pairMatB_map_snd {A B : Type} [Ring A] [Ring B] {m n : Type} (Y : Matrix m n B) :
    (pairMatB (A := A) Y).map (RingHom.snd A B) = Y := by ext i j; rfl

lemma pairMat_mul {A B : Type} [Ring A] [Ring B] {l m n : Type} [Fintype m]
    (X : Matrix l m A) (Y : Matrix m n A) :
    pairMat (B := B) X * pairMat (B := B) Y = pairMat (B := B) (X * Y) := by
  ext i j
  · simp only [pairMat_apply, Matrix.mul_apply, Prod.fst_sum, Prod.mk_mul_mk, mul_zero]
  · simp only [pairMat_apply, Matrix.mul_apply, Prod.snd_sum, Prod.mk_mul_mk, mul_zero,
      Finset.sum_const_zero]

lemma pairMatB_mul {A B : Type} [Ring A] [Ring B] {l m n : Type} [Fintype m]
    (X : Matrix l m B) (Y : Matrix m n B) :
    pairMatB (A := A) X * pairMatB (A := A) Y = pairMatB (A := A) (X * Y) := by
  ext i j
  · simp only [pairMatB_apply, Matrix.mul_apply, Prod.fst_sum, Prod.mk_mul_mk, zero_mul,
      Finset.sum_const_zero]
  · simp only [pairMatB_apply, Matrix.mul_apply, Prod.snd_sum, Prod.mk_mul_mk, zero_mul]

/-! ### Products of matrices over a product ring -/

lemma Mat.ext_prod {A B : Type} [Ring A] [Ring B] {n : ℕ}
    {M N : Matrix (Fin n) (Fin n) (A × B)}
    (h1 : M.map (RingHom.fst A B) = N.map (RingHom.fst A B))
    (h2 : M.map (RingHom.snd A B) = N.map (RingHom.snd A B)) : M = N := by
  refine Matrix.ext fun i j => ?_
  exact Prod.ext (by simpa [Matrix.map] using congrFun (congrFun h1 i) j)
    (by simpa [Matrix.map] using congrFun (congrFun h2 i) j)

lemma Mat.ext_prod_mat {A B : Type} [Ring A] [Ring B] {M N : Mat (A × B)}
    (h1 : M.map (RingHom.fst A B) = N.map (RingHom.fst A B))
    (h2 : M.map (RingHom.snd A B) = N.map (RingHom.snd A B)) : M = N := by
  obtain ⟨n, Mn⟩ := M
  obtain ⟨m, Nn⟩ := N
  have hnm : n = m := by
    have h := congrArg (fun x : Mat A => x.1) h1
    simpa [Mat.map] using h
  subst hnm
  have h1' : Mn.map (RingHom.fst A B) = Nn.map (RingHom.fst A B) := by
    have h := h1
    simp only [Mat.map] at h
    exact eq_of_heq (Sigma.mk.inj h).2
  have h2' : Mn.map (RingHom.snd A B) = Nn.map (RingHom.snd A B) := by
    have h := h2
    simp only [Mat.map] at h
    exact eq_of_heq (Sigma.mk.inj h).2
  refine Sigma.ext rfl (heq_of_eq ?_)
  exact Mat.ext_prod h1' h2'

lemma Mat.sum_map {R S : Type} [Ring R] [Ring S] (φ : R →+* S) (p q : Mat R) :
    (p.sum q).map φ = (p.map φ).sum (q.map φ) := by
  unfold Mat.sum Mat.map
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
  ext i j
  simp only [Matrix.map_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b <;> simp

lemma zeroMat_isIdem {R : Type} [Ring R] (n : ℕ) : (zeroMat R n).IsIdem := by
  unfold Mat.IsIdem
  rw [Matrix.mul_zero]

lemma zeroMat_sum {R : Type} [Ring R] (m n : ℕ) :
    Mat.sum (zeroMat R m) (zeroMat R n) = zeroMat R (m + n) := by
  refine Sigma.ext rfl ?_
  refine heq_of_eq ?_
  ext i j
  simp [Mat.sum, zeroMat]

lemma cls_zeroMat {R : Type} [Ring R] (n : ℕ) : cls (zeroMat R n) = 0 := by
  have h0 : cls (zeroMat R 0) = 0 := by
    have hs := cls_sum (zeroMat_isIdem (R := R) 0) (zeroMat_isIdem (R := R) 0)
    rw [zeroMat_sum] at hs
    simp only [Nat.add_zero] at hs
    have h : cls (zeroMat R 0) + 0 = cls (zeroMat R 0) + cls (zeroMat R 0) := by
      rw [add_zero]; exact hs
    exact (add_left_cancel h).symm
  have hmvn : Mat.MvN (zeroMat R n) (zeroMat R 0) := by
    refine ⟨0, 0, ?_, ?_⟩ <;> simp [zeroMat]
  rw [sphKTshim_cls_eq_of_mvn (zeroMat_isIdem n) (zeroMat_isIdem 0) hmvn, h0]

/-! ### The diagonal embeddings -/

@[simp] lemma diagA_snd_eq {A B : Type} [Ring A] [Ring B] (p : Mat A) :
    (diagA A B p).2 = pairMat (B := B) p.2 := rfl

@[simp] lemma diagB_snd_eq {A B : Type} [Ring A] [Ring B] (q : Mat B) :
    (diagB A B q).2 = pairMatB (A := A) q.2 := rfl

lemma diagA_fst {A B : Type} [Ring A] [Ring B] (p : Mat A) :
    (diagA A B p).2.map (RingHom.fst A B) = p.2 := by
  rw [diagA_snd_eq]; exact pairMat_map_fst p.2

lemma diagA_snd {A B : Type} [Ring A] [Ring B] (p : Mat A) :
    (diagA A B p).2.map (RingHom.snd A B) = 0 := by
  rw [diagA_snd_eq]; exact pairMat_map_snd p.2

lemma diagB_fst {A B : Type} [Ring A] [Ring B] (q : Mat B) :
    (diagB A B q).2.map (RingHom.fst A B) = 0 := by
  rw [diagB_snd_eq]; exact pairMatB_map_fst q.2

lemma diagB_snd {A B : Type} [Ring A] [Ring B] (q : Mat B) :
    (diagB A B q).2.map (RingHom.snd A B) = q.2 := by
  rw [diagB_snd_eq]; exact pairMatB_map_snd q.2

lemma diagA_isIdem {A B : Type} [Ring A] [Ring B] {p : Mat A} (hp : p.IsIdem) :
    (diagA A B p).IsIdem := by
  apply Mat.ext_prod
  · rw [← sphKTshim_map_mul', diagA_fst]
    show p.2 * p.2 = p.2
    exact hp
  · rw [← sphKTshim_map_mul', diagA_snd]
    show (0 : Matrix (Fin (diagA A B p).1) (Fin (diagA A B p).1) B) * 0 = 0
    rw [Matrix.mul_zero]

lemma diagB_isIdem {A B : Type} [Ring A] [Ring B] {q : Mat B} (hq : q.IsIdem) :
    (diagB A B q).IsIdem := by
  apply Mat.ext_prod
  · rw [← sphKTshim_map_mul', diagB_fst]
    show (0 : Matrix (Fin (diagB A B q).1) (Fin (diagB A B q).1) A) * 0 = 0
    rw [Matrix.mul_zero]
  · rw [← sphKTshim_map_mul', diagB_snd]
    show q.2 * q.2 = q.2
    exact hq

lemma diagA_map_fst {A B : Type} [Ring A] [Ring B] (p : Mat A) :
    (diagA A B p).map (RingHom.fst A B) = p := by
  obtain ⟨n, M⟩ := p
  refine Sigma.ext rfl ?_
  refine heq_of_eq ?_
  ext i j; rfl

lemma diagA_map_snd {A B : Type} [Ring A] [Ring B] (p : Mat A) :
    (diagA A B p).map (RingHom.snd A B) = zeroMat B p.1 := by
  obtain ⟨n, M⟩ := p
  refine Sigma.ext rfl ?_
  refine heq_of_eq ?_
  ext i j; rfl

lemma diagB_map_snd {A B : Type} [Ring A] [Ring B] (q : Mat B) :
    (diagB A B q).map (RingHom.snd A B) = q := by
  obtain ⟨n, M⟩ := q
  refine Sigma.ext rfl ?_
  refine heq_of_eq ?_
  ext i j; rfl

lemma diagB_map_fst {A B : Type} [Ring A] [Ring B] (q : Mat B) :
    (diagB A B q).map (RingHom.fst A B) = zeroMat A q.1 := by
  obtain ⟨n, M⟩ := q
  refine Sigma.ext rfl ?_
  refine heq_of_eq ?_
  ext i j; rfl

lemma diagA_sum {A B : Type} [Ring A] [Ring B] (p q : Mat A) :
    diagA A B (Mat.sum p q) = Mat.sum (diagA A B p) (diagA A B q) := by
  apply Mat.ext_prod_mat
  · simp only [diagA_map_fst, Mat.sum_map]
  · simp only [diagA_map_snd, Mat.sum_map, zeroMat_sum]
    rfl

lemma diagB_sum {A B : Type} [Ring A] [Ring B] (p q : Mat B) :
    diagB A B (Mat.sum p q) = Mat.sum (diagB A B p) (diagB A B q) := by
  apply Mat.ext_prod_mat
  · simp only [diagB_map_fst, Mat.sum_map, zeroMat_sum]
    rfl
  · simp only [diagB_map_snd, Mat.sum_map]

lemma diagA_mvN {A B : Type} [Ring A] [Ring B] {p q : Mat A} (h : p.MvN q) :
    (diagA A B p).MvN (diagA A B q) := by
  obtain ⟨a, b, hba, hab⟩ := h
  refine ⟨pairMat (B := B) a, pairMat (B := B) b, ?_, ?_⟩
  · rw [pairMat_mul, hba]; rfl
  · rw [pairMat_mul, hab]; rfl

lemma diagB_mvN {A B : Type} [Ring A] [Ring B] {p q : Mat B} (h : p.MvN q) :
    (diagB A B p).MvN (diagB A B q) := by
  obtain ⟨a, b, hba, hab⟩ := h
  refine ⟨pairMatB (A := A) a, pairMatB (A := A) b, ?_, ?_⟩
  · rw [pairMatB_mul, hba]; rfl
  · rw [pairMatB_mul, hab]; rfl



/-! ### `zeroMat` under a ring map -/

lemma zeroMat_map {R S : Type} [Ring R] [Ring S] (φ : R →+* S) (n : ℕ) :
    (zeroMat R n).map φ = zeroMat S n := by
  refine Sigma.ext rfl ?_
  refine heq_of_eq ?_
  ext i j
  simp [Mat.map]

/-! ### The diagonal embeddings of `K₀` -/

/-- `K₀(A) → K₀(A × B)`, `[p] ↦ [p ⊕ 0]`. -/
def PsiA (A B : Type) [Ring A] [Ring B] : K0 A →+ K0 (A × B) :=
  QuotientAddGroup.lift (K0Rel A)
    (FreeAbelianGroup.lift (fun p : Mat A => if p.IsIdem then cls (diagA A B p) else 0))
    (by
      rw [K0Rel, AddSubgroup.closure_le]
      rintro x ((⟨p, q, hp, hq, rfl⟩ | ⟨p, q, hp, hq, hmvn, rfl⟩) | ⟨p, hp, rfl⟩)
      · simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub,
          FreeAbelianGroup.lift_apply_of, if_pos hp, if_pos hq, if_pos (sphKTshim_sum_isIdem hp hq)]
        rw [diagA_sum, cls_sum (diagA_isIdem hp) (diagA_isIdem hq)]
        abel
      · simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub,
          FreeAbelianGroup.lift_apply_of, if_pos hp, if_pos hq]
        rw [sub_eq_zero]
        exact sphKTshim_cls_eq_of_mvn (diagA_isIdem hp) (diagA_isIdem hq) (diagA_mvN hmvn)
      · simp only [SetLike.mem_coe, AddMonoidHom.mem_ker,
          FreeAbelianGroup.lift_apply_of, if_neg hp])

/-- `K₀(B) → K₀(A × B)`, `[q] ↦ [0 ⊕ q]`. -/
def PsiB (A B : Type) [Ring A] [Ring B] : K0 B →+ K0 (A × B) :=
  QuotientAddGroup.lift (K0Rel B)
    (FreeAbelianGroup.lift (fun q : Mat B => if q.IsIdem then cls (diagB A B q) else 0))
    (by
      rw [K0Rel, AddSubgroup.closure_le]
      rintro x ((⟨p, q, hp, hq, rfl⟩ | ⟨p, q, hp, hq, hmvn, rfl⟩) | ⟨q, hq, rfl⟩)
      · simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub,
          FreeAbelianGroup.lift_apply_of, if_pos hp, if_pos hq, if_pos (sphKTshim_sum_isIdem hp hq)]
        rw [diagB_sum, cls_sum (diagB_isIdem hp) (diagB_isIdem hq)]
        abel
      · simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub,
          FreeAbelianGroup.lift_apply_of, if_pos hp, if_pos hq]
        rw [sub_eq_zero]
        exact sphKTshim_cls_eq_of_mvn (diagB_isIdem hp) (diagB_isIdem hq) (diagB_mvN hmvn)
      · simp only [SetLike.mem_coe, AddMonoidHom.mem_ker,
          FreeAbelianGroup.lift_apply_of, if_neg hq])

lemma PsiA_cls {A B : Type} [Ring A] [Ring B] (p : Mat A) :
    PsiA A B (cls p) = if p.IsIdem then cls (diagA A B p) else 0 := by
  classical
  unfold cls PsiA
  rw [QuotientAddGroup.lift_mk, FreeAbelianGroup.lift_apply_of]
  rfl

lemma PsiB_cls {A B : Type} [Ring A] [Ring B] (q : Mat B) :
    PsiB A B (cls q) = if q.IsIdem then cls (diagB A B q) else 0 := by
  classical
  unfold cls PsiB
  rw [QuotientAddGroup.lift_mk, FreeAbelianGroup.lift_apply_of]
  rfl

/-! ### The two projections of `K₀(A × B)` -/

/-- `K₀(A × B) → K₀(A) × K₀(B)`, `[p] ↦ ([p_A], [p_B])`. -/
def Phi (A B : Type) [Ring A] [Ring B] : K0 (A × B) →+ K0 A × K0 B :=
  (K0.map (RingHom.fst A B)).prod (K0.map (RingHom.snd A B))

/-- `K₀(A) × K₀(B) → K₀(A × B)`, `(x, y) ↦ x ⊕ y`. -/
def Psi (A B : Type) [Ring A] [Ring B] : K0 A × K0 B →+ K0 (A × B) :=
  (PsiA A B).comp (AddMonoidHom.fst (K0 A) (K0 B)) +
  (PsiB A B).comp (AddMonoidHom.snd (K0 A) (K0 B))

@[simp] lemma Phi_apply {A B : Type} [Ring A] [Ring B] (z : K0 (A × B)) :
    Phi A B z = (K0.map (RingHom.fst A B) z, K0.map (RingHom.snd A B) z) := rfl

@[simp] lemma Psi_apply {A B : Type} [Ring A] [Ring B] (w : K0 A × K0 B) :
    Psi A B w = PsiA A B w.1 + PsiB A B w.2 := rfl

lemma map_fst_PsiA (A B : Type) [Ring A] [Ring B] :
    (K0.map (RingHom.fst A B)).comp (PsiA A B) = AddMonoidHom.id (K0 A) := by
  apply sphKTshim_addHom_ext
  intro p
  rw [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, PsiA_cls]
  by_cases hp : p.IsIdem
  · rw [if_pos hp, sphKTshim_K0_map_cls _ (diagA_isIdem hp), diagA_map_fst]
  · rw [if_neg hp, map_zero, sphKTshim_cls_eq_zero_of_not_idem p hp]

lemma map_snd_PsiA (A B : Type) [Ring A] [Ring B] :
    (K0.map (RingHom.snd A B)).comp (PsiA A B) = 0 := by
  apply sphKTshim_addHom_ext
  intro p
  rw [AddMonoidHom.comp_apply, PsiA_cls]
  by_cases hp : p.IsIdem
  · rw [if_pos hp, sphKTshim_K0_map_cls _ (diagA_isIdem hp), diagA_map_snd, cls_zeroMat]
    rfl
  · rw [if_neg hp, map_zero]
    rfl

lemma map_snd_PsiB (A B : Type) [Ring A] [Ring B] :
    (K0.map (RingHom.snd A B)).comp (PsiB A B) = AddMonoidHom.id (K0 B) := by
  apply sphKTshim_addHom_ext
  intro q
  rw [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, PsiB_cls]
  by_cases hq : q.IsIdem
  · rw [if_pos hq, sphKTshim_K0_map_cls _ (diagB_isIdem hq), diagB_map_snd]
  · rw [if_neg hq, map_zero, sphKTshim_cls_eq_zero_of_not_idem q hq]

lemma map_fst_PsiB (A B : Type) [Ring A] [Ring B] :
    (K0.map (RingHom.fst A B)).comp (PsiB A B) = 0 := by
  apply sphKTshim_addHom_ext
  intro q
  rw [AddMonoidHom.comp_apply, PsiB_cls]
  by_cases hq : q.IsIdem
  · rw [if_pos hq, sphKTshim_K0_map_cls _ (diagB_isIdem hq), diagB_map_fst, cls_zeroMat]
    rfl
  · rw [if_neg hq, map_zero]
    rfl

/-! ### The crux: `[p_A ⊕ 0] + [0 ⊕ p_B] = [p]` -/

lemma cls_diagA_add_diagB {A B : Type} [Ring A] [Ring B] (p : Mat (A × B))
    (hp : p.IsIdem) :
    cls (diagA A B (p.map (RingHom.fst A B))) + cls (diagB A B (p.map (RingHom.snd A B)))
      = cls p := by
  have hpA : (p.map (RingHom.fst A B)).IsIdem := sphKTshim_isIdem_map _ hp
  have hpB : (p.map (RingHom.snd A B)).IsIdem := sphKTshim_isIdem_map _ hp
  rw [← cls_sum (diagA_isIdem hpA) (diagB_isIdem hpB)]
  have h2 : cls (Mat.sum p (zeroMat (A × B) p.1)) = cls p := by
    rw [cls_sum hp (zeroMat_isIdem (R := A × B) p.1), cls_zeroMat, add_zero]
  rw [← h2]
  have hMvN : Mat.MvN (Mat.sum (diagA A B (p.map (RingHom.fst A B)))
      (diagB A B (p.map (RingHom.snd A B))))
      (Mat.sum p (zeroMat (A × B) p.1)) := by
    apply K0prod.mvN_prod
    · have hL : (Mat.sum (diagA A B (p.map (RingHom.fst A B)))
            (diagB A B (p.map (RingHom.snd A B)))).map (RingHom.fst A B)
          = Mat.sum (p.map (RingHom.fst A B)) (zeroMat A p.1) := by
        rw [Mat.sum_map, diagA_map_fst, diagB_map_fst]
        rfl
      have hR : (Mat.sum p (zeroMat (A × B) p.1)).map (RingHom.fst A B)
          = Mat.sum (p.map (RingHom.fst A B)) (zeroMat A p.1) := by
        rw [Mat.sum_map, zeroMat_map]
      rw [hL, hR]
      exact sphKTshim_mvN_refl (sphKTshim_sum_isIdem (sphKTshim_isIdem_map _ hp) (zeroMat_isIdem p.1))
    · have hL : (Mat.sum (diagA A B (p.map (RingHom.fst A B)))
            (diagB A B (p.map (RingHom.snd A B)))).map (RingHom.snd A B)
          = Mat.sum (zeroMat B p.1) (p.map (RingHom.snd A B)) := by
        rw [Mat.sum_map, diagA_map_snd, diagB_map_snd]
        rfl
      have hR : (Mat.sum p (zeroMat (A × B) p.1)).map (RingHom.snd A B)
          = Mat.sum (p.map (RingHom.snd A B)) (zeroMat B p.1) := by
        rw [Mat.sum_map, zeroMat_map]
      rw [hL, hR]
      exact K0prod.mvN_zero_sum (p.map (RingHom.snd A B)) hpB
  exact sphKTshim_cls_eq_of_mvn
    (sphKTshim_sum_isIdem (diagA_isIdem hpA) (diagB_isIdem hpB))
    (sphKTshim_sum_isIdem hp (zeroMat_isIdem (R := A × B) p.1)) hMvN

/-! ### The two composites -/

lemma Phi_comp_Psi (A B : Type) [Ring A] [Ring B] :
    (Phi A B).comp (Psi A B) = AddMonoidHom.id (K0 A × K0 B) := by
  apply AddMonoidHom.ext
  intro w
  obtain ⟨x, y⟩ := w
  have h1 : K0.map (RingHom.fst A B) (Psi A B (x, y)) = x := by
    have e1 : K0.map (RingHom.fst A B) (PsiA A B x) = x :=
      DFunLike.congr_fun (map_fst_PsiA A B) x
    have e2 : K0.map (RingHom.fst A B) (PsiB A B y) = 0 :=
      DFunLike.congr_fun (map_fst_PsiB A B) y
    rw [Psi_apply, map_add, e1, e2, add_zero]
  have h2z : K0.map (RingHom.snd A B) (Psi A B (x, y)) = y := by
    have e1 : K0.map (RingHom.snd A B) (PsiA A B x) = 0 :=
      DFunLike.congr_fun (map_snd_PsiA A B) x
    have e2 : K0.map (RingHom.snd A B) (PsiB A B y) = y :=
      DFunLike.congr_fun (map_snd_PsiB A B) y
    rw [Psi_apply, map_add, e1, e2, zero_add]
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, Phi_apply]
  exact Prod.ext h1 h2z

lemma Psi_comp_Phi (A B : Type) [Ring A] [Ring B] :
    (Psi A B).comp (Phi A B) = AddMonoidHom.id (K0 (A × B)) := by
  apply sphKTshim_addHom_ext
  intro p
  rw [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, Phi_apply]
  by_cases hp : p.IsIdem
  · rw [sphKTshim_K0_map_cls _ hp, sphKTshim_K0_map_cls _ hp, Psi_apply, PsiA_cls, PsiB_cls,
      if_pos (sphKTshim_isIdem_map _ hp), if_pos (sphKTshim_isIdem_map _ hp),
      cls_diagA_add_diagB p hp]
  · rw [sphKTshim_cls_eq_zero_of_not_idem p hp]
    simp [Psi_apply]

/-- **`K₀` preserves products.** -/
theorem K0_prod (A B : Type) [Ring A] [Ring B] :
    ∃ e : K0 (A × B) ≃+ (K0 A × K0 B),
      ∀ z, e z = (K0.map (RingHom.fst A B) z, K0.map (RingHom.snd A B) z) := by
  refine ⟨AddEquiv.ofBijective (Phi A B) ⟨?_, ?_⟩, fun z => rfl⟩
  · intro z z' h
    have hz : Psi A B (Phi A B z) = z := DFunLike.congr_fun (Psi_comp_Phi A B) z
    have hz' : Psi A B (Phi A B z') = z' := DFunLike.congr_fun (Psi_comp_Phi A B) z'
    calc z = Psi A B (Phi A B z) := hz.symm
      _ = Psi A B (Phi A B z') := by rw [h]
      _ = z' := hz'
  · intro w
    exact ⟨Psi A B w, DFunLike.congr_fun (Phi_comp_Psi A B) w⟩
