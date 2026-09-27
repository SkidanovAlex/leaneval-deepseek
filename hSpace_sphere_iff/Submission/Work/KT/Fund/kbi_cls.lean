import Mathlib
import Submission.Work.KT.Fund.kbi_defs
import Submission.Work.KT.Fund.kbi_frame
import Submission.Work.KT.Fund.kbi_hopfsq
import Submission.Work.KT.Fund.kbi_Wbd
import Submission.Work.KT.Fund.kbi_or_sum
import Submission.Work.KT.mvN_comm
import Submission.Work.KT.mvN_assoc

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Work.KT.Fund

open _root_.Matrix
open Work.KT.Fund.KBI

noncomputable section

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- The canonical equivalence `Fin 1 ⊕ Fin 1 ≃ Fin 2`. -/
abbrev kbic_e : Fin 1 ⊕ Fin 1 ≃ Fin 2 := finSumFinEquiv

/-! ## A calculus for `pairMat` -/

lemma kbic_pairMat_irrel {ι : Type} (M₀ M₁ : Matrix ι ι C(X × Work.KT.Ball ℂ, ℂ))
    (h h' : M₀.map (fun f => bdryRestrict X f) = M₁.map (fun f => bdryRestrict X f)) :
    pairMat X M₀ M₁ h = pairMat X M₀ M₁ h' := by
  refine Matrix.ext fun i j => ?_
  exact Subtype.ext rfl

lemma kbic_pairMat_congr {ι : Type} (M₀ M₀' M₁ M₁' : Matrix ι ι C(X × Work.KT.Ball ℂ, ℂ))
    (h₀ : M₀ = M₀') (h₁ : M₁ = M₁')
    (h : M₀.map (fun f => bdryRestrict X f) = M₁.map (fun f => bdryRestrict X f))
    (h' : M₀'.map (fun f => bdryRestrict X f) = M₁'.map (fun f => bdryRestrict X f)) :
    pairMat X M₀ M₁ h = pairMat X M₀' M₁' h' := by
  subst h₀; subst h₁
  exact kbic_pairMat_irrel X M₀ M₁ h h'

lemma kbic_pairMat_add {ι : Type} (M₀ M₁ N₀ N₁ : Matrix ι ι C(X × Work.KT.Ball ℂ, ℂ))
    (hM : M₀.map (fun f => bdryRestrict X f) = M₁.map (fun f => bdryRestrict X f))
    (hN : N₀.map (fun f => bdryRestrict X f) = N₁.map (fun f => bdryRestrict X f))
    (h : (M₀+N₀).map (fun f => bdryRestrict X f) = (M₁+N₁).map (fun f => bdryRestrict X f)) :
    pairMat X (M₀+N₀) (M₁+N₁) h = pairMat X M₀ M₁ hM + pairMat X N₀ N₁ hN := by
  refine Matrix.ext fun i j => ?_
  exact Subtype.ext rfl

lemma kbic_pairMat_zero {ι : Type}
    (h : (0 : Matrix ι ι C(X × Work.KT.Ball ℂ, ℂ)).map (fun f => bdryRestrict X f)
      = (0 : Matrix ι ι C(X × Work.KT.Ball ℂ, ℂ)).map (fun f => bdryRestrict X f)) :
    pairMat X 0 0 h = 0 := by
  refine Matrix.ext fun i j => ?_
  exact Subtype.ext rfl

lemma kbic_pairMat_mul {ι : Type} [Fintype ι]
    (M₀ M₁ N₀ N₁ : Matrix ι ι C(X × Work.KT.Ball ℂ, ℂ))
    (h₀ : M₀.map (fun f => bdryRestrict X f) = N₀.map (fun f => bdryRestrict X f))
    (h₁ : M₁.map (fun f => bdryRestrict X f) = N₁.map (fun f => bdryRestrict X f))
    (h : (M₀*M₁).map (fun f => bdryRestrict X f) = (N₀*N₁).map (fun f => bdryRestrict X f)) :
    pairMat X (M₀*M₁) (N₀*N₁) h = pairMat X M₀ N₀ h₀ * pairMat X M₁ N₁ h₁ := by
  apply mat_ext X
  · show (pairMat X (M₀*M₁) (N₀*N₁) h).map (prF X) = _
    simp only [pairMat_map_prF, Matrix.map_mul]
  · show (pairMat X (M₀*M₁) (N₀*N₁) h).map (prS X) = _
    simp only [pairMat_map_prS, Matrix.map_mul]

lemma kbic_pairMat_isIdem {ι : Type} [Fintype ι]
    (M₀ M₁ : Matrix ι ι C(X × Work.KT.Ball ℂ, ℂ))
    (h : M₀.map (fun f => bdryRestrict X f) = M₁.map (fun f => bdryRestrict X f))
    (h0 : M₀*M₀ = M₀) (h1 : M₁*M₁ = M₁) :
    pairMat X M₀ M₁ h * pairMat X M₀ M₁ h = pairMat X M₀ M₁ h := by
  have h' : (M₀*M₀).map (fun f => bdryRestrict X f) = (M₁*M₁).map (fun f => bdryRestrict X f) := by
    rw [show (fun f => bdryRestrict X f) = ⇑(bdryRestrict X) from rfl]
    rw [Matrix.map_mul, Matrix.map_mul, h]
  rw [← kbic_pairMat_mul X M₀ M₀ M₁ M₁ h h h']
  exact kbic_pairMat_congr X _ _ _ _ h0 h1 h' h

lemma kbic_map_reindex {ι ι' : Type} (e : ι ≃ ι') {R S : Type} [Ring R] [Ring S]
    (φ : R →+* S) (M : Matrix ι ι R) :
    (Matrix.reindex e e M).map φ = Matrix.reindex e e (M.map φ) := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply]

lemma kbic_map_kronMat {R S : Type} [Ring R] [Ring S] (φ : R →+* S) {n k : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (N : Matrix (Fin k) (Fin k) R) :
    (Work.KT.kronMat M N).map φ = Work.KT.kronMat (M.map φ) (N.map φ) := by
  ext i j
  simp only [Work.KT.kronMat, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.map_apply, Matrix.kroneckerMap_apply, map_mul]

lemma kbic_pairMat_kron {n k : ℕ}
    (A₀ A₁ : Matrix (Fin n) (Fin n) C(X × Work.KT.Ball ℂ, ℂ))
    (B₀ B₁ : Matrix (Fin k) (Fin k) C(X × Work.KT.Ball ℂ, ℂ))
    (hA : A₀.map (fun f => bdryRestrict X f) = A₁.map (fun f => bdryRestrict X f))
    (hB : B₀.map (fun f => bdryRestrict X f) = B₁.map (fun f => bdryRestrict X f))
    (h : (Work.KT.kronMat A₀ B₀).map (fun f => bdryRestrict X f)
        = (Work.KT.kronMat A₁ B₁).map (fun f => bdryRestrict X f)) :
    pairMat X (Work.KT.kronMat A₀ B₀) (Work.KT.kronMat A₁ B₁) h
      = Work.KT.kronMat (pairMat X A₀ A₁ hA) (pairMat X B₀ B₁ hB) := by
  apply mat_ext X
  · show (pairMat X (Work.KT.kronMat A₀ B₀) (Work.KT.kronMat A₁ B₁) h).map (prF X) = _
    simp only [pairMat_map_prF, kbic_map_kronMat]
  · show (pairMat X (Work.KT.kronMat A₀ B₀) (Work.KT.kronMat A₁ B₁) h).map (prS X) = _
    simp only [pairMat_map_prS, kbic_map_kronMat]

lemma kbic_map_diagPull {n : ℕ} (M : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    (M.map (diagPull X)).map (prF X) = M.map (KC.discHom X) := by
  ext i j
  rw [Matrix.map_apply, Matrix.map_apply]
  have h : diagPull X (M i j) = mkPair X (KC.discHom X (M i j)) (KC.discHom X (M i j)) rfl := by
    refine Subtype.ext (Prod.ext ?_ ?_)
    · ext p; rfl
    · ext p; rfl
  rw [h]
  rfl

lemma kbic_map_diagPull' {n : ℕ} (M : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    (M.map (diagPull X)).map (prS X) = M.map (KC.discHom X) := by
  ext i j
  rw [Matrix.map_apply, Matrix.map_apply]
  have h : diagPull X (M i j) = mkPair X (KC.discHom X (M i j)) (KC.discHom X (M i j)) rfl := by
    refine Subtype.ext (Prod.ext ?_ ?_)
    · ext p; rfl
    · ext p; rfl
  rw [h]
  rfl

/-- The diagonal embedding `C(X × D, ℂ) →+* pullAlg2 X`, `f ↦ (f, f)`. -/
def kbic_pairHom : C(X × Work.KT.Ball ℂ, ℂ) →+* ↥(pullAlg2 X) where
  toFun f := ⟨(f, f), rfl⟩
  map_one' := Subtype.ext rfl
  map_mul' a b := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' a b := Subtype.ext rfl

lemma kbic_diagPull_eq : diagPull X = (kbic_pairHom X).comp (KC.discHom X) := by
  refine RingHom.ext fun f => ?_
  refine Subtype.ext (Prod.ext ?_ ?_)
  · ext p; rfl
  · ext p; rfl

lemma kbic_pairMat_self {ι : Type} (M : Matrix ι ι C(X × Work.KT.Ball ℂ, ℂ))
    (h : M.map (fun f => bdryRestrict X f) = M.map (fun f => bdryRestrict X f)) :
    pairMat X M M h = M.map (kbic_pairHom X) := by
  refine Matrix.ext fun i j => ?_
  exact Subtype.ext rfl

lemma kbic_PR {n : ℕ} (P : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    PR X n P = pairMat X (Pd X n P) (Pd X n P)
      (rfl : (Pd X n P).map (fun f => bdryRestrict X f)
        = (Pd X n P).map (fun f => bdryRestrict X f)) := by
  show PR X n P = _
  rw [show PR X n P = P.map (diagPull X) from rfl]
  rw [kbic_diagPull_eq X]
  rw [← Work.KT.Bott.matrix_map_map (KC.discHom X) (kbic_pairHom X) P]
  show (Pd X n P).map (kbic_pairHom X) = pairMat X (Pd X n P) (Pd X n P) rfl
  exact (kbic_pairMat_self X (Pd X n P) rfl).symm

lemma kbic_QR {n : ℕ} (P : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    QR X n P = pairMat X (Qd X n P) (Qd X n P)
      (rfl : (Qd X n P).map (fun f => bdryRestrict X f)
        = (Qd X n P).map (fun f => bdryRestrict X f)) := by
  show QR X n P = _
  rw [show QR X n P = (1 - P).map (diagPull X) from rfl]
  rw [kbic_diagPull_eq X]
  rw [← Work.KT.Bott.matrix_map_map (KC.discHom X) (kbic_pairHom X) (1 - P)]
  rw [Matrix.map_sub (⇑(KC.discHom X)) (fun a b => map_sub (KC.discHom X) a b),
    Work.KT.Bott.matrix_map_one (KC.discHom X)]
  show (1 - Pd X n P).map (kbic_pairHom X) = pairMat X (Qd X n P) (Qd X n P) rfl
  exact (kbic_pairMat_self X (Qd X n P) rfl).symm

lemma kbic_E00_sq : E00 X * E00 X = E00 X := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [E00]

lemma kbic_pairMat_E00
    (h : (E00 X).map (fun f => bdryRestrict X f) = (E00 X).map (fun f => bdryRestrict X f)) :
    pairMat X (E00 X) (E00 X) h
      = Matrix.of (fun i j : Fin 2 => if i = 0 ∧ j = 0 then (1 : ↥(pullAlg2 X)) else 0) := by
  rw [kbic_pairMat_self X (E00 X) h]
  refine Matrix.ext fun i j => ?_
  show (kbic_pairHom X) (E00 X i j) = (if i = 0 ∧ j = 0 then (1 : ↥(pullAlg2 X)) else 0)
  rw [show E00 X i j = (if i = 0 ∧ j = 0 then (1 : C(X × Work.KT.Ball ℂ, ℂ)) else 0) from rfl]
  by_cases hij : i = 0 ∧ j = 0
  · rw [if_pos hij, if_pos hij]; exact map_one (kbic_pairHom X)
  · rw [if_neg hij, if_neg hij]; exact map_zero (kbic_pairHom X)

lemma kbic_reindex_cancel {ι ι' : Type} (e : ι ≃ ι')
    (M : Matrix ι' ι' C(X × Work.KT.Ball ℂ, ℂ)) :
    Matrix.reindex e e (Matrix.reindex e.symm e.symm M) = M := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.apply_symm_apply]

lemma kbic_pairIdem_eq
    (h1 : (h1e X).map (fun f => bdryRestrict X f) = (h2e X).map (fun f => bdryRestrict X f)) :
    pairIdem X (h1e X) (h2e X) h1
      = ⟨2, pairMat X (h1m X) (h2m X) ((kbi_hopfsq X).2.2)⟩ := by
  unfold pairIdem
  have hmat : Matrix.reindex finSumFinEquiv finSumFinEquiv (pairMat X (h1e X) (h2e X) h1)
      = pairMat X (h1m X) (h2m X) ((kbi_hopfsq X).2.2) := by
    apply mat_ext X
    · rw [kbic_map_reindex, pairMat_map_prF]
      show Matrix.reindex kbic_e kbic_e (Matrix.reindex kbic_e.symm kbic_e.symm (h1m X)) = h1m X
      exact kbic_reindex_cancel X kbic_e (h1m X)
    · rw [kbic_map_reindex, pairMat_map_prS]
      show Matrix.reindex kbic_e kbic_e (Matrix.reindex kbic_e.symm kbic_e.symm (h2m X)) = h2m X
      exact kbic_reindex_cancel X kbic_e (h2m X)
  exact Sigma.ext rfl (heq_of_eq hmat)

lemma kbic_pairIdem_snd
    (h1 : (h1e X).map (fun f => bdryRestrict X f) = (h2e X).map (fun f => bdryRestrict X f)) :
    pairMat X (h1m X) (h2m X) ((kbi_hopfsq X).2.2)
      = (pairIdem X (h1e X) (h2e X) h1).2 := by
  apply mat_ext X
  · rw [pairMat_map_prF]
    show h1m X = (Matrix.reindex finSumFinEquiv finSumFinEquiv
      (pairMat X (h1e X) (h2e X) h1)).map (prF X)
    rw [kbic_map_reindex, pairMat_map_prF]
    show h1m X = Matrix.reindex kbic_e kbic_e (Matrix.reindex kbic_e.symm kbic_e.symm (h1m X))
    exact (kbic_reindex_cancel X kbic_e (h1m X)).symm
  · rw [pairMat_map_prS]
    show h2m X = (Matrix.reindex finSumFinEquiv finSumFinEquiv
      (pairMat X (h1e X) (h2e X) h1)).map (prS X)
    rw [kbic_map_reindex, pairMat_map_prS]
    show h2m X = Matrix.reindex kbic_e kbic_e (Matrix.reindex kbic_e.symm kbic_e.symm (h2m X))
    exact (kbic_reindex_cancel X kbic_e (h2m X)).symm

/-! ## Kronecker products of disc matrices -/

lemma kbic_kronMat_mul {R : Type} [CommRing R] {n k : ℕ}
    (M M' : Matrix (Fin n) (Fin n) R) (N N' : Matrix (Fin k) (Fin k) R) :
    Work.KT.kronMat M N * Work.KT.kronMat M' N' = Work.KT.kronMat (M * M') (N * N') := by
  unfold Work.KT.kronMat
  rw [Work.KT.reindexMul finProdFinEquiv finProdFinEquiv finProdFinEquiv]
  rw [← Work.KT.kroneckerMap_mul (fun x y => mul_comm x y) M M' N N']

lemma kbic_kronMat_zero_left {R : Type} [Ring R] {n k : ℕ}
    (N : Matrix (Fin k) (Fin k) R) :
    Work.KT.kronMat (0 : Matrix (Fin n) (Fin n) R) N = 0 := by
  ext i j
  simp only [Work.KT.kronMat, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, Matrix.zero_apply, zero_mul]

/-! ## `p ⊗ E₀₀ ~ p` -/

lemma kbic_one_sub_sq {R : Type} [Ring R] {n : ℕ} {P : Matrix (Fin n) (Fin n) R}
    (hP : P * P = P) : (1 - P) * (1 - P) = 1 - P := by
  have h : (1 - P) * (1 - P) = 1 - P - (P - P * P) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
  rw [h, hP]
  abel

/-- The `2 × 2` matrix `diag(1, 0)`. -/
def kbic_E2 (R : Type) [Ring R] : Matrix (Fin 2) (Fin 2) R :=
  Matrix.of fun i j : Fin 2 => if i = 0 ∧ j = 0 then (1 : R) else 0

lemma kbic_E2_sq {R : Type} [Ring R] : kbic_E2 R * kbic_E2 R = kbic_E2 R := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [kbic_E2]

lemma kbic_E2_mvN_one {R : Type} [Ring R] :
    Work.KT.Mat.MvN (⟨2, kbic_E2 R⟩ : Work.KT.Mat R)
      (⟨1, (1 : Matrix (Fin 1) (Fin 1) R)⟩ : Work.KT.Mat R) := by
  refine ⟨(Matrix.of fun _ (j : Fin 2) => if j = 0 then (1 : R) else 0 : Matrix (Fin 1) (Fin 2) R),
    (Matrix.of fun (i : Fin 2) _ => if i = 0 then (1 : R) else 0 : Matrix (Fin 2) (Fin 1) R), ?_, ?_⟩
  · ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_one]
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [kbic_E2, hi, hj]
  · ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp

lemma kbic_E00_mvN {R : Type} [Ring R] (hcomm : ∀ x y : R, x * y = y * x)
    (p : Work.KT.Mat R) (hp : p.IsIdem) :
    Work.KT.Mat.MvN (p.kron (⟨2, kbic_E2 R⟩ : Work.KT.Mat R)) p := by
  have hE1 : Work.KT.Mat.MvN (⟨2, kbic_E2 R⟩ : Work.KT.Mat R) (Work.KT.Mat.one R 1) :=
    kbic_E2_mvN_one (R := R)
  have honeidem : Work.KT.Mat.IsIdem (Work.KT.Mat.one R 1) := by
    show (1 : Matrix (Fin 1) (Fin 1) R) * (1 : Matrix (Fin 1) (Fin 1) R) = 1
    rw [Matrix.mul_one]
  have hEidem : Work.KT.Mat.IsIdem (⟨2, kbic_E2 R⟩ : Work.KT.Mat R) := by
    show kbic_E2 R * kbic_E2 R = kbic_E2 R
    exact kbic_E2_sq
  have h2 : Work.KT.Mat.MvN (p.kron (⟨2, kbic_E2 R⟩ : Work.KT.Mat R))
      (p.kron (Work.KT.Mat.one R 1)) := Work.KT.mvN_kron_right hcomm hE1 hp
  have h31 : Work.KT.Mat.MvN (p.kron (Work.KT.Mat.one R 1))
      ((Work.KT.Mat.one R 1).kron p) := Work.KT.mvN_kron_comm hcomm p (Work.KT.Mat.one R 1)
  have h32 : Work.KT.Mat.MvN ((Work.KT.Mat.one R 1).kron p) p :=
    Work.KT.mvNassoc_kron_unit p
  have h3 : Work.KT.Mat.MvN (p.kron (Work.KT.Mat.one R 1)) p :=
    Work.KT.Mat.mvN_trans (Work.KT.Mat.kron_idem hcomm hp honeidem)
      (Work.KT.Mat.kron_idem hcomm honeidem hp) hp h31 h32
  exact Work.KT.Mat.mvN_trans (Work.KT.Mat.kron_idem hcomm hp hEidem)
    (Work.KT.Mat.kron_idem hcomm hp honeidem) hp h2 h3

/-! ## The main computation -/

theorem kbi_cls (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (P : Matrix (Fin n) (Fin n) C(X, ℂ)) (hP : P * P = P)
    (h1 : (Work.KT.Fund.KBI.h1e X).map (fun f => Work.KT.Fund.bdryRestrict X f) =
      (Work.KT.Fund.KBI.h2e X).map (fun f => Work.KT.Fund.bdryRestrict X f))
    (hW : (Work.KT.Fund.KBI.W1 X n P).map (fun f => Work.KT.Fund.bdryRestrict X f) =
      (Work.KT.Fund.KBI.W2 X n P).map (fun f => Work.KT.Fund.bdryRestrict X f))
    (μ : Work.KT.K0 ↥(Work.KT.Fund.pullAlg2 X) →+ Work.KT.K0 ↥(Work.KT.Fund.pullAlg2 X) →+
      Work.KT.K0 ↥(Work.KT.Fund.pullAlg2 X))
    (hμ : Work.KT.IsK0Mul μ) :
    Work.KT.cls (⟨n*2, Work.KT.Fund.pairMat X (Work.KT.Fund.KBI.W1 X n P)
        (Work.KT.Fund.KBI.W2 X n P) hW⟩ : Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X))
      = μ (Work.KT.cls (⟨n, Work.KT.Fund.KBI.PR X n P⟩ : Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X)))
            (Work.KT.cls (Work.KT.Fund.pairIdem X (Work.KT.Fund.KBI.h1e X)
              (Work.KT.Fund.KBI.h2e X) h1))
        + Work.KT.cls (⟨n, Work.KT.Fund.KBI.QR X n P⟩ : Work.KT.Mat ↥(Work.KT.Fund.pullAlg2 X)) := by
  let A₀ : Matrix (Fin (n*2)) (Fin (n*2)) C(X × Work.KT.Ball ℂ, ℂ) :=
    Work.KT.kronMat (Pd X n P) (h1m X)
  let A₁ : Matrix (Fin (n*2)) (Fin (n*2)) C(X × Work.KT.Ball ℂ, ℂ) :=
    Work.KT.kronMat (Pd X n P) (h2m X)
  let B₀ : Matrix (Fin (n*2)) (Fin (n*2)) C(X × Work.KT.Ball ℂ, ℂ) :=
    Work.KT.kronMat (Qd X n P) (E00 X)
  let B₁ : Matrix (Fin (n*2)) (Fin (n*2)) C(X × Work.KT.Ball ℂ, ℂ) :=
    Work.KT.kronMat (Qd X n P) (E00 X)
  have hW1k : W1 X n P = A₀ + B₀ := W1_eq_kron X n P
  have hW2k : W2 X n P = A₁ + B₁ := W2_eq_kron X n P
  have hsum : (A₀+B₀).map (fun f => bdryRestrict X f)
      = (A₁+B₁).map (fun f => bdryRestrict X f) := by
    rw [← hW1k, ← hW2k]; exact hW
  have hB : B₀.map (fun f => bdryRestrict X f) = B₁.map (fun f => bdryRestrict X f) := rfl
  have hA : A₀.map (fun f => bdryRestrict X f) = A₁.map (fun f => bdryRestrict X f) := by
    have h := hsum
    rw [show (fun f => bdryRestrict X f) = ⇑(bdryRestrict X) from rfl] at h
    rw [Matrix.map_add ⇑(bdryRestrict X) (fun a b => map_add (bdryRestrict X) a b),
      Matrix.map_add ⇑(bdryRestrict X) (fun a b => map_add (bdryRestrict X) a b)] at h
    rw [show B₀.map ⇑(bdryRestrict X) = B₁.map ⇑(bdryRestrict X) from rfl] at h
    exact add_right_cancel h
  let A : Matrix (Fin (n*2)) (Fin (n*2)) ↥(pullAlg2 X) := pairMat X A₀ A₁ hA
  let B : Matrix (Fin (n*2)) (Fin (n*2)) ↥(pullAlg2 X) := pairMat X B₀ B₁ hB
  have hPd : (Pd X n P).map (fun f => bdryRestrict X f)
      = (Pd X n P).map (fun f => bdryRestrict X f) := rfl
  have hQd : (Qd X n P).map (fun f => bdryRestrict X f)
      = (Qd X n P).map (fun f => bdryRestrict X f) := rfl
  have hE00glue : (E00 X).map (fun f => bdryRestrict X f)
      = (E00 X).map (fun f => bdryRestrict X f) := rfl
  have hA0sq : A₀ * A₀ = A₀ := by
    show Work.KT.kronMat (Pd X n P) (h1m X) * Work.KT.kronMat (Pd X n P) (h1m X)
      = Work.KT.kronMat (Pd X n P) (h1m X)
    rw [kbic_kronMat_mul, Pd_sq X n P hP, (kbi_hopfsq X).1]
  have hA1sq : A₁ * A₁ = A₁ := by
    show Work.KT.kronMat (Pd X n P) (h2m X) * Work.KT.kronMat (Pd X n P) (h2m X)
      = Work.KT.kronMat (Pd X n P) (h2m X)
    rw [kbic_kronMat_mul, Pd_sq X n P hP, (kbi_hopfsq X).2.1]
  have hB0sq : B₀ * B₀ = B₀ := by
    show Work.KT.kronMat (Qd X n P) (E00 X) * Work.KT.kronMat (Qd X n P) (E00 X)
      = Work.KT.kronMat (Qd X n P) (E00 X)
    rw [kbic_kronMat_mul, KBIFrameAux.Qd_mul_Qd X n P hP, kbic_E00_sq X]
  have hB1sq : B₁ * B₁ = B₁ := hB0sq
  have hAidem : Work.KT.Mat.IsIdem (⟨n*2, A⟩ : Work.KT.Mat ↥(pullAlg2 X)) := by
    show pairMat X A₀ A₁ hA * pairMat X A₀ A₁ hA = pairMat X A₀ A₁ hA
    exact kbic_pairMat_isIdem X A₀ A₁ hA hA0sq hA1sq
  have hBidem : Work.KT.Mat.IsIdem (⟨n*2, B⟩ : Work.KT.Mat ↥(pullAlg2 X)) := by
    show pairMat X B₀ B₁ hB * pairMat X B₀ B₁ hB = pairMat X B₀ B₁ hB
    exact kbic_pairMat_isIdem X B₀ B₁ hB hB0sq hB1sq
  have hA0B0 : A₀ * B₀ = 0 := by
    show Work.KT.kronMat (Pd X n P) (h1m X) * Work.KT.kronMat (Qd X n P) (E00 X) = 0
    rw [kbic_kronMat_mul, KBIFrameAux.Pd_mul_Qd X n P hP]
    exact kbic_kronMat_zero_left (h1m X * E00 X)
  have hA1B1 : A₁ * B₁ = 0 := by
    show Work.KT.kronMat (Pd X n P) (h2m X) * Work.KT.kronMat (Qd X n P) (E00 X) = 0
    rw [kbic_kronMat_mul, KBIFrameAux.Pd_mul_Qd X n P hP]
    exact kbic_kronMat_zero_left (h2m X * E00 X)
  have hB0A0 : B₀ * A₀ = 0 := by
    show Work.KT.kronMat (Qd X n P) (E00 X) * Work.KT.kronMat (Pd X n P) (h1m X) = 0
    rw [kbic_kronMat_mul, KBIFrameAux.Qd_mul_Pd X n P hP]
    exact kbic_kronMat_zero_left (E00 X * h1m X)
  have hB1A1 : B₁ * A₁ = 0 := by
    show Work.KT.kronMat (Qd X n P) (E00 X) * Work.KT.kronMat (Pd X n P) (h2m X) = 0
    rw [kbic_kronMat_mul, KBIFrameAux.Qd_mul_Pd X n P hP]
    exact kbic_kronMat_zero_left (E00 X * h2m X)
  have hzero : (0 : Matrix (Fin (n*2)) (Fin (n*2)) C(X × Work.KT.Ball ℂ, ℂ)).map
      (fun f => bdryRestrict X f)
      = (0 : Matrix (Fin (n*2)) (Fin (n*2)) C(X × Work.KT.Ball ℂ, ℂ)).map
        (fun f => bdryRestrict X f) := rfl
  have hAB0 : A * B = 0 := by
    show pairMat X A₀ A₁ hA * pairMat X B₀ B₁ hB = 0
    have hg : (A₀*B₀).map (fun f => bdryRestrict X f)
        = (A₁*B₁).map (fun f => bdryRestrict X f) := by
      rw [hA0B0, hA1B1]
    have hzero' : pairMat X (A₀*B₀) (A₁*B₁) hg = pairMat X 0 0 hzero :=
      kbic_pairMat_congr X _ _ _ _ hA0B0 hA1B1 hg hzero
    rw [← kbic_pairMat_mul X A₀ B₀ A₁ B₁ hA hB hg, hzero', kbic_pairMat_zero X hzero]
  have hBA0 : B * A = 0 := by
    show pairMat X B₀ B₁ hB * pairMat X A₀ A₁ hA = 0
    have hg : (B₀*A₀).map (fun f => bdryRestrict X f)
        = (B₁*A₁).map (fun f => bdryRestrict X f) := by
      rw [hB0A0, hB1A1]
    have hzero' : pairMat X (B₀*A₀) (B₁*A₁) hg = pairMat X 0 0 hzero :=
      kbic_pairMat_congr X _ _ _ _ hB0A0 hB1A1 hg hzero
    rw [← kbic_pairMat_mul X B₀ A₀ B₁ A₁ hB hA hg, hzero', kbic_pairMat_zero X hzero]
  have hAB : (⟨n*2, pairMat X (W1 X n P) (W2 X n P) hW⟩ : Work.KT.Mat ↥(pullAlg2 X))
      = ⟨n*2, A + B⟩ := by
    have h1' : pairMat X (W1 X n P) (W2 X n P) hW = pairMat X (A₀+B₀) (A₁+B₁) hsum :=
      kbic_pairMat_congr X _ _ _ _ hW1k hW2k hW hsum
    have h2' : pairMat X (A₀+B₀) (A₁+B₁) hsum = A + B :=
      kbic_pairMat_add X A₀ A₁ B₀ B₁ hA hB hsum
    rw [h1', h2']
  have hcomm : ∀ x y : ↥(pullAlg2 X), x * y = y * x := fun x y =>
    Subtype.ext (Prod.ext (mul_comm x.1.1 y.1.1) (mul_comm x.1.2 y.1.2))
  have hPRidem : Work.KT.Mat.IsIdem (⟨n, PR X n P⟩ : Work.KT.Mat ↥(pullAlg2 X)) := by
    show PR X n P * PR X n P = PR X n P
    rw [show PR X n P = P.map (diagPull X) from rfl]
    rw [← Matrix.map_mul (f := diagPull X), hP]
  have hQRidem : Work.KT.Mat.IsIdem (⟨n, QR X n P⟩ : Work.KT.Mat ↥(pullAlg2 X)) := by
    show QR X n P * QR X n P = QR X n P
    rw [show QR X n P = (1 - P).map (diagPull X) from rfl]
    rw [← Matrix.map_mul (f := diagPull X), kbic_one_sub_sq hP]
  have hHopfidem : Work.KT.Mat.IsIdem (pairIdem X (h1e X) (h2e X) h1) := by
    rw [kbic_pairIdem_eq X h1]
    show pairMat X (h1m X) (h2m X) ((kbi_hopfsq X).2.2)
        * pairMat X (h1m X) (h2m X) ((kbi_hopfsq X).2.2)
      = pairMat X (h1m X) (h2m X) ((kbi_hopfsq X).2.2)
    exact kbic_pairMat_isIdem X (h1m X) (h2m X) ((kbi_hopfsq X).2.2)
      (kbi_hopfsq X).1 (kbi_hopfsq X).2.1
  have hE2idem : Work.KT.Mat.IsIdem (⟨2, Matrix.of fun i j : Fin 2 =>
      if i = 0 ∧ j = 0 then (1 : ↥(pullAlg2 X)) else 0⟩ : Work.KT.Mat ↥(pullAlg2 X)) := by
    show kbic_E2 ↥(pullAlg2 X) * kbic_E2 ↥(pullAlg2 X) = kbic_E2 ↥(pullAlg2 X)
    exact kbic_E2_sq
  have hAeq : A = Work.KT.kronMat (PR X n P) ((pairIdem X (h1e X) (h2e X) h1).2) := by
    show pairMat X (Work.KT.kronMat (Pd X n P) (h1m X))
      (Work.KT.kronMat (Pd X n P) (h2m X)) hA = _
    rw [kbic_pairMat_kron X (Pd X n P) (Pd X n P) (h1m X) (h2m X) hPd ((kbi_hopfsq X).2.2) hA]
    rw [show pairMat X (Pd X n P) (Pd X n P) hPd = PR X n P from
          (kbic_pairMat_irrel X _ _ hPd rfl).trans (kbic_PR X P).symm]
    exact congrArg (fun M => Work.KT.kronMat (PR X n P) M) (kbic_pairIdem_snd X h1)
  have hAcls : Work.KT.cls (⟨n*2, A⟩ : Work.KT.Mat ↥(pullAlg2 X))
      = μ (Work.KT.cls (⟨n, PR X n P⟩ : Work.KT.Mat ↥(pullAlg2 X)))
          (Work.KT.cls (pairIdem X (h1e X) (h2e X) h1)) := by
    have hmat : (⟨n*2, A⟩ : Work.KT.Mat ↥(pullAlg2 X))
        = Work.KT.Mat.kron (⟨n, PR X n P⟩ : Work.KT.Mat ↥(pullAlg2 X))
            (pairIdem X (h1e X) (h2e X) h1) := by
      refine Sigma.ext rfl (heq_of_eq ?_)
      show A = Work.KT.kronMat (PR X n P) ((pairIdem X (h1e X) (h2e X) h1).2)
      exact hAeq
    rw [hmat, Work.KT.IsK0Mul_cls hμ hPRidem hHopfidem]
  have hBeq : B = Work.KT.kronMat (QR X n P) (Matrix.of fun i j : Fin 2 =>
      if i = 0 ∧ j = 0 then (1 : ↥(pullAlg2 X)) else 0) := by
    show pairMat X (Work.KT.kronMat (Qd X n P) (E00 X))
      (Work.KT.kronMat (Qd X n P) (E00 X)) hB = _
    rw [kbic_pairMat_kron X (Qd X n P) (Qd X n P) (E00 X) (E00 X) hQd hE00glue hB]
    rw [show pairMat X (Qd X n P) (Qd X n P) hQd = QR X n P from
          (kbic_pairMat_irrel X _ _ hQd rfl).trans (kbic_QR X P).symm]
    exact congrArg (fun M => Work.KT.kronMat (QR X n P) M) (kbic_pairMat_E00 X hE00glue)
  have hBcls : Work.KT.cls (⟨n*2, B⟩ : Work.KT.Mat ↥(pullAlg2 X))
      = Work.KT.cls (⟨n, QR X n P⟩ : Work.KT.Mat ↥(pullAlg2 X)) := by
    have hmat : (⟨n*2, B⟩ : Work.KT.Mat ↥(pullAlg2 X))
        = Work.KT.Mat.kron (⟨n, QR X n P⟩ : Work.KT.Mat ↥(pullAlg2 X))
            (⟨2, Matrix.of fun i j : Fin 2 =>
              if i = 0 ∧ j = 0 then (1 : ↥(pullAlg2 X)) else 0⟩ : Work.KT.Mat ↥(pullAlg2 X)) := by
      refine Sigma.ext rfl (heq_of_eq ?_)
      show B = Work.KT.kronMat (QR X n P) (Matrix.of fun i j : Fin 2 =>
        if i = 0 ∧ j = 0 then (1 : ↥(pullAlg2 X)) else 0)
      exact hBeq
    rw [hmat]
    exact Work.KT.cls_eq_of_mvN (Work.KT.Mat.kron_idem hcomm hQRidem hE2idem) hQRidem
      (kbic_E00_mvN hcomm (⟨n, QR X n P⟩ : Work.KT.Mat ↥(pullAlg2 X)) hQRidem)
  have hABidem : Work.KT.Mat.IsIdem (⟨n*2, A + B⟩ : Work.KT.Mat ↥(pullAlg2 X)) := by
    show (A + B) * (A + B) = A + B
    calc (A + B) * (A + B) = A * A + A * B + (B * A + B * B) := by
          rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
      _ = A + B := by
          rw [show A * A = A from hAidem, show B * B = B from hBidem, hAB0, hBA0]
          abel
  have hor : Work.KT.Mat.MvN (⟨n*2, A + B⟩ : Work.KT.Mat ↥(pullAlg2 X))
      (Work.KT.Mat.sum ⟨n*2, A⟩ ⟨n*2, B⟩) :=
    kbi_or_sum (n*2) A B hAidem hBidem hAB0 hBA0
  have hsumcls : Work.KT.cls (⟨n*2, A + B⟩ : Work.KT.Mat ↥(pullAlg2 X))
      = Work.KT.cls (⟨n*2, A⟩ : Work.KT.Mat ↥(pullAlg2 X))
        + Work.KT.cls (⟨n*2, B⟩ : Work.KT.Mat ↥(pullAlg2 X)) := by
    rw [Work.KT.cls_eq_of_mvN hABidem (Work.KT.Mat.sum_idem hAidem hBidem) hor,
      Work.KT.cls_sum hAidem hBidem]
  rw [hAB, hsumcls, hAcls, hBcls]

end

end Work.KT.Fund
