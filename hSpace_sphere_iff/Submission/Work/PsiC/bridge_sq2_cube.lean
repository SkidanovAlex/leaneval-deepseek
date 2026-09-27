import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.PsiC.bridge_defs

namespace Work.PsiC

open Matrix Work.KT.PsiC

noncomputable section

variable {A : Type} [Ring A] [Algebra ℂ A]

/-! ## Bilinearity of `kroneckerMap` in the form needed below -/

theorem kronMap_add_left {ι κ : Type} (X Y : Matrix ι ι A) (Z : Matrix κ κ A) :
    Matrix.kroneckerMap (fun x y : A => x * y) (X + Y) Z =
      Matrix.kroneckerMap (fun x y : A => x * y) X Z +
        Matrix.kroneckerMap (fun x y : A => x * y) Y Z :=
  Matrix.kroneckerMap_add_left (· * ·) (fun a b c => add_mul a b c) X Y Z

theorem kronMap_add_right {ι κ : Type} (X : Matrix ι ι A) (Y Z : Matrix κ κ A) :
    Matrix.kroneckerMap (fun x y : A => x * y) X (Y + Z) =
      Matrix.kroneckerMap (fun x y : A => x * y) X Y +
        Matrix.kroneckerMap (fun x y : A => x * y) X Z :=
  Matrix.kroneckerMap_add_right (· * ·) (fun a b c => mul_add a b c) X Y Z

theorem kronMap_smul_left {ι κ : Type} (c : A) (X : Matrix ι ι A) (Z : Matrix κ κ A) :
    Matrix.kroneckerMap (fun x y : A => x * y) (c • X) Z =
      c • Matrix.kroneckerMap (fun x y : A => x * y) X Z :=
  Matrix.kroneckerMap_smul_left (· * ·) c (fun a b => mul_assoc c a b) X Z

theorem kronMap_smul_right (hA : ∀ x y : A, x * y = y * x) {ι κ : Type} (c : A)
    (X : Matrix ι ι A) (Z : Matrix κ κ A) :
    Matrix.kroneckerMap (fun x y : A => x * y) X (c • Z) =
      c • Matrix.kroneckerMap (fun x y : A => x * y) X Z :=
  Matrix.kroneckerMap_smul_right (· * ·) c
    (fun a b => by show a * (c * b) = c * (a * b); rw [← mul_assoc, hA a c, mul_assoc]) X Z

theorem kronMap_one_one {ι κ : Type} [DecidableEq ι] [DecidableEq κ] :
    Matrix.kroneckerMap (fun x y : A => x * y) (1 : Matrix ι ι A) (1 : Matrix κ κ A) = 1 :=
  Matrix.kroneckerMap_one_one (· * ·) (fun b => zero_mul b) (fun a => mul_zero a) (one_mul 1)

/-! ## The cyclic projector under `⊗ 1` and `1 ⊗ ·` -/

theorem kron_cycProj_one_left (hA : ∀ x y : A, x * y = y * x) (n : ℕ) (lam : ℂ) :
    Matrix.kroneckerMap (fun x y : A => x * y)
        (Work.KT.PsiC.cycProj (A := A) (Work.KT.cycPermP n) lam)
        (1 : Matrix (Work.KT.PsiC.I3 n) (Work.KT.PsiC.I3 n) A) =
      Work.KT.PsiC.cycProj (A := A) (Work.KT.PsiC.c1A n) lam := by
  have hPm : (Work.KT.PsiC.c1A n).permMatrix A =
      Matrix.kroneckerMap (fun x y : A => x * y) ((Work.KT.cycPermP n).permMatrix A)
        (1 : Matrix (Work.KT.PsiC.I3 n) (Work.KT.PsiC.I3 n) A) := by
    rw [show Work.KT.PsiC.c1A n =
        Equiv.prodCongr (Work.KT.cycPermP n) (Equiv.refl (Work.KT.PsiC.I3 n)) from rfl,
      ← Work.KT.PsiC.kroneckerMap_permMatrix', Matrix.permMatrix_refl]
  unfold Work.KT.PsiC.cycProj
  rw [hPm]
  simp only [kronMap_smul_left, kronMap_add_left, kronMap_one_one]
  rw [kron_mul'' hA, Matrix.mul_one]

theorem kron_cycProj_one_right (hA : ∀ x y : A, x * y = y * x) (n : ℕ) (lam : ℂ) :
    Matrix.kroneckerMap (fun x y : A => x * y)
        (1 : Matrix (Work.KT.PsiC.I3 n) (Work.KT.PsiC.I3 n) A)
        (Work.KT.PsiC.cycProj (A := A) (Work.KT.cycPermP n) lam) =
      Work.KT.PsiC.cycProj (A := A) (Work.KT.PsiC.c2A n) lam := by
  have hPm : (Work.KT.PsiC.c2A n).permMatrix A =
      Matrix.kroneckerMap (fun x y : A => x * y)
        (1 : Matrix (Work.KT.PsiC.I3 n) (Work.KT.PsiC.I3 n) A)
        ((Work.KT.cycPermP n).permMatrix A) := by
    rw [show Work.KT.PsiC.c2A n =
        Equiv.prodCongr (Equiv.refl (Work.KT.PsiC.I3 n)) (Work.KT.cycPermP n) from rfl,
      ← Work.KT.PsiC.kroneckerMap_permMatrix', Matrix.permMatrix_refl]
  unfold Work.KT.PsiC.cycProj
  rw [hPm]
  simp only [kronMap_smul_right hA, kronMap_add_left, kronMap_add_right, kronMap_one_one]
  rw [kron_mul'' hA, Matrix.one_mul]

/-! ## The main matrix identity of frame A -/

theorem _kron_cycProj_self (hA : ∀ x y : A, x * y = y * x) (p : Work.KT.Mat A) (lam : ℂ) :
    Matrix.kroneckerMap (fun x y : A => x * y)
        (Work.KT.PsiC.cycProj (A := A) (Work.KT.cycPermP p.1) lam)
        (Work.KT.PsiC.cycProj (A := A) (Work.KT.cycPermP p.1) lam) =
      Work.KT.PsiC.cycProj (A := A) (Work.KT.PsiC.c1A p.1) lam *
        Work.KT.PsiC.cycProj (A := A) (Work.KT.PsiC.c2A p.1) lam := by
  have h1 := kron_cycProj_one_left (A := A) hA p.1 lam
  have h2 := kron_cycProj_one_right (A := A) hA p.1 lam
  calc Matrix.kroneckerMap (fun x y : A => x * y)
        (Work.KT.PsiC.cycProj (A := A) (Work.KT.cycPermP p.1) lam)
        (Work.KT.PsiC.cycProj (A := A) (Work.KT.cycPermP p.1) lam)
      = Matrix.kroneckerMap (fun x y : A => x * y)
          (Work.KT.PsiC.cycProj (A := A) (Work.KT.cycPermP p.1) lam * 1)
          (1 * Work.KT.PsiC.cycProj (A := A) (Work.KT.cycPermP p.1) lam) := by
        rw [Matrix.mul_one, Matrix.one_mul]
    _ = Matrix.kroneckerMap (fun x y : A => x * y)
          (Work.KT.PsiC.cycProj (A := A) (Work.KT.cycPermP p.1) lam)
          (1 : Matrix (Work.KT.PsiC.I3 p.1) (Work.KT.PsiC.I3 p.1) A) *
        Matrix.kroneckerMap (fun x y : A => x * y)
          (1 : Matrix (Work.KT.PsiC.I3 p.1) (Work.KT.PsiC.I3 p.1) A)
          (Work.KT.PsiC.cycProj (A := A) (Work.KT.cycPermP p.1) lam) :=
        (kron_mul'' hA _ _ _ _).symm
    _ = Work.KT.PsiC.cycProj (A := A) (Work.KT.PsiC.c1A p.1) lam *
        Work.KT.PsiC.cycProj (A := A) (Work.KT.PsiC.c2A p.1) lam := by rw [h1, h2]

/-! ## The frame-A computation of `ψ²ψ³` on a generator -/

theorem _sq2_cubePart_frameA (hA : ∀ x y : A, x * y = y * x) (p : Work.KT.Mat A)
    (eps lam : ℂ) :
    Work.KT.cls (Work.KT.sq2Part eps (Work.KT.cubePart lam p)) =
      Work.KT.Psi.clsM (Work.KT.PsiC.IA p.1) (VA (A := A) p eps lam) := by
  set e : Work.KT.PsiC.I3 p.1 ≃ Fin (p.1 * p.1 * p.1) := (Work.KT.cycIdx p.1).symm with he
  have hconj : (Equiv.prodCongr e e).symm.trans
        ((Work.KT.PsiC.sA p.1).trans (Equiv.prodCongr e e)) =
      Equiv.prodComm (Fin (p.1 * p.1 * p.1)) (Fin (p.1 * p.1 * p.1)) := by
    apply Equiv.ext
    intro x
    rcases x with ⟨a, b⟩
    simp [Work.KT.PsiC.sA]
  have hhalf : Work.KT.PsiC.halfProj (A := A) eps
        (Equiv.prodComm (Fin (p.1 * p.1 * p.1)) (Fin (p.1 * p.1 * p.1))) =
      Matrix.reindex (Equiv.prodCongr e e) (Equiv.prodCongr e e)
        (Work.KT.PsiC.halfProj (A := A) eps (Work.KT.PsiC.sA p.1)) := by
    rw [Work.KT.PsiC.reindex_halfProj, hconj]
  have hkr : Matrix.kroneckerMap (fun x y : A => x * y)
        (Work.KT.cubePartP lam p) (Work.KT.cubePartP lam p) *
        Work.KT.PsiC.halfProj (A := A) eps (Work.KT.PsiC.sA p.1) =
      Work.KT.PsiC.PA p * (Matrix.kroneckerMap (fun x y : A => x * y)
        (Work.KT.PsiC.cycProj (A := A) (Work.KT.cycPermP p.1) lam)
        (Work.KT.PsiC.cycProj (A := A) (Work.KT.cycPermP p.1) lam) *
        Work.KT.PsiC.halfProj (A := A) eps (Work.KT.PsiC.sA p.1)) := by
    rw [show Matrix.kroneckerMap (fun x y : A => x * y)
          (Work.KT.cubePartP lam p) (Work.KT.cubePartP lam p) =
        Work.KT.PsiC.PA p * Matrix.kroneckerMap (fun x y : A => x * y)
          (Work.KT.PsiC.cycProj (A := A) (Work.KT.cycPermP p.1) lam)
          (Work.KT.PsiC.cycProj (A := A) (Work.KT.cycPermP p.1) lam) from by
      rw [show Work.KT.cubePartP lam p =
          Matrix.kroneckerMap (fun x y : A => x * y)
            (Matrix.kroneckerMap (fun x y : A => x * y) p.2 p.2) p.2 *
          Work.KT.PsiC.cycProj (A := A) (Work.KT.cycPermP p.1) lam from rfl]
      rw [(kron_mul'' hA _ _ _ _).symm]
      rfl]
    rw [mul_assoc]
  have hq : Work.KT.cubePart lam p =
      (⟨p.1 * p.1 * p.1, Matrix.reindex e e (Work.KT.cubePartP lam p)⟩ :
        Work.KT.Mat A) := by
    rw [Work.KT.cubePart_eq]
  have hmat : Matrix.kroneckerMap (fun x y : A => x * y)
        (Matrix.reindex e e (Work.KT.cubePartP lam p))
        (Matrix.reindex e e (Work.KT.cubePartP lam p)) *
        Work.KT.PsiC.halfProj (A := A) eps
          (Equiv.prodComm (Fin (p.1 * p.1 * p.1)) (Fin (p.1 * p.1 * p.1))) =
      Matrix.reindex (Equiv.prodCongr e e) (Equiv.prodCongr e e) (VA (A := A) p eps lam) := by
    rw [Matrix.kroneckerMap_reindex]
    rw [hhalf]
    rw [← Work.KT.reindex_mul' (Equiv.prodCongr e e)
      (Matrix.kroneckerMap (fun x y : A => x * y)
        (Work.KT.cubePartP lam p) (Work.KT.cubePartP lam p))
      (Work.KT.PsiC.halfProj (A := A) eps (Work.KT.PsiC.sA p.1))]
    rw [hkr]
    rfl
  rw [show Work.KT.cls (Work.KT.sq2Part eps (Work.KT.cubePart lam p)) =
      Work.KT.cls (Work.KT.sq2Part eps (⟨p.1 * p.1 * p.1,
        Matrix.reindex e e (Work.KT.cubePartP lam p)⟩ : Work.KT.Mat A)) from
    congrArg (fun q => Work.KT.cls (Work.KT.sq2Part eps q)) hq]
  rw [cls_sq2Part_eq_clsM_aux eps (⟨p.1 * p.1 * p.1,
        Matrix.reindex e e (Work.KT.cubePartP lam p)⟩ : Work.KT.Mat A)]
  rw [sq2PartP_eq_explicit eps (p.1 * p.1 * p.1) (Matrix.reindex e e (Work.KT.cubePartP lam p))]
  rw [hmat]
  exact clsM_reindex_aux (A := A) (Equiv.prodCongr e e) (VA (A := A) p eps lam)

/-! ## The frame change -/

theorem reindex_Phi_VA (hA : ∀ x y : A, x * y = y * x) (p : Work.KT.Mat A) (eps lam : ℂ) :
    Matrix.reindex (Work.KT.PsiC.Phi p.1) (Work.KT.PsiC.Phi p.1) (VA (A := A) p eps lam) =
      VB (A := A) p eps lam := by
  simp only [VA, VB]
  rw [Work.KT.reindex_mul', Work.KT.reindex_mul']
  rw [Work.KT.PsiC.reindex_Phi_PA (A := A) p hA]
  rw [_kron_cycProj_self (A := A) hA p lam]
  rw [Work.KT.reindex_mul', reindex_Phi_cycProj_c1A, reindex_Phi_cycProj_c2A,
    reindex_Phi_halfProj_sA]
  simp only [mul_assoc]

end

theorem bridge_sq2_cube (A : Type) [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    (p : Work.KT.Mat A) (hp : p.IsIdem) (eps lam : ℂ) (heps : eps ^ 2 = 1) (hlam : lam ^ 3 = 1) :
    Work.KT.cls (Work.KT.sq2Part eps (Work.KT.cubePart lam p)) =
      Work.KT.Psi.clsM (Work.KT.PsiC.IB p.1)
        (Work.KT.PsiC.PB p * (Work.KT.PsiC.cycProj (Work.KT.PsiC.uB p.1) lam *
          Work.KT.PsiC.cycProj (Work.KT.PsiC.vB p.1) lam) *
          Work.KT.PsiC.halfProj eps (Work.KT.PsiC.sB p.1)) := by
  rw [_sq2_cubePart_frameA (A := A) hA p eps lam]
  rw [← clsM_reindex_aux (A := A) (Work.KT.PsiC.Phi p.1) (VA (A := A) p eps lam)]
  rw [reindex_Phi_VA (A := A) hA p eps lam]
  rfl

end Work.PsiC
