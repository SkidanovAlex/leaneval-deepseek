import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.PsiC.BFrame
import Submission.Work.KT.Psi.cubePart_idem
import Submission.Work.KT.Psi.sq2Part_idem

/-!
# `Work.PsiC.bridge_cube_sq2`

The class of `cubePart λ (sq2Part ε p)` (the sixfold tensor power `p^{⊗6}` in the bracketing
`((p⊗p)⊗(p⊗p))⊗(p⊗p)`, cut down by the joint `ε`-projector of the three pair swaps and by the
`λ`-projector of the pair cycle) equals the class of
`PB p * Eeps ε p.1 * cycProj (cB p.1) λ` in the frame-B index type `IB p.1`,
i.e. the same sixfold tensor power with the projectors pulled out in front.

The proof goes through three independent computations:

* `BridgeCS2.kron3_sq2PartP` : `kron3 (sq2PartP ε p) = PB p * Eeps ε p.1` (Kronecker bookkeeping);
* `BridgeCS2.reindex_cubePartP` : the reindexing of `cubePartP λ (sq2Part ε p)` to `IB p.1`;
* `BridgeCS2.cls_cubePart_sq2_eq` : the `cls`/`clsM` bookkeeping.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Work.PsiC

namespace BridgeCS2

open Matrix Work.KT Work.KT.Psi Work.KT.PsiC

noncomputable section

variable {A : Type} [Ring A] [Algebra ℂ A]

/-- Triple Kronecker product over the frame-B index type. -/
def kron3 {n : ℕ} (X : Matrix (I2 n) (I2 n) A) : Matrix (IB n) (IB n) A :=
  kroneckerMap (· * ·) (kroneckerMap (· * ·) X X) X

theorem kronMap_add_left {ι κ : Type} (X Y : Matrix ι ι A) (Z : Matrix κ κ A) :
    kroneckerMap (· * ·) (X + Y) Z =
      kroneckerMap (· * ·) X Z + kroneckerMap (· * ·) Y Z :=
  Matrix.kroneckerMap_add_left (· * ·) (fun a b c => add_mul a b c) X Y Z

theorem kronMap_add_right {ι κ : Type} (X : Matrix ι ι A) (Y Z : Matrix κ κ A) :
    kroneckerMap (· * ·) X (Y + Z) =
      kroneckerMap (· * ·) X Y + kroneckerMap (· * ·) X Z :=
  Matrix.kroneckerMap_add_right (· * ·) (fun a b c => mul_add a b c) X Y Z

theorem kronMap_smul_left {ι κ : Type} (c : A) (X : Matrix ι ι A) (Z : Matrix κ κ A) :
    kroneckerMap (· * ·) (c • X) Z = c • kroneckerMap (· * ·) X Z :=
  Matrix.kroneckerMap_smul_left (· * ·) c (fun a b => mul_assoc c a b) X Z

theorem kronMap_smul_right (hA : ∀ x y : A, x * y = y * x) {ι κ : Type} (c : A)
    (X : Matrix ι ι A) (Z : Matrix κ κ A) :
    kroneckerMap (· * ·) X (c • Z) = c • kroneckerMap (· * ·) X Z :=
  Matrix.kroneckerMap_smul_right (· * ·) c
    (fun a b => by show a * (c * b) = c * (a * b); rw [← mul_assoc, hA a c, mul_assoc]) X Z

theorem kronMap_one_one {ι κ : Type} [DecidableEq ι] [DecidableEq κ] :
    kroneckerMap (· * ·) (1 : Matrix ι ι A) (1 : Matrix κ κ A) = 1 :=
  Matrix.kroneckerMap_one_one (· * ·) (fun b => zero_mul b) (fun a => mul_zero a) (one_mul 1)

theorem permMatrix_sg0 (n : ℕ) :
    (sg0 n).permMatrix A =
      kroneckerMap (· * ·) (kroneckerMap (· * ·)
        (Equiv.Perm.permMatrix A (Equiv.prodComm (Fin n) (Fin n))) 1) 1 := by
  rw [show sg0 n = Equiv.prodCongr (Equiv.prodCongr (Equiv.prodComm (Fin n) (Fin n))
      (Equiv.refl (I2 n))) (Equiv.refl (I2 n)) from rfl]
  rw [← kroneckerMap_permMatrix', ← kroneckerMap_permMatrix']
  simp [Matrix.permMatrix_refl]

theorem permMatrix_sg1 (n : ℕ) :
    (sg1 n).permMatrix A =
      kroneckerMap (· * ·) (kroneckerMap (· * ·) 1
        (Equiv.Perm.permMatrix A (Equiv.prodComm (Fin n) (Fin n)))) 1 := by
  rw [show sg1 n = Equiv.prodCongr (Equiv.prodCongr (Equiv.refl (I2 n))
      (Equiv.prodComm (Fin n) (Fin n))) (Equiv.refl (I2 n)) from rfl]
  rw [← kroneckerMap_permMatrix', ← kroneckerMap_permMatrix']
  simp [Matrix.permMatrix_refl]

theorem permMatrix_sg2 (n : ℕ) :
    (sg2 n).permMatrix A =
      kroneckerMap (· * ·) (kroneckerMap (· * ·) 1 1)
        (Equiv.Perm.permMatrix A (Equiv.prodComm (Fin n) (Fin n))) := by
  rw [show sg2 n = Equiv.prodCongr (Equiv.prodCongr (Equiv.refl (I2 n))
      (Equiv.refl (I2 n))) (Equiv.prodComm (Fin n) (Fin n)) from rfl]
  rw [← kroneckerMap_permMatrix', ← kroneckerMap_permMatrix']
  simp [Matrix.permMatrix_refl]

theorem halfProj_sg0 (n : ℕ) (eps : ℂ) :
    halfProj (A := A) eps (sg0 n) =
      kroneckerMap (· * ·) (kroneckerMap (· * ·)
        (halfProj (A := A) eps (Equiv.prodComm (Fin n) (Fin n))) 1) 1 := by
  unfold halfProj
  rw [permMatrix_sg0]
  simp only [kronMap_add_left, kronMap_smul_left, kronMap_one_one]

theorem halfProj_sg1 (hA : ∀ x y : A, x * y = y * x) (n : ℕ) (eps : ℂ) :
    halfProj (A := A) eps (sg1 n) =
      kroneckerMap (· * ·) (kroneckerMap (· * ·) 1
        (halfProj (A := A) eps (Equiv.prodComm (Fin n) (Fin n)))) 1 := by
  unfold halfProj
  rw [permMatrix_sg1]
  simp only [kronMap_add_left, kronMap_add_right, kronMap_smul_left,
    kronMap_smul_right hA, kronMap_one_one]

theorem halfProj_sg2 (hA : ∀ x y : A, x * y = y * x) (n : ℕ) (eps : ℂ) :
    halfProj (A := A) eps (sg2 n) =
      kroneckerMap (· * ·) (kroneckerMap (· * ·) 1 1)
        (halfProj (A := A) eps (Equiv.prodComm (Fin n) (Fin n))) := by
  unfold halfProj
  rw [permMatrix_sg2]
  simp only [kronMap_add_left, kronMap_add_right, kronMap_smul_left,
    kronMap_smul_right hA, kronMap_one_one]

/-- Multiplication of two "three-slot" Kronecker products. -/
theorem kron3_slot_mul (hA : ∀ x y : A, x * y = y * x) {γ : Type} [Fintype γ] [DecidableEq γ]
    (X0 X1 X2 Y0 Y1 Y2 : Matrix γ γ A) :
    kroneckerMap (· * ·) (kroneckerMap (· * ·) X0 X1) X2 *
      kroneckerMap (· * ·) (kroneckerMap (· * ·) Y0 Y1) Y2 =
      kroneckerMap (· * ·) (kroneckerMap (· * ·) (X0 * Y0) (X1 * Y1)) (X2 * Y2) := by
  rw [kron_mul'' (A := A) hA, kron_mul'' (A := A) hA]

/-- **`Eeps` as a triple Kronecker product.** -/
theorem Eeps_eq_kron3 (hA : ∀ x y : A, x * y = y * x) (n : ℕ) (eps : ℂ) :
    Eeps (A := A) eps n =
      kron3 (A := A) (halfProj (A := A) eps (Equiv.prodComm (Fin n) (Fin n))) := by
  have h0 := halfProj_sg0 (A := A) n eps
  have h1 := halfProj_sg1 (A := A) hA n eps
  have h2 := halfProj_sg2 (A := A) hA n eps
  show halfProj eps (sg0 n) * halfProj eps (sg1 n) * halfProj eps (sg2 n) = kron3 _
  rw [h0, h1, h2]
  unfold kron3
  rw [kron3_slot_mul (A := A) hA, kron3_slot_mul (A := A) hA]
  simp only [Matrix.mul_one, Matrix.one_mul]

/-- **`ψ³` on `sq2PartP` in Kronecker form.** -/
theorem kron3_sq2PartP (hA : ∀ x y : A, x * y = y * x) (p : Mat A) (eps : ℂ) :
    kron3 (A := A) (sq2PartP eps p) = PB p * Eeps (A := A) eps p.1 := by
  have hSP : sq2PartP eps p = kroneckerMap (· * ·) p.2 p.2 *
      halfProj (A := A) eps (Equiv.prodComm (Fin p.1) (Fin p.1)) := rfl
  rw [hSP, Eeps_eq_kron3 (A := A) hA]
  unfold kron3 PB
  rw [← kron3_slot_mul (A := A) hA]

/-- Reindexing of the `cycProj` of `cycPermP` to `cycProj (cB n)`. -/
theorem reindex_cycProj_cycPermP (n : ℕ) (lam : ℂ) :
    Matrix.reindex (cBIdx n).symm (cBIdx n).symm
        (cycProj (A := A) (cycPermP (n * n)) lam) = cycProj (A := A) (cB n) lam := by
  rw [reindex_cycProj]
  congr 1

/-- **Reindexing bridge** for `cubePartP ∘ sq2Part`. -/
theorem reindex_cubePartP (p : Mat A) (eps lam : ℂ) :
    Matrix.reindex (cBIdx p.1).symm (cBIdx p.1).symm (cubePartP lam (sq2Part eps p)) =
      kron3 (A := A) (sq2PartP eps p) * cycProj (A := A) (cB p.1) lam := by
  have hS : (sq2Part eps p).2 =
      Matrix.reindex finProdFinEquiv finProdFinEquiv (sq2PartP eps p) :=
    (sq2Part_reindex eps p).symm
  have hrf : Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm
      (Matrix.reindex finProdFinEquiv finProdFinEquiv (sq2PartP eps p)) = sq2PartP eps p := by
    rw [reindex_reindex, Equiv.self_trans_symm, Matrix.reindex_refl_refl]
  have hcBInv : (cBIdx p.1).symm =
      Equiv.prodCongr (Equiv.prodCongr finProdFinEquiv.symm finProdFinEquiv.symm)
        finProdFinEquiv.symm := by
    rw [cBIdx, Equiv.prodCongr_symm, Equiv.prodCongr_symm]
  have hproj : Matrix.reindex (cBIdx p.1).symm (cBIdx p.1).symm
      (cycProj (A := A) (cycPermP ((sq2Part eps p).1)) lam) =
      cycProj (A := A) (cB p.1) lam :=
    reindex_cycProj_cycPermP (A := A) p.1 lam
  show Matrix.reindex (cBIdx p.1).symm (cBIdx p.1).symm
      (kroneckerMap (· * ·) (kroneckerMap (· * ·) (sq2Part eps p).2 (sq2Part eps p).2)
        (sq2Part eps p).2 *
        cycProj (A := A) (cycPermP ((sq2Part eps p).1)) lam) = _
  erw [hS]
  erw [reindex_mul']
  erw [hproj]
  congr 1
  erw [hcBInv]
  erw [← kroneckerMap_reindex (· * ·)
        (Equiv.prodCongr finProdFinEquiv.symm finProdFinEquiv.symm)
        (Equiv.prodCongr finProdFinEquiv.symm finProdFinEquiv.symm)
        finProdFinEquiv.symm finProdFinEquiv.symm]
  erw [← kroneckerMap_reindex (· * ·) finProdFinEquiv.symm finProdFinEquiv.symm
        finProdFinEquiv.symm finProdFinEquiv.symm, hrf]
  rfl

/-- Unconditional invariance of `cls` under reindexing. -/
theorem cls_reindex_any {m m' : ℕ} (X : Matrix (Fin m) (Fin m) A) (τ : Fin m ≃ Fin m') :
    cls ⟨m, X⟩ = cls ⟨m', Matrix.reindex τ τ X⟩ := by
  by_cases hX : X * X = X
  · exact cls_reindex (A := A) X hX τ
  · have hZ : Matrix.reindex τ.symm τ.symm (Matrix.reindex τ τ X) = X := by
      rw [reindex_reindex, Equiv.self_trans_symm, Matrix.reindex_refl_refl]
    have hX' : ¬ (Matrix.reindex τ τ X * Matrix.reindex τ τ X =
        Matrix.reindex τ τ X) := by
      intro h
      apply hX
      have h2 := congrArg (Matrix.reindex τ.symm τ.symm) h
      rw [Work.KT.reindex_mul_self τ.symm (Matrix.reindex τ τ X), hZ] at h2
      exact h2
    rw [Work.KT.PsiC.cls_of_not_idem (p := (⟨m, X⟩ : Mat A)) (by simpa [Mat.IsIdem] using hX),
      Work.KT.PsiC.cls_of_not_idem (p := (⟨m', Matrix.reindex τ τ X⟩ : Mat A))
        (by simpa [Mat.IsIdem] using hX')]

theorem cls_eq_clsM_fin {m : ℕ} (X : Matrix (Fin m) (Fin m) A) :
    cls ⟨m, X⟩ = clsM (Fin m) X := by
  show cls ⟨m, X⟩ = cls ⟨Fintype.card (Fin m),
    Matrix.reindex (Fintype.equivFin (Fin m)) (Fintype.equivFin (Fin m)) X⟩
  exact cls_reindex_any X (Fintype.equivFin (Fin m))

/-- **Class-level bookkeeping** for `cubePart ∘ sq2Part`. -/
theorem cls_cubePart_sq2_eq (hA : ∀ x y : A, x * y = y * x) (p : Mat A) (hp : p.IsIdem)
    (eps lam : ℂ) (heps : eps ^ 2 = 1) (hlam : lam ^ 3 = 1) :
    cls (cubePart lam (sq2Part eps p)) =
      clsM (IB p.1) (Matrix.reindex (cBIdx p.1).symm (cBIdx p.1).symm
        (cubePartP lam (sq2Part eps p))) := by
  have hQi : (sq2Part eps p).IsIdem :=
    sq2Part_idem (A := A) hA eps (by rw [← pow_two]; exact heps) hp
  have hZi : cubePartP lam (sq2Part eps p) * cubePartP lam (sq2Part eps p) =
      cubePartP lam (sq2Part eps p) :=
    cubePartP_idem (A := A) hA lam hlam hQi
  have h1 : cls (cubePart lam (sq2Part eps p)) =
      clsE (cubePartP lam (sq2Part eps p))
        ((sq2Part eps p).1 * (sq2Part eps p).1 * (sq2Part eps p).1)
        ((cycIdx (sq2Part eps p).1).symm) := by
    rw [cubePart_eq]
    rfl
  have h2 : clsM (IB p.1) (Matrix.reindex (cBIdx p.1).symm (cBIdx p.1).symm
        (cubePartP lam (sq2Part eps p))) =
      clsE (cubePartP lam (sq2Part eps p)) (Fintype.card (IB p.1))
        ((cBIdx p.1).symm.trans (Fintype.equivFin (IB p.1))) := by
    rw [show clsM (IB p.1) (Matrix.reindex (cBIdx p.1).symm (cBIdx p.1).symm
          (cubePartP lam (sq2Part eps p))) =
        cls ⟨Fintype.card (IB p.1), Matrix.reindex (Fintype.equivFin (IB p.1))
          (Fintype.equivFin (IB p.1)) (Matrix.reindex (cBIdx p.1).symm (cBIdx p.1).symm
            (cubePartP lam (sq2Part eps p)))⟩ from rfl]
    erw [reindex_reindex]
    rfl
  rw [h1, h2]
  exact (Work.KT.clsE_wellDefined hZi
    ((cycIdx (sq2Part eps p).1).symm) ((cBIdx p.1).symm.trans (Fintype.equivFin (IB p.1))))

/-- The requested bridge lemma. -/
theorem bridge_cube_sq2_aux (hA : ∀ x y : A, x * y = y * x)
    (p : Mat A) (hp : p.IsIdem) (eps lam : ℂ) (heps : eps ^ 2 = 1) (hlam : lam ^ 3 = 1) :
    cls (cubePart lam (sq2Part eps p)) =
      clsM (IB p.1) (PB p * Eeps eps p.1 * cycProj (cB p.1) lam) := by
  rw [cls_cubePart_sq2_eq (A := A) hA p hp eps lam heps hlam,
    reindex_cubePartP (A := A) p eps lam, kron3_sq2PartP (A := A) hA p eps]

end

end BridgeCS2

open Matrix Work.KT Work.KT.Psi Work.KT.PsiC

/-- **The bridge `cubePart ∘ sq2Part`.** -/
theorem bridge_cube_sq2 (A : Type) [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    (p : Work.KT.Mat A) (hp : p.IsIdem) (eps lam : ℂ) (heps : eps ^ 2 = 1) (hlam : lam ^ 3 = 1) :
    Work.KT.cls (Work.KT.cubePart lam (Work.KT.sq2Part eps p)) =
      Work.KT.Psi.clsM (Work.KT.PsiC.IB p.1)
        (Work.KT.PsiC.PB p * Work.KT.PsiC.Eeps eps p.1 * Work.KT.PsiC.cycProj (Work.KT.PsiC.cB p.1) lam) := by
  exact BridgeCS2.bridge_cube_sq2_aux (A := A) hA p hp eps lam heps hlam

end Work.PsiC
