import Mathlib
import Submission.Work.KT.PsiC.Setup
import Submission.Work.KT.PsiC.ReindexAux
import Submission.Work.KT.PsiC.CycProj
import Submission.Work.KT.PsiC.FramePerm
import Submission.Work.KT.PsiC.FramePerm2

namespace Work.KT.PsiC

open Matrix
open Work.KT.Psi

noncomputable section

variable {A : Type} [Ring A] [Algebra ℂ A]
variable {M : Type} [Monoid M]

theorem conj_mul' (u a b : M) (hu : u * u = 1) :
    u * (a * b) * u = (u * a * u) * (u * b * u) := by
  rw [show u * (a * b) * u = u * a * (u * u) * b * u from by
    rw [hu, mul_one]; simp only [mul_assoc]]
  simp only [mul_assoc]

/-! ## Transport of the projectors along an index equivalence -/

theorem reindex_cycProj {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (σ : Equiv.Perm ι) (lam : ℂ) :
    Matrix.reindex e e (cycProj (A := A) σ lam) =
      cycProj (A := A) (e.symm.trans (σ.trans e)) lam := by
  simp only [cycProj, reindex_add', reindex_one', reindex_mul', reindex_smul,
    reindex_permMatrix]

theorem reindex_halfProj {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (σ : Equiv.Perm ι) (ε : ℂ) :
    Matrix.reindex e e (halfProj (A := A) ε σ) =
      halfProj (A := A) ε (e.symm.trans (σ.trans e)) := by
  simp only [halfProj, reindex_add', reindex_one', reindex_smul, reindex_permMatrix]

/-! ## `cB` facts -/

theorem cB_cube (n : ℕ) : cB n * cB n * cB n = 1 := by
  apply Equiv.ext
  intro y
  rcases y with ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, ⟨e, f⟩⟩
  show cB n (cB n (cB n (((a, b), (c, d)), (e, f)))) = (((a, b), (c, d)), (e, f))
  rw [cB_apply, cB_apply, cB_apply]

theorem sB_apply (n : ℕ) (a b c d e f : Fin n) :
    sB n (((a, b), (c, d)), (e, f)) = (((b, a), (d, c)), (f, e)) := rfl

theorem cB_comm_sB (n : ℕ) : cB n * sB n = sB n * cB n := by
  apply Equiv.ext
  intro y
  rcases y with ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, ⟨e, f⟩⟩
  show cB n (sB n (((a, b), (c, d)), (e, f))) = sB n (cB n (((a, b), (c, d)), (e, f)))
  rw [sB_apply n a b c d e f, cB_apply n a b c d e f, sB_apply n e f a b c d]
  exact cB_apply n b a d c f e

end

end Work.KT.PsiC

namespace Work.KT.PsiC

open Matrix
open Work.KT.Psi

noncomputable section

variable {A : Type} [Ring A] [Algebra ℂ A]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Conjugation by an involutive permutation matrix is reindexing. -/
theorem permMatrix_mul_reindex (ρ : Equiv.Perm ι) (hρ : ρ * ρ = 1) (X : Matrix ι ι A) :
    ρ.permMatrix A * X * (ρ⁻¹).permMatrix A = Matrix.reindex ρ ρ X := by
  have hinv : ρ⁻¹ = ρ := inv_eq_of_mul_eq_one_right hρ
  rw [hinv]
  ext i j
  rw [mul_permMatrix, permMatrix_mul, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [show ρ.symm = ρ from hinv]

/-- Conjugating a cyclic projector by an involutive permutation. -/
theorem conj_cycProj_perm (σ ρ : Equiv.Perm ι) (hρ : ρ * ρ = 1) (lam : ℂ) :
    ρ.permMatrix A * cycProj (A := A) σ lam * ρ.permMatrix A =
      cycProj (A := A) (ρ * σ * ρ) lam := by
  have hinv : ρ⁻¹ = ρ := inv_eq_of_mul_eq_one_right hρ
  rw [show ρ.permMatrix A * cycProj (A := A) σ lam * ρ.permMatrix A =
      ρ.permMatrix A * cycProj (A := A) σ lam * (ρ⁻¹).permMatrix A from by rw [hinv]]
  rw [permMatrix_mul_reindex ρ hρ, reindex_cycProj]
  congr 1
  apply Equiv.ext
  intro x
  rw [Equiv.trans_apply, Equiv.trans_apply, show ρ.symm = ρ from hinv, Equiv.Perm.mul_apply,
    Equiv.Perm.mul_apply]

theorem conj_halfProj_perm (σ ρ : Equiv.Perm ι) (hρ : ρ * ρ = 1) (ε : ℂ) :
    ρ.permMatrix A * halfProj (A := A) ε σ * ρ.permMatrix A =
      halfProj (A := A) ε (ρ * σ * ρ) := by
  have hinv : ρ⁻¹ = ρ := inv_eq_of_mul_eq_one_right hρ
  rw [show ρ.permMatrix A * halfProj (A := A) ε σ * ρ.permMatrix A =
      ρ.permMatrix A * halfProj (A := A) ε σ * (ρ⁻¹).permMatrix A from by rw [hinv]]
  rw [permMatrix_mul_reindex ρ hρ, reindex_halfProj]
  congr 1
  apply Equiv.ext
  intro x
  rw [Equiv.trans_apply, Equiv.trans_apply, show ρ.symm = ρ from hinv, Equiv.Perm.mul_apply,
    Equiv.Perm.mul_apply]

/-- Commutation of a cyclic projector with anything commuting with `σ`. -/
theorem cycProj_comm_of (hA : ∀ x y : A, x * y = y * x) (σ : Equiv.Perm ι) (lam : ℂ)
    (X : Matrix ι ι A) (h : X * σ.permMatrix A = σ.permMatrix A * X) :
    X * cycProj (A := A) σ lam = cycProj (A := A) σ lam * X := by
  letI : CommRing A := { ‹Ring A› with mul_comm := hA }
  have h2 : X * (σ.permMatrix A * σ.permMatrix A) =
      (σ.permMatrix A * σ.permMatrix A) * X := by
    rw [← mul_assoc, h, mul_assoc, h, ← mul_assoc]
  simp only [cycProj, mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_one, one_mul,
    h, h2]

theorem halfProj_comm_of (hA : ∀ x y : A, x * y = y * x) (σ : Equiv.Perm ι) (ε : ℂ)
    (X : Matrix ι ι A) (h : X * σ.permMatrix A = σ.permMatrix A * X) :
    X * halfProj (A := A) ε σ = halfProj (A := A) ε σ * X := by
  letI : CommRing A := { ‹Ring A› with mul_comm := hA }
  simp only [halfProj, mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_one, one_mul, h]

end

end Work.KT.PsiC
