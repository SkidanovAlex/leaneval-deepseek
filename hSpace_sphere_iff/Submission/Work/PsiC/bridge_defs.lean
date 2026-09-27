import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.PsiC.BFrame
import Submission.Work.KT.Psi.psi2sum_Setup

/-!
# `Work.PsiC.bridge_defs` — the two frames for `ψ²ψ³[p]`

The class `cls (sq2Part ε (cubePart λ p))` of  `ψ²ψ³`  on a generator is computed on the six-fold
tensor power `p^{⊗6}` in the bracketing `(E^{⊗3})^{⊗2}`;  the corresponding class for `ψ³ψ²` is
computed in the bracketing `(E^{⊗2})^{⊗3}`.  This file records the two matrices

* `VA ε λ p` — in frame A (`IA p.1 = I3 p.1 × I3 p.1`),
* `VB ε λ p` — in frame B (`IB p.1 = I2 p.1 × I2 p.1 × I2 p.1`, written as three pairs),

and the elementary reindexing lemmas used to pass between them.
-/

namespace Work.PsiC

open Matrix Work.KT.PsiC

noncomputable section

variable {A : Type} [Ring A] [Algebra ℂ A]

/-- The frame-A matrix `P_A · (C_λ ⊗ C_λ) · h_ε(s_A)`. -/
def VA (p : Work.KT.Mat A) (eps lam : ℂ) :
    Matrix (Work.KT.PsiC.IA p.1) (Work.KT.PsiC.IA p.1) A :=
  Work.KT.PsiC.PA p *
    (Matrix.kroneckerMap (fun x y : A => x * y)
        (Work.KT.PsiC.cycProj (A := A) (Work.KT.cycPermP p.1) lam)
        (Work.KT.PsiC.cycProj (A := A) (Work.KT.cycPermP p.1) lam) *
      Work.KT.PsiC.halfProj (A := A) eps (Work.KT.PsiC.sA p.1))

/-- The frame-B matrix `P_B · (U · V) · h_ε(s_B)`. -/
def VB (p : Work.KT.Mat A) (eps lam : ℂ) :
    Matrix (Work.KT.PsiC.IB p.1) (Work.KT.PsiC.IB p.1) A :=
  Work.KT.PsiC.PB p *
    (Work.KT.PsiC.cycProj (A := A) (Work.KT.PsiC.uB p.1) lam *
      Work.KT.PsiC.cycProj (A := A) (Work.KT.PsiC.vB p.1) lam) *
    Work.KT.PsiC.halfProj (A := A) eps (Work.KT.PsiC.sB p.1)

/-! ## Small class lemmas (no idempotency hypothesis) -/

/-- `clsM` is invariant under reindexing. -/
theorem clsM_reindex_aux {ι κ : Type} [Fintype ι] [Fintype κ] (g : ι ≃ κ)
    (M : Matrix ι ι A) :
    Work.KT.Psi.clsM κ (Matrix.reindex g g M) = Work.KT.Psi.clsM ι M :=
  Work.KT.Psi.clsI_reindex g M

/-- The class of `sq2Part ε p` is that of the unreindexed `sq2PartP ε p`. -/
theorem cls_sq2Part_eq_clsM_aux (ε : ℂ) (p : Work.KT.Mat A) :
    Work.KT.cls (Work.KT.sq2Part ε p) =
      Work.KT.Psi.clsM (Fin p.1 × Fin p.1) (Work.KT.sq2PartP ε p) := by
  rw [Work.KT.sq2Part_eq, Work.KT.Psi.clsM_eq_cls]
  exact Work.KT.Psi.cls_ofIdx_irrel (Work.KT.sq2PartP ε p) finProdFinEquiv
    (Fintype.equivFin (Fin p.1 × Fin p.1))

/-- `sq2PartP` at an explicit matrix, in the `halfProj` form. -/
theorem sq2PartP_eq_explicit (ε : ℂ) (N : ℕ) (M : Matrix (Fin N) (Fin N) A) :
    Work.KT.sq2PartP ε (⟨N, M⟩ : Work.KT.Mat A) =
      Matrix.kroneckerMap (fun x y : A => x * y) M M *
        Work.KT.PsiC.halfProj (A := A) ε (Equiv.prodComm (Fin N) (Fin N)) := rfl

/-! ## Transport of the spectral projectors across `Phi` -/

theorem reindex_Phi_cycProj_c1A (n : ℕ) (lam : ℂ) :
    Matrix.reindex (Work.KT.PsiC.Phi n) (Work.KT.PsiC.Phi n)
        (Work.KT.PsiC.cycProj (A := A) (Work.KT.PsiC.c1A n) lam) =
      Work.KT.PsiC.cycProj (A := A) (Work.KT.PsiC.uB n) lam := by
  rw [Work.KT.PsiC.reindex_cycProj]
  rfl

theorem reindex_Phi_cycProj_c2A (n : ℕ) (lam : ℂ) :
    Matrix.reindex (Work.KT.PsiC.Phi n) (Work.KT.PsiC.Phi n)
        (Work.KT.PsiC.cycProj (A := A) (Work.KT.PsiC.c2A n) lam) =
      Work.KT.PsiC.cycProj (A := A) (Work.KT.PsiC.vB n) lam := by
  rw [Work.KT.PsiC.reindex_cycProj]
  rfl

theorem reindex_Phi_halfProj_sA (n : ℕ) (eps : ℂ) :
    Matrix.reindex (Work.KT.PsiC.Phi n) (Work.KT.PsiC.Phi n)
        (Work.KT.PsiC.halfProj (A := A) eps (Work.KT.PsiC.sA n)) =
      Work.KT.PsiC.halfProj (A := A) eps (Work.KT.PsiC.sB n) := by
  rw [Work.KT.PsiC.reindex_halfProj, Work.KT.PsiC.Phi_conj_sA]

end

end Work.PsiC
