import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.PsiC.BFrame
import Submission.Work.KT.PsiC.CycProj
import Submission.Work.KT.PsiC.FramePerm2
import Submission.Work.KT.PsiC.FramePerm3
import Submission.Work.KT.Psi.ClsM
import Submission.Work.KT.Psi.clsM_idem_add
import Submission.Work.PsiC.psi23_defs
import Submission.Work.PsiC.psi23_ident
import Submission.Work.PsiC.PB_comm_frame
import Submission.Work.PsiC.PB_comm_cycProj
import Submission.Work.PsiC.psiAB_idem_orth
import Submission.Work.PsiC.bridge_sq2_cube

/-!
# `Work.PsiC.step_psi2psi3` — the matrix form of `ψ²` on a `cubePart` generator

`bridge_sq2_cube` computes the class of `sq2Part eps (cubePart lam p)` on the six-fold tensor
power in frame B:

`cls (sq2Part ε (cubePart λ p)) = [PB p · U_λ · V_λ · H_ε]`.

The six-cycle identity `psi23_ident` splits the spectral projector `cycProj6 (λ ε)` of `gamB` as
`psiA + psiB`, and `psiAB_idem_orth` shows that the two summands are orthogonal idempotents; since
`PB p` commutes with both (`PB_comm_psiA`, `PB_comm_psiB`) their `PB`-multiples are again
orthogonal idempotents, so their classes add (`clsM_idem_add`).  This gives

`[PB p · U_λ · V_λ · H_ε] = [PB p · cycProj6 (λ ε)] - [PB p · Q2m_λ · H_ε]`,

which is the statement.
-/

namespace Work.PsiC

open Matrix

noncomputable section

/-- A product of two commuting idempotents is idempotent. -/
theorem psi_aux_mul_idem {R : Type} [Ring R] {P X : R} (hP : P * P = P) (hX : X * X = X)
    (h : P * X = X * P) : (P * X) * (P * X) = P * X :=
  (show IsIdempotentElem P from hP).mul_of_commute (show Commute P X from h) hX

/-- The product `(P X)(P Y)` vanishes when `X Y = 0` and `P` is an idempotent commuting with `X`. -/
theorem psi_aux_mul_orth {R : Type} [Ring R] {P X Y : R} (hP : P * P = P)
    (h : P * X = X * P) (hXY : X * Y = 0) : (P * X) * (P * Y) = 0 := by
  calc (P * X) * (P * Y)
      = P * (X * (P * Y)) := mul_assoc P X (P * Y)
    _ = P * ((X * P) * Y) := by rw [mul_assoc X P Y]
    _ = P * ((P * X) * Y) := by rw [← h]
    _ = P * (P * (X * Y)) := by rw [mul_assoc P X Y]
    _ = 0 := by rw [hXY, mul_zero, mul_zero]

/-- `PB p` commutes with the diagonal summand `psiA p eps lam`. -/
theorem PB_comm_psiA (A : Type) [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    (p : Work.KT.Mat A) (hp : p.IsIdem) (eps lam : ℂ) :
    Work.KT.PsiC.PB p * psiA p eps lam = psiA p eps lam * Work.KT.PsiC.PB p := by
  have hU := (Work.PsiC.PB_comm_cycProj A hA p hp lam).1
  have hV := (Work.PsiC.PB_comm_cycProj A hA p hp lam).2
  have hS := Work.PsiC.PB_comm_sB hA p
  have hH := Work.KT.PsiC.halfProj_comm_of (A := A) hA (Work.KT.PsiC.sB p.1) eps
    (Work.KT.PsiC.PB p) hS
  unfold psiA
  exact Work.PsiC.comm_mul_of_comm _ _ _ (Work.PsiC.comm_mul_of_comm _ _ _ hU hV) hH

/-- `PB p` commutes with the off-diagonal summand `psiB p eps lam`. -/
theorem PB_comm_psiB (A : Type) [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    (p : Work.KT.Mat A) (hp : p.IsIdem) (eps lam : ℂ) :
    Work.KT.PsiC.PB p * psiB p eps lam = psiB p eps lam * Work.KT.PsiC.PB p := by
  have hQ1 := Work.PsiC.PB_comm_cycProj A hA p hp (lam * Work.KT.omega)
  have hQ2 := Work.PsiC.PB_comm_cycProj A hA p hp (lam * Work.KT.omega ^ 2)
  have hQ : Work.KT.PsiC.PB p * Work.KT.PsiC.Q2m p lam =
      Work.KT.PsiC.Q2m p lam * Work.KT.PsiC.PB p := by
    unfold Work.KT.PsiC.Q2m
    rw [Matrix.mul_add, Matrix.add_mul,
      Work.PsiC.comm_mul_of_comm _ _ _ hQ1.1 hQ2.2,
      Work.PsiC.comm_mul_of_comm _ _ _ hQ2.1 hQ1.2]
  have hS := Work.PsiC.PB_comm_sB hA p
  have hH := Work.KT.PsiC.halfProj_comm_of (A := A) hA (Work.KT.PsiC.sB p.1) eps
    (Work.KT.PsiC.PB p) hS
  unfold psiB
  exact Work.PsiC.comm_mul_of_comm _ _ _ hQ hH

theorem step_psi2psi3 (A : Type) [Ring A] [Algebra ℂ A] (hA : ∀ x y : A, x * y = y * x)
    (p : Work.KT.Mat A) (hp : p.IsIdem) (eps lam : ℂ) (heps : eps ^ 2 = 1) (hlam : lam ^ 3 = 1) :
    Work.KT.cls (Work.KT.sq2Part eps (Work.KT.cubePart lam p)) =
      Work.KT.PsiC.Tcls (A := A) p (lam * eps) - Work.KT.PsiC.Q2cls (A := A) p eps lam := by
  -- the two summands of the `gamB`-projector and their commutation with `PB p`
  obtain ⟨hAA, hBB, hAB, hBA⟩ := psiAB_idem_orth A hA p eps lam heps hlam
  have hPA : Work.KT.PsiC.PB p * psiA p eps lam = psiA p eps lam * Work.KT.PsiC.PB p :=
    PB_comm_psiA A hA p hp eps lam
  have hPB : Work.KT.PsiC.PB p * psiB p eps lam = psiB p eps lam * Work.KT.PsiC.PB p :=
    PB_comm_psiB A hA p hp eps lam
  have hPP : Work.KT.PsiC.PB p * Work.KT.PsiC.PB p = Work.KT.PsiC.PB p :=
    Work.KT.PsiC.PB_idem p hA hp
  -- `PB·psiA` and `PB·psiB` are orthogonal idempotents
  have hAidem : (Work.KT.PsiC.PB p * psiA p eps lam) * (Work.KT.PsiC.PB p * psiA p eps lam) =
      Work.KT.PsiC.PB p * psiA p eps lam := psi_aux_mul_idem hPP hAA hPA
  have hBidem : (Work.KT.PsiC.PB p * psiB p eps lam) * (Work.KT.PsiC.PB p * psiB p eps lam) =
      Work.KT.PsiC.PB p * psiB p eps lam := psi_aux_mul_idem hPP hBB hPB
  have hABo : (Work.KT.PsiC.PB p * psiA p eps lam) * (Work.KT.PsiC.PB p * psiB p eps lam) = 0 :=
    psi_aux_mul_orth hPP hPA hAB
  have hBAo : (Work.KT.PsiC.PB p * psiB p eps lam) * (Work.KT.PsiC.PB p * psiA p eps lam) = 0 :=
    psi_aux_mul_orth hPP hPB hBA
  -- additivity of the class
  have hsum := Work.KT.Psi.clsM_idem_add (A := A) (ι := Work.KT.PsiC.IB p.1)
    (Work.KT.PsiC.PB p * psiA p eps lam) (Work.KT.PsiC.PB p * psiB p eps lam)
    hAidem hBidem hABo hBAo
  have hcp : Work.KT.PsiC.PB p * psiA p eps lam + Work.KT.PsiC.PB p * psiB p eps lam =
      Work.KT.PsiC.PB p * Work.KT.PsiC.cycProj6 (A := A) p.1 (lam * eps) := by
    rw [← Matrix.mul_add, ← psi23_ident A p eps lam heps hlam]
  have hmain : Work.KT.Psi.clsM (Work.KT.PsiC.IB p.1) (Work.KT.PsiC.PB p * psiA p eps lam) =
      Work.KT.Psi.clsM (Work.KT.PsiC.IB p.1)
          (Work.KT.PsiC.PB p * Work.KT.PsiC.cycProj6 (A := A) p.1 (lam * eps)) -
        Work.KT.Psi.clsM (Work.KT.PsiC.IB p.1) (Work.KT.PsiC.PB p * psiB p eps lam) := by
    have hsum' : Work.KT.Psi.clsM (Work.KT.PsiC.IB p.1)
          (Work.KT.PsiC.PB p * Work.KT.PsiC.cycProj6 (A := A) p.1 (lam * eps)) =
        Work.KT.Psi.clsM (Work.KT.PsiC.IB p.1) (Work.KT.PsiC.PB p * psiA p eps lam) +
          Work.KT.Psi.clsM (Work.KT.PsiC.IB p.1) (Work.KT.PsiC.PB p * psiB p eps lam) := by
      rw [← hcp]; exact hsum
    rw [hsum']; abel
  -- the bridge to frame B
  have hbridge : Work.KT.cls (Work.KT.sq2Part eps (Work.KT.cubePart lam p)) =
      Work.KT.Psi.clsM (Work.KT.PsiC.IB p.1) (Work.KT.PsiC.PB p * psiA p eps lam) := by
    rw [bridge_sq2_cube A hA p hp eps lam heps hlam]
    rw [show Work.KT.PsiC.PB p * (Work.KT.PsiC.cycProj (A := A) (Work.KT.PsiC.uB p.1) lam *
          Work.KT.PsiC.cycProj (A := A) (Work.KT.PsiC.vB p.1) lam) *
          Work.KT.PsiC.halfProj (A := A) eps (Work.KT.PsiC.sB p.1) =
        Work.KT.PsiC.PB p * psiA p eps lam from by rw [psiA, mul_assoc]]
  rw [hbridge, hmain]
  rw [show Work.KT.PsiC.Q2cls (A := A) p eps lam =
      Work.KT.Psi.clsM (Work.KT.PsiC.IB p.1) (Work.KT.PsiC.PB p * psiB p eps lam) from by
    rw [Work.KT.PsiC.Q2cls, psiB, mul_assoc]]
  rfl

end

end Work.PsiC
