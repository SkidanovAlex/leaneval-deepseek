import Mathlib
import Submission.Work.KT.PsiC.Setup
import Submission.Work.KT.PsiC.ReindexAux
import Submission.Work.KT.PsiC.CycProj
import Submission.Work.KT.Psi.k3Aux

namespace Work.KT.PsiC

open Matrix
open Work.KT.Psi

noncomputable section

variable {A : Type} [Ring A] [Algebra ℂ A]

/-! ## Frame A permutations (all proved pointwise) -/

theorem sA_mul_self (n : ℕ) : sA n * sA n = 1 := by
  apply Equiv.ext; intro x; rcases x with ⟨a, b⟩; rfl

theorem c1A_cube (n : ℕ) : c1A n * c1A n * c1A n = 1 := by
  apply Equiv.ext; intro x; rcases x with ⟨u, v⟩; rfl

theorem c2A_cube (n : ℕ) : c2A n * c2A n * c2A n = 1 := by
  apply Equiv.ext; intro x; rcases x with ⟨u, v⟩; rfl

theorem c1A_comm_c2A (n : ℕ) : c1A n * c2A n = c2A n * c1A n := by
  apply Equiv.ext; intro x; rcases x with ⟨u, v⟩; rfl

theorem tA_eq (n : ℕ) : tA n = c1A n * c2A n := by
  apply Equiv.ext; intro x; rcases x with ⟨u, v⟩; rfl

theorem tA_cube (n : ℕ) : tA n * tA n * tA n = 1 := by
  apply Equiv.ext; intro x; rcases x with ⟨u, v⟩; rfl

theorem RA_mul_self (n : ℕ) : RA n * RA n = 1 := by
  apply Equiv.ext; intro x; rcases x with ⟨u, v⟩; rfl

theorem RA_conj_c1A (n : ℕ) : RA n * c1A n * RA n = c1A n * c1A n := by
  apply Equiv.ext; intro x; rcases x with ⟨u, v⟩; rfl

theorem RA_conj_c2A (n : ℕ) : RA n * c2A n * RA n = c2A n * c2A n := by
  apply Equiv.ext; intro x; rcases x with ⟨u, v⟩; rfl

theorem RA_conj_tA (n : ℕ) : RA n * tA n * RA n = tA n * tA n := by
  apply Equiv.ext; intro x; rcases x with ⟨u, v⟩; rfl

theorem RA_conj_sA (n : ℕ) : RA n * sA n * RA n = sA n := by
  apply Equiv.ext; intro x; rcases x with ⟨u, v⟩ <;> rfl

/-! ## Frame B permutations -/

theorem sg0_mul_self (n : ℕ) : sg0 n * sg0 n = 1 := by
  apply Equiv.ext; intro x; rcases x with ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, ⟨e, f⟩⟩; rfl

theorem sg1_mul_self (n : ℕ) : sg1 n * sg1 n = 1 := by
  apply Equiv.ext; intro x; rcases x with ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, ⟨e, f⟩⟩; rfl

theorem sg2_mul_self (n : ℕ) : sg2 n * sg2 n = 1 := by
  apply Equiv.ext; intro x; rcases x with ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, ⟨e, f⟩⟩; rfl

theorem sg_comm01 (n : ℕ) : sg0 n * sg1 n = sg1 n * sg0 n := by
  apply Equiv.ext; intro x; rcases x with ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, ⟨e, f⟩⟩; rfl

theorem sg_comm02 (n : ℕ) : sg0 n * sg2 n = sg2 n * sg0 n := by
  apply Equiv.ext; intro x; rcases x with ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, ⟨e, f⟩⟩; rfl

theorem sg_comm12 (n : ℕ) : sg1 n * sg2 n = sg2 n * sg1 n := by
  apply Equiv.ext; intro x; rcases x with ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, ⟨e, f⟩⟩; rfl

theorem sB_mul_self (n : ℕ) : sB n * sB n = 1 := by
  rw [sB, show sg0 n * sg1 n * sg2 n * (sg0 n * sg1 n * sg2 n) = 1 from by
    apply Equiv.ext; intro x; rcases x with ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, ⟨e, f⟩⟩; rfl]

/-! ## The transport of the pair cycle -/

theorem cBIdx_apply (n : ℕ) (X Y Z : I2 n) :
    cBIdx n ((X, Y), Z) = ((finProdFinEquiv X, finProdFinEquiv Y), finProdFinEquiv Z) := rfl

theorem cBIdx_symm_apply (n : ℕ) (X Y Z : Fin (n * n)) :
    (cBIdx n).symm ((X, Y), Z) =
      ((finProdFinEquiv.symm X, finProdFinEquiv.symm Y), finProdFinEquiv.symm Z) := rfl

theorem cB_apply (n : ℕ) (a b c d e f : Fin n) :
    cB n (((a, b), (c, d)), (e, f)) = (((e, f), (a, b)), (c, d)) := by
  show (cBIdx n).symm (cycPermP (n * n) (cBIdx n (((a, b), (c, d)), (e, f)))) = _
  rw [cBIdx_apply]
  show (cBIdx n).symm (cycPermP (n * n)
      (((finProdFinEquiv (a, b), finProdFinEquiv (c, d)), finProdFinEquiv (e, f)))) = _
  rw [show cycPermP (n * n)
      (((finProdFinEquiv (a, b), finProdFinEquiv (c, d)), finProdFinEquiv (e, f))) =
      (((finProdFinEquiv (e, f), finProdFinEquiv (a, b)), finProdFinEquiv (c, d))) from rfl]
  rw [cBIdx_symm_apply]
  simp

/-! ## The bridge `Phi` -/

theorem Phi_conj_sA (n : ℕ) : (Phi n).symm.trans ((sA n).trans (Phi n)) = sB n := by
  apply Equiv.ext; intro x; rcases x with ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, ⟨e, f⟩⟩; rfl

theorem Phi_conj_tA (n : ℕ) : (Phi n).symm.trans ((tA n).trans (Phi n)) = cB n := by
  apply Equiv.ext
  intro y
  rcases y with ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, ⟨e, f⟩⟩
  have h1 : (Phi n).symm (((a, b), (c, d)), (e, f)) = (((a, c), e), ((b, d), f)) := rfl
  have h2 : tA n ((((a, c), e), ((b, d), f)) : IA n) = (((e, a), c), ((f, b), d)) := rfl
  have h3 : Phi n ((((e, a), c), ((f, b), d)) : IA n) = (((e, f), (a, b)), (c, d)) := rfl
  have h4 : cB n (((a, b), (c, d)), (e, f)) = (((e, f), (a, b)), (c, d)) :=
    cB_apply n a b c d e f
  rw [show (Phi n).symm.trans ((tA n).trans (Phi n)) (((a, b), (c, d)), (e, f)) =
      Phi n (tA n ((Phi n).symm (((a, b), (c, d)), (e, f)))) from rfl, h1, h2, h3, h4]

end

end Work.KT.PsiC
