import Mathlib
import Submission.Work.PsiC.psi23_defs
import Submission.Work.PsiC.gamB_decomp
import Submission.Work.PsiC.cycProj_diag
import Submission.Work.KT.PsiC.CycProj

namespace Work.PsiC

open Matrix

/-- **`Work.PsiC.psi23_ident`** — the six-fold spectral projector `cycProj6 p.1 (λ ε)` of the
six-cycle `gamB` splits as the sum of the diagonal part `psiA p ε λ` and the off-diagonal part
`psiB p ε λ`.

`gamB_decomp` writes `cycProj6 n μ = cycProj (cB n) (μ²) · h_{μ³}(sB)`.  For `μ = λ ε` with
`λ³ = 1` and `ε² = 1` one has `μ² = λ²` and `μ³ = ε`, so the goal becomes
`cycProj (cB n) (λ²) · h_ε(sB)`, and `cycProj_diag` expands `cycProj (cB n) (λ²)` into the
diagonal term and the off-diagonal `Q2m` term; distributing over the sum gives the result. -/
theorem psi23_ident (A : Type) [Ring A] [Algebra ℂ A] (p : Work.KT.Mat A) (eps lam : ℂ)
    (heps : eps ^ 2 = 1) (hlam : lam ^ 3 = 1) :
    Work.KT.PsiC.cycProj6 (A := A) p.1 (lam * eps) =
      Work.PsiC.psiA p eps lam + Work.PsiC.psiB p eps lam := by
  have hmu : (lam * eps) ^ 6 = 1 := by
    rw [mul_pow]
    have hl : lam ^ 6 = 1 := by
      have h : lam ^ 6 = (lam ^ 3) ^ 2 := by ring
      rw [h, hlam]; norm_num
    have he : eps ^ 6 = 1 := by
      have h : eps ^ 6 = (eps ^ 2) ^ 3 := by ring
      rw [h, heps]; norm_num
    rw [hl, he, one_mul]
  have h2 : (lam * eps) ^ 2 = lam ^ 2 := by rw [mul_pow, heps, mul_one]
  have h3 : (lam * eps) ^ 3 = eps := by
    rw [mul_pow, hlam, one_mul]
    rw [show eps ^ 3 = eps by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, heps, one_mul, pow_one]]
  rw [Work.PsiC.gamB_decomp (A := A) p.1 (lam * eps) hmu, h2, h3]
  rw [Work.PsiC.cycProj_diag (A := A) p.1 lam hlam]
  simp only [Work.PsiC.psiA, Work.PsiC.psiB, Work.KT.PsiC.Q2m]
  noncomm_ring

end Work.PsiC
