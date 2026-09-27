import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.PsiC.BFrame

/-!
# `Work.PsiC.psi23_defs` — the two matrix summands of the `ψ²ψ³` step

The class `cls (sq2Part eps (cubePart lam p))` of `ψ²ψ³` on a generator is computed in frame B
(`IB p.1 = (Fin n × Fin n) × (Fin n × Fin n) × (Fin n × Fin n)`, `n = p.1`) on the six-fold
tensor power `PB p`.  Its matrix is the sum of two orthogonal projectors:

* `psiA p eps lam` — the *diagonal* part `U_λ · V_λ · H_ε`, where `U_• = cycProj (uB p.1) •`,
  `V_• = cycProj (vB p.1) •` and `H_ε = halfProj ε (sB p.1)`;
* `psiB p eps lam` — the *off-diagonal* part `Q2m_λ · H_ε`.

Their sum is the six-fold spectral projector `cycProj6 p.1 (lam * eps)` of `gamB`
(`Work.PsiC.psi23_ident`), and they are orthogonal idempotents (`Work.PsiC.psiAB_idem_orth`).
-/

namespace Work.PsiC

open Matrix

noncomputable section

variable {A : Type} [Ring A] [Algebra ℂ A]

/-- The diagonal summand `U_λ · V_λ · H_ε` of the `gamB`-projector at `lam * eps`. -/
def psiA (p : Work.KT.Mat A) (eps lam : ℂ) :
    Matrix (Work.KT.PsiC.IB p.1) (Work.KT.PsiC.IB p.1) A :=
  Work.KT.PsiC.cycProj (A := A) (Work.KT.PsiC.uB p.1) lam *
    Work.KT.PsiC.cycProj (A := A) (Work.KT.PsiC.vB p.1) lam *
    Work.KT.PsiC.halfProj (A := A) eps (Work.KT.PsiC.sB p.1)

/-- The off-diagonal summand `Q2m_λ · H_ε` of the `gamB`-projector at `lam * eps`. -/
def psiB (p : Work.KT.Mat A) (eps lam : ℂ) :
    Matrix (Work.KT.PsiC.IB p.1) (Work.KT.PsiC.IB p.1) A :=
  Work.KT.PsiC.Q2m p lam * Work.KT.PsiC.halfProj (A := A) eps (Work.KT.PsiC.sB p.1)

end

end Work.PsiC
