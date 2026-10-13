import Mathlib
import Submission.Work.WilG4c.FibreLimitPiOmega
import Submission.Work.WilG4c.SlicedDerivDefs
import Submission.Work.WilG4a.CD.fibreLimitEqMem
import Submission.Work.WilG1.Basic
import Submission.Work.WilG0.API

namespace Work.WilG4c

theorem fibreLimitEqMem_pi {p n : ℕ} {S : WilkiesDesign.SOMin} :
    ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ {F D : ℕ} (A : Set (Fin (p + (n + 1) + 1) → ℝ)), A ∈ S.Ω F D (p + (n + 1) + 1) →
        {w : Fin (p + (n + 1) + 1) → ℝ | ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
          ∀ y : Fin (n + 1) → ℝ, y ≠ Work.WilkG4c.cubePt (Fin.init w) →
            (∀ j, |y j - Work.WilkG4c.cubePt (Fin.init w) j| < δ) →
            ∀ v : ℝ, Fin.snoc (Fin.append (Work.WilkG4c.parPt (Fin.init w)) y) v ∈ A →
              |v - w (Fin.last (p + (n + 1)))| ≤ ε} ∈
          S.Ω (F + a) (b.eval D) (p + (n + 1) + 1) := by
  refine ⟨fmtA p n, Polynomial.X + Polynomial.C (degK n), ?_⟩
  intro F D A hA
  change LimeqP p n A ∈ S.Ω (F + fmtA p n)
    ((Polynomial.X + Polynomial.C (degK n)).eval D) (Wp p n)
  rw [← BsetP_eq_LimeqP]
  refine Work.WilG1.Omega.mono (BsetP_mem (S := S) (hA := hA)) le_rfl ?_
  rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]

end Work.WilG4c
