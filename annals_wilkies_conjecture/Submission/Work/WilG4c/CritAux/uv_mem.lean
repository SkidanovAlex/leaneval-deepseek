import Mathlib
import Submission.Work.WilG4c.CritAux
import Submission.Work.WilG4c.fibreLimitEqMem_pi
import Submission.Work.WilG1.Basic

namespace Work.WilG4c.CritAux

theorem uv_mem (S : WilkiesDesign.SOMin) (hder : S.SharpDeriv) (p n F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ), ∀ (D k : ℕ)
      (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ),
      WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
      Work.WilkG4c.UV p n f k ∈ S.Ω a (MvPolynomial.eval ![D, k] b) (p + (n + 1)) := by
  sorry

end Work.WilG4c.CritAux
