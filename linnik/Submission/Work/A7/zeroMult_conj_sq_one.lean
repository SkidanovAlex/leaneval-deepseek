import Mathlib
import Submission.Work.A7.zeroMult_conj_inv

namespace Work.A7

/-- For a quadratic (real, `χ ^ 2 = 1`) Dirichlet character, the zero multiplicity of the
completed L-function is invariant under complex conjugation of the zero. This is immediate
from `zeroMult_conj_inv` since `χ⁻¹ = χ` for such a character. -/
theorem zeroMult_conj_sq_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) (ρ : ℂ) :
    Work.LinnikContract.zeroMult χ ((starRingEnd ℂ) ρ) = Work.LinnikContract.zeroMult χ ρ := by
  have h2 : χ * χ = 1 := by rw [pow_two] at hχ; exact hχ
  have hinv : χ⁻¹ = χ := inv_eq_of_mul_eq_one_right h2
  calc Work.LinnikContract.zeroMult χ ((starRingEnd ℂ) ρ)
      = Work.LinnikContract.zeroMult χ⁻¹ ((starRingEnd ℂ) ρ) := by rw [hinv]
    _ = Work.LinnikContract.zeroMult χ ρ := Work.A7.zeroMult_conj_inv χ ρ

end Work.A7
