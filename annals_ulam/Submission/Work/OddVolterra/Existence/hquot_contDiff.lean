import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.Analysis.Calculus.contDiff_dslope

namespace Work.OddVolterra.Existence

/-- `hquot h s σ` is by definition the integral `∫ τ in 0..1, deriv h (s + τ * (σ - s))`,
which is the divided difference of `h`; hence it is `C^∞` in `(s,σ)` whenever `h` is. -/
theorem hquot_contDiff {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => Work.OddVolterra.hquot h p.1 p.2) := by
  have hfun : (fun p : ℝ × ℝ => Work.OddVolterra.hquot h p.1 p.2)
      = fun q : ℝ × ℝ => dslope h q.1 q.2 := by
    funext q
    exact (Work.Analysis.Calculus.dslope_eq_integral_deriv h hh q.1 q.2).symm
  rw [hfun]
  exact Work.Analysis.Calculus.contDiff_dslope h hh

end Work.OddVolterra.Existence
