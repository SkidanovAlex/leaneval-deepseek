import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Basic.pd_cheb_setup
import Submission.Work.TMC16Core.Basic.pd_cheb_symm
import Submission.Work.TMC16Core.Basic.pd_cheb_deg
import Submission.Work.TMC16Core.Basic.pd_cheb_red
import Submission.Work.TMC16Core.Basic.pd_cheb_eval

namespace Work.TMC16Core.Basic

theorem pd_cheb (α lam : ℝ) (E : ℂ) (k : ℕ) :
    ∃ Q : Polynomial ℂ, Q.natDegree ≤ k ∧ ∀ x : ℝ,
      Q.eval (((Real.cos (2 * Real.pi * x) : ℝ)) : ℂ) =
        Work.TMC16Core.pd α lam (x - (((k : ℝ) - 1) / 2) * α) E (k + 1) := by
  obtain ⟨Q, hQdeg, hQ⟩ :=
    pd_cheb_red (Work.TMC16Core.Cheb.Pbiv α lam E k) k
      (pd_cheb_symm α lam E k)
      (pd_cheb_deg α lam E k)
  refine ⟨Q, hQdeg, fun x => ?_⟩
  have htrig : (((Real.sin (2 * Real.pi * x) : ℝ)) : ℂ) ^ 2 =
      1 - (((Real.cos (2 * Real.pi * x) : ℝ)) : ℂ) ^ 2 := by
    have h := Complex.sin_sq_add_cos_sq (((2 * Real.pi * x : ℝ)) : ℂ)
    rw [← Complex.ofReal_sin, ← Complex.ofReal_cos] at h
    rw [eq_sub_iff_add_eq]
    exact h
  rw [hQ _ _ htrig]
  exact pd_cheb_eval α lam E k x

end Work.TMC16Core.Basic
