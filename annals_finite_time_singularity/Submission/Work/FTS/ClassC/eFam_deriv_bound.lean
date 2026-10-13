import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_Lzero
import Submission.Work.FTS.PhiStar.Gegenbauer.gC_ode

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC

open scoped Real

/-- `eFam m = cos · (gC (2m+1) ∘ sin)` is `C^3`, being a product of `C^3` functions. -/
theorem contDiff_three_eFam (m : ℕ) : ContDiff ℝ 3 (Work.FTS.PhiStar.Gegenbauer.eFam m) := by
  have h1 : ContDiff ℝ 3 (Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1)) :=
    Work.FTS.PhiStar.Gegenbauer.contDiff_gC _
  exact Real.contDiff_cos.mul (h1.comp Real.contDiff_sin)

theorem eFam_deriv_bound (m : ℕ) : ∃ Q : ℝ, 0 ≤ Q ∧ ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
    |deriv (Work.FTS.PhiStar.Gegenbauer.eFam m) θ| ≤ Q := by
  have hcont : Continuous (deriv (Work.FTS.PhiStar.Gegenbauer.eFam m)) := by
    have h : ContDiffOn ℝ 2 (deriv (Work.FTS.PhiStar.Gegenbauer.eFam m)) Set.univ :=
      (contDiff_three_eFam m).contDiffOn.deriv_of_isOpen isOpen_univ
        (by norm_num : ((2 : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((3 : ℕ∞) : WithTop ℕ∞))
    exact continuousOn_univ.mp h.continuousOn
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (Real.pi / 2))) hcont.continuousOn
  refine ⟨C, le_trans (norm_nonneg _) (hC 0 ⟨le_refl 0, by linarith [Real.pi_pos]⟩), ?_⟩
  intro θ hθ
  simpa [Real.norm_eq_abs] using hC θ hθ

end Work.FTS.ClassC
