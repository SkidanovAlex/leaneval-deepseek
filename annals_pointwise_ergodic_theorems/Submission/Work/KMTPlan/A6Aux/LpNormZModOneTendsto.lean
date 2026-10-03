import Mathlib
import Submission.Work.Analysis.Concentration.Basic

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.KMTPlan.A6Aux

open Filter

/-- At `p = 1` the normalized `L^p` norm on `ℤ/Qℤ` is just the average of the absolute
values: `‖f‖_{L^1} = Q⁻¹ ∑_x ‖f x‖`. -/
lemma LpNormZMod_one_eq {Q : ℕ} [NeZero Q] (h' : ZMod Q → ℂ) :
    Work.Analysis.Concentration.LpNormZMod Q 1 h' = (Q : ℝ)⁻¹ * ∑ x : ZMod Q, ‖h' x‖ := by
  simp [Work.Analysis.Concentration.LpNormZMod]

theorem LpNormZModOneTendsto {Q : ℕ} [NeZero Q] {f : ℕ → ZMod Q → ℂ} {g : ZMod Q → ℂ}
    (h : ∀ z : ZMod Q, Filter.Tendsto (fun N : ℕ => f N z) Filter.atTop (nhds (g z))) :
    Filter.Tendsto (fun N : ℕ => Work.Analysis.Concentration.LpNormZMod Q 1 (f N)) Filter.atTop
      (nhds (Work.Analysis.Concentration.LpNormZMod Q 1 g)) := by
  simp only [LpNormZMod_one_eq]
  exact Filter.Tendsto.const_mul _
    (tendsto_finsetSum _ (fun z _ => (continuous_norm.tendsto (g z)).comp (h z)))

end Work.KMTPlan.A6Aux
