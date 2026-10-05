import Mathlib
import Submission.Work.RPB.B5.LagData
import Submission.Work.RPB.B5.Defs

namespace Work.RPB.B5

theorem lagData_rho_inj (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (D : Work.RPB.B5.LagData CI a) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ s : ℝ, ∀ x ∈ Set.Icc (-Real.sqrt 2) 0,
      ∀ x' ∈ Set.Icc (-Real.sqrt 2) 0, D.rho τ x s = D.rho τ x' s → x = x' := by
  intro τ hτ s x hx x' hx' heq
  by_contra hne
  -- `rho` is smooth on the whole plane, hence in particular in the `x`-variable.
  have hg : ContDiff ℝ 8 (fun y : ℝ => (τ, (y, s))) := by fun_prop
  have hcomp := D.hrhosm.comp hg
  have he : ((fun z : ℝ × (ℝ × ℝ) => D.rho z.1 z.2.1 z.2.2) ∘ fun y : ℝ => (τ, (y, s)))
      = fun y : ℝ => D.rho τ y s := by funext y; rfl
  have hf : ContDiff ℝ 8 (fun y : ℝ => D.rho τ y s) := by rwa [he] at hcomp
  have hdiff : Differentiable ℝ (fun y : ℝ => D.rho τ y s) := hf.differentiable (by norm_num)
  -- Between two distinct points of `[-√2, 0]` there is an interior point where the
  -- derivative equals the (vanishing) slope; but the derivative never vanishes there.
  have key : ∀ a b : ℝ, a ∈ Set.Icc (-Real.sqrt 2) 0 → b ∈ Set.Icc (-Real.sqrt 2) 0 →
      a < b → D.rho τ a s = D.rho τ b s → False := by
    intro a b ha hb hab heqab
    obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope (fun y : ℝ => D.rho τ y s) hab
      hf.continuous.continuousOn hdiff.differentiableOn
    refine D.hrhoderiv τ hτ c ⟨lt_of_le_of_lt ha.1 hc.1, le_of_lt (lt_of_lt_of_le hc.2 hb.2)⟩ s ?_
    rw [heqab, sub_self, zero_div] at hcd
    exact hcd
  rcases lt_or_gt_of_ne hne with h | h
  · exact key x x' hx hx' h heq
  · exact key x' x hx' hx h heq.symm

end Work.RPB.B5
