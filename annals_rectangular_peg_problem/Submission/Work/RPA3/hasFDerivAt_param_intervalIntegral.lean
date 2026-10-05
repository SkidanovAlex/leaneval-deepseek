import Mathlib
import Submission.Work.RPA3.contDiff_param_intervalIntegral

/-!
Differentiation under the integral sign for a parametric *interval* integral, in `HasFDerivAt`
form.  The statement is proved as `Work.RPA3.hasFDerivAt_param_intervalIntegral_aux`, the inductive
step of `Work.RPA3.contDiff_param_intervalIntegral` (fed with the local uniform bound of
`Work.RPA3.local_bound_continuous_prod` for the continuous derivative
`(x,u) ↦ (fderiv ℝ G (x,u)) ∘ inl`), and is recorded here under this name.
-/

namespace Work.RPA3

open scoped Interval

universe u

theorem hasFDerivAt_param_intervalIntegral {X F : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (g : X → ℝ → F) (hg : ContDiff ℝ 1 (fun z : X × ℝ => g z.1 z.2)) (a b : ℝ) (x₀ : X) :
    HasFDerivAt (fun x : X => ∫ u in a..b, g x u)
      (∫ u in a..b,
        (fderiv ℝ (fun z : X × ℝ => g z.1 z.2) (x₀, u)).comp (ContinuousLinearMap.inl ℝ X ℝ)) x₀ :=
  hasFDerivAt_param_intervalIntegral_aux g hg a b x₀

end Work.RPA3
