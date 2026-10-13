import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.GalFields.Norm.Hk5SlotTriangle
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.StrongEps.EpsE4Thr

theorem HkIntegrand_sqrt_add_le (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Real.sqrt (Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ)
        ≤ Real.sqrt (Work.Spaces.HkIntegrand α k f z θ)
          + Real.sqrt (Work.Spaces.HkIntegrand α k g z θ) := by
  intro z hz θ hθ
  -- The right-hand side is nonnegative, so the two degenerate cases are immediate.
  have hRHS : 0 ≤ Real.sqrt (Work.Spaces.HkIntegrand α k f z θ)
      + Real.sqrt (Work.Spaces.HkIntegrand α k g z θ) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hzpos
  · -- `z = 0`: the integrand vanishes (the radial weight is `0` there).
    subst h0
    rw [Work.FTS.LocData.HkIntegrand_zero_fst, Real.sqrt_zero]
    exact hRHS
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ θ from hθ.1) with h1 | hθpos
  · -- `θ = 0`: `sin (2θ) = 0`, and the integrand vanishes there identically.
    subst h1
    rw [Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α k
        (fun z θ => f z θ + g z θ) z 0 (by norm_num), Real.sqrt_zero]
    exact hRHS
  rcases lt_or_eq_of_le hθ.2 with h2 | h2
  · -- The open quadrant: the pointwise Euclidean triangle inequality of the slot vector.
    exact Work.FTS.GalFields.Norm.hk5_sqrt_HkIntegrand_add_le α k
      (Work.FTS.EllipticEst.smoothOpen_of_forall hf)
      (Work.FTS.EllipticEst.smoothOpen_of_forall hg)
      z θ hzpos hθpos h2
  · -- `θ = π/2`: `sin (2θ) = 0`, and the integrand vanishes there identically.
    subst h2
    rw [Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α k
        (fun z θ => f z θ + g z θ) z (π / 2)
        (by rw [show 2 * (π / 2) = π by ring]; exact Real.sin_pi), Real.sqrt_zero]
    exact hRHS

end Work.FTS.StrongEps.EpsE4Thr
