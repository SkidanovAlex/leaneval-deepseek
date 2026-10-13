import Mathlib
import Submission.Work.WilG3.Defs

namespace Work.WilG3

-- The tower of within-derivatives of a `C^(r+1)` function on the open interval `I = (0,1)` is a
-- tower of honest derivatives: for `j ≤ r`, the `j`-th within-derivative of `f` has derivative
-- equal to the `(j+1)`-st within-derivative at every point of `I`.  This is the bridge from BNZ
-- arXiv 2202.05305 §5.1 to `iteratedDerivWithin` (see `WilkieDesign.CG.G3_discrete_Cr`).
-- Useful Mathlib input: `ContDiffOn.differentiableOn_iteratedDerivWithin`,
-- `DifferentiableWithinAt.hasDerivWithinAt`, `HasDerivWithinAt.hasDerivAt`,
-- `derivWithin_of_mem_nhds`, `iteratedDerivWithin_succ`, `uniqueDiffOn_Ioo`, `isOpen_Ioo`.
theorem WithinTowerHasDerivAt (r j : ℕ) (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ (r + 1) f (Set.Ioo (0 : ℝ) 1)) (hj : j ≤ r) :
    ∀ y ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (fun z => iteratedDerivWithin j f (Set.Ioo (0 : ℝ) 1) z)
        (iteratedDerivWithin (j + 1) f (Set.Ioo (0 : ℝ) 1) y) y := by
  intro y hy
  -- `f` is `C^(r+1)`, so for `j ≤ r` the `j`-th within-derivative is differentiable on `I`.
  have hdiff : DifferentiableOn ℝ (iteratedDerivWithin j f (Set.Ioo (0 : ℝ) 1))
      (Set.Ioo (0 : ℝ) 1) :=
    hf.differentiableOn_iteratedDerivWithin (Nat.cast_lt.mpr (Nat.lt_succ_of_le hj))
      (uniqueDiffOn_Ioo 0 1)
  -- hence it has a within-derivative at `y`, whose value is `derivWithin ... y`.
  have hdw : HasDerivWithinAt (fun z => iteratedDerivWithin j f (Set.Ioo (0 : ℝ) 1) z)
      (derivWithin (iteratedDerivWithin j f (Set.Ioo (0 : ℝ) 1)) (Set.Ioo (0 : ℝ) 1) y)
      (Set.Ioo (0 : ℝ) 1) y :=
    (hdiff y hy).hasDerivWithinAt
  -- `I` is open, so the within-derivative at an interior point is an honest derivative.
  have hnhds : Set.Ioo (0 : ℝ) 1 ∈ nhds y := isOpen_Ioo.mem_nhds hy
  -- and `derivWithin` of the `j`-th within-derivative is the `(j+1)`-st within-derivative.
  rw [iteratedDerivWithin_succ]
  exact hdw.hasDerivAt hnhds

end Work.WilG3
