import Mathlib
import Submission.Work.Implosion.All
import Submission.Work.PARIMPL.Basic
import Submission.Work.PARIMPL2.Direct.sum_lam2_div_sin_sq_le
import Submission.Work.PARIMPL2.Direct.norm_ecalPt_sq_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

/-!
# `∑ ‖ζ_j‖² ≤ 24/R` along a model orbit in the transit strip

Let `a = iλ` with `λ > 0`, `R ≥ 128`, `λ R² ≤ 1`, and let `u : ℕ → ℂ` be any sequence
of points whose real parts stay in the transit strip
`R/4 + 2 ≤ Re u_j ≤ π/λ − R/4` and decrease by at least `1/3` at each step.

Then `∑_{j<n} ‖ecalPt (iλ) (u_j)‖² ≤ 24/R`.

This is a direct combination of two already established estimates, and it needs *no*
information about the model dynamics or the imaginary parts:

* the pointwise bound `‖ecalPt (iλ) u‖² ≤ λ² / sin²(λ Re u)` (`norm_ecalPt_sq_le`),
  valid on the half strip `0 < Re u < π/λ`;
* the real-variable sum estimate `∑ λ²/sin²(λ x_j) ≤ 24/R` (`sum_lam2_div_sin_sq_le`),
  which uses the strip and the `1/3`-decrease.
-/

theorem sum_zeta_sq_24 (lam R : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R) (hlamR : lam * R ^ 2 ≤ 1)
    (n : ℕ) (u : ℕ → ℂ)
    (hx1 : ∀ j ≤ n, R / 4 + 2 ≤ (u j).re)
    (hx2 : ∀ j ≤ n, (u j).re ≤ Real.pi / lam - R / 4)
    (hdec : ∀ j < n, (u (j + 1)).re ≤ (u j).re - 1 / 3) :
    ∑ j ∈ Finset.range n, ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖ ^ 2 ≤ 24 / R := by
  -- Pointwise reduction to the `λ²/sin²(λ x)` kernel.
  have hper : ∀ j ∈ Finset.range n,
      ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖ ^ 2
        ≤ lam ^ 2 / (Real.sin (lam * (u j).re)) ^ 2 := by
    intro j hj
    have hjle : j ≤ n := le_of_lt (Finset.mem_range.mp hj)
    exact norm_ecalPt_sq_le lam (u j) hlam (by linarith [hx1 j hjle])
      (by linarith [hx2 j hjle])
  calc ∑ j ∈ Finset.range n, ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) (u j)‖ ^ 2
      ≤ ∑ j ∈ Finset.range n, lam ^ 2 / (Real.sin (lam * (u j).re)) ^ 2 :=
        Finset.sum_le_sum hper
    _ ≤ 24 / R := sum_lam2_div_sin_sq_le lam R u n hlam hR hlamR hx1 hx2 hdec

end Work.PARIMPL2.Direct
