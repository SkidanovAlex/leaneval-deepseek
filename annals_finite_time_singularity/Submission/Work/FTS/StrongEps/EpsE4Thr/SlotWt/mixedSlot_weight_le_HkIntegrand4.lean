/-
Copyright: work module for the Elgindi finite-time singularity project.

# A single mixed slot of the strong weight is dominated by `HkIntegrand α 4 g`

For `c ≥ -γ(α)` and a slot `(b,a)` with `a ≥ 1`, `a + b ≤ 4`, the weighted square
`w(z)² · sin(2θ)^c · (D_z^b D_θ^a g)²` is bounded *pointwise* by `HkIntegrand α 4 g`.

Indeed, the mixed part of `HkIntegrand` contains the term
`(mixed b a g · Wt α)² = (mixed b a g)² · w² · sin(2θ)^{-γ}` (because
`Wt = w · sin(2θ)^{-γ/2}`), and on `θ ∈ (0,π/2)` one has `0 < sin(2θ) ≤ 1`, so
`sin(2θ)^c = sin(2θ)^{-γ} · sin(2θ)^{c+γ}` with `sin(2θ)^{c+γ} ≤ 1` (as `c + γ ≥ 0`).

Note: the statement of the target theorem uses the notation `π`, which requires
`open scoped Real` in this workspace (the file otherwise fails to elaborate, since the
project sets `autoImplicit = false`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.pgfAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.StrongEps.EpsE4Thr.SlotWt

theorem mixedSlot_weight_le_HkIntegrand4 {α c : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ} {a b : ℕ}
    (hc : -(Work.Spaces.gam α) ≤ c) (ha : 1 ≤ a) (hab : a + b ≤ 4) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ c * (Work.Spaces.mixed b a g z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  have hθ2 : θ < π / 2 := hθ.2
  -- `sin(2θ) ∈ (0,1]` on the open strip
  have hsin_pos : 0 < Real.sin (2 * θ) := by
    refine Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) ?_
    have hp := Real.pi_pos
    linarith
  have hsin_le : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hgam : 0 ≤ Work.Spaces.gam α := le_of_lt (Work.Spaces.gam_pos hα)
  have hcg : 0 ≤ c + Work.Spaces.gam α := by linarith
  -- the resulting power of `sin(2θ)` is at most `1`
  have hs_cg_le : (Real.sin (2 * θ)) ^ (c + Work.Spaces.gam α) ≤ 1 :=
    Real.rpow_le_one hsin_pos.le hsin_le hcg
  -- the matching slot of the `H^k`-integrand
  have hterm := Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ a b ha hab
  -- split `sin(2θ)^c = sin(2θ)^{-γ} · sin(2θ)^{c+γ}`
  have h1 : (Real.sin (2 * θ)) ^ c
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        * (Real.sin (2 * θ)) ^ (c + Work.Spaces.gam α) := by
    rw [← Real.rpow_add hsin_pos]
    congr 1
    ring
  -- `(sin(2θ)^{-γ/2})² = sin(2θ)^{-γ}`
  have h3 : (Real.sin (2 * θ) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hsin_pos.le]
    congr 1
    ring
  -- expand the weighted mixed slot
  have h2 : (Work.Spaces.mixed b a g z θ * Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.mixed b a g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, mul_pow, h3]
    ring
  calc (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ c * (Work.Spaces.mixed b a g z θ) ^ 2
      = (Work.Spaces.mixed b a g z θ * Work.Spaces.Wt α z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (c + Work.Spaces.gam α) := by
        rw [h1, h2]; ring
    _ ≤ (Work.Spaces.mixed b a g z θ * Work.Spaces.Wt α z θ) ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hs_cg_le
          (sq_nonneg (Work.Spaces.mixed b a g z θ * Work.Spaces.Wt α z θ))
    _ = (Work.Spaces.mixed b a g z θ * Work.Spaces.Wt α z θ) ^ 2 := mul_one _
    _ ≤ Work.Spaces.HkIntegrand α 4 g z θ := hterm

end Work.FTS.StrongEps.EpsE4Thr.SlotWt
