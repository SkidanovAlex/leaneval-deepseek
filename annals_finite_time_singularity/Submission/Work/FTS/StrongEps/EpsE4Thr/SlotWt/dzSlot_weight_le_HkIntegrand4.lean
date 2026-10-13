/-
Copyright: work module for the Elgindi finite-time singularity project.

# A single pure `D_z`-slot of the strong weight is dominated by `HkIntegrand α 4 g`

For `c ≥ -η` and a slot `m ≤ 4`, the weighted square
`w(z)² · sin(2θ)^c · (D_z^m g)²` is bounded *pointwise* by `HkIntegrand α 4 g`.

Indeed, the `z`-part of `HkIntegrand` contains the term
`(D_z^m g · w / sin(2θ)^{η/2})² = (D_z^m g)² · w² · sin(2θ)^{-η}`, and on `θ ∈ (0,π/2)`
one has `0 < sin(2θ) ≤ 1`, so `sin(2θ)^c = sin(2θ)^{-η} · sin(2θ)^{c+η}` with
`sin(2θ)^{c+η} ≤ 1` (as `c + η ≥ 0`).

Note: the statement of the target theorem uses the notation `π`, which requires
`open scoped Real` in this workspace (the file otherwise fails to elaborate, since the
project sets `autoImplicit = false`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.H2.HeasyBlocksId
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.pgfAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.StrongEps.EpsE4Thr.SlotWt

theorem dzSlot_weight_le_HkIntegrand4 {α c : ℝ} {g : ℝ → ℝ → ℝ} {m : ℕ}
    (hc : -(Work.Spaces.eta) ≤ c) (hm : m ≤ 4) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ c * (Work.Spaces.DzIter m g z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  -- `sin(2θ) ∈ (0,1]` on the open strip
  have hsin_pos : 0 < Real.sin (2 * θ) := by
    refine Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) ?_
    have hp := Real.pi_pos
    linarith [hθ.2]
  have hsin_le : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hcη : 0 ≤ c + Work.Spaces.eta := by linarith [Work.Spaces.eta_pos]
  -- the resulting power of `sin(2θ)` is at most `1`
  have hs_cη_le : (Real.sin (2 * θ)) ^ (c + Work.Spaces.eta) ≤ 1 :=
    Real.rpow_le_one hsin_pos.le hsin_le hcη
  -- the matching slot of the `H^k`-integrand
  have hterm := Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ m hm
  -- split `sin(2θ)^c = sin(2θ)^{-η} · sin(2θ)^{c+η}`
  have h1 : (Real.sin (2 * θ)) ^ c
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        * (Real.sin (2 * θ)) ^ (c + Work.Spaces.eta) := by
    rw [← Real.rpow_add hsin_pos]
    congr 1
    ring
  -- `(sin(2θ)^{η/2})² = sin(2θ)^{η}`
  have h3 : (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Real.sin (2 * θ)) ^ (Work.Spaces.eta) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hsin_pos.le]
    congr 1
    ring
  -- expand the weighted `D_z`-slot
  have h2 : (Work.Spaces.DzIter m g z θ
        * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
      = (Work.Spaces.DzIter m g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    rw [mul_pow, div_pow, h3, Real.rpow_neg hsin_pos.le]
    ring
  calc (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ c * (Work.Spaces.DzIter m g z θ) ^ 2
      = (Work.Spaces.DzIter m g z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2
        * (Real.sin (2 * θ)) ^ (c + Work.Spaces.eta) := by
        rw [h1, h2]; ring
    _ ≤ (Work.Spaces.DzIter m g z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hs_cη_le
          (sq_nonneg (Work.Spaces.DzIter m g z θ
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))))
    _ = (Work.Spaces.DzIter m g z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 := mul_one _
    _ ≤ Work.Spaces.HkIntegrand α 4 g z θ := hterm

end Work.FTS.StrongEps.EpsE4Thr.SlotWt
