import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.EllExist.Honesty.RadGreenDefs
import Submission.Work.FTS.EllExist.Honesty.IooIntervalTool
import Submission.Work.FTS.EllExist.Honesty.G1_est
import Submission.Work.FTS.EllExist.Honesty.G2_est

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllExist.Honesty

open MeasureTheory Set
open scoped Real Topology

-- `radGreen α m c` is the decaying solution of the mode-`m` radial Euler equation
-- `-α²z²a'' - α(5+α)z a' + λ_m a = c` (λ_m = 2m(2m+5)), in explicit Green's-function form
-- (`Work.FTS.PhiStar.Radial.radGreen`, with `s⁻ = -(2m+5)/α`, `s⁺ = 2m/α`,
--  `K = 1/(α(4m+5))`).  This is the `z → 0` half of the weighted `L²`-honesty of `radGreen`,
-- i.e. of the mode-`m` coefficient `a m = radGreen α m (cmode m F)` of the solution
-- `Ψ = Σ_m a m(z) e_m(θ)` of `bslOp α Ψ = F`.
--
-- ROUTE (as proved; the two Green terms separately, `radGreen = K(G₁+G₂)` and `(G₁+G₂)² ≤ 2G₁²+2G₂²`).
-- With `G₁ := G1 α m c = z^{s⁻}∫_0^z c t^{-1-s⁻}dt` and `G₂ := G2 α m c = z^{s⁺}∫_z^∞ c t^{-1-s⁺}dt`
-- (`s⁻ = -(2m+5)/α`, `s⁺ = 2m/α`, `K = 1/(α(4m+5))`; see `RadGreenDefs`), both terms are estimated
-- by an *energy identity* plus the FTC — no Tonelli/Fubini is needed, and this is the route
-- formalised here (`G1_est`, `G2_est`):
-- * `z·G₁' = s⁻·G₁ + c`  and  `z·G₂' = s⁺·G₂ - c`; hence `u := G₁²/z³` satisfies
--   `u' = ((2s⁻-3)G₁² + 2cG₁)/z⁴` and `v := G₂²/z³` satisfies `v' = ((2s⁺-3)G₂² - 2cG₂)/z⁴`.
-- * FTC on `[x,y] ⊆ (0,1)`: `(3-2s⁻)∫_x^y G₁²/z⁴ = 2∫_x^y cG₁/z⁴ + G₁(x)²/x³ - G₁(y)²/y³`.
--   The *pointwise* estimate `|G₁(z)| ≤ z^{3/2}√(M₀/(2a+3))` (`a := (2m+5)/α = -s⁻`,
--   `M₀ := ∫_0^1 c²/z⁴ < ∞`) only gives `G₁²/z⁴ = O(1/z)`, which is NOT integrable, so the endpoint
--   term is bounded instead by an AM–GM with the `x`-dependent weight `λ := x^{a-1/2}`
--   (`2|XY| ≤ λX² + Y²/λ`, `X = |c u|/u`, `Y = u^a`): `G₁(x)²/x³ ≤ CΦ` uniformly for `x ∈ (0,1]`.
--   The AM–GM `2|cG₁|/z⁴ ≤ η c²/z⁴ + η^{-1}G₁²/z⁴`, `η := 2/(3-2s⁻)`, together with
--   `∫_x^y c²/z⁴ ≤ M₀` then bounds `∫_x^y G₁²/z⁴` uniformly in `0 < x < y < 1`.
-- * For `G₂` the same identity on `[x,1]` has the harmless endpoint `-G₂(x)²/x³ ≤ 0` and
--   `G₂(1)² = (∫_{Ioi 1} c t^{-1-s⁺}dt)² ≤ (∫_{Ioi 1}|c|t^{-1-s⁺}dt)²`, which is finite by `hinf`;
--   no decay of `G₂` at `0` is needed, and none holds (for `c(z) = z²`, `∫_{Ioi z} c t^{-1-s⁺}dt`
--   blows up like `z^{-s⁺-1}` while `G₂(z) = z^{s⁺}·(that)` stays bounded).
-- * `integrableOn_add_sq_div_of_interval_bounds` (`IooIntervalTool`) turns the two uniform interval
--   bounds and the two continuity statements into `IntegrableOn ((G₁+G₂)²/z⁴) (0,1)`; multiplying by
--   `K²` and rewriting `radGreen = K(G₁+G₂)` gives the claim.
-- The range `1 ≤ m`, `α ≤ 1/4` is load-bearing: `2s⁺ = 4m/α ≥ 16 > 3`, which is what makes the
-- `G₂`-energy identity's AM–GM and the `z → 0` behaviour of `G₂²/z⁴` work.

theorem radGreen_l2_near_zero (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) (hm : 1 ≤ m)
    {c : ℝ → ℝ} (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun z => c z ^ 2 / z ^ 4) (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t => |c t| * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn
      (fun z => Work.FTS.PhiStar.Radial.radGreen α m c z ^ 2 / z ^ 4) (Set.Ioo 0 1) := by
  -- `radGreen = K·(G1 + G2)`; each of the two Green terms has uniformly bounded weighted
  -- `L²`-interval integrals near `z = 0` and is continuous on `(0,1)`, so their sum has an integrable
  -- weighted square (`integrableOn_add_sq_div_of_interval_bounds`); multiplying by `K²` gives the claim.
  obtain ⟨⟨M₁, hM₁, hb₁⟩, hc₁⟩ := G1_est α hα m hc h0
  obtain ⟨⟨M₂, hM₂, hb₂⟩, hc₂⟩ := G2_est α hα hα4 m hm hc h0 hinf
  have hc₂' : ContinuousOn (fun z => G2 α m c z) (Set.Ioo 0 1) :=
    hc₂.mono Set.Ioo_subset_Ioi_self
  have hsum : MeasureTheory.IntegrableOn
      (fun z => (G1 α m c z + G2 α m c z) ^ 2 / z ^ 4) (Set.Ioo 0 1) :=
    integrableOn_add_sq_div_of_interval_bounds hM₁ hM₂ hc₁ hc₂' hb₁ hb₂
  have hkey : (fun z => Work.FTS.PhiStar.Radial.radGreen α m c z ^ 2 / z ^ 4)
      = fun z => (1 / (α * (4 * (m : ℝ) + 5))) ^ 2 *
          ((G1 α m c z + G2 α m c z) ^ 2 / z ^ 4) := by
    funext z
    rw [radGreen_eq_G1_add_G2]
    ring
  rw [hkey]
  exact hsum.const_mul _

/-- The weighted `L²`-integrability of the `z^{s⁻}` Green term alone (the `z → 0` half). -/
theorem G1_sq_div_z4_integrableOn (α : ℝ) (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun z => c z ^ 2 / z ^ 4) (Set.Ioo 0 1)) :
    MeasureTheory.IntegrableOn (fun z => G1 α m c z ^ 2 / z ^ 4) (Set.Ioo 0 1) := by
  obtain ⟨⟨M₁, hM₁, hb₁⟩, hc₁⟩ := G1_est α hα m hc h0
  have h := integrableOn_add_sq_div_of_interval_bounds
    (F := fun z => G1 α m c z) (G := fun _ : ℝ => (0 : ℝ))
    hM₁ le_rfl hc₁ continuous_const.continuousOn hb₁ (by
      intro x y _ _ _
      simp)
  simpa using h

/-- The weighted `L²`-integrability of the `z^{s⁺}` Green term alone (the `z → 0` half). -/
theorem G2_sq_div_z4_integrableOn (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) (hm : 1 ≤ m)
    {c : ℝ → ℝ} (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun z => c z ^ 2 / z ^ 4) (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t => |c t| * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn (fun z => G2 α m c z ^ 2 / z ^ 4) (Set.Ioo 0 1) := by
  obtain ⟨⟨M₂, hM₂, hb₂⟩, hc₂⟩ := G2_est α hα hα4 m hm hc h0 hinf
  have h := integrableOn_add_sq_div_of_interval_bounds
    (F := fun _ : ℝ => (0 : ℝ)) (G := fun z => G2 α m c z)
    le_rfl hM₂ continuous_const.continuousOn (hc₂.mono Set.Ioo_subset_Ioi_self) (by
      intro x y _ _ _
      simp) hb₂
  simpa using h

end Work.FTS.EllExist.Honesty
