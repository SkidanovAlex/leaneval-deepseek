/-
# `Work.FTS.PhiStar.RadGreenActA`

The mode-`m` radial Green operator `radGreen α m` (`Radial/Defs.lean`) commutes with the radial
Euler operator `A = α z²∂_zz + (5+α) z ∂_z` up to the indicial constant:

  `radGreen α m (A c) z = α z² (radGreen α m c)'' z + (5+α) z (radGreen α m c)' z`   (`z > 0`),

for every `c` of class `C²` on `(0,∞)` decaying like `1/t` (with its two derivatives,
`|c^(k)(t)| ≤ A/(1+t^{k+1})`, `k ≤ 2`).

Mathematically: with `q = (2m+5)/α`, `p = 2m/α` and `K = 1/(α(4m+5))`,
`radGreen α m c z = K (z^{-q}A_c(z) + z^p B_c(z))`, `A_c = ∫₀^z c t^{q-1}`,
`B_c = ∫_z^∞ c t^{-p-1}`, and `radGreen α m c` solves `-α²z²a'' - α(5+α)z a' + λ_m a = c`
(`λ_m = 2m(2m+5) = α²pq`), so the right-hand side is `(λ_m a - c)/α`.  On the other side, two
integrations by parts of the Green formula applied to `d = A c` with the primitives
`α t^{q+1}c' - 2mt^q c` and `α t^{1-p}c' + (2m+5)t^{-p} c` (whose boundary terms vanish by the
growth hypothesis) give

  `radGreen α m d z = K (2mq z^{-q}A_c + αpq z^p B_c - (4m+5) c)`,

and `2mq = αpq` together with `K(4m+5) = 1/α`, `λ_m/α = αpq` makes the two sides agree.

## Structure of the proof

* `RadGreenSupport.src_integrable` — the two integrability conditions on `c` (from the growth
  hypothesis), which feed the ODE for `radGreen α m c`;
* `RadGreenSupport.radGreen_ode_weak` — the ODE `-α²z²a'' - α(5+α)z a' + λ_m a = c` under exactly
  those hypotheses;
* `RadGreenSupport.ibp_lower`, `RadGreenSupport.ibp_upper` — the two integrations by parts of the
  Green formula for the source `d = α t² c'' + (5+α) t c'`;
* the remaining rewriting/arithmetic is done here (with the powers `z^{-q}`, `z^{q+1}`, `z^q`,
  `z^p`, `z^{1-p}`, `z^{-p}` abstracted so that the final step is `field_simp; ring`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.PhiStar.Radial.radGreen_solves
import Submission.Work.FTS.PhiStar.Radial.radGreenIntended
import Submission.Work.FTS.PhiStar.RadGreenSupport.src_integrable
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_lower
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

theorem RadGreenActA {α : ℝ} (m : ℕ) (hα : 0 < α) (hα5 : α ≤ 1 / 5) (hm : 1 ≤ m) {c : ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A) (hc : ContDiffOn ℝ 2 c (Set.Ioi 0)) (hb : ∀ k : ℕ, k ≤ 2 → ∀ t : ℝ, 0 < t → |iteratedDeriv k c t| ≤ A / (1 + t ^ (k + 1))) : ∀ z : ℝ, 0 < z → Work.FTS.PhiStar.Radial.radGreen α m (fun t => α * t ^ 2 * iteratedDeriv 2 c t + (5 + α) * t * deriv c t) z = α * z ^ 2 * iteratedDeriv 2 (Work.FTS.PhiStar.Radial.radGreen α m c) z + (5 + α) * z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z := by
  intro z hz
  -- ### 1. the hypotheses of the ODE for `radGreen α m c`
  have hcont : ContinuousOn c (Set.Ioi 0) := hc.continuousOn
  obtain ⟨h0, hinf⟩ := RadGreenSupport.src_integrable hα m hA hc hb
  have hode := RadGreenSupport.radGreen_ode_weak hα m hcont h0 hinf z hz
  -- ### 2. the right-hand side is `(λ_m · radGreen α m c z - c z)/α`
  have hI2 : iteratedDeriv 2 (Radial.radGreen α m c) z
      = deriv (deriv (Radial.radGreen α m c)) z := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [hI2]
  have hαne : α ≠ 0 := ne_of_gt hα
  have hR : α * z ^ 2 * deriv (deriv (Radial.radGreen α m c)) z
      + (5 + α) * z * deriv (Radial.radGreen α m c) z
      = (Radial.lamR m * Radial.radGreen α m c z - c z) / α := by
    rw [eq_div_iff hαne]
    linear_combination (-1) * hode
  rw [hR]
  -- ### 3. unfold the Green formula and integrate by parts in both integrals
  simp only [Radial.radGreen, neg_div]
  rw [RadGreenSupport.ibp_lower hα m hA hc hb hz,
    RadGreenSupport.ibp_upper hα m hA hc hb hz]
  -- ### 4. abstract the six powers, the two integrals, `K`, `c z` and `(deriv c) z`
  set Ac : ℝ := ∫ t in (0 : ℝ)..z, c t * t ^ ((2 * (m : ℝ) + 5) / α - 1) with hAc
  set Bc : ℝ := ∫ t in Set.Ioi z, c t * t ^ (-(2 * (m : ℝ) / α) - 1) with hBc
  set q : ℝ := (2 * (m : ℝ) + 5) / α with hq
  set p : ℝ := 2 * (m : ℝ) / α with hp
  set Zq : ℝ := z ^ (-q) with hZq
  set Zq1 : ℝ := z ^ (q + 1) with hZq1
  set Zq0 : ℝ := z ^ q with hZq0
  set Zp : ℝ := z ^ p with hZp
  set Zp1 : ℝ := z ^ (1 - p) with hZp1
  set Zp0 : ℝ := z ^ (-p) with hZp0
  set K : ℝ := 1 / (α * (4 * (m : ℝ) + 5)) with hK
  set cc : ℝ := c z with hcc
  set cd : ℝ := deriv c z with hcd
  -- ### 5. the four `rpow` products
  have hZqZq1 : Zq * Zq1 = z := by
    rw [hZq, hZq1, ← Real.rpow_add hz, show -q + (q + 1) = 1 from by ring, Real.rpow_one]
  have hZqZq0 : Zq * Zq0 = 1 := by
    rw [hZq, hZq0, ← Real.rpow_add hz, show -q + q = 0 from by ring, Real.rpow_zero]
  have hZpZp1 : Zp * Zp1 = z := by
    rw [hZp, hZp1, ← Real.rpow_add hz, show p + (1 - p) = 1 from by ring, Real.rpow_one]
  have hZpZp0 : Zp * Zp0 = 1 := by
    rw [hZp, hZp0, ← Real.rpow_add hz, show p + -p = 0 from by ring, Real.rpow_zero]
  -- ### 6. the two IBP results, cleaned up
  have hA1 : Zq * (α * Zq1 * cd - 2 * (m : ℝ) * Zq0 * cc + 2 * (m : ℝ) * q * Ac)
      = α * z * cd - 2 * (m : ℝ) * cc + 2 * (m : ℝ) * q * (Zq * Ac) := by
    rw [show Zq * (α * Zq1 * cd - 2 * (m : ℝ) * Zq0 * cc + 2 * (m : ℝ) * q * Ac)
        = α * cd * (Zq * Zq1) - 2 * (m : ℝ) * cc * (Zq * Zq0)
          + 2 * (m : ℝ) * q * (Zq * Ac) from by ring]
    rw [hZqZq1, hZqZq0]
    ring
  have hB1 : Zp * (-α * Zp1 * cd - (2 * (m : ℝ) + 5) * Zp0 * cc + (2 * (m : ℝ) + 5) * p * Bc)
      = -α * z * cd - (2 * (m : ℝ) + 5) * cc + (2 * (m : ℝ) + 5) * p * (Zp * Bc) := by
    rw [show Zp * (-α * Zp1 * cd - (2 * (m : ℝ) + 5) * Zp0 * cc + (2 * (m : ℝ) + 5) * p * Bc)
        = -α * cd * (Zp * Zp1) - (2 * (m : ℝ) + 5) * cc * (Zp * Zp0)
          + (2 * (m : ℝ) + 5) * p * (Zp * Bc) from by ring]
    rw [hZpZp1, hZpZp0]
    ring
  -- ### 7. the final arithmetic
  rw [eq_div_iff hαne]
  rw [hA1, hB1]
  have h45 : (4 * (m : ℝ) + 5) ≠ 0 := ne_of_gt (by positivity)
  have h5 : α * (4 * (m : ℝ) + 5) ≠ 0 := mul_ne_zero hαne h45
  simp only [hq, hp, hK, Radial.lamR]
  field_simp
  ring

end Work.FTS.PhiStar
