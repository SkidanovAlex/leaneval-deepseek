/-
# `Work.FTS.RegPkgGal.Der.L12fDensUnif` — the linearity-free uniform bound on the `L₁₂`-density

The density of the fundamental model along a time slice is

  `L12dens K (gSlice F τ) s = ∫_{θ ∈ Iθ} K(θ)·F(s,θ,τ)/s dθ`,   `K(θ) = 3 sin θ cos²θ`,

and the claim is the *uniform bound*

  `|L12dens K (gSlice F τ) s| ≤ 6·max Kl N`  for `s > 0`, `τ ∈ [0,S]`,

from the `Jet` data (uniform bound `N` and joint `α`-Hölder) together with *linearity of the
profile at the axis*, `|F z θ τ| ≤ Kl·z` for `0 < z < 1` — and **with no support hypothesis**
(compare `L12fDensBound`, whose first conjunct this is: that conjunct never uses the support).

The mathematics is the elementary split at `s = 1`:

* `0 < s < 1`: `|F s θ τ| ≤ Kl·s`, so the integrand is dominated by `3·(Kl·s)/s = 3·Kl`;
* `s ≥ 1`: `|F s θ τ| ≤ N`, so the integrand is dominated by `3·N/s ≤ 3·N`.

In both cases the angular integral over `Iθ` is at most `3·max Kl N·(π/2) ≤ 6·max Kl N`, because
`π < 4`.  (The proof is the first branch of `L12fDensBound`, transcribed so as to dispense with the
unused support hypothesis.)
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.RegPkgGal.Der.L12fBasic
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FM.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.RegPkgGal.Der

set_option autoImplicit false

theorem L12fDensUnif {α S N Kl : ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hJ : Work.FTS.Regularity.Jet α S N F)
    (hlin : 0 ≤ Kl ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      |F z θ τ| ≤ Kl * z) :
    ∀ τ ∈ Set.Icc 0 S, ∀ s : ℝ, 0 < s →
      |Work.FM.L12dens Work.Spaces.K (Work.FTS.Regularity.gSlice F τ) s| ≤ 6 * max Kl N := by
  have hKl0 : 0 ≤ Kl := hlin.1
  have hN0 : 0 ≤ N := hJ.nonneg
  intro τ hτ s hs
  -- the pointwise bound on the integrand, uniformly in `θ ∈ Iθ`
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      ‖Work.Spaces.K θ * Work.FTS.Regularity.gSlice F τ s θ / s‖ ≤ 3 * max Kl N := by
    intro θ hθ
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hs, abs_mul]
    have hK : |Work.Spaces.K θ| ≤ 3 := abs_K_le_three hθ
    rcases lt_or_ge s 1 with hlt | hge
    · -- `s < 1`: linearity of the profile near the axis
      have hF : |Work.FTS.Regularity.gSlice F τ s θ| ≤ Kl * s :=
        hlin.2 τ hτ θ hθ s ⟨hs, hlt⟩
      have h1 : |Work.Spaces.K θ| * |Work.FTS.Regularity.gSlice F τ s θ| / s
          ≤ 3 * (Kl * s) / s := by
        apply div_le_div_of_nonneg_right _ hs.le
        exact mul_le_mul hK hF (abs_nonneg _) (by norm_num)
      have h2 : 3 * (Kl * s) / s = 3 * Kl := by
        rw [mul_div_assoc, mul_div_cancel_right₀ Kl (ne_of_gt hs)]
      have h3 : 3 * Kl ≤ 3 * max Kl N := by linarith [le_max_left Kl N]
      linarith
    · -- `s ≥ 1`: the uniform `Jet` bound
      have hF : |Work.FTS.Regularity.gSlice F τ s θ| ≤ N :=
        hJ.abs_le (le_of_lt hs) hθ hτ
      have h1 : |Work.Spaces.K θ| * |Work.FTS.Regularity.gSlice F τ s θ| / s
          ≤ 3 * N / s := by
        apply div_le_div_of_nonneg_right _ hs.le
        exact mul_le_mul hK hF (abs_nonneg _) (by norm_num)
      have h2 : 3 * N / s ≤ 3 * N := by
        rw [div_le_iff₀ hs]; nlinarith [hN0, hge]
      have h3 : 3 * N ≤ 3 * max Kl N := by linarith [le_max_right Kl N]
      linarith
  -- integrate the pointwise bound over the finite measure `volume ↾ Iθ`
  have hmain : |∫ θ in Work.Spaces.Iθ,
        Work.Spaces.K θ * Work.FTS.Regularity.gSlice F τ s θ / s|
      ≤ (3 * max Kl N) * (Real.pi / 2) := by
    rw [← Work.Spaces.volume_real_Iθ, ← Real.norm_eq_abs]
    exact MeasureTheory.norm_setIntegral_le_of_norm_le_const Work.Spaces.volume_Iθ_lt_top hpt
  have hfin : (3 * max Kl N) * (Real.pi / 2) ≤ 6 * max Kl N := by
    have hpi : Real.pi / 2 ≤ 2 := by linarith [Real.pi_lt_four]
    calc (3 * max Kl N) * (Real.pi / 2) = 3 * (Real.pi / 2) * max Kl N := by ring
      _ ≤ 3 * 2 * max Kl N := by
          have h0 : (0 : ℝ) ≤ max Kl N := le_trans hKl0 (le_max_left Kl N)
          have hm : 3 * (Real.pi / 2) ≤ 3 * 2 := by linarith
          exact mul_le_mul_of_nonneg_right hm h0
      _ = 6 * max Kl N := by ring
  rw [Work.FM.L12dens]
  exact le_trans hmain hfin

end Work.FTS.RegPkgGal.Der
