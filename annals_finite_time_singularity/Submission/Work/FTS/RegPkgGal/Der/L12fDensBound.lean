/-
# `Work.FTS.RegPkgGal.Der.L12fDensBound` — the pointwise bound and the support of the density

`L12dens K f s = ∫_{θ∈Iθ} K(θ) f(s,θ)/s`, with `K(θ) = 3 sinθ cos²θ ≥ 0`.

**The two claims.**  For a `Jet` profile `F` which is additionally *linear near the axis*
(`|F z θ τ| ≤ Kl·z` for `0 < z < 1`) and *supported in `z ≤ Lf`*:

* `|L12dens K (gSlice F τ) s| ≤ 6 · max Kl N` for every `s > 0`;
* `L12dens K (gSlice F τ) s = 0` for `s ≥ Lf`.

**The mathematics.**  The second claim is immediate: `F s θ τ = 0` for every `θ` as soon as
`s ≥ Lf`, so the integrand vanishes identically.

For the first, split at `s = 1`:

* `0 < s < 1`: `|F s θ τ| ≤ Kl·s`, so the integrand is dominated by `3·(Kl·s)/s = 3·Kl`;
* `s ≥ 1`: `|F s θ τ| ≤ N` by the `Jet` bound, so the integrand is dominated by
  `3·N/s ≤ 3·N`.

In both cases the angular integral over `Iθ` is at most `3·max Kl N·(π/2) ≤ 6·max Kl N`, since
`π < 4`.  The factor `6` of the consumer `jet_L12f` is comfortable for this argument.

The only measure theory used is `norm_setIntegral_le_of_norm_le_const` on the finite measure
`volume ↾ Iθ` (`volume_Iθ_lt_top`, `volume_real_Iθ = π/2`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.RegPkgGal.Der.L12fBasic

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

theorem L12fDensBound {α S N Kl Lf : ℝ} {F : ℝ → ℝ → ℝ → ℝ}
    (hJ : Work.FTS.Regularity.Jet α S N F)
    (hlin : 0 ≤ Kl ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      |F z θ τ| ≤ Kl * z)
    (hsupp : 0 < Lf ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, Lf ≤ z → F z θ τ = 0) :
    (∀ τ ∈ Set.Icc 0 S, ∀ s : ℝ, 0 < s →
        |Work.FM.L12dens Work.Spaces.K (Work.FTS.Regularity.gSlice F τ) s| ≤ 6 * max Kl N) ∧
    (∀ τ ∈ Set.Icc 0 S, ∀ s : ℝ, Lf ≤ s →
        Work.FM.L12dens Work.Spaces.K (Work.FTS.Regularity.gSlice F τ) s = 0) := by
  have hKl0 : 0 ≤ Kl := hlin.1
  have hN0 : 0 ≤ N := hJ.nonneg
  refine ⟨?_, ?_⟩
  · intro τ hτ s hs
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
  · intro τ hτ s hs
    -- the slice vanishes identically beyond `Lf`, so the density is `0`
    rw [Work.FM.L12dens]
    have hzero : (fun θ : ℝ =>
        Work.Spaces.K θ * (Work.FTS.Regularity.gSlice F τ) s θ / s) = fun _ => (0 : ℝ) := by
      funext θ
      rw [Work.FTS.Regularity.gSlice_apply, hsupp.2 τ hτ s θ hs]
      ring
    rw [hzero, integral_zero]

end Work.FTS.RegPkgGal.Der
