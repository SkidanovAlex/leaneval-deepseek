import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FM.Core2
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS_RegExport.RXT.Slots.v2_hkMem_pointwise_min
import Submission.Work.FTS_RegExport.RXT.continuousAt_integral_Itheta_of_bound
import Submission.Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_integrableOn_of_continuousOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `∂_z L₁₂(f)(z) = - L12dens (f)(z)` for a `C⁴` datum in `ℋ⁴`

This module proves `hasDerivAt_L12_C4`: for `0 < α ≤ 1`, a datum `f` which is `C⁴` on the
*open* quadrant `Q0 = (0,∞) × (0,π/2)` and honestly in `ℋ⁴` (`Work.Spaces.HkMem α 4 f`, i.e.
weighted integrability on the quadrant, with **no** boundary-traces and **no** decay), the
fundamental-model operator

  `Work.Construction.L12 f z = ∫_z^∞ ∫_0^{π/2} K(θ) f(s,θ)/s dθ ds`

is differentiable at every `z > 0`, with derivative `- L12dens f z`.

## Route

The two analytic inputs are completely independent.

* **Integrability** of the density on `(0,∞)` follows from continuity of `f` on the open quadrant
  and `HkMem α 4 f` alone
  (`Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_integrableOn_of_continuousOn`: Cauchy–Schwarz in
  `θ` against `K ∈ L²` together with the pointwise domination
  `(f s θ)² ≤ HkIntegrand α 4 f s θ / w(s)²`, then AM–GM against the two integrable pieces
  `(s/(1+s)²)²` and `s ↦ ∫_θ HkIntegrand α 4 f s θ`).

* **Continuity** of the density at `z > 0` (`L12dens_continuousAt_C4` below) is a dominated
  convergence statement: on `Iθ` the integrand `(f s θ/s)·K(θ)` converges pointwise to its value
  at `s = z` (continuity of `f` on the open quadrant, the two endpoints being null) and is
  dominated by the constant `C·|f|_{ℋ⁴}·K(θ)`, where `C` is the trace-free pointwise bound
  `|f s θ| ≤ C·min s 1·|f|_{ℋ⁴}` of `Work.FTS_RegExport.RXT.v2_hkMem_pointwise_min` — the
  `ℋ⁴ → L^∞` trade-off, which needs no boundary traces because it replaces the angular and
  radial Hardy inequalities by a mean-value and an Agmon-type localisation argument.

The fundamental theorem of calculus for the tail integral `∫_z^∞ g`
(`Work.FM.hasDerivAt_L12`) then finishes the proof, since `L₁₂` is the tail integral of its
density.

All declarations in this file rest on `[propext, Classical.choice, Quot.sound]` only.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Real

namespace Work.FTS_RegExport.RXT.STC

/-- **Continuity of the `L₁₂`-density of a `C⁴` datum in `ℋ⁴`.**

For `0 < α ≤ 1` and `f` which is `C⁴` on the open quadrant `Q0 = (0,∞) × (0,π/2)` and honestly
in `ℋ⁴`, the density `s ↦ ∫_θ K(θ) f(s,θ)/s` is continuous at every `z > 0`.

The only quantitative input is the trace-free pointwise bound
`|f s θ| ≤ C · min s 1 · |f|_{ℋ⁴}` (`v2_hkMem_pointwise_min`), which turns the pointwise
convergence of the integrand into a uniform domination by the integrable function
`C·|f|_{ℋ⁴}·K(·)` on `Iθ`. -/
theorem L12dens_continuousAt_C4 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) {z : ℝ} (hz : 0 < z) :
    ContinuousAt (Work.Construction.L12dens f) z := by
  -- the trace-free `ℋ⁴ → L^∞` trade-off
  obtain ⟨C, hC0, hCbd⟩ := Work.FTS_RegExport.RXT.v2_hkMem_pointwise_min hα hα1
  have hfc : ContinuousOn (Function.uncurry f) Work.FTS.EllipticEst.Q0 := hf.continuousOn
  have hCN : 0 ≤ C * Work.Spaces.HkNorm α 4 f :=
    mul_nonneg hC0 (Real.sqrt_nonneg _)
  have hpt : ∀ s θ : ℝ, 0 < s → 0 < θ → θ < π / 2 →
      |f s θ| ≤ C * min s 1 * Work.Spaces.HkNorm α 4 f := by
    intro s θ hs hθ0 hθ1
    exact hCbd f hf hmem 0 0 (by norm_num) s θ hs hθ0 hθ1
  -- the angular weight is continuous
  have hKIθ : ContinuousOn Work.Spaces.K Work.Spaces.Iθ := by
    rw [← Work.Elliptic.Ktheta_eq_K]
    exact Work.Elliptic.continuous_ktheta.continuousOn
  have hKIoo : ContinuousOn Work.Spaces.K (Set.Ioo 0 (π / 2)) :=
    hKIθ.mono Set.Ioo_subset_Icc_self
  -- a.e. strong measurability of the integrand for `s` near `z`
  have hG_meas : ∀ᶠ s in 𝓝 z, AEStronglyMeasurable
      (fun θ : ℝ => f s θ / s * Work.Spaces.K θ) (volume.restrict (Set.Ioo 0 (π / 2))) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with s hs
    have hslice : ContinuousOn (fun θ : ℝ => f s θ) (Set.Ioo 0 (π / 2)) :=
      hfc.comp (continuous_const.prodMk continuous_id).continuousOn (fun θ hθ => ⟨hs, hθ⟩)
    exact ((hslice.div_const s).mul hKIoo).aestronglyMeasurable measurableSet_Ioo
  -- the uniform domination `|f s θ / s| ≤ C·|f|_{ℋ⁴}` for `0 < s` and a.e. `θ`
  have hbound : ∀ᶠ s in 𝓝 z, ∀ᵐ θ ∂(volume.restrict (Set.Ioo 0 (π / 2))),
      ‖f s θ / s‖ ≤ C * Work.Spaces.HkNorm α 4 f := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with s hs
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hle : |f s θ| ≤ C * s * Work.Spaces.HkNorm α 4 f := by
      have h1 := hpt s θ hs hθ.1 hθ.2
      calc |f s θ| ≤ C * min s 1 * Work.Spaces.HkNorm α 4 f := h1
        _ = (C * Work.Spaces.HkNorm α 4 f) * min s 1 := by ring
        _ ≤ (C * Work.Spaces.HkNorm α 4 f) * s :=
            mul_le_mul_of_nonneg_left (min_le_left s 1) hCN
        _ = C * s * Work.Spaces.HkNorm α 4 f := by ring
    have hsabs : |s| = s := abs_of_pos hs
    have hnabs : ‖f s θ / s‖ = |f s θ| / s := by
      rw [Real.norm_eq_abs, abs_div, hsabs]
    rw [hnabs, div_le_iff₀ hs]
    have hrr : C * s * Work.Spaces.HkNorm α 4 f
        = (C * Work.Spaces.HkNorm α 4 f) * s := by ring
    rw [← hrr]
    exact hle
  -- pointwise convergence on the interior of `Iθ`
  have hcont : ∀ᵐ θ ∂(volume.restrict (Set.Ioo 0 (π / 2))),
      ContinuousAt (fun s : ℝ => f s θ / s) z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hθQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ⟩
    have hfat : ContinuousAt (Function.uncurry f) (z, θ) :=
      hfc.continuousAt ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds hθQ)
    have h2 : ContinuousAt (fun s : ℝ => (s, θ)) z :=
      (Continuous.prodMk continuous_id continuous_const).continuousAt
    have hsl : ContinuousAt (fun s : ℝ => Function.uncurry f (s, θ)) z :=
      hfat.comp (x := z) (f := fun s : ℝ => (s, θ)) h2
    have hsl' : ContinuousAt (fun s : ℝ => f s θ) z := by
      simpa only [Function.uncurry_apply_pair] using hsl
    exact hsl'.div continuousAt_id (ne_of_gt hz)
  have hmain := Work.FTS_RegExport.RXT.continuousAt_integral_Itheta_of_bound
      (G := fun s θ => f s θ / s) (φ := Work.Spaces.K) (z₀ := z)
      (K := C * Work.Spaces.HkNorm α 4 f) hCN hKIθ hG_meas hbound hcont
  -- the two integrals agree: `Icc 0 (π/2)` and `Ioo 0 (π/2)` differ by a null set
  have hmeas_eq : volume.restrict (Set.Icc (0 : ℝ) (π / 2))
      = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
    (Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc).symm
  have hfun : Work.Construction.L12dens f
      = fun s => ∫ θ, f s θ / s * Work.Spaces.K θ
          ∂(volume.restrict (Set.Ioo 0 (π / 2))) := by
    funext s
    show (∫ θ in Set.Icc (0 : ℝ) (π / 2), Work.Spaces.K θ * f s θ / s)
        = ∫ θ, f s θ / s * Work.Spaces.K θ ∂(volume.restrict (Set.Ioo 0 (π / 2)))
    rw [hmeas_eq]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun θ => ?_)
    ring
  rw [hfun]
  exact hmain

theorem hasDerivAt_L12_C4 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hmem : Work.Spaces.HkMem α 4 f) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z' => Work.Construction.L12 f z') (-(Work.Construction.L12dens f z)) z := by
  have hcontOn : ContinuousOn (Function.uncurry f) Work.FTS.EllipticEst.Q0 := hf.continuousOn
  have hint : IntegrableOn (Work.FM.L12dens Work.Spaces.K f) (Set.Ioi 0) :=
    Work.FTS.MeridianDyn.Bridge.Pieces.L12dens_integrableOn_of_continuousOn hcontOn hmem
  have hcontAt : ContinuousAt (Work.FM.L12dens Work.Spaces.K f) z :=
    L12dens_continuousAt_C4 hα hα1 hf hmem hz
  exact Work.FM.hasDerivAt_L12 (K := Work.Spaces.K) (f := f) hint hcontAt hz

end Work.FTS_RegExport.RXT.STC
