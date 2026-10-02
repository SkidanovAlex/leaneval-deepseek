import Mathlib
import Submission.Work.MRMT.Found.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found.PLWD

open MeasureTheory Filter Topology
open scoped Topology ENNReal

/-- Dominated convergence for the coefficient difference: the approximating coefficients `μn n`
of a principal solution converge a.e. to `μ`, they are uniformly bounded, and `χ` is a
compactly supported continuous multiplier, so `∫ ‖(μn n − μ) · χ‖² → 0`. -/
theorem tendsto_integral_normSq_mu_sub_mul {μ : ℂ → ℂ} (hμ : Work.MRMT.Found.Admissible μ)
    (d : Work.MRMT.Found.PrincipalData μ) {χ : ℂ → ℂ} (hχc : Continuous χ)
    (hχs : HasCompactSupport χ) :
    Filter.Tendsto (fun n => ∫ z, ‖(d.μn n z - μ z) * χ z‖ ^ 2) Filter.atTop (nhds 0) := by
  obtain ⟨k, hk, hkb⟩ := hμ.bound
  -- `‖χ‖²` is integrable (continuous, compactly supported)
  have hsq : HasCompactSupport (fun z : ℂ => ‖χ z‖ ^ 2) :=
    hχs.comp_left (g := fun w : ℂ => ‖w‖ ^ 2) (by simp)
  have hint : Integrable (fun z : ℂ => ‖χ z‖ ^ 2) (volume : Measure ℂ) :=
    (hχc.norm.pow 2).integrable_of_hasCompactSupport hsq
  -- the integrands are a.e. strongly measurable
  have hmeas : ∀ n, AEStronglyMeasurable (fun z => ‖(d.μn n z - μ z) * χ z‖ ^ 2)
      (volume : Measure ℂ) := fun n =>
    ((((d.contDiff_μn n).continuous.aestronglyMeasurable.sub hμ.meas).mul
      hχc.aestronglyMeasurable).norm.pow 2)
  -- uniform domination by `4‖χ‖²`
  have hbound : ∀ n, ∀ᵐ z ∂(volume : Measure ℂ),
      ‖(‖(d.μn n z - μ z) * χ z‖ ^ 2 : ℝ)‖ ≤ 4 * ‖χ z‖ ^ 2 := by
    intro n
    filter_upwards [hkb] with z hz
    have h1 : ‖d.μn n z - μ z‖ ≤ 2 := by
      calc ‖d.μn n z - μ z‖ ≤ ‖d.μn n z‖ + ‖μ z‖ := norm_sub_le _ _
        _ ≤ d.k + k := add_le_add (d.norm_μn n z) hz
        _ ≤ 2 := by linarith [d.hk]
    rw [Real.norm_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
    have h2 : ‖d.μn n z - μ z‖ ^ 2 ≤ 4 := by
      nlinarith [h1, norm_nonneg (d.μn n z - μ z)]
    exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
  -- a.e. pointwise convergence to `0`
  have hlim : ∀ᵐ z ∂(volume : Measure ℂ),
      Filter.Tendsto (fun n => ‖(d.μn n z - μ z) * χ z‖ ^ 2) Filter.atTop (nhds 0) := by
    filter_upwards [d.tendsto_μn] with z hz
    have h1 : Filter.Tendsto (fun n => d.μn n z - μ z) Filter.atTop (nhds (μ z - μ z)) :=
      hz.sub tendsto_const_nhds
    have h2 : Filter.Tendsto (fun n => (d.μn n z - μ z) * χ z) Filter.atTop
        (nhds ((μ z - μ z) * χ z)) := h1.mul tendsto_const_nhds
    have h3 : Filter.Tendsto (fun n => ‖(d.μn n z - μ z) * χ z‖) Filter.atTop
        (nhds ‖(μ z - μ z) * χ z‖) := h2.norm
    have h4 := h3.pow 2
    simpa using h4
  have h := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := (volume : Measure ℂ))
    (F := fun n z => ‖(d.μn n z - μ z) * χ z‖ ^ 2) (f := fun _ => 0)
    (fun z => 4 * ‖χ z‖ ^ 2) hmeas (hint.const_mul 4) hbound hlim
  simpa using h

end Work.MRMT.Found.PLWD
