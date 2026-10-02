import Mathlib
import Submission.Work.MRMT.Found.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

open MeasureTheory Filter Topology
open scoped Topology ENNReal

/-- If the Beltrami coefficient `μ` vanishes a.e. on a neighbourhood `U` of the compact set `L`,
then the approximating coefficients `μn` of a principal solution have vanishing `L²`-norm on `L`:
`∫_L ‖μn n‖² → 0`.  This is dominated convergence on `L` (which has finite measure),
using the uniform bound `‖μn n‖ ≤ k < 1` and the a.e. pointwise convergence `μn n → μ`. -/
theorem tendsto_integral_normSq_muN {μ : ℂ → ℂ} (d : PrincipalData μ)
    {U L : Set ℂ} (hL : IsCompact L) (hLU : L ⊆ U)
    (h0 : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), z ∈ U → μ z = 0) :
    Filter.Tendsto (fun n => ∫ z in L, ‖d.μn n z‖ ^ 2) Filter.atTop (nhds 0) := by
  have hI : IsFiniteMeasure ((MeasureTheory.volume : MeasureTheory.Measure ℂ).restrict L) := by
    rw [isFiniteMeasure_restrict]; exact hL.measure_lt_top.ne
  -- a.e. pointwise convergence of `‖μn n ·‖²` to `0` on `L`
  have hlim : ∀ᵐ z ∂((MeasureTheory.volume : MeasureTheory.Measure ℂ).restrict L),
      Filter.Tendsto (fun n => ‖d.μn n z‖ ^ 2) Filter.atTop (nhds 0) := by
    rw [MeasureTheory.ae_restrict_iff' hL.measurableSet]
    filter_upwards [d.tendsto_μn, h0] with z hz hz0 hzL
    have hzU : z ∈ U := hLU hzL
    have hμz : μ z = 0 := hz0 hzU
    have h1 : Filter.Tendsto (fun n => ‖d.μn n z‖) Filter.atTop (nhds 0) := by
      have h2 := hz.norm
      rw [hμz, norm_zero] at h2
      exact h2
    have h3 := h1.pow 2
    simpa using h3
  -- uniform bound `‖μn n‖² ≤ (max k 0)²`
  have hC : ∃ C : ℝ, ∀ᶠ n in Filter.atTop,
      ∀ᵐ ω ∂((MeasureTheory.volume : MeasureTheory.Measure ℂ).restrict L),
        ‖‖d.μn n ω‖ ^ 2‖ ≤ C := by
    refine ⟨(max d.k 0) ^ 2, Filter.Eventually.of_forall fun n => ?_⟩
    filter_upwards with ω
    have hle : ‖d.μn n ω‖ ≤ max d.k 0 := le_trans (d.norm_μn n ω) (le_max_left _ _)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) hle 2
  -- measurability of the integrands
  have hmeas : ∀ᶠ n in Filter.atTop,
      AEStronglyMeasurable (fun z => ‖d.μn n z‖ ^ 2)
        ((MeasureTheory.volume : MeasureTheory.Measure ℂ).restrict L) :=
    Filter.Eventually.of_forall fun n =>
      (((d.contDiff_μn n).continuous.norm.pow 2)).aestronglyMeasurable
  have h := MeasureTheory.tendsto_integral_filter_of_norm_le_const
    (μ := (MeasureTheory.volume : MeasureTheory.Measure ℂ).restrict L) (l := Filter.atTop)
    (F := fun n z => ‖d.μn n z‖ ^ 2) (f := fun _ => 0) hmeas hC hlim
  simpa using h

end Work.MRMT.Found
