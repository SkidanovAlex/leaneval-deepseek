import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Filter

namespace Work.FTS.ClassC.VopGen.Core

/-- If `χ N : ℝ → ℝ` are measurable, take values in `[0,1]`, and converge pointwise to `1`
on `(0,∞)`, then for every `g` integrable on `Iz = [0,∞)` the integrals
`∫ z in Iz, (χ N z)^2 * g z` converge to `∫ z in Iz, g z`.

This is the dominated convergence theorem with dominating function `‖g‖`: the pointwise
convergence holds on `(0,∞)`, and the missing point `0` is `volume`-null in
`volume.restrict Iz`. -/
theorem cutoffTendsto {χ : ℕ → ℝ → ℝ}
    (hχm : ∀ N, Measurable (χ N))
    (hχnn : ∀ N z, 0 ≤ χ N z) (hχle : ∀ N z, χ N z ≤ 1)
    (hsat : ∀ z : ℝ, 0 < z → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → χ N z = 1)
    {g : ℝ → ℝ} (hg : MeasureTheory.Integrable g (MeasureTheory.volume.restrict Work.Spaces.Iz)) :
    Filter.Tendsto (fun N : ℕ => ∫ z in Work.Spaces.Iz, (χ N z) ^ 2 * g z) Filter.atTop
      (nhds (∫ z in Work.Spaces.Iz, g z)) := by
  -- `Iz` is measurable, hence is a.e. equal to the whole space for `volume.restrict Iz`.
  have hae_mem : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), z ∈ Work.Spaces.Iz :=
    MeasureTheory.ae_restrict_mem measurableSet_Ici
  -- the single point `0` is null for the restricted measure
  have hzero : (MeasureTheory.volume.restrict Work.Spaces.Iz) {0} = 0 := by
    rw [MeasureTheory.Measure.restrict_apply (measurableSet_singleton 0)]
    simp [Work.Spaces.Iz]
  have hae_ne : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), z ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    have : {a : ℝ | ¬ a ≠ 0} = {0} := by ext z; simp
    rw [this]; exact hzero
  -- pointwise convergence a.e.
  have hlim : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      Filter.Tendsto (fun N : ℕ => (χ N z) ^ 2 * g z) Filter.atTop (nhds (g z)) := by
    filter_upwards [hae_mem, hae_ne] with z hz hz0
    have hpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
    obtain ⟨N₀, hN₀⟩ := hsat z hpos
    have heq : (fun N : ℕ => (χ N z) ^ 2 * g z) =ᶠ[Filter.atTop] (fun _ => g z) := by
      filter_upwards [Filter.eventually_ge_atTop N₀] with N hN
      rw [hN₀ N hN]; ring
    exact Filter.Tendsto.congr' heq.symm tendsto_const_nhds
  -- measurability of the approximants
  have hFmeas : ∀ N, MeasureTheory.AEStronglyMeasurable (fun z => (χ N z) ^ 2 * g z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    fun N => ((hχm N).pow_const 2).aestronglyMeasurable.mul hg.aestronglyMeasurable
  -- `‖g‖` dominates every approximant pointwise
  have hbound : ∀ N, ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ‖(χ N z) ^ 2 * g z‖ ≤ ‖g z‖ := by
    intro N
    filter_upwards with z
    have h1 : (χ N z) ^ 2 ≤ 1 := pow_le_one₀ (hχnn N z) (hχle N z)
    rw [norm_mul, Real.norm_of_nonneg (pow_nonneg (hχnn N z) 2)]
    exact mul_le_of_le_one_left (norm_nonneg _) h1
  exact MeasureTheory.tendsto_integral_of_dominated_convergence (fun z => ‖g z‖)
    hFmeas hg.norm hbound hlim

end Work.FTS.ClassC.VopGen.Core
