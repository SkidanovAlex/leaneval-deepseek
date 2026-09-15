import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace Commons.Analysis.Integral

open MeasureTheory Filter Set intervalIntegral
open scoped Topology

theorem interval_avg_left_tendsto (f : ℝ → ℂ) (hf : Continuous f) (t₀ : ℝ) :
    Filter.Tendsto
      (fun τ : ℝ => (1 / τ) • intervalIntegral f (t₀ - τ) t₀ (MeasureTheory.volume : MeasureTheory.Measure ℝ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f t₀)) := by
  change Tendsto (fun τ : ℝ => (1 / τ) • ∫ x in (t₀ - τ)..t₀, f x) (𝓝[>] 0) (𝓝 (f t₀))
  -- The primitive `F u = ∫ x in t₀..u, f x` has derivative `f t₀` at `t₀`.
  have hF : HasDerivAt (fun u => ∫ x in t₀..u, f x) (f t₀) t₀ :=
    (hf.integral_hasStrictDerivAt t₀ t₀).hasDerivAt
  -- Hence its slope tends to `f t₀` from the left.
  have hslope : Tendsto (slope (fun u => ∫ x in t₀..u, f x) t₀) (𝓝[<] t₀) (𝓝 (f t₀)) :=
    (hasDerivAt_iff_tendsto_slope_left_right.mp hF).1
  -- The map `τ ↦ t₀ - τ` sends `𝓝[>] 0` to `𝓝[<] t₀`.
  have ht : Tendsto (fun τ : ℝ => t₀ - τ) (𝓝[>] 0) (𝓝[<] t₀) := by
    have h1 : Tendsto (fun τ : ℝ => -τ) (𝓝[>] 0) (𝓝[<] 0) := by
      simpa using tendsto_neg_nhdsGT_neg (a := (0 : ℝ))
    have h2 : Tendsto (fun τ : ℝ => t₀ + τ) (𝓝[<] 0) (𝓝[<] t₀) := by
      have hmap : map (fun τ : ℝ => t₀ + τ) (𝓝[<] (0 : ℝ)) = 𝓝[<] t₀ := by
        simpa using Filter.map_add_left_nhdsLT (c := t₀) (a := 0)
      exact hmap.le
    simpa [sub_eq_add_neg, Function.comp_def] using h2.comp h1
  have hcomp : Tendsto (fun τ : ℝ => slope (fun u => ∫ x in t₀..u, f x) t₀ (t₀ - τ)) (𝓝[>] 0) (𝓝 (f t₀)) :=
    hslope.comp ht
  -- The two functions agree.
  refine hcomp.congr fun τ => ?_
  rw [slope_def_module]
  rw [intervalIntegral.integral_same, sub_zero]
  have hsub : (t₀ - τ) - t₀ = -τ := by ring
  rw [hsub]
  conv_lhs => rw [intervalIntegral.integral_symm (a := t₀ - τ) (b := t₀)]
  rw [← neg_inv, neg_smul, smul_neg, neg_neg, one_div]

end Commons.Analysis.Integral