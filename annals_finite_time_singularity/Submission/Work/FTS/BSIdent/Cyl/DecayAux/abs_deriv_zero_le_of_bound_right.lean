import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Set Function Filter
open scoped Topology

namespace Work.FTS.BSIdent.Cyl.DecayAux

theorem abs_deriv_zero_le_of_bound_right {f : ℝ → ℝ} {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 < δ)
    (hdiff : ∀ z ∈ Set.Ioo 0 δ, DifferentiableAt ℝ f z)
    (hbound : ∀ z ∈ Set.Ioo 0 δ, |deriv f z| ≤ M) :
    |deriv f 0| ≤ M := by
  by_cases h0 : DifferentiableAt ℝ f 0
  · -- `f` is differentiable at `0`: the difference quotients on the right of `0`
    -- converge to `deriv f 0`, and each of them is a derivative of `f` at an interior
    -- point of `(0, δ)`, hence bounded by `M` in absolute value.
    have hsub : Set.Ioi (0 : ℝ) ⊆ ({0}ᶜ : Set ℝ) := fun y hy => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt hy
    have hslope : Tendsto (slope f 0) (𝓝[>] (0 : ℝ)) (𝓝 (deriv f 0)) :=
      h0.hasDerivAt.tendsto_slope.mono_left (nhdsWithin_mono 0 hsub)
    apply le_of_tendsto hslope.abs
    filter_upwards [Ioo_mem_nhdsGT hδ] with x hx
    have hcont : ContinuousOn f (Icc 0 x) := fun y hy => by
      rcases eq_or_lt_of_le hy.1 with rfl | hlt
      · exact h0.continuousAt.continuousWithinAt
      · exact ((hdiff y ⟨hlt, lt_of_le_of_lt hy.2 hx.2⟩).continuousAt).continuousWithinAt
    have hdiffOn : DifferentiableOn ℝ f (Ioo 0 x) := fun y hy =>
      (hdiff y ⟨hy.1, lt_trans hy.2 hx.2⟩).differentiableWithinAt
    obtain ⟨c, hc, hceq⟩ := exists_deriv_eq_slope f hx.1 hcont hdiffOn
    have hs : slope f 0 x = deriv f c := by rw [hceq, slope_def_field]
    rw [hs]
    exact hbound c ⟨hc.1, lt_trans hc.2 hx.2⟩
  · -- `f` is not differentiable at `0`: `deriv f 0 = 0` and `M ≥ 0`.
    rw [deriv_zero_of_not_differentiableAt h0, abs_zero]
    exact hM

end Work.FTS.BSIdent.Cyl.DecayAux
