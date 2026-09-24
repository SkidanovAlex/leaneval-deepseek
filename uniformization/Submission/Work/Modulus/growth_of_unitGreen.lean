import Mathlib
import Submission.Work.Modulus.Defs

/-!
# Growth of a unit Green function at its pole

If a real-valued function `E` on a complex one-manifold `X` satisfies the coefficient-one
logarithmic bound
`|E x + log ‖chart_z₀ x - chart_z₀ z₀‖| ≤ C`
on a neighbourhood `V` of the pole `z₀`, then `E x → +∞` as `x → z₀` off the pole: for every real
`A` there is a neighbourhood `W` of `z₀` on which `E > A` away from `z₀`.

This is purely topological/real-analytic: the chart at `z₀` is continuous and injective on its
(open) source, so `‖chart_z₀ x - chart_z₀ z₀‖` can be made smaller than `exp (-(A + C))`
(and strictly positive for `x ≠ z₀`), whence `E x ≥ -C - log ‖…‖ > A`.
-/

open scoped Manifold Topology

open Filter Set

namespace Work.Modulus

theorem growth_of_unitGreen
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {z₀ : X} {E : X → ℝ} {C : ℝ} {V : Set X} (hV : V ∈ nhds z₀)
    (hbnd : ∀ x ∈ V, x ≠ z₀ →
      |E x + Real.log ‖(chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀‖| ≤ C) :
    ∀ A : ℝ, ∃ W : Set X, W ∈ nhds z₀ ∧ ∀ x ∈ W, x ≠ z₀ → A < E x := by
  intro A
  set e := chartAt ℂ z₀ with he
  have hzsrc : z₀ ∈ e.source := mem_chart_source ℂ z₀
  have htend : Tendsto (fun x => ‖e x - e z₀‖) (𝓝 z₀) (𝓝 0) := by
    have h1 : Tendsto (fun x => e x) (𝓝 z₀) (𝓝 (e z₀)) :=
      e.continuousOn.continuousAt (e.open_source.mem_nhds hzsrc)
    have h2 : Tendsto (fun _ : X => e z₀) (𝓝 z₀) (𝓝 (e z₀)) := tendsto_const_nhds
    simpa using (h1.sub h2).norm
  have hev : {x | ‖e x - e z₀‖ < Real.exp (-(A + C))} ∈ 𝓝 z₀ :=
    htend.eventually (isOpen_Iio.mem_nhds (Real.exp_pos _))
  refine ⟨{x | ‖e x - e z₀‖ < Real.exp (-(A + C))} ∩ e.source ∩ V, ?_, ?_⟩
  · exact inter_mem (inter_mem hev (e.open_source.mem_nhds hzsrc)) hV
  · intro x hx hxne
    obtain ⟨⟨hx1, hx2⟩, hxV⟩ := hx
    have hne : e x ≠ e z₀ := fun h => hxne (e.injOn hx2 hzsrc h)
    have hr0 : 0 < ‖e x - e z₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hlog : Real.log ‖e x - e z₀‖ < -(A + C) := by
      have h := Real.log_lt_log hr0 hx1
      rwa [Real.log_exp] at h
    have hb := (abs_le.mp (hbnd x hxV hxne)).1
    linarith

end Work.Modulus
