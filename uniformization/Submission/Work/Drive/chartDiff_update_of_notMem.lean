import Mathlib
import Submission.Work.Drive.EnergyCover

/-!
# Changing a function at a point outside the set on which it is differentiable in a chart

`Work.Drive.chartDiff_update_of_notMem`: if `f` is differentiable in the chart `c` at every point
of `Ω ∩ c.source` and `q ∉ Ω`, then changing the value of `f` at the single point `q` does not
destroy this property.  Indeed `q ∉ Ω` means `x ≠ q` for every `x ∈ Ω ∩ c.source`, and `c.symm` is
continuous at `c x` (it is continuous on the open set `c.target`), so `c.symm w ≠ q` for all `w` in
a neighbourhood of `c x`; the two chart representatives therefore agree on a neighbourhood of
`c x`.
-/

namespace Work.Drive

theorem chartDiff_update_of_notMem {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] {c : OpenPartialHomeomorph X ℂ} {f : X → ℝ} {Ω : Set X}
    {q : X} {c₀ : ℝ} [DecidableEq X] (hq : q ∉ Ω) (h : Work.Drive.ChartDiff c f Ω) :
    Work.Drive.ChartDiff c (Function.update f q c₀) Ω := by
  intro x hx
  obtain ⟨hxΩ, hxsrc⟩ := hx
  have hxc : c x ∈ c.target := c.map_source hxsrc
  have hxsymm : c.symm (c x) = x := c.left_inv hxsrc
  have hcont : ContinuousAt c.symm (c x) :=
    c.continuousOn_symm.continuousAt (c.open_target.mem_nhds hxc)
  have hne : c.symm (c x) ≠ q := by rw [hxsymm]; exact fun hxy => hq (hxy ▸ hxΩ)
  have hpre : ∀ᶠ w in nhds (c x), c.symm w ≠ q :=
    hcont.preimage_mem_nhds ((isClosed_singleton (x := q)).isOpen_compl.mem_nhds hne)
  have hev : (fun w : ℂ => f (c.symm w))
      =ᶠ[nhds (c x)] (fun w => Function.update f q c₀ (c.symm w)) :=
    hpre.mono fun w hw => by simp [hw]
  exact (h x ⟨hxΩ, hxsrc⟩).congr_of_eventuallyEq hev.symm

end Work.Drive
