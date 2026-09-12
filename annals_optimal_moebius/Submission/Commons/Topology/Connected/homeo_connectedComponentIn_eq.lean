import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Connected.Basic

namespace Commons.Topology.Connected

theorem homeo_connectedComponentIn_eq {X : Type*} [TopologicalSpace X] (e : X ≃ₜ X)
    {s : Set X} (hs : e '' s = s) (x : X) (hx : x ∈ s) :
    e '' connectedComponentIn s x = connectedComponentIn s (e x) := by
  -- `e x` lies in `s`, since `x` does and `e '' s = s`.
  have hex : e x ∈ s := by
    rw [← hs]
    exact Set.mem_image_of_mem e hx
  -- Forward inclusion: the image of the connected component of `x` in `s`
  -- is preconnected and contains `e x`, hence is contained in the component.
  have h1 : e '' connectedComponentIn s x ⊆ connectedComponentIn s (e x) := by
    have hf : ContinuousOn (⇑e) s := e.continuous.continuousOn
    have h1raw :
        e '' connectedComponentIn s x ⊆ connectedComponentIn (e '' s) (e x) :=
      ContinuousOn.image_connectedComponentIn_subset hf hx
    simpa [hs] using h1raw
  -- Reverse inclusion, using the inverse homeomorphism.
  have hs' : e.symm '' s = s := by
    calc
      e.symm '' s = e.symm '' (e '' s) := by rw [hs]
      _ = s := by
        rw [← Set.image_comp, Homeomorph.symm_comp_self e]
        simp
  have h2 : e.symm '' connectedComponentIn s (e x) ⊆ connectedComponentIn s x := by
    have hg : ContinuousOn (⇑e.symm) s := e.symm.continuous.continuousOn
    have h2raw :
        e.symm '' connectedComponentIn s (e x) ⊆
          connectedComponentIn (e.symm '' s) (e.symm (e x)) :=
      ContinuousOn.image_connectedComponentIn_subset hg hex
    simpa [hs'] using h2raw
  have h3 : connectedComponentIn s (e x) ⊆ e '' connectedComponentIn s x := by
    have hmono :
        e '' (e.symm '' connectedComponentIn s (e x)) ⊆ e '' connectedComponentIn s x :=
      Set.image_mono h2
    have hcomp :
        e '' (e.symm '' connectedComponentIn s (e x)) = connectedComponentIn s (e x) := by
      rw [← Set.image_comp, Homeomorph.self_comp_symm e]
      simp
    simpa [hcomp] using hmono
  exact subset_antisymm h1 h3

end Commons.Topology.Connected