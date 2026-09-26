import Mathlib.Analysis.Normed.Order.Lattice

namespace Commons.Topology.Homeomorph

open Set

theorem intervalHomeo_coord_strictMono_or_anti {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (e : ({x : ℝ // x ∈ Set.Ioo a b}) ≃ₜ ({x : ℝ // x ∈ Set.Ioo c d})) :
    StrictMono (fun x : {x : ℝ // x ∈ Set.Ioo a b} => (e x : ℝ)) ∨
    StrictAnti (fun x : {x : ℝ // x ∈ Set.Ioo a b} => (e x : ℝ)) := by
  let f : ℝ → ℝ := fun x => if hx : x ∈ Set.Ioo a b then (e ⟨x, hx⟩ : ℝ) else 0
  have hf_agrees : ∀ z : {x : ℝ // x ∈ Set.Ioo a b}, f (z : ℝ) = (e z : ℝ) := by
    intro z
    have hz : (z : ℝ) ∈ Set.Ioo a b := z.2
    change (if hx : (z : ℝ) ∈ Set.Ioo a b then (e ⟨(z : ℝ), hx⟩ : ℝ) else 0) = (e z : ℝ)
    rw [dif_pos hz]
  have hf_cont : ContinuousOn f (Set.Ioo a b) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have h1 : (Set.Ioo a b).domRestrict f =
        fun z : {x : ℝ // x ∈ Set.Ioo a b} => (e z : ℝ) := by
      funext z
      exact hf_agrees z
    rw [h1]
    exact continuous_subtype_val.comp e.continuous
  have hf_inj : InjOn f (Set.Ioo a b) := by
    intro x hx y hy hxy
    unfold f at hxy
    rw [dif_pos hx, dif_pos hy] at hxy
    have heq : e ⟨x, hx⟩ = e ⟨y, hy⟩ := Subtype.ext hxy
    have hxye : (⟨x, hx⟩ : {x : ℝ // x ∈ Set.Ioo a b}) = ⟨y, hy⟩ := e.injective heq
    exact congrArg Subtype.val hxye
  have hmono_or := ContinuousOn.strictMonoOn_of_injOn_Ioo (α := ℝ) (δ := ℝ) hab hf_cont hf_inj
  rcases hmono_or with hmono | hanti
  · left
    intro x y hxy
    have hxmem : (x : ℝ) ∈ Set.Ioo a b := x.2
    have hymem : (y : ℝ) ∈ Set.Ioo a b := y.2
    have hxylt : (x : ℝ) < (y : ℝ) := hxy
    have hlt : f (x : ℝ) < f (y : ℝ) := hmono hxmem hymem hxylt
    rw [hf_agrees x, hf_agrees y] at hlt
    exact hlt
  · right
    intro x y hxy
    have hxmem : (x : ℝ) ∈ Set.Ioo a b := x.2
    have hymem : (y : ℝ) ∈ Set.Ioo a b := y.2
    have hxylt : (x : ℝ) < (y : ℝ) := hxy
    have hlt : f (y : ℝ) < f (x : ℝ) := hanti hxmem hymem hxylt
    rw [hf_agrees x, hf_agrees y] at hlt
    exact hlt

end Commons.Topology.Homeomorph