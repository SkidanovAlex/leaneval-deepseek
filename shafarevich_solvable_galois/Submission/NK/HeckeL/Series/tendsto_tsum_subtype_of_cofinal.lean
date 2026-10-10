import Mathlib.Analysis.Normed.Group.Uniform
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.HeckeL.Series

/-- If `u : α → Set β` is a cofinal family of subsets of `β` (every finite set is eventually
contained in `u a`), then the sums of a summable `f : β → E` over the subtypes `u a` tend to the
total sum. -/
theorem tendsto_tsum_subtype_of_cofinal {β : Type*} {α : Type*} [Preorder α] [IsDirectedOrder α]
    [Nonempty α] {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] (f : β → E) (hf : Summable f)
    (u : α → Set β) (hu : ∀ t : Finset β, ∃ a : α, ∀ b : α, a ≤ b → (↑t : Set β) ⊆ u b) :
    Filter.Tendsto (fun a : α => ∑' (x : u a), f x) Filter.atTop (nhds (∑' x, f x)) := by
  -- The contribution of the complement of `u a` is eventually small.
  have hcompl : Filter.Tendsto (fun a : α => ∑' (x : ((u a)ᶜ : Set β)), f x) Filter.atTop
      (nhds 0) := by
    intro e he
    rw [Filter.mem_map]
    obtain ⟨s, hs⟩ := hf.tsum_vanishing he
    obtain ⟨a, ha⟩ := hu s
    exact Filter.mem_atTop_sets.mpr
      ⟨a, fun b hb => hs ((u b)ᶜ) (Set.disjoint_left.mpr fun x hx hxs => hx (ha b hb hxs))⟩
  -- Hence `∑' x in u a, f x = (∑' x, f x) - ∑' x in (u a)ᶜ, f x` tends to `∑' x, f x`.
  have hconst : Filter.Tendsto (fun _ : α => (∑' x, f x)) Filter.atTop (nhds (∑' x, f x)) :=
    tendsto_const_nhds
  have hmain : Filter.Tendsto (fun a : α => ∑' x, f x + -(∑' (x : ((u a)ᶜ : Set β)), f x))
      Filter.atTop (nhds (∑' x, f x)) := by
    have := hconst.add hcompl.neg
    simpa using this
  exact Filter.Tendsto.congr (fun a => by
    rw [← hf.tsum_subtype_add_tsum_subtype_compl (u a)]
    abel) hmain

end NK.HeckeL.Series
