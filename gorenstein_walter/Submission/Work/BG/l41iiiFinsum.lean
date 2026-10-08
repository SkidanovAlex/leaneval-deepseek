import Mathlib

namespace Work.BG

/-- A set-restricted `finsum` over a set `s` lying inside the range of an injective map
`f : ι → α` agrees with the ordinary finite sum over the (finite) fibre of `s` under `f`.

Since `s ⊆ Set.range f` and `ι` is finite, `s.indicator g` is supported inside the finite set
`Finset.univ.image f`; rewriting the `finsum` as a sum over that Finset and using the injectivity
of `f` identifies the two sides term by term. -/
theorem l41iiiFinsum {ι : Type*} [Fintype ι] [DecidableEq ι] {α : Type*}
    [DecidableEq α] (f : ι → α) (hinj : Function.Injective f) (s : Set α)
    [DecidablePred (fun x => x ∈ s)] (hs : s ⊆ Set.range f) (g : α → ℂ) :
    (∑ᶠ x ∈ s, g x) = ∑ i ∈ Finset.univ.filter (fun i => f i ∈ s), g (f i) := by
  classical
  -- Write the set-restricted `finsum` as the `finsum` of the indicator function of `s`.
  rw [finsum_mem_def]
  -- The image of the finite type `ι` under `f` is exactly the range of `f`.
  have hset : (↑(Finset.univ.image f) : Set α) = Set.range f := by
    simp [Finset.coe_image]
  -- Hence the support of the indicator of `s` lies in the finite set `Finset.univ.image f`.
  have hsupp : Function.support (s.indicator g) ⊆ ↑(Finset.univ.image f) := by
    intro x hx
    rw [Function.mem_support] at hx
    rw [hset]
    exact hs (by
      by_contra h
      exact hx (by rw [Set.indicator_of_notMem h]))
  -- Replace the `finsum` by a finite sum over the image, then push forward along the injection `f`.
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  rw [Finset.sum_image (fun a _ b _ h => hinj h)]
  -- Both sides are now sums over `Finset.univ` with the same summand.
  rw [Finset.sum_filter]
  simp only [Set.indicator_apply]

end Work.BG
