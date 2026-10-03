import Mathlib

namespace Work.Horn.HB

/-! # Properness of a first-return-like map on connected components of a preimage

Let `f : ℂ → ℂ` be proper over a set `B` in the sense that `B ∩ f ⁻¹' L` is compact for every
compact `L ⊆ B`.  Let `W ⊆ B` and let `V = B ∩ f ⁻¹' W`.  Then for every `K ⊆ W` compact, the part
of the connected component of `x` in `V` lying over `K` is compact.

This is the version used to feed the tower of preimages of an immediate basin: with `B` the basin,
`W = V n`, `V = V (n+1)`, `hproper` the properness of `f` over the basin, the conclusion says that
the restriction of `f` to the component of `x` in `V (n+1)` is proper over `K`.

The proof only needs that a connected component of the subspace `V` is closed *in* `V`, i.e.
`C = V ∩ closure C`, together with the identity `V ∩ f ⁻¹' K = B ∩ f ⁻¹' K` (valid because
`K ⊆ W`).  The latter set is compact by `hproper`, and intersecting it with the closed set
`closure C` stays compact. -/

/-- A connected component of the subspace `F` is closed in `F`, recorded as
`connectedComponentIn F x = F ∩ closure (connectedComponentIn F x)`.  (For `x ∉ F` the statement is
also true, both sides being empty, but only the case `x ∈ F` is used.) -/
private lemma connectedComponentIn_eq_inter_closure_of_mem {α : Type*} [TopologicalSpace α]
    {F : Set α} {x : α} (hx : x ∈ F) :
    connectedComponentIn F x = F ∩ closure (connectedComponentIn F x) := by
  refine subset_antisymm ?_ ?_
  · intro y hy
    exact ⟨connectedComponentIn_subset F x hy, subset_closure hy⟩
  · -- `F ∩ closure C` lies between the preconnected set `C` and its closure, hence is
    -- preconnected; containing `x` and being contained in `F` it must be inside `C`.
    have hpre : IsPreconnected (F ∩ closure (connectedComponentIn F x)) :=
      IsPreconnected.subset_closure (s := connectedComponentIn F x)
        isPreconnected_connectedComponentIn
        (fun z hz => ⟨connectedComponentIn_subset F x hz, subset_closure hz⟩)
        Set.inter_subset_right
    exact hpre.subset_connectedComponentIn
      ⟨hx, subset_closure (mem_connectedComponentIn hx)⟩ Set.inter_subset_left

theorem isCompact_component_inter_preimage {f : ℂ → ℂ} {B W V : Set ℂ} {x : ℂ}
    (hproper : ∀ L ⊆ B, IsCompact L → IsCompact (B ∩ f ⁻¹' L))
    (hWsub : W ⊆ B) (hVeq : V = B ∩ f ⁻¹' W) :
    ∀ K ⊆ W, IsCompact K → IsCompact (connectedComponentIn V x ∩ f ⁻¹' K) := by
  intro K hKW hKc
  by_cases hx : x ∈ V
  · -- `x ∈ V`: then `K ⊆ W ⊆ B`, and `V ∩ f ⁻¹' K = B ∩ f ⁻¹' K` is compact.
    have hKB : K ⊆ B := hKW.trans hWsub
    have hA : connectedComponentIn V x = V ∩ closure (connectedComponentIn V x) :=
      connectedComponentIn_eq_inter_closure_of_mem hx
    have hVK : V ∩ f ⁻¹' K = B ∩ f ⁻¹' K := by
      rw [hVeq]
      ext y
      simp only [Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · rintro ⟨⟨hyB, _⟩, hyK⟩; exact ⟨hyB, hyK⟩
      · rintro ⟨hyB, hyK⟩; exact ⟨⟨hyB, hKW hyK⟩, hyK⟩
    have hgoal : connectedComponentIn V x ∩ f ⁻¹' K
        = (V ∩ f ⁻¹' K) ∩ closure (connectedComponentIn V x) := by
      conv_lhs => rw [hA]
      ext y
      simp only [Set.mem_inter_iff]
      tauto
    rw [hgoal, hVK]
    exact (hproper K hKB hKc).inter_right isClosed_closure
  · -- `x ∉ V`: `connectedComponentIn V x = ∅`, so the intersection is empty.
    rw [connectedComponentIn_eq_empty hx, Set.empty_inter]
    exact isCompact_empty

end Work.Horn.HB
