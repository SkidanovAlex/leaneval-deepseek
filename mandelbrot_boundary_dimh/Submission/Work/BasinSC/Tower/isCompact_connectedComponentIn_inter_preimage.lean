import Mathlib

namespace Work.BasinSC.Tower

/-- A connected component of the subspace `F` is closed in `F`, which we record as
`connectedComponentIn F x = F ∩ closure (connectedComponentIn F x)`.  (For `x ∉ F` the
statement is also true, both sides being empty, but only the case `x ∈ F` is needed.) -/
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

/-- **Properness of the first-return map on connected components of a tower.**

Let `f : ℂ → ℂ` be "proper over `B`" in the sense that `B ∩ f ⁻¹' L` is compact for every compact
`L ⊆ B`, and let `V = B ∩ f ⁻¹' W` with `W ⊆ B`.  Then for every point `x` and every compact
`K` contained in the connected component of `f x` in `W`, the part of the connected component of
`x` in `V` lying over `K` is compact.

This is the structural input for the inductive step of the tower of preimages: with
`B` the immediate basin, `W = V n`, `V = V (n+1)` and `x ∈ V (n+1)` the hypothesis
`hproper` is the properness of `f` over the basin, and the conclusion says that the restriction
`f : component of x in V (n+1) → component of f x in V n` is proper.

Proof.  If `x ∉ V` there is nothing to prove, since `connectedComponentIn V x = ∅`.  Otherwise
`x ∈ V = B ∩ f ⁻¹' W`, so `f x ∈ W` and hence `K ⊆ connectedComponentIn W (f x) ⊆ W ⊆ B`.
Writing `C = connectedComponentIn V x`, the elementary fact that a connected component of the
subspace `V` is closed in `V` gives `C = V ∩ closure C`, and therefore
`C ∩ f ⁻¹' K = (V ∩ f ⁻¹' K) ∩ closure C`.  Now `V ∩ f ⁻¹' K = B ∩ f ⁻¹' (W ∩ K) = B ∩ f ⁻¹' K`
because `K ⊆ W`, which is compact by `hproper`; intersecting it with the closed set
`closure C` stays compact. -/
theorem isCompact_connectedComponentIn_inter_preimage {f : ℂ → ℂ} {B W V : Set ℂ} {x : ℂ}
    (hproper : ∀ L ⊆ B, IsCompact L → IsCompact (B ∩ f ⁻¹' L))
    (hWsub : W ⊆ B) (hVeq : V = B ∩ f ⁻¹' W) :
    ∀ K ⊆ connectedComponentIn W (f x), IsCompact K →
      IsCompact (connectedComponentIn V x ∩ f ⁻¹' K) := by
  intro K hK hKc
  by_cases hx : x ∈ V
  · -- `x ∈ V`: then `f x ∈ W`, so `K ⊆ W ⊆ B` and `V ∩ f ⁻¹' K = B ∩ f ⁻¹' K` is compact.
    have hxW : f x ∈ W := by
      have h1 : x ∈ B ∩ f ⁻¹' W := hVeq ▸ hx
      exact h1.2
    have hKW : K ⊆ W := fun y hy => connectedComponentIn_subset W (f x) (hK hy)
    have hKB : K ⊆ B := hKW.trans hWsub
    have hA : connectedComponentIn V x = V ∩ closure (connectedComponentIn V x) :=
      connectedComponentIn_eq_inter_closure_of_mem hx
    have hVK : V ∩ f ⁻¹' K = B ∩ f ⁻¹' K := by
      rw [hVeq]
      ext y
      simp only [Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · rintro ⟨⟨hyB, hyW⟩, hyK⟩; exact ⟨hyB, hyK⟩
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

end Work.BasinSC.Tower
