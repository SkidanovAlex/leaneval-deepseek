import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The topological Krull dimension is local for an open cover

If `U : ι → Set X` is an open cover of a topological space `X`, then
`dim X ≤ ⨆ i, dim (U i)`.  The proof uses that the irreducible closed subsets of an open
subspace `U i` are order-isomorphic (via the closure map) to the irreducible closed subsets of `X`
meeting `U i`, and that this order isomorphism preserves coheight.  Since every irreducible closed
subset of `X` is nonempty, it meets some `U i`, so every coheight in `X` is realised as a coheight
in one of the `U i`, and `krullDim` is the supremum of the coheights.
-/

open Set Order Topology

namespace Work.Twist

/-- The topological Krull dimension of a space is at most the supremum of the topological Krull
dimensions of the members of any open cover. -/
theorem topologicalKrullDim_le_iSup_of_isOpenCover {X : Type*} [TopologicalSpace X] {ι : Type*}
    (U : ι → Set X) (hUo : ∀ i, IsOpen (U i)) (hcover : ⋃ i, U i = Set.univ) :
    topologicalKrullDim X ≤ ⨆ i, topologicalKrullDim ↥(U i) := by
  simp only [topologicalKrullDim]
  conv_lhs => rw [Order.krullDim_eq_iSup_coheight]
  refine iSup_le fun V => ?_
  -- every irreducible closed subset of `X` meets some member of the cover
  obtain ⟨x, hxV⟩ := V.isIrreducible.nonempty
  obtain ⟨i, hxi⟩ : ∃ i, x ∈ U i := by
    have hx : x ∈ ⋃ i, U i := by rw [hcover]; trivial
    exact Set.mem_iUnion.mp hx
  have hf : IsOpenEmbedding (Subtype.val : ↥(U i) → X) := (hUo i).isOpenEmbedding_subtypeVal
  have hmem : (Subtype.val ⁻¹' (V : Set X)).Nonempty := ⟨⟨x, hxi⟩, hxV⟩
  -- the closure map is an order isomorphism onto the irreducible closed sets meeting `U i`
  let e := TopologicalSpace.IrreducibleCloseds.orderIsoOfIsOpenEmbedding
    (Subtype.val : ↥(U i) → X) hf
  let Z : TopologicalSpace.IrreducibleCloseds ↥(U i) := e.symm ⟨V, hmem⟩
  have hmap : TopologicalSpace.IrreducibleCloseds.map (Subtype.val : ↥(U i) → X)
      hf.continuous Z = V := by
    have h := e.apply_symm_apply ⟨V, hmem⟩
    exact congrArg Subtype.val h
  -- the isomorphism preserves coheight
  have hco : Order.coheight V = Order.coheight Z := by
    rw [← hmap, Topology.IsOpenEmbedding.coheight_map hf Z]
  calc ↑(Order.coheight V) = ↑(Order.coheight Z) := by rw [hco]
    _ ≤ Order.krullDim (TopologicalSpace.IrreducibleCloseds ↥(U i)) :=
        Order.coheight_le_krullDim Z
    _ ≤ ⨆ i, Order.krullDim (TopologicalSpace.IrreducibleCloseds ↥(U i)) :=
        le_iSup (fun i => Order.krullDim (TopologicalSpace.IrreducibleCloseds ↥(U i))) i

end Work.Twist
