import Mathlib
import Submission.Work.Smooth.JordanSeparation.simplyConnectedSpace_onePoint_complex

/-!
# The union of two simply connected open sets with path connected intersection is simply
connected

This is the elementary (van Kampen) fact underpinning the Jordan-separation arguments: if `A` and
`B` are open, simply connected subsets of a space `X` and `A ∩ B` is path connected, then
`A ∪ B` is simply connected.

The single ingredient not available in Mathlib is the elementary van Kampen lemma

`Work.Smooth.JordanSeparation.loop_nullhomotopic_of_cover`

(proved in `simplyConnectedSpace_onePoint_complex.lean`): a loop in `U ∪ V` based at a point of
`U ∩ V`, where `U`, `V` are open and simply connected with path connected intersection, is
null-homotopic.

## Main result

* `Work.Smooth.JordanSeparation.isSimplyConnected_union_of_isOpen`

## Proof outline

We package the statement in the *space* `Z = ↥(A ∪ B)` where the two sets cover everything: for the
open cover `U = (↑)⁻¹' A`, `V = (↑)⁻¹' B` of `↥(A ∪ B)` we have `U ∪ V = univ`, and both `U` and
`V` are simply connected because the subtype projection is an embedding.  In that formulation the
van Kampen lemma applies directly to any loop based at a point of `U ∩ V` (*with no containment
bookkeeping*): since the ambient space here is the subspace itself, "null-homotopic in `Z`" is
exactly what is needed.

The base point of a general loop in `↥(A ∪ B)` is dealt with by conjugation: `Z` is path connected,
so a loop at `x` is conjugate (in the fundamental groupoid) to one based at a point of `U ∩ V`,
which is trivial.  This is the calculation carried out on the level of
`Path.Homotopic.Quotient`.
-/

namespace Work.Smooth.JordanSeparation

open Set

/-- **Van Kampen, in the "open cover of the whole space" form.**  If a space `Z` is covered by two
open simply connected sets `U`, `V` whose intersection is path connected, then `Z` is simply
connected.  (The proof uses `loop_nullhomotopic_of_cover` and conjugates a general loop to a loop
based in `U ∩ V`.) -/
theorem simplyConnectedSpace_of_isOpen_cover {Z : Type*} [TopologicalSpace Z] {U V : Set Z}
    (hUo : IsOpen U) (hVo : IsOpen V) (hU : IsSimplyConnected U) (hV : IsSimplyConnected V)
    (hUV : IsPathConnected (U ∩ V)) (hcover : U ∪ V = univ) : SimplyConnectedSpace Z := by
  have hpc : PathConnectedSpace Z := by
    rw [pathConnectedSpace_iff_univ, ← hcover]
    exact hU.isPathConnected.union hV.isPathConnected hUV.nonempty
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨hpc, fun x γ => ?_⟩
  -- a point of `U ∩ V` to conjugate the base point to
  obtain ⟨z, hzU, hzV⟩ := hUV.nonempty
  set δ : Path x z := (hpc.joined x z).somePath with hδ
  -- the conjugate loop at `z` is null-homotopic by the van Kampen lemma
  have hμ : Path.Homotopic (δ.symm.trans (γ.trans δ)) (Path.refl z) :=
    loop_nullhomotopic_of_cover hUo hVo hzU hzV hU hV hUV
      (δ.symm.trans (γ.trans δ)) (fun t => by rw [hcover]; trivial)
  -- quotient algebra: `γ` is homotopic to `δ.trans (δ.symm.trans (γ.trans δ)).trans δ.symm`
  set D : Path.Homotopic.Quotient x z := ⟦δ⟧ with hD
  set G : Path.Homotopic.Quotient x x := ⟦γ⟧ with hG
  have h1 : D.symm.trans (G.trans D) = Path.Homotopic.Quotient.refl z := by
    rw [hD, hG]; exact Quotient.sound hμ
  have h2 : G.trans D = D := by
    have h := congrArg (fun q : Path.Homotopic.Quotient z z => D.trans q) h1
    rw [← Path.Homotopic.Quotient.trans_assoc D D.symm (G.trans D),
      Path.Homotopic.Quotient.trans_symm D, Path.Homotopic.Quotient.refl_trans (G.trans D),
      Path.Homotopic.Quotient.trans_refl D] at h
    exact h
  have h3 : G = Path.Homotopic.Quotient.refl x := by
    have h := congrArg (fun q : Path.Homotopic.Quotient x z => q.trans D.symm) h2
    rw [Path.Homotopic.Quotient.trans_assoc G D D.symm, Path.Homotopic.Quotient.trans_symm D,
      Path.Homotopic.Quotient.trans_refl G] at h
    exact h
  rw [hG] at h3
  exact Quotient.eq.mp h3

/-- **The union of two simply connected open sets with path connected intersection is simply
connected.** -/
theorem isSimplyConnected_union_of_isOpen {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAo : IsOpen A) (hBo : IsOpen B) (hA : IsSimplyConnected A) (hB : IsSimplyConnected B)
    (hAB : IsPathConnected (A ∩ B)) : IsSimplyConnected (A ∪ B) := by
  -- `A` and `B`, pulled back along the projection `↥(A ∪ B) → X`, are simply connected
  have he : Topology.IsEmbedding (Subtype.val : ↥(A ∪ B) → X) := Topology.IsEmbedding.subtypeVal
  have himgA : Subtype.val '' ((Subtype.val : ↥(A ∪ B) → X) ⁻¹' A) = A := by
    rw [Subtype.image_preimage_coe]
    exact Set.inter_eq_right.mpr Set.subset_union_left
  have himgB : Subtype.val '' ((Subtype.val : ↥(A ∪ B) → X) ⁻¹' B) = B := by
    rw [Subtype.image_preimage_coe]
    exact Set.inter_eq_right.mpr Set.subset_union_right
  have hA' : IsSimplyConnected ((Subtype.val : ↥(A ∪ B) → X) ⁻¹' A) := by
    rw [← Topology.IsEmbedding.isSimplyConnected_image he, himgA]
    exact hA
  have hB' : IsSimplyConnected ((Subtype.val : ↥(A ∪ B) → X) ⁻¹' B) := by
    rw [← Topology.IsEmbedding.isSimplyConnected_image he, himgB]
    exact hB
  -- their intersection is path connected, and together they cover the subspace
  have hAB' : IsPathConnected ((Subtype.val : ↥(A ∪ B) → X) ⁻¹' A ∩
      (Subtype.val : ↥(A ∪ B) → X) ⁻¹' B) := by
    rw [← Set.preimage_inter]
    exact IsPathConnected.preimage_coe hAB (fun x hx => Or.inl hx.1)
  have hcov : (Subtype.val : ↥(A ∪ B) → X) ⁻¹' A ∪ (Subtype.val : ↥(A ∪ B) → X) ⁻¹' B = univ := by
    rw [← Set.preimage_union, Set.preimage_eq_univ_iff, Set.range_subset_iff]
    exact fun y => y.2
  exact simplyConnectedSpace_of_isOpen_cover (Z := ↥(A ∪ B))
    (U := (Subtype.val : ↥(A ∪ B) → X) ⁻¹' A) (V := (Subtype.val : ↥(A ∪ B) → X) ⁻¹' B)
    (hAo.preimage continuous_subtype_val) (hBo.preimage continuous_subtype_val) hA' hB' hAB' hcov

end Work.Smooth.JordanSeparation
