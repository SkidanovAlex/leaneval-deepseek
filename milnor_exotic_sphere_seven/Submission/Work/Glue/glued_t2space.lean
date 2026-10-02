import Mathlib
import Submission.Work.Glue.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The glued space is Hausdorff

`Submission.Work.Glue.Basic` constructs, given two `C^n` manifolds `X`, `Y` over a common model
`H`, two open subsets `U ⊆ X`, `V ⊆ Y` and a diffeomorphism `φ : U ≅ V`, the glued space
`D.Glued` as the quotient of `X ⊕ Y` identifying `x ∈ U` with `φ x ∈ V`.

Here we prove that `D.Glued` is a `T2Space` (Hausdorff) whenever `X` and `Y` are Hausdorff and the
graph of the gluing map,
`{z : X × Y | z.1 ∈ U ∧ φ z.1 = z.2}`,
is closed in `X × Y`.

The argument is the standard criterion for quotients by closed relations: the quotient map `D.q`
is an *open* quotient map (being the quotient map of a disjoint union of two open maps), and a
space `Y` with an open quotient map `π : X → Y` is Hausdorff exactly when the relation
`{q | π q.1 = π q.2}` is closed in `X × X` (`t2Space_iff_of_isOpenQuotientMap`).  The relation
of `D` is the union of the diagonal of `X ⊕ Y` with the two "mixed" graphs
`{(inl x, inr (φ x)) | x ∈ U}` and `{(inr (φ x), inl x) | x ∈ U}`, each of which is closed: the
mixed graphs are closed images of the closed graph of `φ` under the closed embeddings
`inl × inr` resp. `inr × inl`.
-/

namespace Work.Glue

open scoped Manifold ContDiff Topology
open Submission.Glue

set_option linter.unusedVariables false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
variable {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I n X]
variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I n Y]

/-- The quotient map `D.q` from the disjoint union `X ⊕ Y` onto the glued space is an open map.
Indeed it is the union of the open maps `D.ιX` and `D.ιY`. -/
theorem isOpenMap_glued_q (D : Data I n X Y) : IsOpenMap D.q := by
  intro W hW
  have h1 : IsOpen (Sum.inl ⁻¹' W) := hW.preimage continuous_inl
  have h2 : IsOpen (Sum.inr ⁻¹' W) := hW.preimage continuous_inr
  have hWdecomp : W = Sum.inl '' (Sum.inl ⁻¹' W) ∪ Sum.inr '' (Sum.inr ⁻¹' W) := by
    ext a; rcases a with x | y <;> simp
  rw [hWdecomp, Set.image_union]
  refine IsOpen.union ?_ ?_
  · have h : D.q '' (Sum.inl '' (Sum.inl ⁻¹' W)) = D.ιX '' (Sum.inl ⁻¹' W) := by
      rw [← Set.image_comp]; rfl
    rw [h]; exact D.isOpenMap_ιX _ h1
  · have h : D.q '' (Sum.inr '' (Sum.inr ⁻¹' W)) = D.ιY '' (Sum.inr ⁻¹' W) := by
      rw [← Set.image_comp]; rfl
    rw [h]; exact D.isOpenMap_ιY _ h2

/-- If the graph of the gluing map is closed in `X × Y`, then the kernel relation of the quotient
map `D.q` is closed in `(X ⊕ Y) × (X ⊕ Y)`. -/
theorem isClosed_glued_rel [T2Space X] [T2Space Y] (D : Data I n X Y)
    (hgraph : IsClosed {z : X × Y | z.1 ∈ D.U ∧ (D.φ z.1 : Y) = z.2}) :
    IsClosed {q : (X ⊕ Y) × (X ⊕ Y) | D.rel q.1 q.2} := by
  set G : Set (X × Y) := {z | z.1 ∈ D.U ∧ (D.φ z.1 : Y) = z.2} with hG
  have hGcl : IsClosed G := by rw [hG]; exact hgraph
  have hdiag : IsClosed (Set.diagonal (X ⊕ Y)) := isClosed_diagonal
  have h3 : IsClosed (Prod.map (Sum.inl : X → X ⊕ Y) (Sum.inr : Y → X ⊕ Y) '' G) :=
    (Topology.IsClosedEmbedding.inl.prodMap Topology.IsClosedEmbedding.inr).isClosedMap _ hGcl
  have h4 : IsClosed
      (Prod.map (Sum.inr : Y → X ⊕ Y) (Sum.inl : X → X ⊕ Y) '' (Prod.swap ⁻¹' G)) :=
    (Topology.IsClosedEmbedding.inr.prodMap Topology.IsClosedEmbedding.inl).isClosedMap _
      (hGcl.preimage continuous_swap)
  have hunion : {q : (X ⊕ Y) × (X ⊕ Y) | D.rel q.1 q.2}
      = Set.diagonal (X ⊕ Y)
        ∪ (Prod.map (Sum.inl : X → X ⊕ Y) (Sum.inr : Y → X ⊕ Y) '' G
           ∪ Prod.map (Sum.inr : Y → X ⊕ Y) (Sum.inl : X → X ⊕ Y) '' (Prod.swap ⁻¹' G)) := by
    ext q
    constructor
    · intro h
      rcases q with ⟨a, b⟩
      rcases a with x | y <;> rcases b with x' | y'
      · have h' : x = x' := h
        refine Or.inl ?_
        rw [Set.mem_diagonal_iff]
        exact congrArg Sum.inl h'
      · have h' : ∃ (hx : x ∈ D.U), (D.φ x : Y) = y' := h
        refine Or.inr (Or.inl ?_)
        exact ⟨(x, y'), ⟨h'.1, h'.2⟩, rfl⟩
      · have h' : ∃ (hx : x' ∈ D.U), y = (D.φ x' : Y) := h
        refine Or.inr (Or.inr ?_)
        exact ⟨(y, x'), ⟨h'.1, h'.2.symm⟩, rfl⟩
      · have h' : y = y' := h
        refine Or.inl ?_
        rw [Set.mem_diagonal_iff]
        exact congrArg Sum.inr h'
    · simp only [Set.mem_union]
      intro h
      change D.rel q.1 q.2
      rcases h with h | h | h
      · rw [Set.mem_diagonal_iff] at h
        rw [h]; exact D.rel_refl q.2
      · rcases h with ⟨⟨x, y⟩, hxy, hq⟩
        have hxy' : x ∈ D.U ∧ (D.φ x : Y) = y := hxy
        have hq' : q = (Sum.inl x, Sum.inr y) := hq.symm
        rw [hq']
        exact ⟨hxy'.1, hxy'.2⟩
      · rcases h with ⟨⟨y, x⟩, hyx, hq⟩
        have hyx' : x ∈ D.U ∧ (D.φ x : Y) = y := hyx
        have hq' : q = (Sum.inr y, Sum.inl x) := hq.symm
        rw [hq']
        exact ⟨hyx'.1, hyx'.2.symm⟩
  rw [hunion]
  exact hdiag.union (h3.union h4)

open scoped Manifold ContDiff Topology in
open Submission.Glue in
theorem glued_t2space
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I n X]
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I n Y]
    [T2Space X] [T2Space Y] (D : Data I n X Y)
    (hgraph : IsClosed {z : X × Y | z.1 ∈ D.U ∧ (D.φ z.1 : Y) = z.2}) :
    T2Space D.Glued := by
  have hopen : IsOpenQuotientMap D.q :=
    ⟨fun z => Quotient.exists_rep z, D.continuous_q, isOpenMap_glued_q D⟩
  rw [t2Space_iff_of_isOpenQuotientMap hopen]
  have hset : {q : (X ⊕ Y) × (X ⊕ Y) | D.q q.1 = D.q q.2}
      = {q : (X ⊕ Y) × (X ⊕ Y) | D.rel q.1 q.2} := by
    ext q
    change D.q q.1 = D.q q.2 ↔ D.rel q.1 q.2
    exact Quotient.eq
  rw [hset]
  exact isClosed_glued_rel D hgraph

end Work.Glue
