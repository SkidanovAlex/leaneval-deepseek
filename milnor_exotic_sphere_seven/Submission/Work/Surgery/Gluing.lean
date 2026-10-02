import Submission.Work.Surgery.Collar

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Gluing two manifolds with boundary along their boundaries

Given two smooth manifolds `M`, `N` with boundary, modelled on the half-space
`EuclideanHalfSpace (n+1)`, and a homeomorphism `φ : ∂M ≃ₜ ∂N` of their boundaries, one can glue
`M` to `N` along `φ`: the quotient of `M ⊔ N` by the relation identifying `x ∈ ∂M` with `φ x`.

This is the basic operation behind **capping** (`M ∪_φ D^{n+1}`, `Handle.lean`) and behind the
gluing of bordisms.  The workspace's `Submission/Glue/` chapter performs the *boundaryless* case
(gluing along diffeomorphic open subsets); the two constructions differ: identifying whole collar
neighbourhoods is not the same as identifying the boundaries.

## What is here

* `Work.Surgery.GlueData n M N` — the data (the two manifolds and the boundary homeomorphism), with
  the identification map `GlueData.aux` (which sends the interiors of the two pieces and the seam,
  parameterised by `∂M`, to a disjoint sum) and the glued space `GlueData.Glued`.  The glued space
  is defined as the quotient of `M ⊕ N` by the *kernel setoid* of `aux`, so that it is canonically
  the disjoint union of the two interiors and the seam, and the equivalence laws are automatic;
* the identifications are exactly the boundary points (`GlueData.ιM_injective`,
  `GlueData.ιM_eq_ιN_iff`, `GlueData.interior_disjoint`), and the glued space is compact when `M`
  and `N` are (`GlueData.compactSpace`);
* **`Work.Surgery.SmoothGlue`** — the *smooth structure on the glued space*, as a named input: the
  theorem that the glued space carries a smooth structure, is T2, and that the two inclusions are
  open embeddings onto the two halves.  This is the one geometric input of the gluing construction;
  it is not proved here (and is not in Mathlib), and every statement that needs the glued space to
  be a manifold consumes it as a hypothesis.

## Conventions

A manifold with boundary of dimension `k+1` is modelled on `EuclideanHalfSpace (k+1)`, so `n` is
one less than the dimension; the glued space is modelled on `EuclideanSpace ℝ (Fin (n+1))`.
-/

open scoped Manifold Topology ContDiff
open Function
open Classical

namespace Work.Surgery

noncomputable section

variable {n : ℕ}

/-- **Gluing data**: two manifolds with boundary over the same half-space model, together with a
homeomorphism of their boundaries. -/
structure GlueData (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    (N : Type*) [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace (n + 1)) N] where
  /-- the identification of the two boundaries -/
  φ : (𝓡∂ (n + 1)).boundary M ≃ₜ (𝓡∂ (n + 1)).boundary N

namespace GlueData

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace (n + 1)) N]

/-- **The model of the glued set**: the disjoint union of the interiors of `M` and of `N` with the
seam, which is a copy of `∂M` (the identification of `∂N` with `∂M` via `φ`). -/
abbrev Pieces (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    (N : Type*) [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace (n + 1)) N] : Type _ :=
  Sum (Sum {x : M // x ∉ (𝓡∂ (n + 1)).boundary M}
           {y : N // y ∉ (𝓡∂ (n + 1)).boundary N})
    ((𝓡∂ (n + 1)).boundary M)

/-- **The identification map** whose kernel is the gluing relation: the interior of `M`, the
interior of `N`, and the seam `∂M ≅ ∂N`, as a disjoint union. -/
def aux (D : GlueData n M N) : M ⊕ N → Pieces n M N :=
  fun a => match a with
    | Sum.inl x => if hx : x ∈ (𝓡∂ (n + 1)).boundary M then Sum.inr ⟨x, hx⟩
        else Sum.inl (Sum.inl ⟨x, hx⟩)
    | Sum.inr y => if hy : y ∈ (𝓡∂ (n + 1)).boundary N then Sum.inr (D.φ.symm ⟨y, hy⟩)
        else Sum.inl (Sum.inr ⟨y, hy⟩)

theorem aux_inl (D : GlueData n M N) (x : M) :
    D.aux (Sum.inl x) = if hx : x ∈ (𝓡∂ (n + 1)).boundary M then Sum.inr ⟨x, hx⟩
      else Sum.inl (Sum.inl ⟨x, hx⟩) := rfl

theorem aux_inr (D : GlueData n M N) (y : N) :
    D.aux (Sum.inr y) = if hy : y ∈ (𝓡∂ (n + 1)).boundary N then Sum.inr (D.φ.symm ⟨y, hy⟩)
      else Sum.inl (Sum.inr ⟨y, hy⟩) := rfl

/-- The setoid defining the glued space: the kernel of the identification map. -/
def setoid (D : GlueData n M N) : Setoid (M ⊕ N) := Setoid.ker (aux D)

theorem setoid_r_iff (D : GlueData n M N) (a b : M ⊕ N) :
    D.setoid.r a b ↔ D.aux a = D.aux b := Iff.rfl

/-- **The glued space** `M ∪_φ N`. -/
abbrev Glued (D : GlueData n M N) : Type _ := Quotient (D.setoid)

instance instTopologicalSpace (D : GlueData n M N) : TopologicalSpace D.Glued :=
  inferInstanceAs (TopologicalSpace (Quotient (D.setoid)))

/-- The quotient map `M ⊕ N → M ∪_φ N`. -/
def q (D : GlueData n M N) : M ⊕ N → D.Glued := Quotient.mk''

/-- The inclusion of `M` into the glued space. -/
def ιM (D : GlueData n M N) : M → D.Glued := D.q ∘ Sum.inl

/-- The inclusion of `N` into the glued space. -/
def ιN (D : GlueData n M N) : N → D.Glued := D.q ∘ Sum.inr

@[simp] theorem q_inl (D : GlueData n M N) (x : M) : D.q (Sum.inl x) = D.ιM x := rfl

@[simp] theorem q_inr (D : GlueData n M N) (y : N) : D.q (Sum.inr y) = D.ιN y := rfl

theorem continuous_q (D : GlueData n M N) : Continuous D.q := by
  change Continuous (Quotient.mk' (s := D.setoid))
  exact continuous_quotient_mk'

theorem continuous_ιM (D : GlueData n M N) : Continuous D.ιM :=
  D.continuous_q.comp continuous_inl

theorem continuous_ιN (D : GlueData n M N) : Continuous D.ιN :=
  D.continuous_q.comp continuous_inr

/-- The two inclusions are injective: the only identifications are between the two sides. -/
theorem ιM_injective (D : GlueData n M N) : Injective D.ιM := by
  intro x y h
  have h' : D.aux (Sum.inl x) = D.aux (Sum.inl y) := Quotient.exact' h
  rw [D.aux_inl, D.aux_inl] at h'
  by_cases hx : x ∈ (𝓡∂ (n + 1)).boundary M
  · by_cases hy : y ∈ (𝓡∂ (n + 1)).boundary M
    · rw [dif_pos hx, dif_pos hy] at h'
      simp only [Sum.inr.injEq] at h'
      exact congrArg Subtype.val h'
    · rw [dif_pos hx, dif_neg hy] at h'
      exact absurd h' (by simp)
  · by_cases hy : y ∈ (𝓡∂ (n + 1)).boundary M
    · rw [dif_neg hx, dif_pos hy] at h'
      exact absurd h'.symm (by simp)
    · rw [dif_neg hx, dif_neg hy] at h'
      simp only [Sum.inl.injEq, Sum.inr.injEq] at h'
      exact congrArg Subtype.val h'

theorem ιN_injective (D : GlueData n M N) : Injective D.ιN := by
  intro x y h
  have h' : D.aux (Sum.inr x) = D.aux (Sum.inr y) := Quotient.exact' h
  rw [D.aux_inr, D.aux_inr] at h'
  by_cases hx : x ∈ (𝓡∂ (n + 1)).boundary N
  · by_cases hy : y ∈ (𝓡∂ (n + 1)).boundary N
    · rw [dif_pos hx, dif_pos hy] at h'
      simp only [Sum.inr.injEq] at h'
      have h2 := congrArg D.φ h'
      simp only [Homeomorph.apply_symm_apply] at h2
      exact congrArg Subtype.val h2
    · rw [dif_pos hx, dif_neg hy] at h'
      exact absurd h' (by simp)
  · by_cases hy : y ∈ (𝓡∂ (n + 1)).boundary N
    · rw [dif_neg hx, dif_pos hy] at h'
      exact absurd h'.symm (by simp)
    · rw [dif_neg hx, dif_neg hy] at h'
      simp only [Sum.inl.injEq, Sum.inr.injEq] at h'
      exact congrArg Subtype.val h'

/-- The seam: `ιM x = ιN y` for a boundary point `x` and `y = φ x`. -/
theorem ιM_eq_ιN (D : GlueData n M N) (p : (𝓡∂ (n + 1)).boundary M) :
    D.ιM p.1 = D.ιN (D.φ p).1 := by
  apply Quotient.sound'
  show D.aux (Sum.inl p.1) = D.aux (Sum.inr (D.φ p).1)
  rw [D.aux_inl, dif_pos p.2, D.aux_inr, dif_pos (D.φ p).2]
  congr 1
  exact Subtype.ext (congrArg Subtype.val (Homeomorph.symm_apply_apply D.φ p)).symm

/-- **The two sides meet exactly in the boundary**: `ιM x = ιN y` if and only if `x` is a boundary
point and `y` is its image under the gluing homeomorphism. -/
theorem ιM_eq_ιN_iff (D : GlueData n M N) {x : M} {y : N} :
    D.ιM x = D.ιN y ↔ ∃ p : (𝓡∂ (n + 1)).boundary M, x = p.1 ∧ y = (D.φ p).1 := by
  constructor
  · intro h
    have h' : D.aux (Sum.inl x) = D.aux (Sum.inr y) := Quotient.exact' h
    rw [D.aux_inl, D.aux_inr] at h'
    by_cases hx : x ∈ (𝓡∂ (n + 1)).boundary M
    · by_cases hy : y ∈ (𝓡∂ (n + 1)).boundary N
      · rw [dif_pos hx, dif_pos hy] at h'
        refine ⟨⟨x, hx⟩, rfl, ?_⟩
        simp only [Sum.inr.injEq] at h'
        have h2 : (⟨y, hy⟩ : (𝓡∂ (n + 1)).boundary N) = D.φ ⟨x, hx⟩ := by
          rw [h']
          exact (Homeomorph.apply_symm_apply D.φ ⟨y, hy⟩).symm
        exact congrArg Subtype.val h2
      · rw [dif_pos hx, dif_neg hy] at h'
        exact absurd h' (by simp)
    · by_cases hy : y ∈ (𝓡∂ (n + 1)).boundary N
      · rw [dif_neg hx, dif_pos hy] at h'
        exact absurd h' (by simp)
      · rw [dif_neg hx, dif_neg hy] at h'
        exact absurd h' (by simp)
  · rintro ⟨p, rfl, rfl⟩
    exact D.ιM_eq_ιN p

/-- Points of the *interior* of `M` are not identified with anything on the other side. -/
theorem interior_disjoint (D : GlueData n M N) {x : M}
    (hx : x ∉ (𝓡∂ (n + 1)).boundary M) {y : N} : D.ιM x ≠ D.ιN y := by
  rintro h
  obtain ⟨p, rfl, -⟩ := (D.ιM_eq_ιN_iff).mp h
  exact hx p.2

/-- **The glued space is compact** when both pieces are. -/
theorem compactSpace (D : GlueData n M N) [CompactSpace M] [CompactSpace N] :
    CompactSpace D.Glued := by
  rw [← isCompact_univ_iff]
  have h : Set.range D.q = Set.univ := by
    rw [Set.range_eq_univ]
    intro z
    obtain ⟨a, rfl⟩ := Quotient.exists_rep z
    exact ⟨a, rfl⟩
  rw [← h]
  exact isCompact_range D.continuous_q

end GlueData

/-- **The smooth structure on a glued manifold, as a named input.**

Given gluing data `D` for `M ∪_φ N`, this bundles: a smooth (`C^∞`) manifold structure on the glued
space modelled on `EuclideanSpace ℝ (Fin (n+1))`, the Hausdorff property, and the two facts that
make the structure *the* gluing of `M` and `N`:

* the inclusions `ιM`, `ιN` are **embeddings** — so the two halves of the glued space carry the
  topology of `M` and of `N`;
* the inclusions are **open maps on the interior**: `ιM` maps the interior of `M` (i.e. `M ∖ ∂M`)
  onto an open subset of the glued space, and likewise for `N`.

The second point is what the gluing *is*: the seam is exactly where the two interiors meet, and a
point of the seam has no neighbourhood lying in one half.  For instance the double of the half-line
`[0,∞)` is the line `ℝ`, in which the image of the first copy is the *closed* half-line `[0,∞)` —
not an open subset.  So the two halves are closed, not open, and only their interiors are open.

This is the missing geometric theorem of this chapter: it is not in Mathlib and it is not proved
here.  Everything that needs the glued space to be a manifold is stated with an explicit argument
of this type. -/
structure SmoothGlue {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace (n + 1)) N]
    (D : GlueData n M N) : Type _ where
  /-- the charted space structure on the glued space -/
  chartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) D.Glued
  /-- the smooth manifold structure on the glued space -/
  isManifold : @IsManifold ℝ _ (EuclideanSpace ℝ (Fin (n + 1))) _ _
    (EuclideanSpace ℝ (Fin (n + 1))) _ (𝓡 (n + 1)) (∞ : WithTop ℕ∞) D.Glued _ chartedSpace
  /-- the glued space is Hausdorff -/
  t2Space : T2Space D.Glued
  /-- the first inclusion is an embedding -/
  isEmbedding_ιM : @Topology.IsEmbedding M D.Glued _ _ D.ιM
  /-- the second inclusion is an embedding -/
  isEmbedding_ιN : @Topology.IsEmbedding N D.Glued _ _ D.ιN
  /-- the first inclusion is an open map on the interior: `ιM` maps `M ∖ ∂M` onto an open subset
  of the glued space -/
  isOpenMap_interior_ιM : IsOpenMap fun x : Set.Elem ((𝓡∂ (n + 1)).boundary M)ᶜ => D.ιM x.1
  /-- the second inclusion is an open map on the interior -/
  isOpenMap_interior_ιN : IsOpenMap fun y : Set.Elem ((𝓡∂ (n + 1)).boundary N)ᶜ => D.ιN y.1

namespace SmoothGlue

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace (n + 1)) N]
variable {D : GlueData n M N}

/-- **The glued manifold has no boundary**: the two boundaries are glued to each other, so every
point of the glued space is an interior point (the glued space is modelled on the boundaryless model
`𝓡 (n+1)`).  This is what makes a *capping* `M ∪_φ D^{n+1}` a closed manifold. -/
theorem boundary_eq_empty (S : SmoothGlue D) :
    @ModelWithCorners.boundary ℝ _ (EuclideanSpace ℝ (Fin (n + 1))) _ _
      (EuclideanSpace ℝ (Fin (n + 1))) _ (𝓡 (n + 1)) D.Glued _ S.chartedSpace = ∅ := by
  letI := S.chartedSpace
  haveI := S.isManifold
  exact ModelWithCorners.Boundaryless.boundary_eq_empty (I := 𝓡 (n + 1)) (M := D.Glued)

/-- **The glued manifold is compact** when both pieces are. -/
theorem compactSpace (S : SmoothGlue D) [CompactSpace M] [CompactSpace N] :
    CompactSpace D.Glued :=
  D.compactSpace

/-- The glued manifold is a smooth manifold, given the smooth structure input. -/
theorem isManifold' (S : SmoothGlue D) :
    @IsManifold ℝ _ (EuclideanSpace ℝ (Fin (n + 1))) _ _
      (EuclideanSpace ℝ (Fin (n + 1))) _ (𝓡 (n + 1)) (∞ : WithTop ℕ∞) D.Glued _ S.chartedSpace :=
  S.isManifold

/-- **The glued manifold is Hausdorff**, given the smooth structure input. -/
theorem t2Space' (S : SmoothGlue D) : T2Space D.Glued := S.t2Space

end SmoothGlue

end

end Work.Surgery
