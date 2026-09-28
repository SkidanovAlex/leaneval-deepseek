import Mathlib

/-!
# Glueing two charted spaces along an open subset

Given two `C^n` manifolds `X` and `Y` over a common model space `H`, two open subsets `U ⊆ X`,
`V ⊆ Y` and a diffeomorphism `φ : U ≅ V`, one can glue `X` and `Y` along `φ`.  This file
constructs the glued space (a quotient of the disjoint union) and its `C^n` manifold structure.

This is the basic glueing operation used to build Milnor's manifolds
`M_k = (D⁴ × S³) ∪_f (D⁴ × S³)`, with `f(x, y) = (x, x^k y x⁻¹)` on the common boundary
`S³ × S³`.  It is also the general "glueing of manifolds along an open subset" construction, which
Mathlib currently only has in the form of `ChartedSpace` on open subsets, products, sums and
quotients by group actions.
-/

open scoped Topology Manifold ContDiff
open Function Set Topology

namespace Submission.Glue

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]

/-- Glueing data: two `C^n` manifolds over a common model `H`, glued along a diffeomorphism
between two open subsets. -/
structure Data (I : ModelWithCorners ℝ E H) (n : ℕ∞ω) (X : Type*) [TopologicalSpace X]
    [ChartedSpace H X] [IsManifold I n X] (Y : Type*) [TopologicalSpace Y] [ChartedSpace H Y]
    [IsManifold I n Y] where
  /-- the open subset of `X` that is glued -/
  U : Set X
  /-- the open subset of `Y` that is glued -/
  V : Set Y
  isOpen_U : IsOpen U
  isOpen_V : IsOpen V
  /-- the identification between `U` and `V` -/
  φ : OpenPartialHomeomorph X Y
  source_φ : φ.source = U
  target_φ : φ.target = V
  /-- `φ` is a diffeomorphism for the two smooth structures -/
  mem_groupoid : ∀ (e : OpenPartialHomeomorph X H), e ∈ atlas H X →
    ∀ (e' : OpenPartialHomeomorph Y H), e' ∈ atlas H Y →
    e.symm ≫ₕ φ ≫ₕ e' ∈ contDiffGroupoid n I

namespace Data

variable {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
variable {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I n X]
variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I n Y]
variable (D : Data I n X Y)

/-- The relation on the disjoint union `X ⊕ Y` identifying `x ∈ U` with `φ x ∈ V`. -/
def rel : X ⊕ Y → X ⊕ Y → Prop
  | .inl x, .inl x' => x = x'
  | .inr y, .inr y' => y = y'
  | .inl x, .inr y => ∃ (hx : x ∈ D.U), (D.φ x : Y) = y
  | .inr y, .inl x => ∃ (hx : x ∈ D.U), y = (D.φ x : Y)

theorem rel_refl (a : X ⊕ Y) : D.rel a a := by
  cases a <;> rfl

theorem rel_symm : Symmetric D.rel := by
  intro a b h
  cases a with
  | inl x =>
    cases b with
    | inl x' => exact h.symm
    | inr y => exact h.imp fun _ hy => hy.symm
  | inr y =>
    cases b with
    | inl x => exact h.imp fun _ hy => hy.symm
    | inr y' => exact h.symm

theorem rel_trans : ∀ ⦃a b c⦄, D.rel a b → D.rel b c → D.rel a c := by
  intro a b c
  rcases a with x | y
  · rcases b with x' | y'
    · rcases c with x'' | y''
      · exact fun h1 h2 => h1.trans h2
      · exact fun h1 h2 => by subst h1; exact h2
    · rcases c with x'' | y''
      · exact fun h1 h2 => by
          obtain ⟨hx, h1⟩ := h1
          obtain ⟨hx'', h2⟩ := h2
          exact D.φ.injOn (by rw [D.source_φ]; exact hx) (by rw [D.source_φ]; exact hx'')
            (h1.trans h2)
      · exact fun h1 h2 => by obtain ⟨hx, h1⟩ := h1; exact ⟨hx, h1.trans h2⟩
  · rcases b with x' | y'
    · rcases c with x'' | y''
      · exact fun h1 h2 => by subst h2; exact h1
      · exact fun h1 h2 => by
          obtain ⟨hx, h1⟩ := h1
          obtain ⟨hx', h2⟩ := h2
          exact h1.trans h2
    · rcases c with x'' | y''
      · exact fun h1 h2 => by subst h1; exact h2
      · exact fun h1 h2 => h1.trans h2

/-- The setoid defining the glued space. -/
def setoid : Setoid (X ⊕ Y) :=
  ⟨D.rel, fun a => D.rel_refl a, fun {_ _} h => D.rel_symm h,
    fun {_ _ _} h1 h2 => D.rel_trans h1 h2⟩

/-- The glued space. -/
abbrev Glued : Type _ := Quotient D.setoid

instance instTopologicalSpace : TopologicalSpace D.Glued :=
  @instTopologicalSpaceQuotient (X ⊕ Y) D.setoid inferInstance

/-- The quotient map from the disjoint union onto the glued space. -/
def q : X ⊕ Y → D.Glued := fun a => @Quotient.mk'' (X ⊕ Y) D.setoid a

/-- The image of `X` inside the glued space. -/
def ιX : X → D.Glued := D.q ∘ Sum.inl

/-- The image of `Y` inside the glued space. -/
def ιY : Y → D.Glued := D.q ∘ Sum.inr

theorem q_inl (x : X) : D.q (Sum.inl x) = D.ιX x := rfl

theorem q_inr (y : Y) : D.q (Sum.inr y) = D.ιY y := rfl

theorem continuous_q : Continuous D.q := continuous_quotient_mk'

theorem continuous_ιX : Continuous D.ιX :=
  D.continuous_q.comp continuous_inl

theorem continuous_ιY : Continuous D.ιY :=
  D.continuous_q.comp continuous_inr

theorem ιX_injective : Injective D.ιX := by
  intro x x' h
  simp only [ιX, q, Function.comp_apply] at h
  rwa [Quotient.eq] at h

theorem ιY_injective : Injective D.ιY := by
  intro y y' h
  simp only [ιY, q, Function.comp_apply] at h
  rwa [Quotient.eq] at h

theorem ιX_eq_ιY_iff {x : X} {y : Y} :
    D.ιX x = D.ιY y ↔ ∃ (hx : x ∈ D.U), (D.φ x : Y) = y := by
  simp only [ιX, ιY, q, Function.comp_apply]
  rw [Quotient.eq]
  exact Iff.rfl

theorem mem_U_of_ιX_eq_ιY {x : X} {y : Y} (h : D.ιX x = D.ιY y) : x ∈ D.U :=
  (D.ιX_eq_ιY_iff.mp h).choose

theorem φ_apply_of_ιX_eq_ιY {x : X} {y : Y} (h : D.ιX x = D.ιY y) :
    (D.φ x : Y) = y :=
  (D.ιX_eq_ιY_iff.mp h).choose_spec

theorem ιY_eq_ιX_iff {x : X} {y : Y} :
    D.ιY y = D.ιX x ↔ ∃ (hx : x ∈ D.U), (D.φ x : Y) = y := by
  rw [eq_comm, D.ιX_eq_ιY_iff]

theorem range_ιX_union_range_ιY : range D.ιX ∪ range D.ιY = univ := by
  rw [eq_univ_iff_forall]
  intro z
  obtain ⟨a, ha⟩ := Quotient.exists_rep z
  rcases a with x | y
  · exact Or.inl ⟨x, by rw [← ha]; rfl⟩
  · exact Or.inr ⟨y, by rw [← ha]; rfl⟩

theorem preimage_image_U (W : Set X) :
    D.q ⁻¹' (D.ιX '' W) = Sum.inl '' W ∪ Sum.inr '' (D.φ '' (W ∩ D.U)) := by
  ext a
  constructor
  · intro h
    rcases a with x | y
    · obtain ⟨x', hx'W, h⟩ := h
      rw [D.q_inl] at h
      have hx : x = x' := D.ιX_injective h.symm
      exact Or.inl ⟨x, hx ▸ hx'W, rfl⟩
    · obtain ⟨x', hx'W, h⟩ := h
      rw [D.q_inr] at h
      refine Or.inr ⟨y, ⟨x', ⟨hx'W, D.mem_U_of_ιX_eq_ιY h⟩, D.φ_apply_of_ιX_eq_ιY h⟩, rfl⟩
  · rintro (h | h)
    · obtain ⟨x', hx'W, h⟩ := h
      rw [← h]
      exact ⟨x', hx'W, rfl⟩
    · obtain ⟨y', ⟨x', hx', hy'⟩, h⟩ := h
      rw [← h]
      exact ⟨x', hx'.1, (D.ιX_eq_ιY_iff.mpr ⟨hx'.2, hy'⟩)⟩

theorem preimage_image_V (W : Set Y) :
    D.q ⁻¹' (D.ιY '' W) = Sum.inr '' W ∪ Sum.inl '' (D.φ.symm '' (W ∩ D.V)) := by
  ext a
  constructor
  · intro h
    rcases a with x | y
    · obtain ⟨y', hy'W, h⟩ := h
      rw [D.q_inl] at h
      obtain ⟨hxU, hφ⟩ := D.ιX_eq_ιY_iff.mp h.symm
      refine Or.inr ⟨x, ⟨y', ⟨hy'W, ?_⟩, ?_⟩, rfl⟩
      · rw [← hφ, ← D.target_φ]
        exact D.φ.map_source (by rw [D.source_φ]; exact hxU)
      · rw [← hφ]
        exact D.φ.left_inv (by rw [D.source_φ]; exact hxU)
    · obtain ⟨y', hy'W, h⟩ := h
      rw [D.q_inr] at h
      have hy : y = y' := D.ιY_injective h.symm
      exact Or.inl ⟨y, hy ▸ hy'W, rfl⟩
  · rintro (h | h)
    · obtain ⟨y', hy'W, h⟩ := h
      rw [← h]
      exact ⟨y', hy'W, rfl⟩
    · obtain ⟨x', ⟨y', ⟨hy'W, hy'V⟩, hxy⟩, h⟩ := h
      rw [← h]
      refine ⟨y', hy'W, D.ιY_eq_ιX_iff.mpr ⟨?_, ?_⟩⟩
      · have hy : y' ∈ D.φ.symm.source := by rw [D.φ.symm_source, D.target_φ]; exact hy'V
        rw [← hxy, ← D.source_φ, ← D.φ.symm_target]
        exact D.φ.symm.map_source hy
      · rw [← hxy]
        exact D.φ.right_inv (by rw [D.target_φ]; exact hy'V)

theorem isOpenMap_ιX : IsOpenMap D.ιX := by
  intro W hW
  have h : IsOpen (D.q ⁻¹' (D.ιX '' W)) := by
    rw [D.preimage_image_U W]
    refine IsOpen.union (Topology.IsOpenEmbedding.inl.isOpenMap W hW) ?_
    refine Topology.IsOpenEmbedding.inr.isOpenMap _ ?_
    exact (D.φ.isOpen_image_iff_of_subset_source fun x hx => by rw [D.source_φ]; exact hx.2).mpr
      (hW.inter D.isOpen_U)
  change IsOpen[TopologicalSpace.coinduced D.q inferInstance] (D.ιX '' W)
  rwa [isOpen_coinduced]

theorem isOpenMap_ιY : IsOpenMap D.ιY := by
  intro W hW
  have h : IsOpen (D.q ⁻¹' (D.ιY '' W)) := by
    rw [D.preimage_image_V W]
    refine IsOpen.union (Topology.IsOpenEmbedding.inr.isOpenMap W hW) ?_
    refine Topology.IsOpenEmbedding.inl.isOpenMap _ ?_
    exact (D.φ.symm.isOpen_image_iff_of_subset_source fun x hx => by
      rw [D.φ.symm_source, D.target_φ]; exact hx.2).mpr (hW.inter D.isOpen_V)
  change IsOpen[TopologicalSpace.coinduced D.q inferInstance] (D.ιY '' W)
  rwa [isOpen_coinduced]

theorem isOpenEmbedding_ιX : Topology.IsOpenEmbedding D.ιX :=
  Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap D.continuous_ιX D.ιX_injective
    D.isOpenMap_ιX

theorem isOpenEmbedding_ιY : Topology.IsOpenEmbedding D.ιY :=
  Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap D.continuous_ιY D.ιY_injective
    D.isOpenMap_ιY

section Charts

variable [Nonempty X] [Nonempty Y]

/-- The open embedding of `X` into the glued space, as an open partial homeomorphism. -/
noncomputable def homX : OpenPartialHomeomorph X D.Glued :=
  Topology.IsOpenEmbedding.toOpenPartialHomeomorph D.ιX D.isOpenEmbedding_ιX

/-- The open embedding of `Y` into the glued space, as an open partial homeomorphism. -/
noncomputable def homY : OpenPartialHomeomorph Y D.Glued :=
  Topology.IsOpenEmbedding.toOpenPartialHomeomorph D.ιY D.isOpenEmbedding_ιY

theorem homX_apply (x : X) : D.homX x = D.ιX x :=
  congrFun (Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply D.ιX D.isOpenEmbedding_ιX) x

theorem homY_apply (y : Y) : D.homY y = D.ιY y :=
  congrFun (Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply D.ιY D.isOpenEmbedding_ιY) y

theorem homX_source : D.homX.source = univ :=
  Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source D.ιX D.isOpenEmbedding_ιX

theorem homY_source : D.homY.source = univ :=
  Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source D.ιY D.isOpenEmbedding_ιY

theorem homX_target : D.homX.target = range D.ιX :=
  Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target D.ιX D.isOpenEmbedding_ιX

theorem homY_target : D.homY.target = range D.ιY :=
  Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target D.ιY D.isOpenEmbedding_ιY

theorem homX_symm_apply (x : X) : D.homX.symm (D.ιX x) = x := by
  rw [← D.homX_apply x]
  exact D.homX.left_inv (mem_univ x)

theorem homY_symm_apply (y : Y) : D.homY.symm (D.ιY y) = y := by
  rw [← D.homY_apply y]
  exact D.homY.left_inv (mem_univ y)

/-- Charts of the glued space coming from `X`. -/
noncomputable def chartOfX (x : X) : OpenPartialHomeomorph D.Glued H :=
  D.homX.symm.trans (chartAt H x)

/-- Charts of the glued space coming from `Y`. -/
noncomputable def chartOfY (y : Y) : OpenPartialHomeomorph D.Glued H :=
  D.homY.symm.trans (chartAt H y)

/-- A chart of the glued space at each point. -/
noncomputable def chartAt (z : D.Glued) : OpenPartialHomeomorph D.Glued H :=
  Sum.elim D.chartOfX D.chartOfY (Quotient.out z)

theorem chartAt_of_out_inl {z : D.Glued} {x : X} (h : Quotient.out z = Sum.inl x) :
    D.chartAt z = D.chartOfX x := by
  simp only [chartAt, h, Sum.elim_inl]

theorem chartAt_of_out_inr {z : D.Glued} {y : Y} (h : Quotient.out z = Sum.inr y) :
    D.chartAt z = D.chartOfY y := by
  simp only [chartAt, h, Sum.elim_inr]

theorem mem_chartOfX_source {x : X} {z : D.Glued} (hz : z = D.ιX x) :
    z ∈ (D.chartOfX x).source := by
  simp only [chartOfX, OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage,
    OpenPartialHomeomorph.symm_source, D.homX_target]
  refine ⟨⟨x, hz.symm⟩, ?_⟩
  rw [hz, D.homX_symm_apply x]
  exact mem_chart_source H x

theorem mem_chartOfY_source {y : Y} {z : D.Glued} (hz : z = D.ιY y) :
    z ∈ (D.chartOfY y).source := by
  simp only [chartOfY, OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage,
    OpenPartialHomeomorph.symm_source, D.homY_target]
  refine ⟨⟨y, hz.symm⟩, ?_⟩
  rw [hz, D.homY_symm_apply y]
  exact mem_chart_source H y

/-- The charted space structure on the glued space. -/
noncomputable instance instChartedSpace : ChartedSpace H D.Glued where
  atlas := range D.chartAt
  chartAt := D.chartAt
  mem_chart_source z := by
    have hout := Quotient.out_eq z
    cases hout' : Quotient.out z with
    | inl x =>
      have hz : z = D.ιX x := by rw [← hout, hout']; rfl
      rw [D.chartAt_of_out_inl hout']
      exact D.mem_chartOfX_source hz
    | inr y =>
      have hz : z = D.ιY y := by rw [← hout, hout']; rfl
      rw [D.chartAt_of_out_inr hout']
      exact D.mem_chartOfY_source hz
  chart_mem_atlas z := ⟨z, rfl⟩

end Charts

end Data

end Submission.Glue
