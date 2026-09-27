import Mathlib
import Submission.Work.ManifoldParity.Defs
import Submission.Work.ManifoldParity.GraphManifold
import Submission.Work.ManifoldParity.curve_tangent_chart
import Submission.Work.ManifoldParity.CircleParam

/-!
# Local graph data for an ambient predicate `P`

The target `Work.Euclidean.TangentField.exists_smooth_tangent_field` assumes that the *ambient
predicate* `P` is locally the graph of a smooth function over a coordinate axis at every point of
`K ⊆ P` (rather than that `K` itself is locally a graph).  This file collects the elementary
consequences of that hypothesis which the rest of the development uses:

* `PChart` — a local graph presentation of `P`;
* `germSet P F` — the union of the chart opens of a finite family, intersected with `P`; this is the
  set which is genuinely locally a graph (and contains `K` as soon as the family covers `K`);
* `hasLocalGraphCharts_germSet` — `germSet` satisfies `HasLocalGraphCharts`;
* `germSet_chart` — every `PChart` of the family restricts to a graph chart of `germSet`;
* `exists_finite_PChart` — finitely many charts cover a compact set.
-/

namespace Work.Euclidean.TangentField

open scoped ContDiff Topology Manifold
open Set Manifold

noncomputable section

set_option autoImplicit false

variable {n : ℕ}

/-- **A local graph presentation of the ambient predicate `P`:** on the open set `U` the set
`{y | P y}` is exactly the graph of `η` over the `i`-th coordinate. -/
structure PChart (P : EuclideanSpace ℝ (Fin n) → Prop) where
  /-- the coordinate of the graph -/
  i : Fin n
  /-- the open set on which the presentation is valid -/
  U : Set (EuclideanSpace ℝ (Fin n))
  /-- the graphing function -/
  η : ℝ → EuclideanSpace ℝ (Fin n)
  hU : IsOpen U
  hη : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η
  hη0 : ∀ t, η t i = 0
  hgraph : ∀ y ∈ U, (P y ↔ y = (y i) • EuclideanSpace.single i (1 : ℝ) + η (y i))

/-- The graph map of a `PChart`. -/
def PChart.gmap {P : EuclideanSpace ℝ (Fin n) → Prop} (p : PChart P) :
    ℝ → EuclideanSpace ℝ (Fin n) :=
  Work.ManifoldParity.gmap p.i p.η

/-- Points of the chart domain at which `P` holds are graph points. -/
theorem PChart.eq_gmap {P : EuclideanSpace ℝ (Fin n) → Prop} (p : PChart P)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ p.U) (hPx : P x) : x = p.gmap (x p.i) :=
  (p.hgraph x hx).mp hPx

/-- The chart graph lies in `P`. -/
theorem PChart.gmap_mem {P : EuclideanSpace ℝ (Fin n) → Prop} (p : PChart P) {t : ℝ}
    (ht : p.gmap t ∈ p.U) : P (p.gmap t) := by
  have h := (p.hgraph (p.gmap t) ht).mpr
  have hcoord : (p.gmap t) p.i = t := Work.ManifoldParity.gmap_coord p.hη0 t
  rw [hcoord] at h
  exact h rfl

/-- The hypothesis of the target, reassembled as a family of `PChart`s. -/
theorem exists_PChart {P : EuclideanSpace ℝ (Fin n) → Prop}
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hgra : ∀ x ∈ K, ∃ (i : Fin n) (U : Set (EuclideanSpace ℝ (Fin n)))
        (η : ℝ → EuclideanSpace ℝ (Fin n)),
        IsOpen U ∧ x ∈ U ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η ∧ (∀ t, η t i = 0) ∧
        ∀ y ∈ U, (P y ↔ y = (y i) • EuclideanSpace.single i (1:ℝ) + η (y i)))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ K) : ∃ p : PChart P, x ∈ p.U := by
  obtain ⟨i, U, η, hU, hxU, hη, hη0, hgraph⟩ := hgra x hx
  exact ⟨⟨i, U, η, hU, hη, hη0, hgraph⟩, hxU⟩

/-- **The "germ set" of a finite family of charts:** the union of the chart opens, intersected
with `P`.  This is the set which is locally a graph. -/
def germSet {ι : Type*} {n : ℕ} (P : EuclideanSpace ℝ (Fin n) → Prop) (F : ι → PChart P) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  P ∩ ⋃ j : ι, (F j).U

theorem mem_germSet {ι : Type*} {n : ℕ} {P : EuclideanSpace ℝ (Fin n) → Prop} {F : ι → PChart P}
    {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ germSet P F ↔ P x ∧ ∃ j, x ∈ (F j).U := by
  rw [germSet]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rwa [Set.mem_iUnion] at h2
  · rintro ⟨h1, h2⟩
    exact ⟨h1, Set.mem_iUnion.mpr h2⟩

/-- The germ set is contained in `P`. -/
theorem germSet_subset {ι : Type*} {n : ℕ} {P : EuclideanSpace ℝ (Fin n) → Prop}
    {F : ι → PChart P} : germSet P F ⊆ {x | P x} := fun _ hx => hx.1

/-- **Every chart of the family is a graph chart of the germ set.** -/
theorem germSet_chart {ι : Type*} {n : ℕ} {P : EuclideanSpace ℝ (Fin n) → Prop}
    {F : ι → PChart P} (j : ι) :
    Work.ManifoldParity.IsGraphChart (germSet P F) (F j).i (F j).U (F j).η := by
  refine ⟨(F j).hU, (F j).hη, (F j).hη0, ?_⟩
  intro y hy
  rw [mem_germSet]
  constructor
  · rintro ⟨hyP, -⟩
    exact (F j).eq_gmap hy hyP
  · intro hygraph
    have hmem : (F j).gmap (y (F j).i) ∈ (F j).U := by
      rw [show (F j).gmap (y (F j).i) = y from hygraph.symm]
      exact hy
    have hPy : P y := by
      rw [show y = (F j).gmap (y (F j).i) from hygraph]
      exact (F j).gmap_mem hmem
    have hmem' : y ∈ (F j).U := by
      rw [show y = (F j).gmap (y (F j).i) from hygraph]
      exact hmem
    exact ⟨hPy, ⟨j, hmem'⟩⟩

/-- **The germ set satisfies `HasLocalGraphCharts`.** -/
theorem hasLocalGraphCharts_germSet {ι : Type*} {n : ℕ} {P : EuclideanSpace ℝ (Fin n) → Prop}
    (F : ι → PChart P) :
    Work.ManifoldParity.HasLocalGraphCharts (germSet P F) := by
  intro x hx
  rw [mem_germSet] at hx
  obtain ⟨hxP, j, hxj⟩ := hx
  exact ⟨(F j).i, (F j).U, (F j).η, germSet_chart j, hxj⟩

/-- **Finitely many charts whose opens cover `K` exist** when `K` is compact. -/
theorem exists_finite_PChart {P : EuclideanSpace ℝ (Fin n) → Prop}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (hgra : ∀ x ∈ K, ∃ (i : Fin n) (U : Set (EuclideanSpace ℝ (Fin n)))
        (η : ℝ → EuclideanSpace ℝ (Fin n)),
        IsOpen U ∧ x ∈ U ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η ∧ (∀ t, η t i = 0) ∧
        ∀ y ∈ U, (P y ↔ y = (y i) • EuclideanSpace.single i (1:ℝ) + η (y i))) :
    ∃ (m : ℕ) (F : Fin m → PChart P), K ⊆ ⋃ j, (F j).U := by
  classical
  let c : ↥K → PChart P := fun x => Classical.choose (exists_PChart (P := P) hgra x.2)
  have hc : ∀ x : ↥K, ((x : ↥K) : EuclideanSpace ℝ (Fin n)) ∈ (c x).U := fun x =>
    Classical.choose_spec (exists_PChart (P := P) hgra x.2)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : ↥K => (c x).U) (fun x => (c x).hU)
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hc ⟨x, hx⟩⟩)
  let F : Fin t.card → PChart P := fun j => c ((Finset.equivFin t).symm j).1
  refine ⟨t.card, F, fun x hx => ?_⟩
  have hx' : x ∈ ⋃ i ∈ t, (c i).U := ht hx
  simp only [Set.mem_iUnion, exists_prop] at hx'
  obtain ⟨y, hyt, hyx⟩ := hx'
  refine Set.mem_iUnion.mpr ⟨Finset.equivFin t ⟨y, hyt⟩, ?_⟩
  have hpick : F (Finset.equivFin t ⟨y, hyt⟩) = c y := by
    show c ((Finset.equivFin t).symm (Finset.equivFin t ⟨y, hyt⟩)).1 = c y
    rw [Equiv.symm_apply_apply]
  rw [hpick]
  exact hyx

end

end Work.Euclidean.TangentField

namespace Work.Euclidean.TangentField

open scoped ContDiff Topology Manifold
open Set Manifold

noncomputable section

set_option autoImplicit false

variable {n : ℕ}

/-- A point of an open subset of a subtype, seen in the ambient space, has an ambient open
neighbourhood whose points of the subtype all lie in the open subset. -/
theorem exists_isOpen_of_isOpen_subtype {E : Type*} [TopologicalSpace E] {A : Set E}
    {C : Set ↥A} (hC : IsOpen C) {x : E} (hxA : x ∈ A)
    (hxC : (⟨x, hxA⟩ : ↥A) ∈ C) :
    ∃ U' : Set E, IsOpen U' ∧ x ∈ U' ∧
      ∀ y ∈ U', ∀ (hyA : y ∈ A), (⟨y, hyA⟩ : ↥A) ∈ C := by
  rw [isOpen_iff_mem_nhds] at hC
  have h := hC ⟨x, hxA⟩ hxC
  rw [nhds_subtype, Filter.mem_comap] at h
  obtain ⟨t, ht, hsub⟩ := h
  obtain ⟨U', ⟨hxU', hU'o⟩, hU't⟩ := (nhds_basis_opens x).mem_iff.mp ht
  exact ⟨U', hU'o, hxU', fun y hy hyA => hsub (hU't hy)⟩

/-- **Finitely many components of `A` cover a compact `K ⊆ A`**, when `A` is locally a graph (so
that its connected components are open). -/
theorem exists_finite_components_cover {A : Set (EuclideanSpace ℝ (Fin n))}
    (hA : Work.ManifoldParity.HasLocalGraphCharts A)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKsub : K ⊆ A) :
    ∃ (m : ℕ) (p : Fin m → ↥A),
      K ⊆ ⋃ j, Subtype.val '' (connectedComponent (p j) : Set ↥A) := by
  classical
  letI := Work.ManifoldParity.graphChartedSpace A hA
  have hcomp : ∀ p : ↥A, IsOpen (connectedComponent p) :=
    Work.ManifoldParity.isOpen_connectedComponent_graph A hA
  haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
  set φ : ↥K → ↥A := fun y => ⟨(y : EuclideanSpace ℝ (Fin n)), hKsub y.2⟩ with hφ
  have hcontφ : Continuous φ := continuous_subtype_val.subtype_mk _
  have hcover : (Set.univ : Set ↥K) ⊆ ⋃ p : ↥A, φ ⁻¹' (connectedComponent p) := by
    intro y _
    exact mem_iUnion.mpr ⟨φ y, mem_connectedComponent⟩
  obtain ⟨s, hs⟩ := (isCompact_univ_iff.mpr inferInstance).elim_finite_subcover
    (fun p : ↥A => φ ⁻¹' (connectedComponent p))
    (fun p => (hcomp p).preimage hcontφ) hcover
  refine ⟨s.card, fun j => ((Finset.equivFin s).symm j).1, fun x hx => ?_⟩
  have hx'univ : (⟨x, hx⟩ : ↥K) ∈ (Set.univ : Set ↥K) := trivial
  have hxmem : (⟨x, hx⟩ : ↥K) ∈ ⋃ p ∈ s, φ ⁻¹' (connectedComponent p) := hs hx'univ
  simp only [Set.mem_iUnion, exists_prop] at hxmem
  obtain ⟨p, hps, hpcomp⟩ := hxmem
  refine Set.mem_iUnion.mpr ⟨Finset.equivFin s ⟨p, hps⟩, ?_⟩
  refine ⟨⟨x, hKsub hx⟩, ?_, rfl⟩
  have hpick : (Finset.equivFin s).symm (Finset.equivFin s ⟨p, hps⟩) = ⟨p, hps⟩ :=
    Equiv.symm_apply_apply _ _
  show (⟨x, hKsub hx⟩ : ↥A) ∈ connectedComponent
    (((Finset.equivFin s).symm (Finset.equivFin s ⟨p, hps⟩) : ↥s).1)
  rw [hpick]
  exact hpcomp

/-- **A `P`-chart of the ambient family restricts to a graph chart of a component of the germ set.**
The point `x ∈ K` lies in the component `C` of `A`; the chart `(i, U, η)` of `P` at `x`, cut down to
the chart opens of the family and to a neighbourhood of `x` inside `C`, is a graph chart of (the
image of) `C`. -/
theorem isGraphChart_component {ι : Type*} {P : EuclideanSpace ℝ (Fin n) → Prop}
    (F : ι → PChart P) {C : Set ↥(germSet P F)} (hC : IsOpen C) (p : PChart P)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ germSet P F)
    (hxC : (⟨x, hx⟩ : ↥(germSet P F)) ∈ C) (hxp : x ∈ p.U) (hxU : x ∈ ⋃ j, (F j).U) :
    ∃ U' : Set (EuclideanSpace ℝ (Fin n)), IsOpen U' ∧ x ∈ U' ∧ U' ⊆ p.U ∧
      Work.ManifoldParity.IsGraphChart (Subtype.val '' C) p.i U' p.η := by
  obtain ⟨V, hVo, hxV, hVsub⟩ := exists_isOpen_of_isOpen_subtype hC hx hxC
  have hUopen : IsOpen (⋃ j, (F j).U) := isOpen_iUnion fun j => (F j).hU
  have hopen : IsOpen (p.U ∩ (⋃ j, (F j).U) ∩ V) := (p.hU.inter hUopen).inter hVo
  refine ⟨p.U ∩ (⋃ j, (F j).U) ∩ V, hopen, ⟨⟨hxp, hxU⟩, hxV⟩, ?_, ?_⟩
  · intro y hy
    exact hy.1.1
  · refine ⟨hopen, p.hη, p.hη0, ?_⟩
    intro y hy
    constructor
    · rintro ⟨y', hy'C, hy'eq⟩
      have hyA : y ∈ germSet P F := by rw [← hy'eq]; exact y'.2
      exact p.eq_gmap hy.1.1 hyA.1
    · intro hygraph
      have hyP : P y := (p.hgraph y hy.1.1).mpr hygraph
      have hyU : y ∈ ⋃ j, (F j).U := hy.1.2
      have hyA : y ∈ germSet P F := ⟨hyP, hyU⟩
      exact ⟨⟨y, hyA⟩, hVsub y hy.2 hyA, rfl⟩

end

end Work.Euclidean.TangentField

namespace Work.Euclidean.TangentField

open scoped ContDiff Topology Manifold
open Set Manifold

noncomputable section

set_option autoImplicit false

variable {n : ℕ}

/-- **The index set of a finite family of connected components is locally constant.**  If `K ⊆ A` and
`A` is locally a graph (so that its connected components are open — they are always closed), then
for every `x ∈ K` the set of indices `j` with `x` lying in the `j`-th component of the family is
constant on a neighbourhood of `x` inside `K`.

This is the valid version of the "least chart index is locally constant" argument: it must be run
with *closed* pieces (the connected components), not with chart opens. -/
theorem eventually_indexSet_eq {A : Set (EuclideanSpace ℝ (Fin n))}
    (hA : Work.ManifoldParity.HasLocalGraphCharts A) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hKsub : K ⊆ A) {Mc : ℕ} (q : Fin Mc → ↥A) :
    ∀ (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ K), ∃ U ∈ 𝓝 x, ∀ y ∈ U, ∀ (hyK : y ∈ K),
      ∀ j : Fin Mc, ((⟨y, hKsub hyK⟩ : ↥A) ∈ connectedComponent (q j) ↔
        (⟨x, hKsub hx⟩ : ↥A) ∈ connectedComponent (q j)) := by
  letI := Work.ManifoldParity.graphChartedSpace A hA
  have hcomp : ∀ p : ↥A, IsOpen (connectedComponent p) :=
    Work.ManifoldParity.isOpen_connectedComponent_graph A hA
  intro x hx
  set xA : ↥A := ⟨x, hKsub hx⟩ with hxA
  have key : ∀ j : Fin Mc, ∃ U ∈ 𝓝 x, ∀ y ∈ U, ∀ hyA : y ∈ A,
      ((⟨y, hyA⟩ : ↥A) ∈ connectedComponent (q j) ↔ xA ∈ connectedComponent (q j)) := by
    intro j
    by_cases hj : xA ∈ connectedComponent (q j)
    · obtain ⟨U', hU'o, hxU', hsub'⟩ :=
        exists_isOpen_of_isOpen_subtype (hcomp (q j)) (hKsub hx) hj
      exact ⟨U', hU'o.mem_nhds hxU', fun y hy hyA =>
        ⟨fun _ => hj, fun _ => hsub' y hy hyA⟩⟩
    · obtain ⟨U', hU'o, hxU', hsub'⟩ :=
        exists_isOpen_of_isOpen_subtype (isClosed_connectedComponent.isOpen_compl)
          (hKsub hx) hj
      exact ⟨U', hU'o.mem_nhds hxU', fun y hy hyA =>
        ⟨fun h => absurd h (hsub' y hy hyA), fun h => absurd h hj⟩⟩
  choose Uf hUf_mem hUf using key
  exact ⟨⋂ j, Uf j, Filter.iInter_mem.mpr hUf_mem, fun y hy hyK j =>
    hUf j y (Set.mem_iInter.mp hy j) (hKsub hyK)⟩

/-- **The raw version of `isGraphChart_component`:** for a graph chart of the germ set itself (with
its `A`-form graph condition) rather than a `PChart`, the same restriction argument gives a graph
chart of the component with the *same* `(i, η)`. -/
theorem isGraphChart_component_of_raw {ι : Type*} {P : EuclideanSpace ℝ (Fin n) → Prop}
    (F : ι → PChart P) {C : Set ↥(germSet P F)} (hC : IsOpen C)
    {i : Fin n} {V : Set (EuclideanSpace ℝ (Fin n))} {η : ℝ → EuclideanSpace ℝ (Fin n)}
    (hV : Work.ManifoldParity.IsGraphChart (germSet P F) i V η)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ germSet P F)
    (hxC : (⟨x, hx⟩ : ↥(germSet P F)) ∈ C) (hxV : x ∈ V) :
    ∃ U' : Set (EuclideanSpace ℝ (Fin n)), IsOpen U' ∧ x ∈ U' ∧ U' ⊆ V ∧
      Work.ManifoldParity.IsGraphChart (Subtype.val '' C) i U' η := by
  obtain ⟨V₀, hV₀o, hxV₀, hV₀sub⟩ := exists_isOpen_of_isOpen_subtype hC hx hxC
  have hopen : IsOpen (V ∩ V₀) := hV.1.inter hV₀o
  refine ⟨V ∩ V₀, hopen, ⟨hxV, hxV₀⟩, fun y hy => hy.1, ?_⟩
  refine ⟨hopen, hV.2.1, hV.2.2.1, ?_⟩
  intro y hy
  constructor
  · rintro ⟨y', hy'C, hy'eq⟩
    have hyA : y ∈ germSet P F := by rw [← hy'eq]; exact y'.2
    exact (hV.2.2.2 y hy.1).mp hyA
  · intro hygraph
    have hyA : y ∈ germSet P F := (hV.2.2.2 y hy.1).mpr hygraph
    exact ⟨⟨y, hyA⟩, hV₀sub y hy.2 hyA, rfl⟩

end

end Work.Euclidean.TangentField
