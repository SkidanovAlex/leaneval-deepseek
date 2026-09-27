import Mathlib
import Submission.Work.Euclidean.TangentField.Setup
import Submission.Work.Euclidean.TangentField.CurveTangent
import Submission.Work.Euclidean.TangentField.exists_tangent_field_of_component_not_isCompact
import Submission.Work.ManifoldParity.exists_continuous_tangent_field

/-!
# The component-wise construction of a continuous tangent field

This file assembles the continuous non-vanishing tangent field of the `P`-form from the
component-wise data:

* each connected component of the germ set `A = P ∩ ⋃_j U_j` of a finite chart family carries such
  a field parallel to all the graph charts of `A` — the compact components via the manifold chapter
  `Work.ManifoldParity.exists_continuous_tangent_field`, the non-compact ones via
  `Work.Euclidean.TangentField.exists_tangent_field_of_component_not_isCompact`;
* the least index of a component containing a point of `K` is locally constant on `K`
  (`Work.Euclidean.TangentField.eventually_indexSet_eq`), because the components are clopen, so
  gluing the component fields by that index is continuous;
* a `P`-chart at a point of `K` restricts to a graph chart of `A` with the same `(i, η)`, so the
  parallelism with the `P`-charts follows.
-/

namespace Work.Euclidean.TangentField

open scoped ContDiff Topology Manifold
open Set Manifold

noncomputable section

set_option autoImplicit false

variable {n : ℕ}

/-- **Each component of the germ set carries a continuous non-vanishing tangent field**, parallel to
every graph chart of the germ set at its points. -/
theorem exists_component_field {ι : Type*} {P : EuclideanSpace ℝ (Fin n) → Prop}
    (F : ι → PChart P) (p : ↥(germSet P F)) :
    ∃ U : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      ContinuousOn U (Subtype.val '' (connectedComponent p)) ∧
      (∀ y ∈ Subtype.val '' (connectedComponent p), U y ≠ 0) ∧
      (∀ y ∈ Subtype.val '' (connectedComponent p),
        ∀ (i : Fin n) (V : Set (EuclideanSpace ℝ (Fin n))) (η : ℝ → EuclideanSpace ℝ (Fin n)),
          Work.ManifoldParity.IsGraphChart (germSet P F) i V η → y ∈ V →
          ∃ c : ℝ, c ≠ 0 ∧
            U y = c • (EuclideanSpace.single i (1:ℝ) + (fderiv ℝ η (y i)) (1:ℝ))) := by
  letI := Work.ManifoldParity.graphChartedSpace (germSet P F) (hasLocalGraphCharts_germSet F)
  have hCop : IsOpen (connectedComponent p) :=
    Work.ManifoldParity.isOpen_connectedComponent_graph (germSet P F)
      (hasLocalGraphCharts_germSet F) p
  by_cases hcpt : IsCompact (connectedComponent p)
  · have hCcpt : IsCompact (Subtype.val '' (connectedComponent p)) :=
      hcpt.image continuous_subtype_val
    have hCgra : Work.ManifoldParity.HasLocalGraphCharts
        (Subtype.val '' (connectedComponent p)) := by
      intro y hy
      obtain ⟨y', hy'C, rfl⟩ := hy
      obtain ⟨j, hy'Uj⟩ := (mem_germSet.mp y'.2).2
      obtain ⟨U', hU'o, hy'U', -, hchartC⟩ :=
        isGraphChart_component F hCop (F j) y'.2 hy'C hy'Uj (mem_iUnion.mpr ⟨j, hy'Uj⟩)
      exact ⟨(F j).i, U', (F j).η, hchartC, hy'U'⟩
    have hCgra' : ∀ x ∈ Subtype.val '' (connectedComponent p),
        ∃ (i : Fin n) (U : Set (EuclideanSpace ℝ (Fin n)))
          (η : ℝ → EuclideanSpace ℝ (Fin n)),
          IsOpen U ∧ x ∈ U ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η ∧ (∀ t, η t i = 0) ∧
          ∀ y ∈ U, (y ∈ Subtype.val '' (connectedComponent p) ↔
            y = (y i) • EuclideanSpace.single i (1:ℝ) + η (y i)) := by
      intro x hx
      obtain ⟨i, U, η, hchart, hxU⟩ := hCgra x hx
      exact ⟨i, U, η, hchart.1, hxU, hchart.2.1, hchart.2.2.1, hchart.2.2.2⟩
    obtain ⟨U, hUcont, hUne, hUtan⟩ :=
      Work.ManifoldParity.exists_continuous_tangent_field (Subtype.val '' (connectedComponent p))
        hCcpt hCgra'
    refine ⟨U, hUcont, hUne, ?_⟩
    intro y hy i V η hV hyV
    have hyk := hy
    obtain ⟨y', hy'C, hy'eq⟩ := hyk
    have hyA : y ∈ germSet P F := by rw [← hy'eq]; exact y'.2
    have hyV' : y ∈ V := hyV
    have hyC : (⟨y, hyA⟩ : ↥(germSet P F)) ∈ connectedComponent p := by
      have hh : (⟨y, hyA⟩ : ↥(germSet P F)) = y' := Subtype.ext hy'eq.symm
      rw [hh]; exact hy'C
    obtain ⟨U', hU'o, hyU', -, hchart⟩ :=
      isGraphChart_component_of_raw F hCop hV hyA hyC hyV'
    exact hUtan y hy i U' η hU'o hyU' hchart.2.1 hchart.2.2.1 hchart.2.2.2
  · obtain ⟨U, hUcont, hUne, hUtan⟩ :=
      exists_tangent_field_of_component_not_isCompact (germSet P F)
        (hasLocalGraphCharts_germSet F) p hcpt
    exact ⟨U, hUcont, hUne, hUtan⟩

/-- **The `P`-form continuous tangent field**, by the component-wise construction. -/
theorem exists_continuous_tangent_field_localGraph_alt {n : ℕ}
    {P : EuclideanSpace ℝ (Fin n) → Prop} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) (hKsub : ∀ x ∈ K, P x)
    (hgra : ∀ x ∈ K, ∃ (i : Fin n) (U : Set (EuclideanSpace ℝ (Fin n)))
        (η : ℝ → EuclideanSpace ℝ (Fin n)),
        IsOpen U ∧ x ∈ U ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η ∧ (∀ t, η t i = 0) ∧
        ∀ y ∈ U, (P y ↔ y = (y i) • EuclideanSpace.single i (1:ℝ) + η (y i))) :
    ∃ U : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      ContinuousOn U K ∧ (∀ x ∈ K, U x ≠ 0) ∧
      (∀ x ∈ K, ∀ (i : Fin n) (V : Set (EuclideanSpace ℝ (Fin n)))
          (η : ℝ → EuclideanSpace ℝ (Fin n)),
        IsOpen V → x ∈ V → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η → (∀ t, η t i = 0) →
        (∀ y ∈ V, (P y ↔ y = (y i) • EuclideanSpace.single i (1:ℝ) + η (y i))) →
        ∃ c : ℝ, c ≠ 0 ∧
          U x = c • (EuclideanSpace.single i (1:ℝ) + (fderiv ℝ η (x i)) (1:ℝ))) := by
  classical
  obtain ⟨m, F, hcover⟩ := exists_finite_PChart (P := P) hK hgra
  have hsub : K ⊆ germSet P F :=
    fun x hx => mem_germSet.mpr ⟨hKsub x hx, mem_iUnion.mp (hcover hx)⟩
  have hA : Work.ManifoldParity.HasLocalGraphCharts (germSet P F) := hasLocalGraphCharts_germSet F
  obtain ⟨Mc, q, hqcover⟩ := exists_finite_components_cover hA hK hsub
  choose Uf hUfcont hUfne hUftan using fun j : Fin Mc => exists_component_field F (q j)
  -- the finite set of component indices through a point of `K`
  let J : (x : EuclideanSpace ℝ (Fin n)) → x ∈ K → Finset (Fin Mc) := fun x hx =>
    Finset.univ.filter (fun j => (⟨x, hsub hx⟩ : ↥(germSet P F)) ∈ connectedComponent (q j))
  have hJmem : ∀ (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ K) (j : Fin Mc),
      j ∈ J x hx ↔ (⟨x, hsub hx⟩ : ↥(germSet P F)) ∈ connectedComponent (q j) := by
    intro x hx j
    simp only [J, Finset.mem_filter, Finset.mem_univ, true_and]
  have Jne : ∀ (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ K), (J x hx).Nonempty := by
    intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hqcover hx)
    obtain ⟨y', hy'C, hy'eq⟩ := hj
    refine ⟨j, (hJmem x hx j).mpr ?_⟩
    have hh : (⟨x, hsub hx⟩ : ↥(germSet P F)) = y' := Subtype.ext hy'eq.symm
    rw [hh]
    exact hy'C
  let jmin : (x : EuclideanSpace ℝ (Fin n)) → x ∈ K → Fin Mc := fun x hx =>
    (J x hx).min' (Jne x hx)
  have hjmin_mem : ∀ (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ K), jmin x hx ∈ J x hx :=
    fun x hx => Finset.min'_mem _ _
  let U₀ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun x =>
    if hx : x ∈ K then Uf (jmin x hx) x else 0
  have hU₀apply : ∀ (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ K),
      U₀ x = Uf (jmin x hx) x := fun x hx => dif_pos hx
  -- the point lies in the image of its selected component
  have hmem_comp : ∀ (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ K),
      x ∈ Subtype.val '' (connectedComponent (q (jmin x hx))) := fun x hx =>
    ⟨⟨x, hsub hx⟩, (hJmem x hx (jmin x hx)).mp (hjmin_mem x hx), rfl⟩
  -- the index set, hence the selected component, is locally constant
  have hkey : ∀ (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ K), ∃ W ∈ 𝓝 x, ∀ y ∈ W,
      ∀ (hyK : y ∈ K), J y hyK = J x hx ∧
        y ∈ Subtype.val '' (connectedComponent (q (jmin x hx))) := by
    intro x hx
    obtain ⟨W, hW, hW'⟩ := eventually_indexSet_eq hA hsub q x hx
    refine ⟨W, hW, fun y hy hyK => ⟨?_, ?_⟩⟩
    · ext j
      rw [hJmem y hyK j, hJmem x hx j]
      exact hW' y hy hyK j
    · have hJeq : J y hyK = J x hx := by
        ext j
        rw [hJmem y hyK j, hJmem x hx j]
        exact hW' y hy hyK j
      have h1 : jmin x hx ∈ J y hyK := by
        rw [hJeq]
        exact hjmin_mem x hx
      exact ⟨⟨y, hsub hyK⟩, (hJmem y hyK (jmin x hx)).mp h1, rfl⟩
  have hmin : ∀ {s t : Finset (Fin Mc)} (h : s = t) (hs : s.Nonempty) (ht : t.Nonempty),
      s.min' hs = t.min' ht := by
    intro s t h hs ht
    refine le_antisymm ?_ ?_
    · exact Finset.min'_le _ _ (by rw [h]; exact Finset.min'_mem _ _)
    · exact Finset.min'_le _ _ (by rw [← h]; exact Finset.min'_mem _ _)
  have hU₀ne' : ∀ (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ K), U₀ x ≠ 0 := by
    intro x hx
    rw [hU₀apply x hx]
    exact hUfne (jmin x hx) x (hmem_comp x hx)
  have hU₀cont : ContinuousOn U₀ K := by
    intro x₀ hx₀
    obtain ⟨W₁, hW₁, hW₁'⟩ := hkey x₀ hx₀
    have hWW : W₁ ∈ 𝓝 x₀ := hW₁
    have heq : U₀ =ᶠ[𝓝[K] x₀] Uf (jmin x₀ hx₀) := by
      refine Filter.eventuallyEq_of_mem
        (Filter.inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hWW)) ?_
      intro y hy
      obtain ⟨hyK, hyW₁⟩ := hy
      rw [hU₀apply y hyK]
      congr 1
      exact hmin (hW₁' y hyW₁ hyK).1 _ _
    have hcw : ContinuousWithinAt (Uf (jmin x₀ hx₀)) K x₀ :=
      ((hUfcont (jmin x₀ hx₀)).continuousWithinAt (hmem_comp x₀ hx₀)).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset
          (Filter.inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hWW))
          (fun y hy => (hW₁' y hy.2 hy.1).2))
    exact hcw.congr_of_eventuallyEq heq (hU₀apply x₀ hx₀)
  refine ⟨U₀, hU₀cont, hU₀ne', ?_⟩
  intro x hx i V η hVo hxV hηsm hηi hgr
  rw [hU₀apply x hx]
  have hchartA : Work.ManifoldParity.IsGraphChart (germSet P F) i (V ∩ ⋃ j, (F j).U) η := by
    refine ⟨hVo.inter (isOpen_iUnion fun j => (F j).hU), hηsm, hηi, ?_⟩
    intro z hz
    constructor
    · intro hzA
      exact (hgr z hz.1).mp hzA.1
    · intro hzgraph
      exact ⟨(hgr z hz.1).mpr hzgraph, hz.2⟩
  have hxchart : x ∈ V ∩ ⋃ j, (F j).U := ⟨hxV, hcover hx⟩
  exact hUftan (jmin x hx) x (hmem_comp x hx)
    i (V ∩ ⋃ j, (F j).U) η hchartA hxchart

end

end Work.Euclidean.TangentField
