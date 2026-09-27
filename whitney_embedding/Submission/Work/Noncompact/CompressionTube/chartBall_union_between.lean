import Mathlib
import Submission.Work.Noncompact.CompressionTube.flat_ball

/-!
# A compact chart-ball union sandwiched between a compact set and a locally finite set

This file proves `chartBall_union_between`, the "shrinking and covering" step of the flat
refinement scheme: given

* a compact set `A` with `A ⊆ interior N`,
* a set `B` which is *locally finite* in compacta (`B ∩ K` is finite for every compact `K`),
* and the separation hypothesis `b ∈ B → b ∈ interior N → b ∉ A`,

there is a compact set `S` with

  `A ⊆ S ⊆ interior N`,  `S` a finite union of chart balls,  and  `S ∩ (B ∩ interior N) = ∅`.

The proof is the standard one:

* `exists_chartBall_interior_avoiding_B`: for each `a ∈ A` there is a chart ball around `a`,
  contained in `interior N` and disjoint from `B`.  The ball around the chart image of `a` is shrunk
  to a radius smaller than the distance of `φ a` to the (finite, hence closed) set of `B`-points
  that the big ball meets; the finiteness comes from `B ∩ (compact ball)`, the positivity of the
  distance from `φ a ∉ B` and finiteness of the set of distances.
* the *open* chart balls (the `φ.symm`-image of the open balls, `isOpen_symm_image_ball`) cover the
  compact `A`, so finitely many of them suffice (`IsCompact.elim_finite_subcover`); the union of the
  corresponding closed chart balls is the required `S`.

The only point that requires care in the formalisation is the index type of `IsChartBallUnion`,
which is required to live in `Type` (universe `0`) while the finite cover is naturally indexed by a
finite subset of the (universe-polymorphic) manifold `M`; the finite index set is therefore
transported to `Fin (Fintype.card _)` along `Fintype.equivFin`.
-/

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.Noncompact.CompressionTube

open Set Topology Metric

/-- **A chart ball is compact.**  The image under `φ.symm` of a Euclidean closed ball contained in
`φ.target` is a continuous image of a compact set. -/
theorem isCompact_homeoBall {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {c : EuclideanSpace ℝ (Fin n)} {r : ℝ} (htgt : closedBall c r ⊆ φ.target) :
    IsCompact (homeoBall φ c r) :=
  (isCompact_closedBall c r).image_of_continuousOn
    (fun z hz => (φ.continuousAt_symm (htgt hz)).continuousWithinAt)

/-- **The open chart ball is open.**  `φ.symm '' ball c r` is the trace on `φ.source` of the
preimage of a Euclidean open ball, hence open as soon as `ball c r ⊆ φ.target`. -/
theorem isOpen_symm_image_ball {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {c : EuclideanSpace ℝ (Fin n)} {r : ℝ} (htgt : closedBall c r ⊆ φ.target) :
    IsOpen (φ.symm '' ball c r) := by
  have hball : ball c r ⊆ φ.target := fun z hz => htgt (ball_subset_closedBall hz)
  have h_eq : φ.symm '' ball c r = φ.source ∩ φ ⁻¹' ball c r := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨φ.map_target (hball hy),
        by simp only [Set.mem_preimage]; rw [φ.right_inv (hball hy)]; exact hy⟩
    · rintro ⟨hxs, hxf⟩
      exact ⟨φ x, hxf, φ.left_inv hxs⟩
  rw [h_eq]
  exact φ.continuousOn.isOpen_inter_preimage φ.open_source Metric.isOpen_ball

/-- **A finite set of points can be avoided by a closed ball of positive radius.**  If `Y` is
finite and `x ∉ Y`, then for every `ρ > 0` there is `ε ∈ (0, ρ]` with
`closedBall x ε ∩ Y = ∅`.  (When `Y = ∅` one takes `ε = ρ`; otherwise `0 < infDist x Y` because
`Y` is finite and closed.) -/
theorem exists_radius_closedBall_inter_empty {α : Type*} [PseudoMetricSpace α] [T1Space α]
    {x : α} {Y : Set α} (hY : Y.Finite) (hx : x ∉ Y) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ ρ ∧ closedBall x ε ∩ Y = ∅ := by
  by_cases hne : Y.Nonempty
  · have hpos : 0 < infDist x Y := (hY.isClosed.notMem_iff_infDist_pos hne).mp hx
    refine ⟨min ρ (infDist x Y / 2), lt_min hρ (half_pos hpos), min_le_left _ _, ?_⟩
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨y, hy, hyY⟩
    have h1 : infDist x Y ≤ dist y x := by rw [dist_comm]; exact infDist_le_dist_of_mem hyY
    have h4 : dist y x ≤ min ρ (infDist x Y / 2) := by simpa using hy
    have h3 : min ρ (infDist x Y / 2) ≤ infDist x Y / 2 := min_le_right _ _
    linarith
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    exact ⟨ρ, hρ, le_rfl, by rw [hne]; exact Set.inter_empty _⟩

/-- **A chart ball around a point, inside an open set and avoiding a locally finite set.**  Let
`B` be locally finite in compacta, `a ∈ interior N` and `a ∉ B`.  Then there is a chart ball with
centre `a` which lies in `interior N`, is a neighbourhood of `a`, and is disjoint from `B`.

The chart ball is `homeoBall (chartAt a) (φ a) ρ'`, with `ρ'` smaller than both a radius keeping the
closed ball inside the chart target and a radius keeping its `φ.symm`-image inside `interior N`,
and below the distance of `φ a` to `φ '' (B ∩ homeoBall (chartAt a) (φ a) ρ)`, a finite set not
containing `φ a`. -/
theorem exists_chartBall_interior_avoiding_B {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {N B : Set M} (hBfin : ∀ K' : Set M, IsCompact K' → (B ∩ K').Finite)
    {a : M} (haN : a ∈ interior N) (haB : a ∉ B) :
    ∃ (c : EuclideanSpace ℝ (Fin n)) (r : ℝ),
      closedBall c r ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) a).target ∧
      a ∈ interior (homeoBall (chartAt (EuclideanSpace ℝ (Fin n)) a) c r) ∧
      homeoBall (chartAt (EuclideanSpace ℝ (Fin n)) a) c r ⊆ interior N ∧
      Disjoint (homeoBall (chartAt (EuclideanSpace ℝ (Fin n)) a) c r) B := by
  classical
  set φ := chartAt (EuclideanSpace ℝ (Fin n)) a with hφ
  have hasrc : a ∈ φ.source := mem_chart_source _ a
  have hatgt : φ a ∈ φ.target := φ.map_source hasrc
  -- a radius keeping the closed ball inside the chart target
  obtain ⟨ε₁, hε₁pos, hε₁⟩ := Metric.mem_nhds_iff.mp (φ.open_target.mem_nhds hatgt)
  -- a radius keeping the `φ.symm`-image inside `interior N`
  have hnhds : φ.symm ⁻¹' interior N ∈ 𝓝 (φ a) :=
    (φ.continuousAt_symm hatgt).preimage_mem_nhds
      (isOpen_interior.mem_nhds (by rw [φ.left_inv hasrc]; exact haN))
  obtain ⟨ε₂, hε₂pos, hε₂⟩ := Metric.mem_nhds_iff.mp hnhds
  set ρ := min ε₁ ε₂ / 2 with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; exact half_pos (lt_min hε₁pos hε₂pos)
  have hρ1 : ρ < ε₁ := by rw [hρdef]; have := min_le_left ε₁ ε₂; linarith
  have hρ2 : ρ < ε₂ := by rw [hρdef]; have := min_le_right ε₁ ε₂; linarith
  have htgtρ : closedBall (φ a) ρ ⊆ φ.target :=
    fun z hz => hε₁ (closedBall_subset_ball hρ1 hz)
  have himgN : φ.symm '' closedBall (φ a) ρ ⊆ interior N := by
    rintro _ ⟨z, hz, rfl⟩
    exact hε₂ (closedBall_subset_ball hρ2 hz)
  -- the `B`-points met by this ball, in chart coordinates: finite, and avoiding `φ a`
  have hKfin : (B ∩ homeoBall φ (φ a) ρ).Finite := hBfin _ (isCompact_homeoBall htgtρ)
  set Y := φ '' (B ∩ homeoBall φ (φ a) ρ) with hYdef
  have hYfin : Y.Finite := hKfin.image φ
  have hya : φ a ∉ Y := by
    rintro ⟨z, hz, hzφ⟩
    have hzsrc : z ∈ φ.source := by
      obtain ⟨w, hw, rfl⟩ := hz.2
      exact φ.map_target (htgtρ hw)
    have hza : z = a := by rw [← φ.left_inv hzsrc, hzφ, φ.left_inv hasrc]
    exact haB (hza ▸ hz.1)
  obtain ⟨ρ', hρ'pos, hρ'le, hρ'disj⟩ := exists_radius_closedBall_inter_empty hYfin hya hρpos
  have htgtρ' : closedBall (φ a) ρ' ⊆ φ.target :=
    fun z hz => htgtρ (closedBall_subset_closedBall hρ'le hz)
  refine ⟨φ a, ρ', htgtρ', ?_, ?_, ?_⟩
  · -- `a` is an interior point of the chart ball
    refine interior_maximal (image_mono ball_subset_closedBall) (isOpen_symm_image_ball htgtρ') ?_
    exact ⟨φ a, mem_ball_self hρ'pos, φ.left_inv hasrc⟩
  · -- the chart ball stays inside `interior N`
    exact subset_trans (image_mono (closedBall_subset_closedBall hρ'le)) himgN
  · -- the chart ball misses `B`
    rw [Set.disjoint_left]
    rintro z hz hzB
    obtain ⟨w, hw, rfl⟩ := hz
    have hwtgt : w ∈ φ.target := htgtρ (closedBall_subset_closedBall hρ'le hw)
    have hzY : w ∈ Y := by
      refine ⟨φ.symm w, ⟨hzB, ⟨w, closedBall_subset_closedBall hρ'le hw, rfl⟩⟩, ?_⟩
      exact φ.right_inv hwtgt
    have : w ∈ closedBall (φ a) ρ' ∩ Y := ⟨hw, hzY⟩
    rw [hρ'disj] at this
    exact this

/-- **A compact set is contained in a compact finite union of chart balls which lies inside a
prescribed open set and avoids a locally finite set.**  This is the form of the lemma used by the
flat-refinement argument. -/
theorem chartBall_union_between {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M]
    {A N : Set M} (hA : IsCompact A) (hAN : A ⊆ interior N)
    {B : Set M} (hAfinB : ∀ K' : Set M, IsCompact K' → (B ∩ K').Finite)
    (hAB : ∀ b : M, b ∈ B → b ∈ interior N → b ∉ A) :
    ∃ S : Set M, IsCompact S ∧ A ⊆ S ∧ S ⊆ interior N ∧
      Work.Noncompact.CompressionTube.IsChartBallUnion n M S ∧
      ∀ b : M, b ∈ B → b ∈ interior N → b ∉ S := by
  classical
  -- a chart ball around every point of `A`, inside `interior N` and avoiding `B`
  have hpt : ∀ a : {a : M // a ∈ A}, ∃ (c : EuclideanSpace ℝ (Fin n)) (r : ℝ),
      closedBall c r ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) a.1).target ∧
      a.1 ∈ interior (homeoBall (chartAt (EuclideanSpace ℝ (Fin n)) a.1) c r) ∧
      homeoBall (chartAt (EuclideanSpace ℝ (Fin n)) a.1) c r ⊆ interior N ∧
      Disjoint (homeoBall (chartAt (EuclideanSpace ℝ (Fin n)) a.1) c r) B := by
    intro a
    refine exists_chartBall_interior_avoiding_B hAfinB (hAN a.2) ?_
    intro hb
    exact hAB a.1 hb (hAN a.2) a.2
  choose c r hc using hpt
  let F : {a : M // a ∈ A} → Set M := fun a => chartBall a.1 (c a) (r a)
  let U : {a : M // a ∈ A} → Set M := fun a => interior (F a)
  have hUo : ∀ a, IsOpen (U a) := fun a => isOpen_interior
  have hcover : A ⊆ ⋃ a, U a := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, (hc ⟨x, hx⟩).2.1⟩
  -- finitely many of the open chart balls cover `A`
  obtain ⟨t, ht⟩ := hA.elim_finite_subcover U hUo hcover
  have hFc : ∀ a, IsCompact (F a) := fun a => isCompact_homeoBall (hc a).1
  have hFN : ∀ a, F a ⊆ interior N := fun a => (hc a).2.2.1
  have hFB : ∀ a, Disjoint (F a) B := fun a => (hc a).2.2.2
  refine ⟨⋃ a ∈ (t : Set {a : M // a ∈ A}), F a, ?_, ?_, ?_, ?_, ?_⟩
  · -- compact
    exact t.finite_toSet.isCompact_biUnion (fun a _ => hFc a)
  · -- `A ⊆ S`
    intro x hx
    have hxt := ht hx
    simp only [Set.mem_iUnion, exists_prop] at hxt
    obtain ⟨a, hat, hxa⟩ := hxt
    exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨Finset.mem_coe.mpr hat, interior_subset hxa⟩⟩
  · -- `S ⊆ interior N`
    intro x hx
    simp only [Set.mem_iUnion, exists_prop] at hx
    obtain ⟨a, -, hxa⟩ := hx
    exact hFN a hxa
  · -- `S` is a finite union of chart balls
    let I := {a : {a : M // a ∈ A} // a ∈ t}
    haveI : Fintype I := inferInstance
    let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
    refine ⟨Fin (Fintype.card I), inferInstance, fun i => (e.symm i).1.1,
      fun i => c (e.symm i).1, fun i => r (e.symm i).1, ?_, ?_⟩
    · intro i
      exact (hc (e.symm i).1).1
    · apply le_antisymm
      · intro y hy
        simp only [Set.mem_iUnion, exists_prop, Finset.mem_coe] at hy
        obtain ⟨a, ha, hya⟩ := hy
        refine Set.mem_iUnion.mpr ⟨e ⟨a, ha⟩, ?_⟩
        have he : e.symm (e ⟨a, ha⟩) = ⟨a, ha⟩ := Equiv.symm_apply_apply e _
        show y ∈ F (e.symm (e ⟨a, ha⟩)).1
        rw [he]
        exact hya
      · intro y hy
        simp only [Set.mem_iUnion] at hy
        obtain ⟨i, hi⟩ := hy
        exact Set.mem_iUnion.mpr ⟨(e.symm i).1,
          Set.mem_iUnion.mpr ⟨Finset.mem_coe.mpr (e.symm i).2, hi⟩⟩
  · -- `S` misses `B`
    intro b hbB _ hbS
    simp only [Set.mem_iUnion, exists_prop] at hbS
    obtain ⟨a, -, hba⟩ := hbS
    exact Set.disjoint_left.mp (hFB a) hba hbB

end Work.Noncompact.CompressionTube
