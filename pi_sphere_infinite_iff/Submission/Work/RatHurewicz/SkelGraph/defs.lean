import Mathlib
import Submission.Work.RatHurewicz.cycleModelDefs
import Submission.Work.RatHurewicz.finiteGraphDefs

/-!
# The `1`-skeleton of the cycle model as a finite graph

The model `Work.RatHurewicz.Model D` of a cycle is the quotient of a finite disjoint union of
copies of `Δ^{n+2}` and of unit intervals (`Work.RatHurewicz.Raw`) by the gluing relation
`Work.RatHurewicz.modelRel`.  Its `1`-skeleton (`Work.RatHurewicz.skeleton`) consists of the
points of a copy that lie in a cell of dimension at most `1`, and of all points of the arcs.

This file sets up the combinatorial data of that `1`-skeleton: its vertices (the vertices of the
copies and the end points of the arcs, modulo the gluing) and its edges (the `1`-faces of the
copies and the arcs, modulo the gluing), the parametrisation of an edge, and the map from the
abstract finite graph `Work.RatHurewicz.GraphX a b` to the skeleton.
-/

namespace Work.RatHurewicz.SkelGraph

open scoped Topology unitInterval

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}


/-! ## The quotient of a discrete space is discrete -/

theorem discreteTopology_quotient {α : Type*} [TopologicalSpace α] [DiscreteTopology α]
    (s : Setoid α) : DiscreteTopology (Quotient s) := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro q
  rw [← (isQuotientMap_quotient_mk' (s := s)).isCoinducing.isOpen_preimage]
  exact isOpen_discrete _

/-! ## The points of a one-dimensional face of the standard simplex -/

/-- The point of `Δ¹` with barycentric coordinates `(1-s, s)`. -/
def segPt (s : I) : stdSimplex ℝ (Fin 2) :=
  ⟨fun i : Fin 2 => if i = (0 : Fin 2) then 1 - (s : ℝ) else (s : ℝ), by
    refine ⟨fun i => ?_, ?_⟩
    · by_cases h : i = (0 : Fin 2)
      · simp only [h, if_pos]; linarith [s.2.2]
      · simp only [h, if_neg, not_false_iff]; exact s.2.1
    · rw [Fin.sum_univ_two]
      simp⟩

theorem segPt_apply_zero (s : I) : (segPt s : Fin 2 → ℝ) 0 = 1 - (s : ℝ) := by
  show (if (0 : Fin 2) = 0 then 1 - (s : ℝ) else (s : ℝ)) = 1 - (s : ℝ)
  simp

theorem segPt_apply_one (s : I) : (segPt s : Fin 2 → ℝ) 1 = (s : ℝ) := by
  show (if (1 : Fin 2) = 0 then 1 - (s : ℝ) else (s : ℝ)) = (s : ℝ)
  simp

theorem continuous_segPt : Continuous (segPt : I → stdSimplex ℝ (Fin 2)) := by
  apply Continuous.subtype_mk
  show Continuous (fun s : I => fun i : Fin 2 => if i = 0 then 1 - (s : ℝ) else (s : ℝ))
  refine continuous_pi (fun i => ?_)
  by_cases h : i = (0 : Fin 2)
  · simp only [h, if_pos]; fun_prop
  · simp only [h, if_neg, not_false_iff]; fun_prop

/-- The point of `Δ(ι)` with barycentric coordinates `1-s` at `p`, `s` at `q` and `0` at every
other index. -/
def sdPt {ι : Type*} [Fintype ι] (p q : ι) (s : I) : stdSimplex ℝ ι :=
  stdSimplex.map (fun i : Fin 2 => if i = (0 : Fin 2) then p else q) (segPt s)

theorem sdPt_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (p q : ι) (s : I) (j : ι) :
    (sdPt p q s : ι → ℝ) j
      = (if j = p then 1 - (s : ℝ) else 0) + (if j = q then (s : ℝ) else 0) := by
  classical
  rw [sdPt, stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply, Finset.sum_filter,
    Fin.sum_univ_two]
  simp only [Finset.mem_univ, ↓reduceIte, Fin.isValue,
    show (if (1 : Fin 2) = 0 then p else q) = q from if_neg (by decide),
    segPt_apply_zero, segPt_apply_one]
  by_cases hp : j = p <;> by_cases hq : j = q <;> simp_all [eq_comm]

theorem sdPt_apply_left {ι : Type*} [Fintype ι] [DecidableEq ι] {p q : ι} (hpq : p ≠ q) (s : I) :
    (sdPt p q s : ι → ℝ) p = 1 - (s : ℝ) := by
  rw [sdPt_apply]
  simp [hpq, hpq.symm]

theorem sdPt_apply_right {ι : Type*} [Fintype ι] [DecidableEq ι] {p q : ι} (hpq : p ≠ q)
    (s : I) : (sdPt p q s : ι → ℝ) q = (s : ℝ) := by
  rw [sdPt_apply]
  simp [hpq, hpq.symm]

theorem sdPt_apply_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {p q j : ι} (hpq : p ≠ q)
    (s : I) (hjp : j ≠ p) (hjq : j ≠ q) : (sdPt p q s : ι → ℝ) j = 0 := by
  rw [sdPt_apply]
  simp [hjp, hjq]

theorem sdPt_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (p q : ι) :
    sdPt p q (0 : I) = stdSimplex.vertex p := by
  rw [sdPt]
  rw [show segPt (0 : I) = stdSimplex.vertex (0 : Fin 2) from by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [segPt]]
  rw [stdSimplex.map_vertex]
  simp

theorem sdPt_one {ι : Type*} [Fintype ι] [DecidableEq ι] (p q : ι) :
    sdPt p q (1 : I) = stdSimplex.vertex q := by
  rw [sdPt]
  rw [show segPt (1 : I) = stdSimplex.vertex (1 : Fin 2) from by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [segPt]]
  rw [stdSimplex.map_vertex]
  simp

theorem continuous_sdPt {ι : Type*} [Fintype ι] (p q : ι) :
    Continuous (fun s : I => sdPt p q s) :=
  (stdSimplex.continuous_map (fun i : Fin 2 => if i = (0 : Fin 2) then p else q)).comp
    continuous_segPt

/-- The face map `facept` of the standard simplex, computed on the points `sdPt`: this is the
compatibility of the parametrisations of a `1`-face with the gluing relation of the model. -/
theorem facept_sdPt {m : ℕ} (r : Fin (m + 2)) (u v : Fin (m + 1)) (s : I) :
    facept (m + 1) r (sdPt u v s) = sdPt (r.succAbove u) (r.succAbove v) s := by
  show stdSimplex.map r.succAbove (sdPt u v s) = _
  rw [sdPt, stdSimplex.map_comp_apply]
  congr 1
  funext i
  fin_cases i <;> simp

/-! ## The raw vertex data -/

/-- The end point of an arc, as a point of the unit interval. -/
def arcEnd (k : Fin 2) : I := ⟨(k : ℝ), by fin_cases k <;> norm_num⟩

@[simp] theorem arcEnd_zero : arcEnd (0 : Fin 2) = 0 := by
  apply Subtype.ext; simp [arcEnd]

@[simp] theorem arcEnd_one : arcEnd (1 : Fin 2) = 1 := by
  apply Subtype.ext; simp [arcEnd]

/-- The raw vertex data of the model: a vertex of one of the copies of `Δ^{n+2}`, or an end point
of one of the arcs. -/
abbrev VertRaw (D : MData X n x₀) : Type _ :=
  (Σ _ : D.Idx, Fin (n + 2)) ⊕ (Σ _ : D.Idx, Fin 2)

instance instFintypeVertRaw (D : MData X n x₀) : Fintype (VertRaw D) := inferInstance

instance instDiscreteVertRaw (D : MData X n x₀) : DiscreteTopology (VertRaw D) := inferInstance

/-- The point of `Raw D` attached to a raw vertex. -/
def vertPt (D : MData X n x₀) : VertRaw D → Raw D
  | Sum.inl ⟨i, p⟩ => Sum.inl ⟨i, stdSimplex.vertex p⟩
  | Sum.inr ⟨i, k⟩ => Sum.inr ⟨i, arcEnd k⟩

/-- The point of the model attached to a raw vertex. -/
def vertM (D : MData X n x₀) (v : VertRaw D) : Model D := Quotient.mk'' (vertPt D v)

theorem isLowDim_vertPt (D : MData X n x₀) (v : VertRaw D) : isLowDim D (vertPt D v) := by
  rcases v with ⟨i, p⟩ | ⟨i, k⟩
  · show (Finset.univ.filter
      (fun j : Fin (n + 2) => (stdSimplex.vertex p : Fin (n + 2) → ℝ) j ≠ 0)).card ≤ 2
    have hsub : Finset.univ.filter
        (fun j : Fin (n + 2) => (stdSimplex.vertex p : Fin (n + 2) → ℝ) j ≠ 0) ⊆ {p} := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] at hj ⊢
      by_contra h
      exact hj (by
        rw [stdSimplex.vertex_coe, Pi.single_eq_of_ne (M := fun _ => ℝ) h (1 : ℝ)])
    calc (Finset.univ.filter
            (fun j : Fin (n + 2) => (stdSimplex.vertex p : Fin (n + 2) → ℝ) j ≠ 0)).card
        ≤ ({p} : Finset (Fin (n + 2))).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton p
      _ ≤ 2 := by norm_num
  · trivial

theorem mem_skeleton_vertM (D : MData X n x₀) (v : VertRaw D) : vertM D v ∈ skeleton D :=
  ⟨vertPt D v, rfl, isLowDim_vertPt D v⟩

/-- The vertices of the `1`-skeleton: the raw vertices modulo the gluing. -/
abbrev V (D : MData X n x₀) : Type _ := Quotient (Setoid.ker (vertM D))

instance instFintypeV (D : MData X n x₀) : Fintype (V D) :=
  @Quotient.fintype (VertRaw D) _ (Setoid.ker (vertM D)) (fun _ _ => Classical.dec _)

instance instDiscreteV (D : MData X n x₀) : DiscreteTopology (V D) :=
  discreteTopology_quotient (Setoid.ker (vertM D))

/-- The class of a raw vertex. -/
def vCl (D : MData X n x₀) (v : VertRaw D) : V D := Quotient.mk'' v

theorem vCl_eq_of_vertM_eq (D : MData X n x₀) {v w : VertRaw D} (h : vertM D v = vertM D w) :
    vCl D v = vCl D w := Quotient.sound h

/-! ## The raw edge data -/

/-- The raw edge data of the model: a `1`-face (an unordered pair of distinct vertices) of one of
the copies of `Δ^{n+2}`, or one of the arcs. -/
abbrev EdgeRaw (D : MData X n x₀) : Type _ :=
  (Σ _ : D.Idx, {pq : Fin (n + 2) × Fin (n + 2) // pq.1 < pq.2}) ⊕ (Σ _ : D.Idx, PUnit)

instance instFintypeEdgeRaw (D : MData X n x₀) : Fintype (EdgeRaw D) := inferInstance

instance instDiscreteEdgeRaw (D : MData X n x₀) : DiscreteTopology (EdgeRaw D) := inferInstance

/-- The point of `Raw D` at the parameter `s` of a raw edge. -/
def edgePt (D : MData X n x₀) : EdgeRaw D → I → Raw D
  | Sum.inl ⟨i, ⟨⟨p, q⟩, _⟩⟩, s => Sum.inl ⟨i, sdPt p q s⟩
  | Sum.inr ⟨i, _⟩, s => Sum.inr ⟨i, s⟩

/-- The point of the model at the parameter `s` of a raw edge. -/
def edgeM (D : MData X n x₀) (e : EdgeRaw D) (s : I) : Model D := Quotient.mk'' (edgePt D e s)

theorem isLowDim_edgePt (D : MData X n x₀) (e : EdgeRaw D) (s : I) :
    isLowDim D (edgePt D e s) := by
  rcases e with ⟨i, ⟨⟨p, q⟩, hpq⟩⟩ | ⟨i, u⟩
  · show (Finset.univ.filter
      (fun j : Fin (n + 2) => (sdPt p q s : Fin (n + 2) → ℝ) j ≠ 0)).card ≤ 2
    have hsub : (Finset.univ.filter
        (fun j : Fin (n + 2) => (sdPt p q s : Fin (n + 2) → ℝ) j ≠ 0)) ⊆ {p, q} := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton] at hj ⊢
      by_contra h
      push_neg at h
      exact hj (sdPt_apply_eq_zero (ne_of_lt hpq) s h.1 h.2)
    calc (Finset.univ.filter
            (fun j : Fin (n + 2) => (sdPt p q s : Fin (n + 2) → ℝ) j ≠ 0)).card
        ≤ ({p, q} : Finset (Fin (n + 2))).card := Finset.card_le_card hsub
      _ ≤ 2 := by
        have h := Finset.card_insert_le p ({q} : Finset (Fin (n + 2)))
        simp only [Finset.card_singleton] at h
        exact le_trans h (by norm_num)
  · trivial

theorem mem_skeleton_edgeM (D : MData X n x₀) (e : EdgeRaw D) (s : I) :
    edgeM D e s ∈ skeleton D :=
  ⟨edgePt D e s, rfl, isLowDim_edgePt D e s⟩

theorem edgeM_zero_simplex (D : MData X n x₀) (i : D.Idx) (p q : Fin (n + 2)) (hpq : p < q) :
    edgeM D (Sum.inl ⟨i, ⟨⟨p, q⟩, hpq⟩⟩) 0 = vertM D (Sum.inl ⟨i, p⟩) := by
  show Quotient.mk'' (edgePt D (Sum.inl ⟨i, ⟨⟨p, q⟩, hpq⟩⟩) 0) = vertM D (Sum.inl ⟨i, p⟩)
  rw [show edgePt D (Sum.inl ⟨i, ⟨⟨p, q⟩, hpq⟩⟩) 0 = vertPt D (Sum.inl ⟨i, p⟩) from by
    show (Sum.inl ⟨i, sdPt p q 0⟩ : Raw D) = Sum.inl ⟨i, stdSimplex.vertex p⟩
    rw [sdPt_zero]]
  rfl

theorem edgeM_one_simplex (D : MData X n x₀) (i : D.Idx) (p q : Fin (n + 2)) (hpq : p < q) :
    edgeM D (Sum.inl ⟨i, ⟨⟨p, q⟩, hpq⟩⟩) 1 = vertM D (Sum.inl ⟨i, q⟩) := by
  show Quotient.mk'' (edgePt D (Sum.inl ⟨i, ⟨⟨p, q⟩, hpq⟩⟩) 1) = vertM D (Sum.inl ⟨i, q⟩)
  rw [show edgePt D (Sum.inl ⟨i, ⟨⟨p, q⟩, hpq⟩⟩) 1 = vertPt D (Sum.inl ⟨i, q⟩) from by
    show (Sum.inl ⟨i, sdPt p q 1⟩ : Raw D) = Sum.inl ⟨i, stdSimplex.vertex q⟩
    rw [sdPt_one]]
  rfl

theorem edgeM_zero_arc (D : MData X n x₀) (i : D.Idx) (u : PUnit) :
    edgeM D (Sum.inr ⟨i, u⟩) 0 = vertM D (Sum.inr ⟨i, 0⟩) := by
  show Quotient.mk'' (edgePt D (Sum.inr ⟨i, u⟩) 0) = vertM D (Sum.inr ⟨i, 0⟩)
  rw [show edgePt D (Sum.inr ⟨i, u⟩) 0 = vertPt D (Sum.inr ⟨i, 0⟩) from by
    show (Sum.inr ⟨i, (0 : I)⟩ : Raw D) = Sum.inr ⟨i, arcEnd 0⟩
    rw [arcEnd_zero]]
  rfl

theorem edgeM_one_arc (D : MData X n x₀) (i : D.Idx) (u : PUnit) :
    edgeM D (Sum.inr ⟨i, u⟩) 1 = vertM D (Sum.inr ⟨i, 1⟩) := by
  show Quotient.mk'' (edgePt D (Sum.inr ⟨i, u⟩) 1) = vertM D (Sum.inr ⟨i, 1⟩)
  rw [show edgePt D (Sum.inr ⟨i, u⟩) 1 = vertPt D (Sum.inr ⟨i, 1⟩) from by
    show (Sum.inr ⟨i, (1 : I)⟩ : Raw D) = Sum.inr ⟨i, arcEnd 1⟩
    rw [arcEnd_one]]
  rfl

/-- The setoid whose quotient is the set of edges of the `1`-skeleton: two raw edges are
identified when they have the same parametrised image in the model. -/
def edgeSetoid (D : MData X n x₀) : Setoid (EdgeRaw D) where
  r e f := ∀ s : I, edgeM D e s = edgeM D f s
  iseqv := ⟨fun _ _ => rfl, fun h s => (h s).symm, fun h₁ h₂ s => (h₁ s).trans (h₂ s)⟩

/-- The edges of the `1`-skeleton: the raw edges modulo the gluing. -/
abbrev E (D : MData X n x₀) : Type _ := Quotient (edgeSetoid D)

instance instFintypeE (D : MData X n x₀) : Fintype (E D) :=
  @Quotient.fintype (EdgeRaw D) _ (edgeSetoid D) (fun _ _ => Classical.dec _)

instance instDiscreteE (D : MData X n x₀) : DiscreteTopology (E D) :=
  discreteTopology_quotient (edgeSetoid D)

/-- The class of a raw edge. -/
def eCl (D : MData X n x₀) (e : EdgeRaw D) : E D := Quotient.mk'' e

/-! ## The end point maps of the graph -/

/-- The initial vertex of a raw edge. -/
def aRaw (D : MData X n x₀) : EdgeRaw D → V D
  | Sum.inl ⟨i, ⟨(p, _q), _⟩⟩ => vCl D (Sum.inl ⟨i, p⟩)
  | Sum.inr ⟨i, _⟩ => vCl D (Sum.inr ⟨i, 0⟩)

/-- The terminal vertex of a raw edge. -/
def bRaw (D : MData X n x₀) : EdgeRaw D → V D
  | Sum.inl ⟨i, ⟨(_p, q), _⟩⟩ => vCl D (Sum.inl ⟨i, q⟩)
  | Sum.inr ⟨i, _⟩ => vCl D (Sum.inr ⟨i, 1⟩)

theorem aRaw_eq_of_edgeM_eq (D : MData X n x₀) {e f : EdgeRaw D}
    (h : ∀ s : I, edgeM D e s = edgeM D f s) : aRaw D e = aRaw D f := by
  obtain ⟨i, ⟨⟨p, q⟩, hpq⟩⟩ | ⟨i, u⟩ := e
  · obtain ⟨j, ⟨⟨p', q'⟩, hp'q'⟩⟩ | ⟨j, u'⟩ := f
    · show vCl D (Sum.inl ⟨i, p⟩) = vCl D (Sum.inl ⟨j, p'⟩)
      exact vCl_eq_of_vertM_eq D (by
        rw [← edgeM_zero_simplex D i p q hpq, ← edgeM_zero_simplex D j p' q' hp'q']
        exact h 0)
    · show vCl D (Sum.inl ⟨i, p⟩) = vCl D (Sum.inr ⟨j, 0⟩)
      exact vCl_eq_of_vertM_eq D (by
        rw [← edgeM_zero_simplex D i p q hpq, ← edgeM_zero_arc D j u']
        exact h 0)
  · obtain ⟨j, ⟨⟨p', q'⟩, hp'q'⟩⟩ | ⟨j, u'⟩ := f
    · show vCl D (Sum.inr ⟨i, 0⟩) = vCl D (Sum.inl ⟨j, p'⟩)
      exact vCl_eq_of_vertM_eq D (by
        rw [← edgeM_zero_arc D i u, ← edgeM_zero_simplex D j p' q' hp'q']
        exact h 0)
    · show vCl D (Sum.inr ⟨i, 0⟩) = vCl D (Sum.inr ⟨j, 0⟩)
      exact vCl_eq_of_vertM_eq D (by
        rw [← edgeM_zero_arc D i u, ← edgeM_zero_arc D j u']
        exact h 0)

theorem bRaw_eq_of_edgeM_eq (D : MData X n x₀) {e f : EdgeRaw D}
    (h : ∀ s : I, edgeM D e s = edgeM D f s) : bRaw D e = bRaw D f := by
  obtain ⟨i, ⟨⟨p, q⟩, hpq⟩⟩ | ⟨i, u⟩ := e
  · obtain ⟨j, ⟨⟨p', q'⟩, hp'q'⟩⟩ | ⟨j, u'⟩ := f
    · show vCl D (Sum.inl ⟨i, q⟩) = vCl D (Sum.inl ⟨j, q'⟩)
      exact vCl_eq_of_vertM_eq D (by
        rw [← edgeM_one_simplex D i p q hpq, ← edgeM_one_simplex D j p' q' hp'q']
        exact h 1)
    · show vCl D (Sum.inl ⟨i, q⟩) = vCl D (Sum.inr ⟨j, 1⟩)
      exact vCl_eq_of_vertM_eq D (by
        rw [← edgeM_one_simplex D i p q hpq, ← edgeM_one_arc D j u']
        exact h 1)
  · obtain ⟨j, ⟨⟨p', q'⟩, hp'q'⟩⟩ | ⟨j, u'⟩ := f
    · show vCl D (Sum.inr ⟨i, 1⟩) = vCl D (Sum.inl ⟨j, q'⟩)
      exact vCl_eq_of_vertM_eq D (by
        rw [← edgeM_one_arc D i u, ← edgeM_one_simplex D j p' q' hp'q']
        exact h 1)
    · show vCl D (Sum.inr ⟨i, 1⟩) = vCl D (Sum.inr ⟨j, 1⟩)
      exact vCl_eq_of_vertM_eq D (by
        rw [← edgeM_one_arc D i u, ← edgeM_one_arc D j u']
        exact h 1)

/-- The initial vertex map of the graph of the `1`-skeleton. -/
def a (D : MData X n x₀) : E D → V D :=
  Quotient.lift (aRaw D) (fun _ _ h => aRaw_eq_of_edgeM_eq D h)

/-- The terminal vertex map of the graph of the `1`-skeleton. -/
def b (D : MData X n x₀) : E D → V D :=
  Quotient.lift (bRaw D) (fun _ _ h => bRaw_eq_of_edgeM_eq D h)

/-! ## The map from the abstract graph to the skeleton -/

/-- The point of the `1`-skeleton attached to a vertex class. -/
def vertSk (D : MData X n x₀) (v : V D) : ↥(skeleton D) :=
  Quotient.liftOn v (fun r => ⟨vertM D r, mem_skeleton_vertM D r⟩) (fun _ _ h => Subtype.ext h)

/-- The continuous parametrisation of a raw edge. -/
def edgeContinuous (D : MData X n x₀) (e : EdgeRaw D) : C(I, ↥(skeleton D)) where
  toFun s := ⟨edgeM D e s, mem_skeleton_edgeM D e s⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    rcases e with ⟨i, ⟨⟨p, q⟩, hpq⟩⟩ | ⟨i, u⟩
    · show Continuous fun s : I => (Quotient.mk'' (Sum.inl ⟨i, sdPt p q s⟩) : Model D)
      exact continuous_quotient_mk'.comp
        (continuous_inl.comp (continuous_sigmaMk.comp (continuous_sdPt p q)))
    · show Continuous fun s : I => (Quotient.mk'' (Sum.inr ⟨i, s⟩) : Model D)
      exact continuous_quotient_mk'.comp
        (continuous_inr.comp (continuous_sigmaMk.comp continuous_id))

/-- The parametrisation of an edge of the graph, as a continuous path in the skeleton. -/
def edgeParam (D : MData X n x₀) : E D → C(I, ↥(skeleton D)) :=
  Quotient.lift (edgeContinuous D) (fun _ _ h => ContinuousMap.ext (fun s => Subtype.ext (h s)))

/-- The map from the raw graph `V ⊕ (E × I)` to the `1`-skeleton. -/
def psi (D : MData X n x₀) : V D ⊕ (E D × I) → ↥(skeleton D)
  | Sum.inl v => vertSk D v
  | Sum.inr p => edgeParam D p.1 p.2

theorem continuous_edgeParam_uncurry (D : MData X n x₀) :
    Continuous (fun p : E D × I => edgeParam D p.1 p.2) := by
  rw [continuous_def]
  intro U hU
  rw [isOpen_iff_mem_nhds]
  rintro ⟨e, s⟩ hs
  have h2 : (edgeParam D e) ⁻¹' U ∈ 𝓝 s :=
    ((edgeParam D e).continuous.continuousAt).preimage_mem_nhds (hU.mem_nhds hs)
  have h1 : ({e} : Set (E D)) ∈ 𝓝 e := (isOpen_discrete _).mem_nhds rfl
  refine Filter.mem_of_superset (prod_mem_nhds h1 h2) ?_
  rintro ⟨e', s'⟩ ⟨he, hs'⟩
  rw [Set.mem_singleton_iff] at he
  subst he
  exact hs'

theorem continuous_psi (D : MData X n x₀) : Continuous (psi D) := by
  rw [continuous_sum_dom]
  refine ⟨?_, ?_⟩
  · exact continuous_of_discreteTopology
  · exact continuous_edgeParam_uncurry D

end

end Work.RatHurewicz.SkelGraph
