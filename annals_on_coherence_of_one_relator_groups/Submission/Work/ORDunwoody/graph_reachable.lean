import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.Source
import Submission.Work.ORDunwoody.Foundations.Cayley

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORDunwoody

open Work.ORDunwoody.Dunwoody
open Work.ORDunwoody.Cayley

variable {G : Type u} [Group G] {V : Type u} [MulAction G V]
variable {T : GTree G V} {t₀ : V} {P : FinPresentation G}
variable {D : GeoData T t₀ P}

/-! ## The 1-skeleton `Λ''` is connected

The target `graph_reachable` is the statement that the 1-skeleton of the subdivided Cayley
complex `Λ''` (the graph `Dunwoody.graph` on `Dunwoody.Vertex D`) is connected: any two vertices
are joined by a walk.

The proof proceeds by showing that every vertex is reachable from the base vertex
`Sum.inl (1, Sum.inl ())`:

* a *generator edge* gives a path from `(c, ∗)` to `(c * genE (j,true), ∗)` (through the chain of
  cells `pos 0, pos 1, …, pos L` when `L > 0`, and through the collapsed edge `Step.plain` when
  `L = 0`);
* since the generators generate `G`, the set of `c` for which `(c, ∗)` is reachable from the base
  vertex is a subgroup containing all generators, hence is everything;
* every old vertex and every pattern point is at the end of a cell chain based at some `(c, ∗)`. -/

/-- An elementary step of `Λ''` yields a walk. -/
theorem stepRel_reachable {v w : Vertex D} (h : StepRel v w) :
    (graph (D := D)).Reachable v w := by
  by_cases hvw : v = w
  · subst hvw; exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable
      ((graph_adj_iff (D := D) (v := v) (w := w)).2 ⟨hvw, Or.inl h⟩)

/-- The two halves of a cell give a walk from the cell's source to its target. -/
theorem cell_reachable (e : Cell D) :
    (graph (D := D)).Reachable (Sum.inl e.src : Vertex D) (Sum.inl e.tgt : Vertex D) := by
  have h1 : StepRel (Sum.inl e.src : Vertex D) (Sum.inr e.mid : Vertex D) :=
    Or.inl ⟨e, Or.inl ⟨rfl, rfl⟩⟩
  have h2 : StepRel (Sum.inr e.mid : Vertex D) (Sum.inl e.tgt : Vertex D) :=
    Or.inl ⟨e, Or.inr ⟨rfl, rfl⟩⟩
  exact (stepRel_reachable h1).trans (stepRel_reachable h2)

/-- The pattern point of a cell is reachable from the cell's source. -/
theorem mid_reachable (e : Cell D) :
    (graph (D := D)).Reachable (Sum.inl e.src : Vertex D) (Sum.inr e.mid : Vertex D) :=
  stepRel_reachable (Or.inl ⟨e, Or.inl ⟨rfl, rfl⟩⟩)

/-- Along the generator edge `(j,true)` based at `c`, the vertices `pos 0, …, pos m` are joined
by a walk, for every `m ≤ L (j,true)`. -/
theorem pos_reachable_le (c : G) (j : Fin P.n) :
    ∀ m : ℕ, m ≤ D.L (j, true) →
      (graph (D := D)).Reachable (Sum.inl (pos D c j 0) : Vertex D)
        (Sum.inl (pos D c j m) : Vertex D) := by
  intro m
  induction m with
  | zero => intro _; exact SimpleGraph.Reachable.refl _
  | succ m ih =>
      intro hm
      have hm' : m ≤ D.L (j, true) := Nat.le_of_succ_le hm
      have hlt : m < D.L (j, true) := hm
      have hcell : (graph (D := D)).Reachable
          (Sum.inl (pos D c j m) : Vertex D) (Sum.inl (pos D c j (m + 1)) : Vertex D) :=
        cell_reachable (D := D) (⟨c, j, ⟨m, hlt⟩⟩ : Cell D)
      exact (ih hm').trans hcell

/-- The far endpoint of the generator edge `(j,true)` based at `c` (for a non-collapsed
generator: `L (j,true) > 0`). -/
theorem pos_last (c : G) (j : Fin P.n) (h : 0 < D.L (j, true)) :
    pos D c j (D.L (j, true)) = (c * CayV.genE P (j, true), Sum.inl ()) := by
  obtain ⟨i, hi⟩ : ∃ i, D.L (j, true) = i + 1 := ⟨D.L (j, true) - 1, by omega⟩
  rw [hi]
  exact pos_succ_of_not_lt D c j (by omega)

/-- The traversal of a generator edge `(j,true)` based at `c` yields a walk from `(c, ∗)` to
`(c * genE (j,true), ∗)`. -/
theorem gen_edge_reachable (c : G) (j : Fin P.n) :
    (graph (D := D)).Reachable (Sum.inl (c, Sum.inl ()) : Vertex D)
      (Sum.inl (c * CayV.genE P (j, true), Sum.inl ()) : Vertex D) := by
  rcases Nat.eq_zero_or_pos (D.L (j, true)) with hL | hL
  · have hstep : StepRel (Sum.inl (c, Sum.inl ()) : Vertex D)
        (Sum.inl (c * CayV.genE P (j, true), Sum.inl ()) : Vertex D) :=
      Or.inr ⟨c, j, hL, rfl, rfl⟩
    exact stepRel_reachable hstep
  · have h := pos_reachable_le (D := D) c j (D.L (j, true)) le_rfl
    have h0 : pos D c j 0 = (c, Sum.inl ()) := pos_zero D c j
    rw [h0, pos_last (D := D) c j hL] at h
    exact h

/-- Reachability is equivariant for the action of `G`. -/
theorem reachable_smul (g : G) {v w : Vertex D}
    (h : (graph (D := D)).Reachable v w) :
    (graph (D := D)).Reachable (g • v) (g • w) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj rest ih =>
      exact (SimpleGraph.Adj.reachable (graph_smul_adj (D := D) g hadj)).trans ih

/-- Every base vertex `(c, ∗)` is reachable from the base point `(1, ∗)`. -/
theorem base_reachable_all (c : G) :
    (graph (D := D)).Reachable (Sum.inl ((1 : G), Sum.inl ()) : Vertex D)
      (Sum.inl (c, Sum.inl ()) : Vertex D) := by
  let H : Subgroup G :=
    { carrier := {c | (graph (D := D)).Reachable
        (Sum.inl ((1 : G), Sum.inl ()) : Vertex D) (Sum.inl (c, Sum.inl ()) : Vertex D)}
      one_mem' := SimpleGraph.Reachable.refl _
      mul_mem' := by
        intro a b ha hb
        have hb' : (graph (D := D)).Reachable (Sum.inl (a, Sum.inl ()) : Vertex D)
            (Sum.inl (a * b, Sum.inl ()) : Vertex D) := by
          have h1 := reachable_smul (D := D) a hb
          simpa using h1
        exact ha.trans hb'
      inv_mem' := by
        intro a ha
        have h1 := reachable_smul (D := D) a⁻¹ ha
        have h1' : (graph (D := D)).Reachable (Sum.inl (a⁻¹, Sum.inl ()) : Vertex D)
            (Sum.inl ((1 : G), Sum.inl ()) : Vertex D) := by
          simpa using h1
        exact h1'.symm }
  have hrange : Set.range P.gen ⊆ (H : Set G) := by
    rintro x ⟨i, rfl⟩
    have h := gen_edge_reachable (D := D) (1 : G) i
    rw [one_mul] at h
    exact h
  have hle : (⊤ : Subgroup G) ≤ H := by
    have hc : Subgroup.closure (Set.range P.gen) ≤ H := (Subgroup.closure_le H).2 hrange
    rwa [FinPresentation.closure_gen] at hc
  exact hle (Subgroup.mem_top c)

/-- Every vertex of `Λ''` is reachable from the base point `(1, ∗)`. -/
theorem base_reachable (v : Vertex D) :
    (graph (D := D)).Reachable (Sum.inl ((1 : G), Sum.inl ()) : Vertex D) v := by
  cases v with
  | inl p =>
      obtain ⟨c, q⟩ := p
      have hc := base_reachable_all (D := D) c
      cases q with
      | inl u =>
          cases u
          exact hc
      | inr s =>
          obtain ⟨j, i⟩ := s
          have hi : (i : ℕ) + 1 < D.L (j, true) := by
            have := i.isLt; omega
          have hpos : (c, Sum.inr ⟨j, i⟩) = pos D c j ((i : ℕ) + 1) :=
            (pos_succ_of_lt D c j hi).symm
          have h1 := pos_reachable_le (D := D) c j ((i : ℕ) + 1) (le_of_lt hi)
          have h0 : pos D c j 0 = (c, Sum.inl ()) := pos_zero D c j
          rw [h0] at h1
          rw [← hpos] at h1
          exact hc.trans h1
  | inr p =>
      obtain ⟨c, jk⟩ := p
      obtain ⟨j, k⟩ := jk
      have hc := base_reachable_all (D := D) c
      have hk : (k : ℕ) ≤ D.L (j, true) := le_of_lt k.isLt
      have h1 := pos_reachable_le (D := D) c j (k : ℕ) hk
      have h0 : pos D c j 0 = (c, Sum.inl ()) := pos_zero D c j
      rw [h0] at h1
      have hcell : (graph (D := D)).Reachable (Sum.inl (pos D c j (k : ℕ)) : Vertex D)
          (Sum.inr (c, ⟨j, k⟩) : Vertex D) :=
        mid_reachable (D := D) (⟨c, j, k⟩ : Cell D)
      exact hc.trans (h1.trans hcell)

theorem graph_reachable {G : Type u} [Group G] {V : Type u} [MulAction G V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    (D : Work.ORDunwoody.Cayley.GeoData T t₀ P) (a b : Work.ORDunwoody.Dunwoody.Vertex D) :
    (Work.ORDunwoody.Dunwoody.graph (D := D)).Reachable a b := by
  exact (base_reachable a).symm.trans (base_reachable b)

end Work.ORDunwoody
