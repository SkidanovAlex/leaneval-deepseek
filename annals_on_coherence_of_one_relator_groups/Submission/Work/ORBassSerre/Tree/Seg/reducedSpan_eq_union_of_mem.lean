import Mathlib
import Submission.Work.ORBassSerre.Tree.IsTreeAPI

/-!
# Splitting a geodesic at a vertex lying on it

If `c` lies on the geodesic from `a` to `b` in a tree, then that geodesic splits at `c` into the
geodesic from `a` to `c` followed by the geodesic from `c` to `b`, and consequently
`reducedSpan a b = reducedSpan a c ∪ reducedSpan c b`.

The path-theoretic ingredients are recorded first: a vertex of one factor of a composite path is
a vertex of the composite, and a suffix of a reduced path is reduced.
-/

namespace Work.ORBassSerre.Tree.Seg

open Quiver

/-! ## Path bookkeeping -/

/-- A vertex of the first factor of a composite path is a vertex of the composite. -/
theorem mem_vertices_comp_left {V : Type*} [Quiver V] {a b c : V} {p : Quiver.Path a b}
    {q : Quiver.Path b c} {x : V} (h : x ∈ p.vertices) : x ∈ (p.comp q).vertices := by
  rw [Quiver.Path.vertices_comp, List.mem_append]
  rw [← Quiver.Path.dropLast_append_end_eq p, List.mem_append] at h
  rcases h with h | h
  · exact Or.inl h
  · right
    simp only [List.mem_singleton] at h
    subst h
    exact Quiver.Path.start_mem_vertices q

/-- A vertex of the second factor of a composite path is a vertex of the composite. -/
theorem mem_vertices_comp_right {V : Type*} [Quiver V] {a b c : V} {p : Quiver.Path a b}
    {q : Quiver.Path b c} {x : V} (h : x ∈ q.vertices) : x ∈ (p.comp q).vertices := by
  rw [Quiver.Path.vertices_comp, List.mem_append]
  exact Or.inr h

/-- A suffix of a reduced path is reduced. -/
theorem isReduced_of_comp_right {V : Type*} [Quiver V] [Quiver.HasReverse V] {a b c : V}
    {p : Quiver.Path a b} {q : Quiver.Path b c} (h : (p.comp q).IsReduced) : q.IsReduced :=
  fun r hr => h (p.comp r) (hr.comp_left p)

/-! ## The splitting of a geodesic at a point of it -/

/-- In a tree, the geodesic from `a` to `b` through the point `c` splits at `c` into the
geodesic from `a` to `c` followed by the geodesic from `c` to `b`. -/
theorem geodesic_eq_comp_geodesic_of_mem {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    {hT : Work.ORBassSerre.IsTree V} {a b c : V}
    (hc : c ∈ Work.ORBassSerre.reducedSpan a b) :
    ∃ (p₁ : Quiver.Path a c) (p₂ : Quiver.Path c b),
      hT.geodesic a b = p₁.comp p₂ ∧ p₁ = hT.geodesic a c ∧ p₂ = hT.geodesic c b := by
  classical
  have hmem : ∀ (x y z : V), z ∈ Work.ORBassSerre.reducedSpan x y ↔
      z ∈ (hT.geodesic x y).vertices := by
    intro x y z
    rw [hT.reducedSpan_eq x y]
    rfl
  obtain ⟨p₁, p₂, hp_eq⟩ :=
    (hT.geodesic a b).exists_eq_comp_of_mem_vertices ((hmem a b c).1 hc)
  have hgred : (p₁.comp p₂).IsReduced := hp_eq ▸ hT.geodesic_isReduced a b
  exact ⟨p₁, p₂, hp_eq, hT.eq_geodesic (Quiver.Path.IsReduced.of_comp (q := p₂) hgred),
    hT.eq_geodesic (isReduced_of_comp_right hgred)⟩

/-- In a tree, if `c` lies on the geodesic from `a` to `b`, then the geodesic from `a` to `b`
splits at `c` into the geodesic from `a` to `c` followed by the geodesic from `c` to `b`. -/
theorem reducedSpan_eq_union_of_mem {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    {hT : Work.ORBassSerre.IsTree V} {a b c : V}
    (hc : c ∈ Work.ORBassSerre.reducedSpan a b) :
    Work.ORBassSerre.reducedSpan a b =
      Work.ORBassSerre.reducedSpan a c ∪ Work.ORBassSerre.reducedSpan c b := by
  classical
  have hmem : ∀ (x y z : V), z ∈ Work.ORBassSerre.reducedSpan x y ↔
      z ∈ (hT.geodesic x y).vertices := by
    intro x y z
    rw [hT.reducedSpan_eq x y]
    rfl
  obtain ⟨p₁, p₂, hp_eq, hp₁geod, hp₂geod⟩ := geodesic_eq_comp_geodesic_of_mem hc
  refine Set.Subset.antisymm ?_ ?_
  · -- the geodesic from `a` to `b` passes through `c`: it is the concatenation at `c`,
    -- so it splits once more at any of its vertices
    intro v hv
    obtain ⟨r₁, r₂, hr_eq⟩ :=
      (hT.geodesic a b).exists_eq_comp_of_mem_vertices ((hmem a b v).1 hv)
    have hcmp : r₁.comp r₂ = p₁.comp p₂ := hr_eq.symm.trans hp_eq
    rw [Set.mem_union]
    rcases Work.ORBassSerre.Tree.Prefix.qpath_exists_eq_comp_of_comp_eq hcmp with
      ⟨r, hr⟩ | ⟨r, hr⟩
    · -- `c` comes after `v` on the geodesic
      left
      refine (hmem a c v).2 ?_
      rw [← hp₁geod, hr]
      exact mem_vertices_comp_right (Quiver.Path.start_mem_vertices r)
    · -- `c` comes before `v` on the geodesic
      right
      have hr₂eq : r.comp r₂ = p₂ := by
        have h1 : p₁.comp (r.comp r₂) = p₁.comp p₂ := by
          rw [← Quiver.Path.comp_assoc, ← hr]
          exact hcmp
        exact (Quiver.Path.comp_inj_right).1 h1
      refine (hmem c b v).2 ?_
      rw [← hp₂geod, ← hr₂eq]
      exact mem_vertices_comp_right (Quiver.Path.start_mem_vertices r₂)
  · -- both halves of the split are contained in the whole geodesic
    intro v hv
    rw [Set.mem_union] at hv
    rcases hv with hv | hv
    · have hv₁ : v ∈ p₁.vertices := hp₁geod.symm ▸ (hmem a c v).1 hv
      refine (hmem a b v).2 ?_
      rw [hp_eq]
      exact mem_vertices_comp_left hv₁
    · have hv₂ : v ∈ p₂.vertices := hp₂geod.symm ▸ (hmem c b v).1 hv
      refine (hmem a b v).2 ?_
      rw [hp_eq]
      exact mem_vertices_comp_right hv₂

end Work.ORBassSerre.Tree.Seg
