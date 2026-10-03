import Mathlib
import Submission.Work.ORBassSerre.Tree.IsTreeAPI

namespace Work.ORBassSerre.Tree.Seg

open Quiver

/-! ### Auxiliary lemmas about paths and their vertices

These are the elementary facts about `Quiver.Path` that the median argument needs. -/

/-- The vertices of a composite path are the vertices of its two parts. -/
theorem mem_vertices_comp_aux {V : Type*} [Quiver V] {a b c : V} (u : Quiver.Path a b)
    (v : Quiver.Path b c) (w : V) :
    w ∈ (u.comp v).vertices ↔ w ∈ u.vertices ∨ w ∈ v.vertices := by
  rw [Quiver.Path.vertices_comp, List.mem_append]
  constructor
  · rintro (h | h)
    · exact Or.inl (List.mem_of_mem_dropLast h)
    · exact Or.inr h
  · rintro (h | h)
    · have hd : w ∈ u.vertices.dropLast ∨ w ∈ ([b] : List V) := by
        rw [← List.mem_append, Quiver.Path.dropLast_append_end_eq]
        exact h
      rcases hd with hd | hd
      · exact Or.inl hd
      · right
        rw [List.mem_singleton] at hd
        subst hd
        exact Quiver.Path.start_mem_vertices v
    · exact Or.inr h

/-- Reversing a path reverses its list of vertices. -/
theorem vertices_reverse_aux {V : Type*} [Quiver V] [Quiver.HasReverse V] {a b : V}
    (p : Quiver.Path a b) : p.reverse.vertices = p.vertices.reverse := by
  induction p with
  | nil => simp
  | cons p' e ih =>
    show ((Quiver.reverse e).toPath.comp p'.reverse).vertices = (p'.cons e).vertices.reverse
    rw [Quiver.Path.vertices_comp, ih, Quiver.Path.vertices_toPath, Quiver.Path.vertices_cons]
    simp

/-- Reversal does not change the set of vertices of a path. -/
theorem mem_vertices_reverse_aux {V : Type*} [Quiver V] [Quiver.HasReverse V] {a b : V}
    (p : Quiver.Path a b) (w : V) : w ∈ p.reverse.vertices ↔ w ∈ p.vertices := by
  rw [vertices_reverse_aux p, List.mem_reverse]

/-- A subpath of a reduced path is reduced: if `u.comp v` is reduced, then so is `v`. -/
theorem isReduced_of_comp_right_aux {V : Type*} [Quiver V] [Quiver.HasReverse V] {a b c : V}
    {u : Quiver.Path a b} {v : Quiver.Path b c} (h : (u.comp v).IsReduced) : v.IsReduced :=
  fun q hq => h (u.comp q) (hq.comp_left u)

/-- A reduced path through a vertex `m` splits at `m` into two reduced subpaths whose vertices
are vertices of the whole path. -/
theorem exists_decomp_of_mem_vertices_aux {V : Type*} [Quiver V] [Quiver.HasReverse V]
    {a b : V} {p : Quiver.Path a b} (hp : p.IsReduced) {m : V} (hm : m ∈ p.vertices) :
    ∃ (u : Quiver.Path a m) (v : Quiver.Path m b), u.IsReduced ∧ v.IsReduced ∧
      u.comp v = p ∧ (∀ w, w ∈ u.vertices → w ∈ p.vertices) ∧
      (∀ w, w ∈ v.vertices → w ∈ p.vertices) := by
  obtain ⟨u, v, huv⟩ := Quiver.Path.exists_eq_comp_of_mem_vertices p hm
  have hp' : (u.comp v).IsReduced := huv ▸ hp
  refine ⟨u, v, Quiver.Path.IsReduced.of_comp (q := v) hp',
    isReduced_of_comp_right_aux hp', huv.symm, fun w hw => ?_, fun w hw => ?_⟩
  · rw [huv]
    exact (mem_vertices_comp_aux u v w).2 (Or.inl hw)
  · rw [huv]
    exact (mem_vertices_comp_aux u v w).2 (Or.inr hw)

/-- Among the vertices of a path `p` there is one, `m`, closest to a vertex `x` that can reach
the start of `p`: there is a reduced path `q` from `x` to `m` whose length is minimal among the
lengths of all reduced paths from `x` to a vertex of `p`. -/
theorem exists_min_mem_vertices_aux {V : Type*} [Quiver V] [Quiver.HasReverse V] {a b : V}
    (p : Quiver.Path a b) (x : V) (h : Nonempty (Quiver.Path x a)) :
    ∃ (m : V) (q : Quiver.Path x m), m ∈ p.vertices ∧ q.IsReduced ∧
      ∀ w, w ∈ p.vertices → ∀ π : Quiver.Path x w, π.IsReduced → q.length ≤ π.length := by
  classical
  obtain ⟨π₀, hπ₀⟩ := Tree.Reduction.qpath_exists_isReduced h
  have hP : ∃ n, ∃ v : V, v ∈ p.vertices ∧ ∃ π : Quiver.Path x v, π.IsReduced ∧ π.length = n :=
    ⟨π₀.length, a, Quiver.Path.start_mem_vertices p, π₀, hπ₀, rfl⟩
  obtain ⟨m, hm, q, hq, hqlen⟩ := Nat.find_spec hP
  refine ⟨m, q, hm, hq, fun w hw π hπ => ?_⟩
  by_contra hcon
  rw [not_le] at hcon
  rw [hqlen] at hcon
  exact Nat.find_min hP hcon ⟨w, hw, π, hπ, rfl⟩

/-- **Junction lemma for the closest point.**  Let `q : x → m` be a reduced path of minimal
length among the reduced paths from `x` to the vertices of `r`, and let `r : m → c` be reduced
with all its vertices in the set `Q`.  Then `q.comp r` is reduced: a backtrack can only occur at
the junction, and removing it would exhibit a strictly closer vertex of `r`. -/
theorem isReduced_comp_of_min_aux {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    {x m c : V} {q : Quiver.Path x m} {r : Quiver.Path m c} {Q : V → Prop}
    (hq : q.IsReduced) (hr : r.IsReduced)
    (hmin : ∀ w, Q w → ∀ π : Quiver.Path x w, π.IsReduced → q.length ≤ π.length)
    (hsub : ∀ w, w ∈ r.vertices → Q w) : (q.comp r).IsReduced := by
  intro w hdb
  obtain ⟨x', f, q', r', hq_eq, hr_eq, _⟩ :=
    Tree.Geodesic.deleteBacktrack_comp_junction hq hr hdb
  have hq'red : q'.IsReduced :=
    Quiver.Path.IsReduced.of_comp (q := f.toPath)
      (by rw [Quiver.Path.comp_toPath_eq_cons, ← hq_eq]; exact hq)
  have hlen : q.length = q'.length + 1 := by rw [hq_eq]; rfl
  have hx' : x' ∈ r.vertices := by
    rw [hr_eq]
    exact (mem_vertices_comp_aux ((Quiver.reverse f).toPath) r' x').2
      (Or.inl (Quiver.Path.end_mem_vertices ((Quiver.reverse f).toPath)))
  have := hmin x' (hsub x' hx') q' hq'red
  omega

/-- The set of vertices lying on a reduced path from `a` to `b` does not depend on the order of
the two vertices. -/
theorem mem_reducedSpan_comm_aux {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    {a b v : V} : v ∈ reducedSpan a b ↔ v ∈ reducedSpan b a := by
  constructor
  · rintro ⟨p, hp, hv⟩
    exact ⟨p.reverse, hp.reverse, (mem_vertices_reverse_aux p v).2 hv⟩
  · rintro ⟨p, hp, hv⟩
    exact ⟨p.reverse, hp.reverse, (mem_vertices_reverse_aux p v).2 hv⟩

/-- Three vertices of a tree have a common "median": a vertex lying on all three geodesic
segments joining them pairwise. -/
theorem exists_median {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    {hT : Work.ORBassSerre.IsTree V} (x y z : V) :
    ∃ m : V, m ∈ Work.ORBassSerre.reducedSpan x y ∧
      m ∈ Work.ORBassSerre.reducedSpan y z ∧ m ∈ Work.ORBassSerre.reducedSpan z x := by
  classical
  -- A vertex `m` of the geodesic from `y` to `z` that is closest to `x`.
  obtain ⟨m, q, hm, hq, hmin⟩ :=
    exists_min_mem_vertices_aux (hT.geodesic y z) x ⟨hT.geodesic x y⟩
  -- Split that geodesic at `m`.
  obtain ⟨u, v, hu, hv, huv, hsu, hsv⟩ :=
    exists_decomp_of_mem_vertices_aux (hT.geodesic_isReduced y z) hm
  -- `q` followed by the part of the geodesic from `m` back to `y` is reduced,
  -- so `m` lies on the geodesic from `x` to `y`.
  have hxyR : (q.comp u.reverse).IsReduced :=
    isReduced_comp_of_min_aux (Q := fun w => w ∈ (hT.geodesic y z).vertices) hq hu.reverse hmin
      (fun w hw => hsu w ((mem_vertices_reverse_aux u w).1 hw))
  -- `q` followed by the part of the geodesic from `m` to `z` is reduced,
  -- so `m` lies on the geodesic from `x` to `z`.
  have hxzR : (q.comp v).IsReduced :=
    isReduced_comp_of_min_aux (Q := fun w => w ∈ (hT.geodesic y z).vertices) hq hv hmin hsv
  refine ⟨m, ?_, ?_, ?_⟩
  · exact ⟨q.comp u.reverse, hxyR,
      (mem_vertices_comp_aux q u.reverse m).2 (Or.inr (Quiver.Path.start_mem_vertices u.reverse))⟩
  · exact ⟨hT.geodesic y z, hT.geodesic_isReduced y z, hm⟩
  · exact mem_reducedSpan_comm_aux.2
      ⟨q.comp v, hxzR,
        (mem_vertices_comp_aux q v m).2 (Or.inr (Quiver.Path.start_mem_vertices v))⟩

end Work.ORBassSerre.Tree.Seg
