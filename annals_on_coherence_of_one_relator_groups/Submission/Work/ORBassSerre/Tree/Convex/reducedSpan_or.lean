import Mathlib
import Submission.Work.ORBassSerre.Tree.Convex
import Submission.Work.ORBassSerre.Tree.IsTreeAPI

namespace Work.ORBassSerre.Tree.Convex

open Quiver

/-! ## Auxiliary lemmas about the vertices of a path

These are small, general facts about `Quiver.Path.vertices` and reversal which are used in the
proof of `reducedSpan_or` (and are of independent use). -/

/-- Membership in the vertex list of a composite path splits as membership in the vertex list
of either factor. -/
theorem mem_vertices_comp {V : Type*} [Quiver V] {a b c : V} (p : Quiver.Path a b)
    (q : Quiver.Path b c) {v : V} :
    v ∈ (p.comp q).vertices ↔ v ∈ p.vertices ∨ v ∈ q.vertices := by
  rw [Quiver.Path.vertices_comp, List.mem_append]
  constructor
  · rintro (hv | hv)
    · exact Or.inl ((List.dropLast_sublist p.vertices).subset hv)
    · exact Or.inr hv
  · rintro (hv | hv)
    · by_cases hmem : v ∈ p.vertices.dropLast
      · exact Or.inl hmem
      · right
        have h2 : v ∈ p.vertices.dropLast ++ [b] := by
          rw [Quiver.Path.dropLast_append_end_eq p]; exact hv
        rcases List.mem_append.mp h2 with h2 | h2
        · exact absurd h2 hmem
        · have hvb : v = b := by simpa using h2
          subst hvb
          exact Quiver.Path.start_mem_vertices q
    · exact Or.inr hv

/-- Reversing a path reverses its vertex list. -/
theorem vertices_reverse {V : Type*} [Quiver V] [Quiver.HasReverse V] {a b : V}
    (p : Quiver.Path a b) : p.reverse.vertices = p.vertices.reverse := by
  induction p with
  | nil => simp
  | cons p e ih =>
    rw [show (p.cons e).reverse = (Quiver.reverse e).toPath.comp p.reverse from rfl,
      Quiver.Path.vertices_comp, Quiver.Path.vertices_toPath, ih, Quiver.Path.vertices_cons,
      List.concat_eq_append, List.reverse_append]
    simp

/-- A vertex lies on the reverse of a path iff it lies on the path. -/
theorem mem_vertices_reverse {V : Type*} [Quiver V] [Quiver.HasReverse V] {a b : V}
    (p : Quiver.Path a b) {v : V} : v ∈ p.reverse.vertices ↔ v ∈ p.vertices := by
  rw [vertices_reverse, List.mem_reverse]

/-- The right factor of a reduced composite path is reduced. -/
theorem isReduced_of_comp_right {V : Type*} [Quiver V] [Quiver.HasReverse V]
    {a b c : V} {p : Quiver.Path a b} {q : Quiver.Path b c} (h : (p.comp q).IsReduced) :
    q.IsReduced :=
  fun q' hq' => h (p.comp q') (hq'.comp_left p)

/-! ## Cancelling the concatenation of two reduced paths

The main ingredient: if `α : a → b` and `γ : b → c` are reduced paths in a graph with reversal,
then the concatenation `α.comp γ` can be reduced by cancelling a terminal segment of `α` against
an initial segment of `γ` which are mutual reverses.  Consequently every vertex of `α` is a
vertex of the reduced path `α'.comp γ'` or of `γ` itself. -/

theorem exists_cancel_aux {V : Type*} [Quiver V] [Quiver.HasReverse V] (n : ℕ) :
    ∀ {a b c : V} (α : Quiver.Path a b) (γ : Quiver.Path b c),
      α.length + γ.length = n → α.IsReduced → γ.IsReduced →
      ∃ (y : V) (α' : Quiver.Path a y) (γ' : Quiver.Path y c) (s : Quiver.Path y b),
        α = α'.comp s ∧ γ = s.reverse.comp γ' ∧ (α'.comp γ').IsReduced := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b c α γ hlen hα hγ
    by_cases hred : (α.comp γ).IsReduced
    · exact ⟨b, α, γ, Quiver.Path.nil, by simp, by simp, by simpa using hred⟩
    · rw [Quiver.Path.IsReduced] at hred
      push Not at hred
      obtain ⟨w, hw⟩ := hred
      obtain ⟨x, f, u', v', hαeq, hγeq, -⟩ :=
        Work.ORBassSerre.Tree.Geodesic.deleteBacktrack_comp_junction hα hγ hw
      have hu'red : u'.IsReduced := by
        suffices hh : (u'.comp f.toPath).IsReduced by
          exact Quiver.Path.IsReduced.of_comp hh
        rwa [Quiver.Path.comp_toPath_eq_cons, ← hαeq]
      have hv'red : v'.IsReduced := by
        have hh : ((Quiver.reverse f).toPath.comp v').IsReduced := by rwa [← hγeq]
        exact isReduced_of_comp_right hh
      have hlen_lt : u'.length + v'.length < n := by
        have h1 : α.length = u'.length + 1 := by rw [hαeq, Quiver.Path.length_cons]
        have h2 : γ.length = v'.length + 1 := by
          rw [hγeq, Quiver.Path.length_comp, Quiver.Path.length_toPath]
          omega
        omega
      obtain ⟨y, α', γ', s, hα', hγ', hred'⟩ :=
        ih (u'.length + v'.length) hlen_lt u' v' rfl hu'red hv'red
      refine ⟨y, α', γ', s.cons f, ?_, ?_, hred'⟩
      · rw [hαeq, hα']
        simp
      · rw [hγeq, hγ', ← Quiver.Path.comp_assoc]
        rfl

/-- Cancellation form: for reduced paths `α : a → b` and `γ : b → c` there are a vertex `y`,
paths `α' : a → y`, `γ' : y → c`, `s : y → b` with `α = α'.comp s`, `γ = s.reverse.comp γ'`
and `α'.comp γ'` reduced. -/
theorem exists_cancel {V : Type*} [Quiver V] [Quiver.HasReverse V] {a b c : V}
    (α : Quiver.Path a b) (γ : Quiver.Path b c) (hα : α.IsReduced) (hγ : γ.IsReduced) :
    ∃ (y : V) (α' : Quiver.Path a y) (γ' : Quiver.Path y c) (s : Quiver.Path y b),
      α = α'.comp s ∧ γ = s.reverse.comp γ' ∧ (α'.comp γ').IsReduced :=
  exists_cancel_aux (α.length + γ.length) α γ rfl hα hγ

/-- In a tree, a vertex lying on the reduced span from `u` to `w` lies on the span from `u` to `z`
or on the span from `w` to `z`. -/
theorem reducedSpan_or {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (h : Work.ORBassSerre.IsTree V) (u w z : V) {v : V}
    (hv : v ∈ Work.ORBassSerre.reducedSpan u w) :
    v ∈ Work.ORBassSerre.reducedSpan u z ∨ v ∈ Work.ORBassSerre.reducedSpan w z := by
  have hv' : v ∈ (h.geodesic u w).vertices := by
    simpa [Work.ORBassSerre.IsTree.reducedSpan_eq h u w] using hv
  obtain ⟨y, α', γ', s, hα, hγ, hred⟩ :=
    exists_cancel (h.geodesic u w) (h.geodesic w z)
      (h.geodesic_isReduced u w) (h.geodesic_isReduced w z)
  have hgeo : α'.comp γ' = h.geodesic u z := h.eq_geodesic hred
  rw [hα] at hv'
  rcases (mem_vertices_comp α' s).1 hv' with hv' | hv'
  · left
    rw [h.reducedSpan_eq u z, ← hgeo]
    simpa using (mem_vertices_comp α' γ').2 (Or.inl hv')
  · right
    rw [h.reducedSpan_eq w z, hγ]
    simpa using (mem_vertices_comp s.reverse γ').2 (Or.inl ((mem_vertices_reverse s).2 hv'))

end Work.ORBassSerre.Tree.Convex
