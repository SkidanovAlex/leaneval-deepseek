/-
# Howie's Case 1: any non-trivial reduced loop carries a labelling with a non-zero closed path

This is the free case of Howie's Case 2 (see `Submission/Work/ORLocInd/N4_LOCIND_LEAD.md` §L5a, and
the review of `Work.ORLocInd.Howie.hasIndicableLabelling_of_loop`): if a graph `Γ` (a `Quiver` with
an involutive reversal) has a non-trivial reduced closed path `p` at some vertex `x`, then there is
a *balanced* labelling `L : Γ → ℤ` and a closed path `q` whose *level* `pathSum L.toFun q` is
non-zero.

The construction is the obvious one: `p` contains a *simple cycle* `γ` (the sub-path of `p` between
two consecutive occurrences of a repeated vertex).  A simple cycle uses each of its arrows once and
never uses an arrow together with its inverse, so for the first arrow `g` of `γ` the unique
labelling which is `1` on `g`, `-1` on `g⁻¹` and `0` elsewhere is well defined and balanced (the
graph has no self-inverse loop by hypothesis), and `pathSum` of it on `γ` is `1`.

## Contents

* `HasNonzeroLoop` — "there is a labelling and a closed path of non-zero level";
* `not_nodup_vertices_of_closed` — a non-trivial closed path revisits its base vertex;
* `exists_labelling_of_simpleCycle` (imported) — the simple cycle case;
* `hasNonzeroLoop_of_not_nodup` — the extraction of the simple cycle from a repeated vertex;
* `hasIndicableLabelling_of_loop` — the target.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.CoverGraph
import Submission.Work.ORLocInd.Howie.Cover
import Submission.Work.ORLocInd.Howie.ArrowVertex
import Submission.Work.ORLocInd.Howie.isReduced_comp
import Submission.Work.ORLocInd.Howie.exists_labelling_of_simpleCycle

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.Howie

open Quiver

variable {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-- There is a balanced labelling of `Γ` by `ℤ` and a closed path of `Γ` whose level is non-zero:
this is Howie's conclusion that the cyclic cover defined by a labelling of the presentation is
non-trivial in the vertical direction. -/
def HasNonzeroLoop (V : Type*) [Quiver V] [Quiver.HasInvolutiveReverse V] : Prop :=
  ∃ L : Labelling V, ∃ (y : V) (q : Quiver.Path y y), pathSum L.toFun q ≠ 0

/-- A non-trivial closed path revisits its base vertex, so its vertex list is not `Nodup`. -/
theorem not_nodup_vertices_of_closed {a : V} (p : Quiver.Path a a) (h : p.length ≠ 0) :
    ¬ p.vertices.Nodup := by
  intro hnd
  have hlen : 2 ≤ p.vertices.length := by
    rw [Quiver.Path.vertices_length]; omega
  have hhl : p.vertices.head (Quiver.Path.vertices_ne_nil p) =
      p.vertices.getLast (Quiver.Path.vertices_ne_nil p) := by simp
  obtain ⟨x, hx⟩ := (List.Nodup.head_eq_getLast_iff (Quiver.Path.vertices_ne_nil p) hnd).mp hhl
  rw [hx] at hlen
  simp at hlen

/-- **Extraction of a simple cycle.**  If a reduced path `p` (any endpoints) has a repeated vertex,
then `Γ` admits a labelling with a closed path of non-zero level.

Strong induction on the length of `p`.  Writing `p = p' · e`, either `p'` already has a repeated
vertex (and we recurse), or `p'` is injective on vertices and its target `b` is one of them.  The
suffix of `p'` from `b` onwards, followed by `e`, is then a closed path at `b` with a repeated
vertex (recursing again); the only case that does *not* recurse is `b = a`, where the whole of `p`
is a *simple cycle* and the conclusion is `exists_labelling_of_simpleCycle`. -/
theorem hasNonzeroLoop_of_not_nodup (hns : ∀ (a : V) (e : a ⟶ a), Quiver.reverse e ≠ e)
    {a b : V} (p : Quiver.Path a b) (hp : p.IsReduced)
    (h : ¬ p.vertices.Nodup) : HasNonzeroLoop V := by
  suffices key : ∀ n, ∀ {a b : V} (p : Quiver.Path a b), p.length = n → p.IsReduced →
      ¬ p.vertices.Nodup → HasNonzeroLoop V by
    exact key p.length p rfl hp h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b p hlen hp h
    by_cases h0 : p.length = 0
    · -- the empty path has `Nodup` vertices
      exact absurd (by
        obtain rfl := Quiver.Path.eq_of_length_zero p h0
        rw [(Quiver.Path.length_eq_zero_iff p).mp h0]
        simp) h
    · obtain ⟨c, p', e, rfl⟩ := (Quiver.Path.length_ne_zero_iff_eq_cons (p := p)).mp h0
      have hp' : p'.IsReduced := Quiver.Path.IsReduced.of_comp (q := e.toPath) hp
      rw [Quiver.Path.vertices_cons] at h
      by_cases hnod : p'.vertices.Nodup
      · -- `p'` is injective on vertices, so its target `b` is one of them
        have hbmem : b ∈ p'.vertices := by
          by_contra hb
          exact h ((List.nodup_concat p'.vertices b).mpr ⟨hb, hnod⟩)
        by_cases hba : b = a
        · -- `p` is a simple cycle at `a`
          subst hba
          have hnodup : (p'.cons e).vertices.dropLast.Nodup := by
            rw [Quiver.Path.vertices_cons, List.concat_eq_append, List.dropLast_concat]
            exact hnod
          obtain ⟨L, hL⟩ := exists_labelling_of_simpleCycle (V := V) hns (p := p'.cons e)
            hp h0 hnodup
          exact ⟨L, _, p'.cons e, hL⟩
        · -- otherwise recurse on the closed suffix of `p` at `b`
          obtain ⟨r, s, hrs⟩ := Quiver.Path.exists_eq_comp_of_mem_vertices (p := p') hbmem
          have hpt : (p'.cons e) = r.comp (s.cons e) := by
            rw [hrs, ← Quiver.Path.comp_cons]
          have ht_red : (s.cons e).IsReduced :=
            (Quiver.Path.isReduced_comp_iff.mp (hpt ▸ hp)).2.1
          have hlen_t : (s.cons e).length < n := by
            have hlen_r : (r.comp (s.cons e)).length = n := by rw [← hpt]; exact hlen
            have hrc : r.length + (s.cons e).length = n := by
              rw [← hlen_r, Quiver.Path.length_comp]
            have hr1 : 1 ≤ r.length := by
              rcases Nat.eq_zero_or_pos r.length with hz | hpz
              · exact absurd (Quiver.Path.eq_of_length_zero r hz).symm hba
              · exact hpz
            omega
          have hnod_t : ¬ (s.cons e).vertices.Nodup :=
            not_nodup_vertices_of_closed (s.cons e) (by simp)
          exact ih (s.cons e).length hlen_t (s.cons e) rfl ht_red hnod_t
      · -- `p'` already has a repeated vertex
        exact ih p'.length (by rw [Quiver.Path.length_cons] at hlen; omega) p' rfl hp' hnod

theorem hasIndicableLabelling_of_loop {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    [DecidableEq V] (hns : ∀ (a : V) (e : a ⟶ a), Quiver.reverse e ≠ e) {x : V}
    (p : Quiver.Path x x) (hp : p.IsReduced) (hne : p.length ≠ 0) :
    ∃ L : Work.ORLocInd.Howie.Labelling V, ∃ (y : V) (q : Quiver.Path y y),
      Work.ORLocInd.Howie.pathSum L.toFun q ≠ 0 :=
  hasNonzeroLoop_of_not_nodup hns p hp (not_nodup_vertices_of_closed p hne)

end Work.ORLocInd.Howie
