/-
# Reachability in the arrow-deleted graph `Γ ∖ e` (ambient form)

Fix a presentation `P` on a graph `Γ` and an arrow `e` of `Γ`.  Howie's Case 2 deletes the
unoriented edge `{e, e⁻¹}`, i.e. all arrows carrying the code `P.edgeOf e`, and then asks whether
`e` is a *bridge*, i.e. whether `e.right` is joined to `e.left` in the remaining graph.

## Why this file exists (a formalisation trap)

The obvious way to phrase "a path of `Γ ∖ e`" is

    `Nonempty (Quiver.Path (e.left : DelV (P.keepCode (P.edgeOf e))) (y : DelV ...))`

and it is **wrong**.  `DelV K` is a `def` (`Defs2.DelV`) with `DelV K = V` definitionally, and the
vertex ascription `(e.left : DelV K)` is *erased* by elaboration: the `Quiver` instance metavariable
of `Quiver.Path` is solved by the (unique) instance for the *unfolded* type, so the ambient `Quiver V`
is picked and the ascription has no effect.  Consequently such a hypothesis silently says
"there is a path of `Γ`", which is *inconsistent* with `e` being an arrow (the path `e.toPath.reverse`
always exists), so the lemma becomes vacuous.  Use `Defs2.dpath K a b`
(`@Quiver.Path (DelV K) (instDelQuiver K) a b`), which pins the instance, or — preferably, as here —
phrase everything *ambiently* by asking that the path avoid the code of `e`.

The ambient formulation used below is robust: no instance is pinned, and each hypothesis is a
statement about honest paths of `Γ`.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Defs2
import Submission.Work.ORLocInd.Howie.Relator

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.ambiguousOpen false

universe u

namespace Work.ORLocInd.Howie

open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-- A path of `Γ` *avoids* the unoriented edge `e`: none of its arrows has the code of `e`, i.e.
all of its arrows survive the deletion of the pair `{e, e⁻¹}`. -/
def Avoids (P : Presentation V) (e : Quiver.Total V) {a b : V} (q : Quiver.Path a b) : Prop :=
  ∀ g ∈ q.arrowList, P.edgeOf g ≠ P.edgeOf e

theorem avoids_nil (P : Presentation V) (e : Quiver.Total V) {a : V} :
    Avoids P e (Quiver.Path.nil : Quiver.Path a a) := by
  intro g hg
  simp at hg

theorem avoids_cons_iff (P : Presentation V) (e : Quiver.Total V) {a b c : V}
    (q : Quiver.Path a b) (f : b ⟶ c) :
    Avoids P e (q.cons f) ↔
      Avoids P e q ∧ P.edgeOf (Quiver.Total.mk b c f) ≠ P.edgeOf e := by
  simp only [Avoids, Quiver.Path.arrowList_cons, List.mem_append, List.mem_singleton]
  constructor
  · intro h
    exact ⟨fun g hg => h g (Or.inl hg), h _ (Or.inr rfl)⟩
  · rintro ⟨h1, h2⟩ g (hg | rfl)
    · exact h1 g hg
    · exact h2

theorem avoids_comp_iff (P : Presentation V) (e : Quiver.Total V) {a b c : V}
    (p : Quiver.Path a b) (q : Quiver.Path b c) :
    Avoids P e (p.comp q) ↔ Avoids P e p ∧ Avoids P e q := by
  rw [Avoids, Avoids, Avoids, Quiver.Path.arrowList_comp', List.forall_mem_append]

theorem avoids_toPath (P : Presentation V) (e : Quiver.Total V) {a b : V} (f : a ⟶ b)
    (hf : P.edgeOf (Quiver.Total.mk a b f) ≠ P.edgeOf e) :
    Avoids P e (Quiver.Hom.toPath f) := by
  change Avoids P e (Quiver.Path.cons (Quiver.Path.nil : Quiver.Path a a) f)
  exact (avoids_cons_iff P e (Quiver.Path.nil : Quiver.Path a a) f).mpr
    ⟨avoids_nil P e, hf⟩

/-- A path of `Γ` whose single arrow is the reverse of `f` avoids `e` exactly when `f` does. -/
theorem edgeOf_reverse_mk_ne (P : Presentation V) (e : Quiver.Total V) {a b : V} (f : a ⟶ b) :
    (P.edgeOf (Quiver.Total.mk b a (Quiver.reverse f)) ≠ P.edgeOf e) ↔
      (P.edgeOf (Quiver.Total.mk a b f) ≠ P.edgeOf e) := by
  rw [← Quiver.totalReverse_mk, P.edgeOf_reverse]

theorem avoids_reverse (P : Presentation V) (e : Quiver.Total V) {a b : V} :
    ∀ {q : Quiver.Path a b}, Avoids P e q → Avoids P e q.reverse := by
  intro q
  induction q with
  | nil => intro _; exact avoids_nil P e
  | cons q f ih =>
      intro h
      obtain ⟨h1, h2⟩ := (avoids_cons_iff P e q f).mp h
      simp only [Quiver.Path.reverse, avoids_comp_iff]
      exact ⟨avoids_toPath P e (Quiver.reverse f)
        ((edgeOf_reverse_mk_ne P e f).mpr h2), ih h1⟩

/-- `DelReach P e y` : `y` is joined to `e.left` by a path of `Γ` avoiding the edge `e`, i.e. by a
path of `Γ ∖ e`. -/
def DelReach (P : Presentation V) (e : Quiver.Total V) (y : V) : Prop :=
  ∃ q : Quiver.Path e.left y, Avoids P e q

theorem delReach_self (P : Presentation V) (e : Quiver.Total V) : DelReach P e e.left :=
  ⟨Quiver.Path.nil, avoids_nil P e⟩

/-- An arrow of `Γ ∖ e` leads from a vertex reachable in `Γ ∖ e` back to one. -/
theorem delReach_of_delArrow (P : Presentation V) (e : Quiver.Total V) {x y : V}
    (f : x ⟶ y) (hf : P.edgeOf (Quiver.Total.mk x y f) ≠ P.edgeOf e)
    (h : DelReach P e y) : DelReach P e x := by
  obtain ⟨q, hq⟩ := h
  refine ⟨q.cons (Quiver.reverse f), ?_⟩
  rw [avoids_cons_iff]
  refine ⟨hq, ?_⟩
  show P.edgeOf (Quiver.totalReverse (Quiver.Total.mk x y f)) ≠ P.edgeOf e
  rw [P.edgeOf_reverse]
  exact hf

/-- An arrow of `Γ ∖ e` leads *out* of a vertex reachable in `Γ ∖ e`. -/
theorem delReach_of_delArrow' (P : Presentation V) (e : Quiver.Total V) {x y : V}
    (f : x ⟶ y) (hf : P.edgeOf (Quiver.Total.mk x y f) ≠ P.edgeOf e)
    (h : DelReach P e x) : DelReach P e y := by
  obtain ⟨q, hq⟩ := h
  exact ⟨q.cons f, (avoids_cons_iff P e q f).mpr ⟨hq, hf⟩⟩

/-- The bridge hypothesis, read from the other side: `DelReach P e e.right` fails exactly when there
is no path of `Γ ∖ e` from `e.right` back to `e.left`. -/
theorem not_delReach_right_iff (P : Presentation V) (e : Quiver.Total V) :
    (¬ DelReach P e e.right) ↔
      ∀ q : Quiver.Path e.right e.left, Avoids P e q → False := by
  constructor
  · rintro h q hq
    exact h ⟨q.reverse, avoids_reverse P e hq⟩
  · rintro h ⟨q, hq⟩
    exact h q.reverse (avoids_reverse P e hq)

end Work.ORLocInd.Howie
