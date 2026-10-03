/-
# Node N4 / local indicability: the second-generation definitions (D1--D3 of `N4_LOCIND_LEAD.md`)

This file contains the three definitions on which the repaired Case 1 (`case1_descent`) and the
rewritten Case 2 of Howie's proof of Brodskii's theorem are phrased:

* **D1** `Presentation.CodeSeparates` — the edge code *separates* unoriented edges.  Without this,
  `edgeCount P.edgeOf p e` (the number of arrows of `p` carrying the same code as `e`) is not the
  number of occurrences of the unoriented edge `{e, e⁻¹}`, and Howie's Case 2 is false; the
  counterexample is `Howie/case2_cex.lean`.
* **D2** `Presentation.HasIndicableLabelling` — the presentation admits a balanced integer labelling
  which vanishes on the relators and is nonzero on some closed path.  This is the *global* form of
  "some vertex group of the presentation is indicable"; it is the hypothesis of Case 2 (Howie's
  "`G_v` is not indicable") and it is invariant under the Tietze elimination `vertexGroup_eliminate`.
* **D3** `Keep`/`DelV` — a predicate on the arrows of `Γ`, invariant under reversal, and the
  type synonym `DelV K` carrying the *same vertices* with only the kept arrows.  Case 2 deletes
  arrows (and relators) and works on `DelV K` rather than on a subtype of the vertices, so that no
  vertex casts occur anywhere.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Relator
import Submission.Work.ORLocInd.Howie.CoverGraph
import Submission.Work.ORLocInd.Howie.CoverPresentation

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.Howie

open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-! ## D1: the edge code separates unoriented edges -/

/-- The code `P.edgeOf` of the unoriented edges of `P` *separates* them: two arrows have the same
code only if they are the same arrow, or mutually inverse.

This is what "`α`: the type of unoriented edges, as a linearly ordered code" in `Relator.lean`
intends, and it is exactly the extra hypothesis under which `edgeCount P.edgeOf p e` counts the
occurrences of the unoriented edge `{e, e⁻¹}` (and hence under which Howie's Case 2 holds). -/
def Presentation.CodeSeparates (P : Presentation V) : Prop :=
  ∀ e f : Quiver.Total V, P.edgeOf e = P.edgeOf f → e = f ∨ e = Quiver.totalReverse f

/-! ## D2: indicability via labellings -/

/-- The presentation admits an *indicable labelling*: a balanced labelling of the arrows which
vanishes on the relators, and which is nonzero on some closed path.

By `indicable_of_labelling` this is equivalent to the existence of a vertex whose vertex group of
`⟨Γ | R⟩` admits a surjection onto `Multiplicative ℤ`; the formulation by labellings is the one
used in Case 2, because it is preserved by the Tietze elimination. -/
def Presentation.HasIndicableLabelling (P : Presentation V) : Prop :=
  ∃ L : Labelling V, VanishOnRelators L P ∧
    ∃ (x : V) (p : Quiver.Path x x), pathSum L.toFun p ≠ 0

/-! ## D3: arrow deletion on a fixed vertex type -/

/-- A predicate on the arrows of `Γ` which is invariant under reversal: `Keep K` describes the
subgraph of `Γ` whose arrows satisfy `K.pred`. -/
structure Keep (V : Type u) [Quiver V] [Quiver.HasInvolutiveReverse V] where
  /-- the arrows that are kept -/
  pred : Quiver.Total V → Prop
  /-- the predicate is invariant under reversal -/
  rev : ∀ e, pred (Quiver.totalReverse e) ↔ pred e

/-- The vertices of the graph obtained from `Γ` by keeping only the arrows satisfying `K`.

This is a *type synonym* for `V`: the deletion of arrows does not change the vertex set, so no
vertex casts (and no vertex subtypes) ever occur in the arguments of Case 2.  It is a `def` rather
than an `abbrev` so that instance search does not confuse `⟶` in `DelV K` with `⟶` in `V`. -/
def DelV (K : Keep V) : Type u := V

/-- The arrows of the graph obtained from `Γ` by keeping only the arrows satisfying `K`. -/
def DelArrow (K : Keep V) (a b : V) : Type u :=
  {e : a ⟶ b // K.pred (Quiver.Total.mk a b e)}

instance instDelQuiver (K : Keep V) : Quiver (DelV K) := ⟨fun a b => DelArrow K a b⟩

/-- Paths in the deleted graph `DelV K`, with the instance `instDelQuiver K` *pinned*.

This is needed because `DelV K` is definitionally `V`: a plain ascription `(a : DelV K)` is inert and
`Quiver.Path` would resolve to the ambient `Quiver V`.  Use `dpath K a b` whenever the paths are meant
to avoid the deleted arrows. -/
abbrev dpath (K : Keep V) (a b : V) : Type u :=
  @Quiver.Path (DelV K) (instDelQuiver K) a b

/-- The subgraph obtained by deleting the arrows whose code is `c` (the edge-deletion step of
Howie's Case 2). -/
def Presentation.keepCode (P : Presentation V) (c : P.α) : Keep V :=
  ⟨fun g => P.edgeOf g ≠ c, by intro g; rw [P.edgeOf_reverse g]⟩

@[simp] theorem Presentation.keepCode_pred (P : Presentation V) (c : P.α) (g : Quiver.Total V) :
    (P.keepCode c).pred g = (P.edgeOf g ≠ c) := rfl

instance instDelReverse (K : Keep V) : Quiver.HasInvolutiveReverse (DelV K) where
  reverse' := fun {a b} f =>
    ⟨Quiver.reverse f.1, (K.rev (Quiver.Total.mk a b f.1)).2 f.2⟩
  inv' := fun {a b} f => Subtype.ext (Quiver.reverse_reverse f.1)

end Work.ORLocInd.Howie
