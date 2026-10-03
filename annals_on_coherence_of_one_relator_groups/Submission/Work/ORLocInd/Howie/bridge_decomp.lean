/-
# The bridge decomposition of a path (Howie's Case 2, step L5)

Fix a presentation `P`, an arrow `e : e.left ⟶ e.right` of `Γ`, and let `c := P.edgeOf e` be the
code of the unoriented edge `{e, e⁻¹}`.  Say that a vertex `y` is `e`-reachable when `y` is joined
to `e.left` by a path of `Γ ∖ e`, the graph obtained from `Γ` by deleting all arrows of code `c`.

**The bridge decomposition.**  If `e` is a *bridge* of `Γ ∖ e` (`e.right` is not `e`-reachable, so
`e.left` and `e.right` lie in different components of `Γ ∖ e`) and `y` is `e`-reachable, then every
path `t : e.right → y` has a very restricted shape: reading `t` from its end, all of it after its
*last* arrow of code `c` avoids `c`, and that last arrow is `e⁻¹`:

    t = u ∗ e⁻¹ ∗ v      with `v` avoiding the code of `e`,

i.e. `t = (u.cons (Quiver.reverse e.hom)).comp v` with `∀ g ∈ v.arrowList, P.edgeOf g ≠ P.edgeOf e`.
The argument is the induction on `t` carried out below.  Let `f` be the last arrow of `t`,
`t = p.cons f`:

* if the code of `f` is not `c`, then `f` is an arrow of `Γ ∖ e`, so `y` is `e`-reachable iff the
  intermediate vertex is, and the induction hypothesis applies to `p`;
* if the code of `f` is `c`, then by `CodeSeparates` either `f = e` or `f = e⁻¹`.  If `f = e` then
  `y = e.right`, and `e`-reachability of `y` would make `e.right` `e`-reachable, contradicting the
  bridge hypothesis.  Hence `f = e⁻¹`, the initial segment `p` of `t` is a closed path at
  `e.right`, and `v` can be taken empty.

**What this file contains.**  The requested lemma `bridge_decomp` is stated with
`Work.ORLocInd.Howie.Reach` of `BridgeSide.lean`.  As that definition is elaborated it does *not*
mean `e`-reachability as described above; see the remark on `ReachDelV` below.  So the file
contains both

* `bridge_decomp` — the requested statement, proved exactly as written (the proof is the induction
  above; the only place where the meaning of `Reach` is used is the step
  `BridgeSide.reach_of_reach_of_code_ne`, whose statement is the same under either reading), and
* `bridge_decomp_delV` — the same decomposition for the *intended* notion `ReachDelV`, in which the
  `Quiver` instance of `DelV (P.keepCode (P.edgeOf e))` is pinned, so that the paths really are the
  paths of the deleted graph `Γ ∖ e`.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.BridgeSide
import Submission.Work.ORLocInd.Howie.Defs2
import Submission.Work.ORLocInd.Howie.Relator
import Submission.Work.ORLocInd.Howie.isReduced_cons_iff
import Submission.Work.ORLocInd.Howie.Cover

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORLocInd.Howie

variable {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-! ## 1. The intended notion: reachability in `Γ ∖ e`, instance pinned -/

/-- `ReachDelV P e y` : `y` is joined to `e.left` by a path of `Γ ∖ e` (the graph obtained from `Γ`
by deleting the arrows of code `P.edgeOf e`), as the definition `Reach` of `BridgeSide.lean`
intends, but spelled with the `Quiver` instance of `DelV` *pinned*.

Why the pinning matters.  `DelV K` is a `def` equal to `V` (`Defs2.lean`), so the ascriptions
`(e.left : DelV K)` and `(y : DelV K)` are inert: when `Quiver.Path` is elaborated at them,
instance search unfolds `DelV K` to `V` and picks the *ambient* `Quiver V` instance, discarding
`instDelQuiver K`.  Hence the definition

    Reach P e y := Nonempty (Quiver.Path (e.left : DelV K) (y : DelV K))

of `BridgeSide.lean` unfolds (see `#print Work.ORLocInd.Howie.Reach`) to

    Nonempty (@Quiver.Path V inst e.left y),

i.e. to `Nonempty (Quiver.Path e.left y)` *in `Γ`*, with no restriction to `Γ ∖ e` at all — the same
accident as in the other files of this development, where the paths of `DelV K` are written
`@Quiver.Path (DelV K) (instDelQuiver K) a b` (`Delete.lean`, `false_of_bridge_forest_side.lean`,
`not_reach_iff_of_code_eq.lean`).  `ReachDelV` below is that pinned spelling; `Defs2.dpath K a b`
is the abbreviation of the same thing. -/
def ReachDelV (P : Presentation V) (e : Quiver.Total V) (y : V) : Prop :=
  Nonempty (@Quiver.Path (DelV (P.keepCode (P.edgeOf e)))
    (instDelQuiver (P.keepCode (P.edgeOf e)))
    (e.left : DelV (P.keepCode (P.edgeOf e)))
    (y : DelV (P.keepCode (P.edgeOf e))))

/-- An arrow of `Γ` whose code is not the code of `e` is an arrow of `Γ ∖ e`, so it leads from an
`e`-reachable vertex to an `e`-reachable vertex. -/
theorem reachDelV_of_code_ne (P : Presentation V) (e : Quiver.Total V) {x y : V} (f : x ⟶ y)
    (hf : P.edgeOf (Quiver.Total.mk x y f) ≠ P.edgeOf e) (h : ReachDelV P e y) :
    ReachDelV P e x := by
  obtain ⟨p⟩ := h
  have hf' : (P.keepCode (P.edgeOf e)).pred (Quiver.Total.mk x y f) := by
    rw [Presentation.keepCode_pred]
    exact hf
  exact ⟨p.comp (Quiver.reverse
    (⟨f, hf'⟩ : DelArrow (P.keepCode (P.edgeOf e)) x y)).toPath⟩

/-- An arrow of `Γ ∖ e` leads from an `e`-reachable vertex to an `e`-reachable vertex.  (The pinned
analogue of `BridgeSide.reach_of_reach_of_delArrow`.) -/
theorem reachDelV_of_delArrow (P : Presentation V) (e : Quiver.Total V) {x y : V}
    (f : DelArrow (P.keepCode (P.edgeOf e)) x y) (h : ReachDelV P e y) : ReachDelV P e x := by
  obtain ⟨p⟩ := h
  exact ⟨p.comp (Quiver.reverse f).toPath⟩

/-- The bridge hypothesis, read in the other direction: if there is no path of `Γ ∖ e` from
`e.right` to `e.left`, then `e.right` is not `e`-reachable.  (The pinned analogue of
`BridgeSide.not_reach_right_of_bridge`; this is how the hypothesis `hnot` of
`bridge_decomp_delV` is obtained from the bridge hypothesis of the L5 chain.) -/
theorem not_reachDelV_of_bridge (P : Presentation V) (e : Quiver.Total V)
    (hbr : ¬ Nonempty (@Quiver.Path (DelV (P.keepCode (P.edgeOf e)))
      (instDelQuiver (P.keepCode (P.edgeOf e)))
      (e.right : DelV (P.keepCode (P.edgeOf e)))
      (e.left : DelV (P.keepCode (P.edgeOf e))))) :
    ¬ ReachDelV P e e.right := by
  rintro ⟨p⟩
  exact hbr ⟨p.reverse⟩

/-- **The bridge decomposition for the intended (pinned) notion of `e`-reachability.**  If `e` is a
bridge of `Γ ∖ e` (`hnot`) and `y` is `e`-reachable (`hreach`), then a path `t : e.right → y` is
`u ∗ e⁻¹ ∗ v` with all arrows of `v` avoiding the code of `e` (see the file header).

Here neither hypothesis nor conclusion is vacuous: take `Γ` with vertices `0`, `1`, `y` and arrows
`e : 0 ⟶ 1`, `c : 0 ⟶ y`, plus a loop `l` at `1`; let `P` code the unoriented edges injectively (so
that `P.CodeSeparates` holds), and let `t = l ∗ e⁻¹ ∗ w` be a path `1 → y` whose tail `w` avoids
`e`, so that `y` is `e`-reachable while `1 = e.right` is not.  Then `hnot` holds and the conclusion
is the assertion that the last `e`-coded arrow of `t` is its `e⁻¹`. -/
theorem bridge_decomp_delV (P : Presentation V) (hsep : P.CodeSeparates) (e : Quiver.Total V)
    (hnot : ¬ ReachDelV P e e.right) :
    ∀ {y : V} (t : Quiver.Path (e.right : V) y), t.IsReduced → ReachDelV P e y →
      ∃ (u : Quiver.Path (e.right : V) (e.right : V)) (v : Quiver.Path (e.left : V) y),
        t = (u.cons (Quiver.reverse e.hom)).comp v ∧
          (∀ g ∈ v.arrowList, P.edgeOf g ≠ P.edgeOf e) := by
  intro y t
  induction t with
  | nil => intro _ h; exact absurd h hnot
  | cons p f ih =>
    intro ht hreach
    by_cases hc : P.edgeOf (Quiver.Total.mk _ _ f) = P.edgeOf e
    · -- the last arrow of `t` has the code of `e`, so by `hsep` it is `e` or `e⁻¹`
      rcases hsep (Quiver.Total.mk _ _ f) e hc with h | h
      · -- it is `e`, so `y = e.right` and `hreach` contradicts the bridge hypothesis
        exact absurd (congrArg Quiver.Total.right h ▸ hreach) hnot
      · -- it is `e⁻¹`: `t = p ∗ e⁻¹ ∗ nil`
        cases h
        exact ⟨p, Quiver.Path.nil, by rw [Quiver.Path.comp_nil],
          by intro g hg; simp at hg⟩
    · -- the last arrow of `t` is an arrow of `Γ ∖ e`
      obtain ⟨u, v, huv, hv⟩ :=
        ih (isReduced_cons_iff.mp ht).1 (reachDelV_of_code_ne P e f hc hreach)
      refine ⟨u, v.cons f, ?_, ?_⟩
      · rw [huv, Quiver.Path.comp_cons]
      · intro g hg
        rw [Quiver.Path.arrowList_cons] at hg
        rcases List.mem_append.mp hg with hg | hg
        · exact hv g hg
        · simp only [List.mem_singleton] at hg
          subst hg
          exact hc

/-! ## 2. The requested lemma -/

/-- Auxiliary form of `bridge_decomp`, with the step "an arrow of `Γ ∖ e` preserves
`e`-reachability" taken as an explicit hypothesis, so that the proof does not depend on how
`Reach` unfolds.  `BridgeSide.reach_of_reach_of_code_ne` is such a step (under either reading of
`Reach`), which is how `bridge_decomp` below discharges it. -/
theorem bridge_decomp_of_step (P : Presentation V) (hsep : P.CodeSeparates) (e : Quiver.Total V)
    (hstep : ∀ {x y : V} (f : x ⟶ y), P.edgeOf (Quiver.Total.mk x y f) ≠ P.edgeOf e →
      Reach P e y → Reach P e x)
    (hnot : ¬ Reach P e e.right) :
    ∀ {y : V} (t : Quiver.Path (e.right : V) y), t.IsReduced → Reach P e y →
      ∃ (u : Quiver.Path (e.right : V) (e.right : V)) (v : Quiver.Path (e.left : V) y),
        t = (u.cons (Quiver.reverse e.hom)).comp v ∧
          (∀ g ∈ v.arrowList, P.edgeOf g ≠ P.edgeOf e) := by
  intro y t
  induction t with
  | nil => intro _ h; exact absurd h hnot
  | cons p f ih =>
    intro ht hreach
    by_cases hc : P.edgeOf (Quiver.Total.mk _ _ f) = P.edgeOf e
    · -- the last arrow of `t` has the code of `e`, so by `hsep` it is `e` or `e⁻¹`
      rcases hsep (Quiver.Total.mk _ _ f) e hc with h | h
      · -- it is `e`, so `y = e.right` and `hreach` contradicts `hnot`
        exact absurd (congrArg Quiver.Total.right h ▸ hreach) hnot
      · -- it is `e⁻¹`: `t = p ∗ e⁻¹ ∗ nil`
        cases h
        exact ⟨p, Quiver.Path.nil, by rw [Quiver.Path.comp_nil],
          by intro g hg; simp at hg⟩
    · -- the last arrow of `t` is an arrow of `Γ ∖ e`
      obtain ⟨u, v, huv, hv⟩ := ih (isReduced_cons_iff.mp ht).1 (hstep f hc hreach)
      refine ⟨u, v.cons f, ?_, ?_⟩
      · rw [huv, Quiver.Path.comp_cons]
      · intro g hg
        rw [Quiver.Path.arrowList_cons] at hg
        rcases List.mem_append.mp hg with hg | hg
        · exact hv g hg
        · simp only [List.mem_singleton] at hg
          subst hg
          exact hc

-- WARNING (for the reader of `BridgeSide.lean`).
--
-- As `Reach` is currently defined and elaborated, its `DelV`/`keepCode` decoration is erased by
-- instance search: `#print Work.ORLocInd.Howie.Reach` shows the body
-- `Nonempty (@Quiver.Path V inst (Quiver.Total.left e) y)`, reachability in `Γ` itself.  In
-- particular `⟨e.hom.toPath⟩ : Reach P e e.right` for every arrow `e`, so the hypothesis `hnot`
-- below can never be satisfied and the statement below is true for trivial reasons (and so are
-- `BridgeSide.not_reach_right_of_bridge` and `BridgeSide.reach_of_reach_of_delArrow`).  The proof
-- below is nevertheless a proof of the intended mathematics: its only use of the meaning of
-- `Reach` is `BridgeSide.reach_of_reach_of_code_ne`, which is stated with an ambient arrow and an
-- explicit "code ≠ code of `e`" hypothesis — exactly the step one needs for the pinned reading as
-- well.  So if `Reach` is redefined with the instance pinned (`Defs2.dpath`, i.e. the body of
-- `ReachDelV` above), this proof still compiles, and it then proves the intended bridge
-- decomposition; `bridge_decomp_delV` above is a self-contained proof of that statement.

theorem bridge_decomp {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Work.ORLocInd.Howie.Presentation V) (hsep : P.CodeSeparates) (e : Quiver.Total V)
    (hnot : ¬ Work.ORLocInd.Howie.Reach P e e.right)
    {y : V} (t : Quiver.Path (e.right : V) y) (ht : t.IsReduced)
    (hreach : Work.ORLocInd.Howie.Reach P e y) :
    ∃ (u : Quiver.Path (e.right : V) (e.right : V)) (v : Quiver.Path (e.left : V) y),
      t = (u.cons (Quiver.reverse e.hom)).comp v ∧
        (∀ g ∈ v.arrowList, P.edgeOf g ≠ P.edgeOf e) :=
  bridge_decomp_of_step P hsep e
    (fun f hf h => Work.ORLocInd.Howie.reach_of_reach_of_code_ne P e f hf h) hnot t ht hreach

end Work.ORLocInd.Howie
