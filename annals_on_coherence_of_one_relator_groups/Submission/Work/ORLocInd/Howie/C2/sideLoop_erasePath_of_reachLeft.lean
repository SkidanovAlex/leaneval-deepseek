/-
# A loop of the kept subgraph starting in the `ReachLeft` side runs inside that side

Let `P` be a graph presentation, `e` an arrow of `Γ` and `K` a subgraph of `Γ` all of whose arrows
avoid the code of `e`, i.e. survive the deletion of the unoriented edge `{e, e⁻¹}`
(`hK : ∀ g, K.pred g → P.edgeOf g ≠ P.edgeOf e`).

If `x` lies in the `ReachLeft` side of the bridge `e` — that is, `x` is joined to `e.left` by a path
of `Γ ∖ e` (`ReachLeft P e x`) — then every vertex of every path of the subgraph `K` starting at `x`
lies again in that side.  Consequently, for a loop `β` of the subgraph `K` based at `x`, the erasure
`DelV.erasePath K x β` of `β` to `Γ` is a closed path *running inside the side*,
`SideLoop P e (ReachLeft P e) (DelV.erasePath K x β)`; this is the condition under which a labelling
restricted to the side can be evaluated on `β` (`pathSum_restrictSide`).

The proof is the obvious induction along the path: an arrow `f : a ⟶ b` of `Γ ∖ e` extends an
avoiding path to `b` by `f`, and an avoiding path to `a` by the reverse of `f`, so membership in the
side is propagated one arrow at a time; the code condition on the arrows of the erasure of `β` is
exactly `hK`.

## A formalisation remark

`DelV K` is a `def` equal to `V` (`Defs2.DelV`), so an arrow of the erased path has to be matched
against the `Quiver` instance of `DelV K` while `DelV.erasePath` returns a path of `V`; the two
instances are equal only up to unfolding of `DelV`.  As elsewhere in this development (`Delete.lean`,
`C2/*`), we therefore set `backward.isDefEq.respectTransparency false` while rewriting with the
`rfl`-lemmas `DelV.erasePath_nil` / `DelV.erasePath_cons`.  The option is restored immediately after,
so that the elaboration of the final statement is not affected by it.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Case2Bridge
import Submission.Work.ORLocInd.Howie.DelReach

set_option linter.unusedVariables false
set_option linter.ambiguousOpen false
set_option backward.isDefEq.respectTransparency false

namespace Work.ORLocInd.Howie.C2

open Quiver

/-- The induction step of `sideLoop_erasePath_of_reachLeft`, stated for a path of the kept subgraph
`K` starting at a vertex `x` of the `ReachLeft` side and ending anywhere: the endpoint stays in the
side (`ReachLeft P e y`) and every arrow of the erasure of the path runs inside the side.

The endpoint statement is needed in the induction, because the last arrow of the path has the
endpoint of its prefix as its source. -/
theorem sideLoop_erasePath_aux {V : Type*} [Quiver V]
    [Quiver.HasInvolutiveReverse V] (P : Work.ORLocInd.Howie.Presentation V) (e : Quiver.Total V)
    (K : Work.ORLocInd.Howie.Keep V)
    (hK : ∀ g : Quiver.Total V, K.pred g → P.edgeOf g ≠ P.edgeOf e)
    {x : V} (hx : Work.ORLocInd.Howie.ReachLeft P e x) :
    ∀ {y : V} (β : Work.ORLocInd.Howie.dpath K x y),
      Work.ORLocInd.Howie.ReachLeft P e y ∧
        ∀ g ∈ (Work.ORLocInd.Howie.DelV.erasePath K x β).arrowList,
          Work.ORLocInd.Howie.ReachLeft P e g.left ∧
            Work.ORLocInd.Howie.ReachLeft P e g.right ∧
              P.edgeOf g ≠ P.edgeOf e := by
  intro y β
  induction β with
  | nil =>
      -- the empty path: the endpoint is `x` itself, and there is no arrow to check
      refine ⟨hx, ?_⟩
      intro g hg
      rw [Work.ORLocInd.Howie.DelV.erasePath_nil, Quiver.Path.arrowList_nil] at hg
      exact absurd hg List.not_mem_nil
  | cons p f ih =>
      -- `β = p.cons f`: the last arrow `f : a ⟶ b` of `K` avoids the code of `e`, so it leads from
      -- the side of the endpoint `a` of `p` (induction hypothesis) to the side of `b`
      obtain ⟨hy, hall⟩ := ih
      have hf : P.edgeOf (Quiver.Total.mk _ _ f.1) ≠ P.edgeOf e := hK _ f.2
      have hnew : Work.ORLocInd.Howie.ReachLeft P e (Quiver.Total.mk _ _ f.1).right :=
        Work.ORLocInd.Howie.delReach_of_delArrow' P e f.1 hf hy
      refine ⟨hnew, ?_⟩
      intro g hg
      rw [Work.ORLocInd.Howie.DelV.erasePath_cons, Quiver.Path.arrowList_cons] at hg
      rcases List.mem_append.mp hg with hg | hg
      · exact hall g hg
      · simp only [List.mem_singleton] at hg
        subst hg
        exact ⟨hy, hnew, hf⟩

set_option backward.isDefEq.respectTransparency true

theorem sideLoop_erasePath_of_reachLeft {V : Type*} [Quiver V]
    [Quiver.HasInvolutiveReverse V] (P : Work.ORLocInd.Howie.Presentation V) (e : Quiver.Total V)
    (K : Work.ORLocInd.Howie.Keep V)
    (hK : ∀ g : Quiver.Total V, K.pred g → P.edgeOf g ≠ P.edgeOf e)
    {x : V} (β : Work.ORLocInd.Howie.dpath K x x)
    (hx : Work.ORLocInd.Howie.ReachLeft P e x) :
    Work.ORLocInd.Howie.SideLoop P e (Work.ORLocInd.Howie.ReachLeft P e)
      (Work.ORLocInd.Howie.DelV.erasePath K x β) :=
  (sideLoop_erasePath_aux P e K hK hx β).2

end Work.ORLocInd.Howie.C2
