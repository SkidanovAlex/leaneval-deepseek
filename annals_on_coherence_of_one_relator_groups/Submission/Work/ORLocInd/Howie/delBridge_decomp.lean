/-
# The bridge decomposition of a path, for the *honest* (ambient) deletion

This is the companion of `Submission/Work/ORLocInd/Howie/bridge_decomp.lean`, stated with the
ambient notions `DelReach`/`Avoids` of `DelReach.lean` rather than with the `Reach` of
`BridgeSide.lean` (whose `DelV`/`keepCode` decoration is erased by instance search and makes the
hypothesis vacuous; see the header of `bridge_decomp.lean`).

Fix a presentation `P` with `P.CodeSeparates`, an arrow `e : e.left ⟶ e.right` of `Γ`, and let
`c := P.edgeOf e` be the code of the unoriented edge `{e, e⁻¹}`.  Say that `y` is `e`-reachable when
`DelReach P e y`, i.e. when `y` is joined to `e.left` by a path of `Γ` avoiding the code `c` — a path
of `Γ ∖ e`.  If `e` is a *bridge of `Γ ∖ e`* (`hnot : ¬ DelReach P e e.right`: `e.left` and
`e.right` lie in different components of `Γ ∖ e`) and `y` is `e`-reachable, then every reduced path
`t : e.right → y` has a very restricted shape: read from its end, all of it after its *last* arrow of
code `c` avoids `c`, and that last arrow is `e⁻¹`:

    t = u ∗ e⁻¹ ∗ v      with `v` avoiding the code of `e`.

The proof is the induction on `t` carried out below.  Let `f` be the last arrow of `t`,
`t = p.cons f`:

* if the code of `f` is not `c`, then `f` is an arrow of `Γ ∖ e`, so `y` is `e`-reachable iff the
  intermediate vertex is (`delReach_of_delArrow`), and the induction hypothesis applies to `p`;
* if the code of `f` is `c`, then by `CodeSeparates` either `f = e` or `f = e⁻¹`.  If `f = e` then
  `y = e.right`, and `e`-reachability of `y` would make `e.right` `e`-reachable, contradicting the
  bridge hypothesis.  Hence `f = e⁻¹`, the initial segment `p` of `t` is a closed path at `e.right`,
  and `v` can be taken empty.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.DelReach
import Submission.Work.ORLocInd.Howie.Relator
import Submission.Work.ORLocInd.Howie.bridge_decomp
import Submission.Work.ORLocInd.Howie.isReduced_cons_iff

set_option autoImplicit false
set_option linter.ambiguousOpen false

namespace Work.ORLocInd.Howie

open Quiver

theorem delBridge_decomp {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Work.ORLocInd.Howie.Presentation V) (hsep : P.CodeSeparates) (e : Quiver.Total V)
    (hnot : ¬ Work.ORLocInd.Howie.DelReach P e e.right) :
    ∀ {y : V} (t : Quiver.Path e.right y), t.IsReduced → Work.ORLocInd.Howie.DelReach P e y →
      ∃ (u : Quiver.Path e.right e.right) (v : Quiver.Path e.left y),
        t = (u.cons (Quiver.reverse e.hom)).comp v ∧ Work.ORLocInd.Howie.Avoids P e v := by
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
        exact ⟨p, Quiver.Path.nil, by rw [Quiver.Path.comp_nil], avoids_nil P e⟩
    · -- the last arrow of `t` is an arrow of `Γ ∖ e`
      obtain ⟨u, v, huv, hv⟩ :=
        ih (isReduced_cons_iff.mp ht).1 (delReach_of_delArrow P e f hc hreach)
      refine ⟨u, v.cons f, ?_, ?_⟩
      · rw [huv, Quiver.Path.comp_cons]
      · exact (avoids_cons_iff P e v f).mpr ⟨hv, hc⟩

end Work.ORLocInd.Howie
