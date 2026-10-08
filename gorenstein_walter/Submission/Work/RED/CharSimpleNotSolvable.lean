import Mathlib
import Submission.Work.RED.Basic

/-!
# `CharSimpleNotSolvable`

A finite nonabelian group all of whose characteristic subgroups are trivial or the whole
group is not solvable.

The argument is short: the commutator subgroup `⁅K, K⁆` is characteristic, so by hypothesis
it is either `⊥` or `⊤`.

* If `⁅K, K⁆ = ⊥`, then `K` is commutative (`commutator_eq_bot_iff`), contradicting `hnab`.
* If `⁅K, K⁆ = ⊤`, then `K` is *perfect*.  A nontrivial perfect group is not solvable
  (`Group.IsPerfect.not_isSolvable`), and `K` is nontrivial because a trivial group is
  commutative.

Note that `Finite K` is not actually needed for the argument; the group `K` being finite is
part of the intended application.
-/

set_option linter.style.haveILetI false

namespace Work.RED

theorem CharSimpleNotSolvable (K : Type*) [Group K] [Finite K]
    (hchar : ∀ H : Subgroup K, H.Characteristic → H = ⊥ ∨ H = ⊤)
    (hnab : ¬ IsMulCommutative K) : ¬ Group.IsSolvable K := by
  intro hsol
  -- `K` is nontrivial: a trivial group is commutative.
  haveI hnt : Nontrivial K := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hs
    haveI := hs
    exact hnab (IsMulCommutative.of_comm fun a b => Subsingleton.elim _ _)
  -- The commutator subgroup is characteristic, hence either trivial or everything.
  rcases hchar (commutator K) inferInstance with h | h
  · -- `⁅K, K⁆ = ⊥` forces `K` to be commutative.
    exact hnab ((commutator_eq_bot_iff K).mp h)
  · -- `⁅K, K⁆ = ⊤` makes `K` perfect, hence (being nontrivial) not solvable.
    haveI : Group.IsPerfect K := ⟨h⟩
    exact Group.IsPerfect.not_isSolvable K hsol

end Work.RED
