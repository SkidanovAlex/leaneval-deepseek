import Mathlib
import Submission.Work.ORBassSerre.Action.Structure.pathWord_of_generator
import Submission.Work.ORBassSerre.Action.Structure.exists_parent_chain

namespace Work.ORBassSerre.Action.Structure

open Quiver

/-- For every vertex orbit `A` of the quotient graph there is a path word from the root orbit to
`A` whose element in `Γ` is trivial for every presentation datum `D`.  The walk follows the parent
chain of `A` (`exists_parent_chain`), each step is a step along a *tree* edge orbit, and all
letters are trivial; hence `PathWord.elt_eq_one_of_triv` applies. -/
theorem exists_pathWord_root_to {G : Type*} {V : Type*}
    [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V] [MulAction G V]
    [Work.ORBassSerre.GraphAction G V]
    {d : Work.ORBassSerre.Action.Structure.TreeDatum G V}
    [Fintype (Work.ORBassSerre.orbitV G V)] [Fintype (Work.ORBassSerre.orbitE G V)]
    [Nonempty (Work.ORBassSerre.orbitE G V)]
    (A : Work.ORBassSerre.orbitV G V) :
    ∃ W : Work.ORBassSerre.Action.Structure.TreeDatum.PathWord d,
      W.orb 0 = d.root ∧ W.orb W.len = A ∧
        ∀ D : d.PresData, W.elt D = 1 := by
  classical
  obtain ⟨c, n, hc0, hcn, hne, hpar⟩ := exists_parent_chain (G := G) (V := V) d A
  -- The edge orbit of the `k`-th step: the parent edge of `c (k+1)`, for `k < n`.
  let stepE : ℕ → Work.ORBassSerre.orbitE G V :=
    fun k => if h : k < n then Quotient.mk'' (d.parArrow (c (k + 1)) (hne k h))
             else Classical.arbitrary (Work.ORBassSerre.orbitE G V)
  have hstepE : ∀ k (hk : k < n),
      stepE k = Quotient.mk'' (d.parArrow (c (k + 1)) (hne k hk)) :=
    fun k hk => by simp only [stepE, dif_pos hk]
  let W : d.PathWord :=
    { len := n
      orb := c
      letter := fun k => ⟨c k, 1⟩
      letter_orbit := fun k _ => rfl
      stepE := stepE
      stepB := fun _ => true
      step_src := fun k hk => by
        show TreeDatum.moveSrc (stepE k) true = c k
        rw [TreeDatum.moveSrc_true, hstepE k hk, d.srcE_parArrow (hne k hk), hpar k hk]
      step_tgt := fun k hk => by
        show TreeDatum.moveTgt (stepE k) true = c (k + 1)
        rw [TreeDatum.moveTgt_true, hstepE k hk, d.tgtE_parArrow (hne k hk)] }
  refine ⟨W, ?_, ?_, ?_⟩
  · show c 0 = d.root
    exact hc0
  · show c n = A
    exact hcn
  · intro D
    refine TreeDatum.PathWord.elt_eq_one_of_triv (d := d) D W ?_ ?_
    · intro k hk
      have hk' : k < n := hk
      show d.IsTreeEdge (stepE k)
      rw [hstepE k hk']
      exact d.isTreeEdge_mk (hne k hk')
    · intro k hk
      rfl

end Work.ORBassSerre.Action.Structure
