import Mathlib
import Submission.Work.ORHughesFree.Tree.order_defs
import Submission.Work.ORHughesFree.Tree.edge
import Submission.Work.ORHughesFree.Tree.dmOneStep_transGen
import Submission.Work.ORHughesFree.Tree.acc_dmOneStep_of_acc

/-!
# Well-foundedness of the order on finite rooted trees

The tree order is the Dershowitz–Manna order on the multiset of children, and the children of a tree
have strictly fewer edges.  Hence, by induction on the number of edges, it suffices to know that a
multiset all of whose entries are accessible is accessible for the one-step relation; the
Dershowitz–Manna order is then transferred back to the tree order.
-/

namespace Work.ORHughesFree.Tree

open Work.ORHughesFree

/-- If the family `M` is accessible for the one-step relation, then every tree with family `M` is
accessible for the tree order. -/
theorem acc_of_acc_dmOneStep (M : Multiset Tree) (h : Acc (dmOneStep lt) M) :
    ∀ y : Tree, fam y = M → Acc lt y := by
  have main : ∀ (M : Multiset Tree), Acc (dmOneStep lt) M →
      ∀ M', (M' = M ∨ Relation.TransGen (dmOneStep lt) M' M) →
        ∀ y : Tree, fam y = M' → Acc lt y := by
    intro M hM
    induction hM with
    | intro M hstep ih =>
      intro M' hle y hy
      refine Acc.intro y ?_
      intro z hz
      have hzM : Relation.TransGen (dmOneStep lt) (fam z) M := by
        have h1 : Relation.TransGen (dmOneStep lt) (fam z) M' :=
          dmOneStep_transGen (by rw [← hy]; exact (lt_iff_dmLT z y).mp hz)
        rcases hle with rfl | hle
        · exact h1
        · exact h1.trans hle
      obtain ⟨M₀, hrefl, hstep'⟩ := Relation.TransGen.tail'_iff.mp hzM
      refine ih M₀ hstep' (fam z) ?_ z rfl
      rcases (Relation.reflTransGen_iff_eq_or_transGen.mp hrefl) with h | h
      · exact Or.inl h.symm
      · exact Or.inr h
  exact main M h M (Or.inl rfl)

/-- The strict order on finite rooted trees is well-founded. -/
theorem lt_wf : WellFounded lt := by
  apply WellFounded.intro
  intro x
  have key : ∀ n, ∀ x : Tree, edge x = n → Acc lt x := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hx
      refine acc_of_acc_dmOneStep (fam x) (acc_dmOneStep_of_acc (M := fam x) ?_) x rfl
      intro a ha
      exact ih (edge a) (by rw [← hx]; exact edge_lt_of_mem_fam ha) a rfl
  exact key (edge x) x rfl

end Work.ORHughesFree.Tree
