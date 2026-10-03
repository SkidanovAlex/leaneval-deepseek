import Mathlib
import Submission.Work.ORHughesFree.Tree
import Submission.Work.ORHughesFree.Tree.order_defs
import Submission.Work.ORHughesFree.Tree.order_le
import Submission.Work.ORHughesFree.Tree.order_alg

/-!
# The well-order on finite rooted trees ([DHS04, Lemma 3.3], [JZLA20, Lemma 4.1])

The finite rooted trees carry a well-order compatible with `+` and `*`: the recursive
Dershowitz–Manna order on the multiset of children.  This file assembles the existence statement
from the definitions in `order_defs` and the lemmas in `order_le` and `order_alg`.
-/

namespace Work.ORHughesFree.Tree

theorem exists_tree_order :
    ∃ le : Tree → Tree → Prop,
      (∀ x : Tree, le x x) ∧
      (∀ {x y : Tree}, le x y → le y x → x = y) ∧
      (∀ {x y z : Tree}, le x y → le y z → le x z) ∧
      (∀ x y : Tree, le x y ∨ le y x) ∧
      WellFounded (fun x y : Tree => le x y ∧ x ≠ y) ∧
      (∀ {a b c d : Tree}, le a b → le c d → le (a + c) (b + d)) ∧
      (∀ {a b c d : Tree}, le a b → le c d → (a + c = b + d ↔ a = b ∧ c = d)) ∧
      (∀ {a b c d : Tree}, le a b → le c d → le (a * c) (b * d)) ∧
      (∀ {a b c d : Tree}, a ≠ 0 → c ≠ 0 → le a b → le c d →
        (a * c = b * d ↔ a = b ∧ c = d)) := by
  exact ⟨le, le_refl, fun hxy hyx => le_antisymm hxy hyx, fun hxy hyz => le_trans hxy hyz,
    le_total, le_wf, fun hab hcd => le_add hab hcd, fun hab hcd => le_add_eq hab hcd,
    fun hab hcd => le_mul hab hcd, fun ha hc hab hcd => le_mul_eq ha hc hab hcd⟩

end Work.ORHughesFree.Tree
