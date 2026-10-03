/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The concrete DHS04 tree semiring

Builds the model `RootedTrees Tree` of [JZLA20, §4.1]: the finite rooted trees with their
root-identification addition, their product, the operation `exp`, the family map `fam`, and the
well-order of [DHS04, Lemma 3.3] satisfying [JZLA20, Lemma 4.1].
-/
import Mathlib
import Submission.Work.ORHughesFree.TreeAlgebra
import Submission.Work.ORHughesFree.Tree.exists_tree_order

set_option autoImplicit false

universe u

namespace Work.ORHughesFree

/-- A well-order on the concrete trees satisfying [JZLA20, Lemma 4.1]. -/
noncomputable def treeLe : Tree → Tree → Prop := Classical.choose Tree.exists_tree_order

theorem treeLe_spec :
    (∀ x : Tree, treeLe x x) ∧
    (∀ {x y : Tree}, treeLe x y → treeLe y x → x = y) ∧
    (∀ {x y z : Tree}, treeLe x y → treeLe y z → treeLe x z) ∧
    (∀ x y : Tree, treeLe x y ∨ treeLe y x) ∧
    WellFounded (fun x y : Tree => treeLe x y ∧ x ≠ y) ∧
    (∀ {a b c d : Tree}, treeLe a b → treeLe c d → treeLe (a + c) (b + d)) ∧
    (∀ {a b c d : Tree}, treeLe a b → treeLe c d → (a + c = b + d ↔ a = b ∧ c = d)) ∧
    (∀ {a b c d : Tree}, treeLe a b → treeLe c d → treeLe (a * c) (b * d)) ∧
    (∀ {a b c d : Tree}, a ≠ 0 → c ≠ 0 → treeLe a b → treeLe c d →
      (a * c = b * d ↔ a = b ∧ c = d)) :=
  Classical.choose_spec Tree.exists_tree_order

/-- **The concrete DHS04 tree semiring**: the finite rooted trees with the structure of
[JZLA20, §4.1]. -/
noncomputable def rootedTrees : RootedTrees Tree where
  exp := Tree.exp
  exp_zero := rfl
  exp_add := Tree.exp_add
  fam := Tree.fam
  fam_exp := Tree.fam_exp
  sum_fam := Tree.sum_fam
  mul_eq := Tree.mul_eq
  le := treeLe
  le_refl := treeLe_spec.1
  le_antisymm := treeLe_spec.2.1
  le_trans := treeLe_spec.2.2.1
  le_total := treeLe_spec.2.2.2.1
  le_wf := treeLe_spec.2.2.2.2.1
  add_le_add := treeLe_spec.2.2.2.2.2.1
  add_le_add_eq := treeLe_spec.2.2.2.2.2.2.1
  mul_le_mul := treeLe_spec.2.2.2.2.2.2.2.1
  mul_le_mul_eq := treeLe_spec.2.2.2.2.2.2.2.2

/-- The DHS04 tree semiring of [JZLA20, §4.1] exists. -/
theorem exists_rootedTrees : Nonempty (RootedTrees Tree) :=
  ⟨rootedTrees⟩

end Work.ORHughesFree
