import Mathlib
import Submission.Work.ORHughesFree.Tree.order_alg
import Submission.Work.ORHughesFree.Tree.order_defs
import Submission.Work.ORHughesFree.Tree.fam_basic
import Submission.Work.ORHughesFree.Tree.fam_exp
import Submission.Work.ORHughesFree.Tree.mul_one

namespace Work.ORHughesFree.Rat

open Work.ORHughesFree

/-!
# Elementary order facts for the finite rooted trees

`Work.ORHughesFree.Tree` carries the recursive Dershowitz–Manna order `lt` of [DHS04, Lemma 3.3]
(`Submission/Work/ORHughesFree/Tree/order_defs.lean`) together with the semiring operations
`+`, `*`, with `0` the one-vertex tree and `1 = exp 0` the one-edge tree.

Here we collect the facts needed when the finite rooted trees are used as the codomain of the
complexity map of [JZLA20, §4.2]:

* `1` is the least non-zero tree;
* `*` is monotone in its second argument on non-zero elements: `a ≤ a * b`;
* this monotonicity is strict: `a * b = a` forces `b = 1` when `a` and `b` are non-zero.

All three are immediate consequences of the compatibility of `le` with the semiring operations
(`Tree.le_mul`, `Tree.le_mul_eq`) and of the fact that nothing non-zero lies strictly below `1`.
-/

/-- The family of the one-edge tree `1 = exp 0` is the singleton `{0}`. -/
private theorem fam_one_tree : Tree.fam (1 : Tree) = ({0} : Multiset Tree) := Tree.fam_exp 0

/-- The one-edge tree is not the one-vertex tree. -/
private theorem one_tree_ne_zero : (1 : Tree) ≠ 0 := by
  intro h
  have hf : Tree.fam (1 : Tree) = Tree.fam (0 : Tree) := by rw [h]
  rw [fam_one_tree, Tree.fam_zero] at hf
  exact Multiset.singleton_ne_zero (0 : Tree) hf

/-- **Nothing non-zero is strictly below the one-edge tree.**

If `b ≠ 0` and `b < 1`, unfolding `lt` as the Dershowitz–Manna order on families
(`Tree.lt_iff_dmLT`) and using `fam 1 = {0}`, the witnessing decomposition `{0} = X + Z` with
`Z ≠ 0` forces `X = 0` and `Z = {0}`.  Then every element of `Y = fam b` must be strictly below
`0`, contradicting `Tree.not_lt_zero`; and `b ≠ 0` supplies such an element. -/
private theorem not_lt_one_of_ne_zero {b : Tree} (hb : b ≠ 0) : ¬ Tree.lt b 1 := by
  intro h
  have hm := (Tree.lt_iff_dmLT b 1).mp h
  rw [fam_one_tree] at hm
  obtain ⟨X, Y, Z, hZ, hM, hN, hYZ⟩ := hm
  -- `{0} = X + Z` with `Z ≠ 0` forces `X = 0` and `Z = {0}`.
  have hcard : (X + Z).card = 1 := by rw [← hN, Multiset.card_singleton]
  have hZpos : 0 < Z.card := Multiset.card_pos.mpr hZ
  have hXcard : X.card = 0 := by
    have h := Multiset.card_add X Z
    omega
  have hX0 : X = 0 := Multiset.card_eq_zero.mp hXcard
  have hZsing : Z = ({0} : Multiset Tree) := by
    rw [hX0, Multiset.zero_add] at hN
    exact hN.symm
  have hYm : Y = Tree.fam b := by
    rw [hX0, Multiset.zero_add] at hM
    exact hM.symm
  -- every element of `Y = fam b` would have to be strictly below `0`
  have hfam : Tree.fam b ≠ 0 := Tree.ne_zero_iff_fam_ne_zero.mp hb
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hfam
  have haY : a ∈ Y := by rw [hYm]; exact ha
  obtain ⟨c, hcZ, hac⟩ := hYZ a haY
  have hc0 : c = 0 := by
    rw [hZsing] at hcZ
    exact Multiset.mem_singleton.mp hcZ
  rw [hc0] at hac
  exact Tree.not_lt_zero hac

/-- **The one-edge tree is the least non-zero tree.**  By totality of the order it suffices to
rule out `b < 1`, which is `not_lt_one_of_ne_zero`. -/
private theorem le_one_of_ne_zero {b : Tree} (hb : b ≠ 0) : Tree.le 1 b := by
  rcases Tree.le_total (1 : Tree) b with h | h
  · exact h
  · rcases h with h | h
    · exact Or.inl h.symm
    · exact absurd h (not_lt_one_of_ne_zero hb)

/-- **`a ≤ a * b` for non-zero `b`**: multiply the reflexive `a ≤ a` by `1 ≤ b` and use
`a * 1 = a`. -/
private theorem le_self_mul {a b : Tree} (hb : b ≠ 0) : Tree.le a (a * b) := by
  have h := Tree.le_mul (Tree.le_refl a) (le_one_of_ne_zero hb)
  rwa [Tree.mul_one a] at h

/-- **`a * b = a` if and only if `b = 1`, for non-zero `a` and `b`**: strict cancellation for `*`
(`Tree.le_mul_eq`) applied to the monotone pair `a ≤ a`, `1 ≤ b`. -/
private theorem mul_eq_self_iff {a b : Tree} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b = a ↔ b = 1) := by
  have h1 : Tree.le (1 : Tree) b := le_one_of_ne_zero hb
  have hkey := Tree.le_mul_eq (a := a) (b := a) (c := (1 : Tree)) (d := b)
    ha one_tree_ne_zero (Tree.le_refl a) h1
  -- `hkey : a * 1 = a * b ↔ a = a ∧ 1 = b`
  constructor
  · intro h
    have h2 : a * 1 = a * b := by rw [Tree.mul_one a]; exact h.symm
    exact ((hkey.mp h2).2).symm
  · intro h
    rw [h, Tree.mul_one a]

theorem treeOrderFacts :
    (∀ b : Work.ORHughesFree.Tree, b ≠ 0 → Work.ORHughesFree.Tree.le 1 b) ∧
    (∀ a b : Work.ORHughesFree.Tree, a ≠ 0 → b ≠ 0 →
      Work.ORHughesFree.Tree.le a (a * b)) ∧
    (∀ a b : Work.ORHughesFree.Tree, a ≠ 0 → b ≠ 0 → (a * b = a ↔ b = 1)) :=
  ⟨fun _ hb => le_one_of_ne_zero hb,
   fun _ _ _ hb => le_self_mul hb,
   fun _ _ ha hb => mul_eq_self_iff ha hb⟩

end Work.ORHughesFree.Rat
