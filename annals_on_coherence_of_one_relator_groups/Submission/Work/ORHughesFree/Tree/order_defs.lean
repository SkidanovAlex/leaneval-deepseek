import Mathlib
import Submission.Work.ORHughesFree.Tree
import Submission.Work.ORHughesFree.Tree.edge

/-!
# The well-order on finite rooted trees

Following [DHS04, Lemma 3.3] (see also [JZLA20, §4.1]) we put a well-order on the finite rooted
trees.  The order is the *recursive multiset ordering*: `x < y` iff the multiset `fam x` of
children of `x` is below `fam y` in the Dershowitz–Manna (multiset) ordering `dmLT`, in which the
comparison of the elements is again the order `<` on trees.

Because the order is defined recursively (children have strictly fewer edges, `Tree.edge`), we set
it up by well-founded recursion along the number of edges.  This file contains the definitions and
the unfolding lemma `lt_iff`; all properties of the order are proved in the files that import it.
-/

namespace Work.ORHughesFree.Tree

open Work.ORHughesFree

/-- The **Dershowitz–Manna multiset ordering** relative to a relation `r`: `M` is below `N` if `N`
can be obtained from `M` by adding some nonempty multiset `Z` and replacing the elements of some
multiset `Y` by larger ones. -/
def dmLT {α : Type*} (r : α → α → Prop) (M N : Multiset α) : Prop :=
  ∃ X Y Z : Multiset α, Z ≠ 0 ∧ M = X + Y ∧ N = X + Z ∧ ∀ a ∈ Y, ∃ b ∈ Z, r a b

/-- The one-step Dershowitz–Manna relation among families: `N` is obtained from `M` by replacing
the elements of some multiset `Y ⊆ M` by a single strictly larger element `a`. -/
def dmOneStep (r : Tree → Tree → Prop) (M N : Multiset Tree) : Prop :=
  ∃ X Y a, M = X + Y ∧ N = X + {a} ∧ ∀ y ∈ Y, r y a

/-- The **strict order on finite rooted trees** of [DHS04, Lemma 3.3]: `x < y` iff `fam x` is
below `fam y` in the Dershowitz–Manna order (recursively).  Defined by well-founded recursion on
the number of edges of the first argument. -/
noncomputable def lt : Tree → Tree → Prop :=
  WellFounded.fix (measure (fun x : Tree => edge x)).wf (fun x ih y =>
    ∃ (X Y Z : Multiset Tree) (h1 : fam x = X + Y) (h2 : fam y = X + Z),
      Z ≠ 0 ∧ ∀ a, ∀ ha : a ∈ Y, ∃ b, b ∈ Z ∧
        ih a (edge_lt_of_mem_fam (by rw [h1]; exact Multiset.mem_add.mpr (Or.inr ha))) b)

/-- The unfolding of the recursive definition of the tree order: `x < y` iff `fam x` is below
`fam y` in the Dershowitz–Manna order for the (same) tree order on the elements. -/
theorem lt_iff (x y : Tree) :
    lt x y ↔ ∃ X Y Z : Multiset Tree, Z ≠ 0 ∧ fam x = X + Y ∧ fam y = X + Z ∧
      ∀ a, a ∈ Y → ∃ b, b ∈ Z ∧ lt a b := by
  unfold lt
  rw [WellFounded.fix_eq]
  constructor
  · rintro ⟨X, Y, Z, h1, h2, hZ, h⟩
    exact ⟨X, Y, Z, hZ, h1, h2, h⟩
  · rintro ⟨X, Y, Z, hZ, h1, h2, h⟩
    exact ⟨X, Y, Z, h1, h2, hZ, h⟩

/-- The tree order is the Dershowitz–Manna order on the multiset of children. -/
theorem lt_iff_dmLT (x y : Tree) : lt x y ↔ dmLT lt (fam x) (fam y) := lt_iff x y

/-- The **weak order** on finite rooted trees: `x ≤ y` iff `x = y` or `x < y`. -/
def le (x y : Tree) : Prop := x = y ∨ lt x y

/-- The **multiset product** of two families: `M ⊗ N = {a + b | a ∈ M, b ∈ N}`.  It is the
operation on families induced by multiplication of trees: `fam (x * y) = fam x ⊗ fam y`. -/
noncomputable def mulMs (M N : Multiset Tree) : Multiset Tree :=
  M.bind (fun a => N.map (fun b => a + b))

end Work.ORHughesFree.Tree
