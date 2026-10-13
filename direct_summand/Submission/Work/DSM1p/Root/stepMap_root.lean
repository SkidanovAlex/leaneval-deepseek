import Mathlib
import Submission.Work.DSM1p.Basic
import Submission.Work.DSM1p.Root.stepIter_root

namespace Work.DSM1p.Root

open Work.DSM1p

/-- Casting a ring hom into the root tower along an equality of the target index, then applying
it, is the same as applying and then casting the value. -/
lemma eqrec_rootTower_ringHom_apply (R : Type*) [CommRing R] (p : ℕ) (a : R) {i i' j : ℕ}
    (e : i' = j)
    (f : RootTower R p a i →+* RootTower R p a i') (x : RootTower R p a i) :
    (e ▸ f) x = e ▸ (f x) := by
  cases e
  rfl

/-- Casting a power in the root tower along an equality of the index. -/
lemma eqrec_rootTower_pow (R : Type*) [CommRing R] (p : ℕ) (a : R) {i j : ℕ} (e : i = j)
    (x : RootTower R p a i) (n : ℕ) :
    e ▸ (x ^ n) = (e ▸ x) ^ n := by
  cases e
  rfl

/-- Casting the adjoined root of the root tower along an equality of the index. -/
lemma eqrec_rootTower_root (R : Type*) [CommRing R] (p : ℕ) (a : R) {i j : ℕ} (e : i = j) :
    e ▸ (RootTower.root R p a i) = RootTower.root R p a j := by
  cases e
  rfl

theorem stepMap_root (R : Type*) [CommRing R] (p : ℕ) (a : R) (i j : ℕ) (h : i ≤ j) :
    Work.DSM1p.RootTower.stepMap R p a i j h (Work.DSM1p.RootTower.root R p a i) =
      Work.DSM1p.RootTower.root R p a j ^ p ^ (j - i) := by
  have hsm : Work.DSM1p.RootTower.stepMap R p a i j h =
      (Nat.add_sub_cancel' h ▸ Work.DSM1p.RootTower.stepIter R p a i (j - i)) := rfl
  rw [hsm, eqrec_rootTower_ringHom_apply, stepIter_root, eqrec_rootTower_pow,
    eqrec_rootTower_root]

end Work.DSM1p.Root
