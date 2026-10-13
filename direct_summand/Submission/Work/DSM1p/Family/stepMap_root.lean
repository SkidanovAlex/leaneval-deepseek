import Mathlib
import Submission.Work.DSM1p.Family

namespace Work.DSM1p.Family

universe u

/-- The iterated transition map sends the `m`-th root to a `p ^ k`-th power of the `(m+k)`-st
root, exactly as in the one-parameter case. -/
theorem stepIter_root (R : Type u) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R)
    (m k : ℕ) (i : Fin d) :
    Work.DSM1p.FamTower.stepIter R p x m k (Work.DSM1p.FamTower.root R p x m i) =
      (Work.DSM1p.FamTower.root R p x (m + k) i) ^ p ^ k := by
  induction k with
  | zero => simp [Work.DSM1p.FamTower.stepIter]
  | succ k ih =>
    rw [Work.DSM1p.FamTower.stepIter, RingHom.comp_apply, ih, map_pow,
      Work.DSM1p.FamTower.step_root, ← pow_mul, ← pow_succ']
    rfl

/-- Casting a ring hom into the family tower along an equality of the target index, then applying
it, is the same as applying and then casting the value. -/
lemma eqrec_famTower_ringHom_apply (R : Type u) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R)
    {i i' j : ℕ} (e : i' = j)
    (f : Work.DSM1p.FamTower R p x i →+* Work.DSM1p.FamTower R p x i')
    (y : Work.DSM1p.FamTower R p x i) :
    (e ▸ f) y = e ▸ (f y) := by
  cases e
  rfl

/-- Casting a power in the family tower along an equality of the index. -/
lemma eqrec_famTower_pow (R : Type u) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R)
    {i j : ℕ} (e : i = j) (y : Work.DSM1p.FamTower R p x i) (n : ℕ) :
    e ▸ (y ^ n) = (e ▸ y) ^ n := by
  cases e
  rfl

/-- Casting the adjoined root of the family tower along an equality of the index. -/
lemma eqrec_famTower_root (R : Type u) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R)
    {i j : ℕ} (e : i = j) (k : Fin d) :
    e ▸ (Work.DSM1p.FamTower.root R p x i k) = Work.DSM1p.FamTower.root R p x j k := by
  cases e
  rfl

theorem stepMap_root (R : Type*) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R) (m n : ℕ)
    (h : m ≤ n) (i : Fin d) :
    Work.DSM1p.FamTower.stepMap R p x m n h (Work.DSM1p.FamTower.root R p x m i) =
      (Work.DSM1p.FamTower.root R p x n i) ^ p ^ (n - m) := by
  have hsm : Work.DSM1p.FamTower.stepMap R p x m n h =
      (Nat.add_sub_cancel' h ▸ Work.DSM1p.FamTower.stepIter R p x m (n - m)) := rfl
  rw [hsm, eqrec_famTower_ringHom_apply, stepIter_root, eqrec_famTower_pow,
    eqrec_famTower_root]

end Work.DSM1p.Family
