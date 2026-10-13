import Mathlib
import Submission.Work.DSM1p.Family
import Submission.Work.DSM1p.Family.stepMap_root

namespace Work.DSM1p.Family

open Work.DSM1p

lemma eqrec_famTower_algebraMap' (R : Type*) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R)
    {i j : ℕ} (e : i = j) (r : R) :
    e ▸ (algebraMap R (FamTower R p x i) r) = algebraMap R (FamTower R p x j) r := by
  cases e; rfl

lemma stepIter_algebraMap' (R : Type*) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R)
    (m k : ℕ) (r : R) :
    FamTower.stepIter R p x m k (algebraMap R (FamTower R p x m) r) =
      algebraMap R (FamTower R p x (m + k)) r := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show FamTower.step R p x (m + k)
        (FamTower.stepIter R p x m k (algebraMap R (FamTower R p x m) r)) =
      algebraMap R (FamTower R p x (m + (k + 1))) r
    rw [ih]
    simp only [FamTower.step]
    rw [show algebraMap R (FamTower R p x (m + k)) r =
          Ideal.Quotient.mk _ (MvPolynomial.C r) from rfl,
      Ideal.Quotient.lift_mk, MvPolynomial.eval₂Hom_C]
    rfl

theorem stepMap_algebraMap (R : Type*) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R) (m n : ℕ)
    (h : m ≤ n) (r : R) :
    Work.DSM1p.FamTower.stepMap R p x m n h (algebraMap R (Work.DSM1p.FamTower R p x m) r) =
      algebraMap R (Work.DSM1p.FamTower R p x n) r := by
  rw [show FamTower.stepMap R p x m n h =
      (Nat.add_sub_cancel' h ▸ FamTower.stepIter R p x m (n - m)) from rfl]
  rw [eqrec_famTower_ringHom_apply, stepIter_algebraMap']
  exact eqrec_famTower_algebraMap' R p x (Nat.add_sub_cancel' h) r

end Work.DSM1p.Family
