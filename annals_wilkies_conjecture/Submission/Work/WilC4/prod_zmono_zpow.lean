import Mathlib
import Submission.Work.WilC4.Defs

namespace Work.WilC4

/-- In a field, a product of integral powers of one fixed nonzero element is the power of the
sum of the exponents. -/
lemma zpow_finset_prod_sum {M : Type} [Field M] {ι : Type} (y : M) (hy : y ≠ 0)
    (g : ι → ℤ) (s : Finset ι) :
    ∏ j ∈ s, y ^ (g j) = y ^ (∑ j ∈ s, g j) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert k s hks ih =>
      rw [Finset.prod_insert hks, Finset.sum_insert hks, ih, zpow_add₀ hy]

/-- The equality of `prod_zmono_zpow`, seen one coordinate at a time. -/
lemma zpow_prod_coord {M : Type} [Field M] {r m : ℕ} (x : Fin r → M) (q : Fin m → Fin r → ℤ)
    (a : Fin m → ℤ) (i : Fin r) (h : x i ≠ 0 ∨ ∀ j, q j i = 0) :
    ∏ j, (x i ^ (q j i)) ^ (a j) = x i ^ (∑ j, a j * q j i) := by
  rcases h with hx0 | hq
  · calc ∏ j, (x i ^ (q j i)) ^ (a j)
        = ∏ j, x i ^ (q j i * a j) := by
            apply Finset.prod_congr rfl
            intro j _
            exact (zpow_mul (x i) (q j i) (a j)).symm
      _ = x i ^ (∑ j, q j i * a j) :=
            zpow_finset_prod_sum (x i) hx0 (fun j => q j i * a j) Finset.univ
      _ = x i ^ (∑ j, a j * q j i) := by
            rw [Finset.sum_congr rfl (fun j _ => mul_comm (q j i) (a j))]
  · simp [hq]

theorem prod_zmono_zpow {M : Type} [Field M] {r m : ℕ} (x : Fin r → M) (q : Fin m → Fin r → ℤ)
    (a : Fin m → ℤ) (hx : ∀ i, x i ≠ 0 ∨ ∀ j, q j i = 0) :
    ∏ j, (Work.WilC4.zmono x (q j)) ^ a j = Work.WilC4.zmono x (fun i => ∑ j, a j * q j i) := by
  classical
  simp only [zmono]
  rw [Finset.prod_congr rfl
    (fun j _ => (Finset.prod_zpow (fun i => x i ^ (q j i)) Finset.univ (a j)).symm)]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i _
  exact zpow_prod_coord x q a i (hx i)

end Work.WilC4
