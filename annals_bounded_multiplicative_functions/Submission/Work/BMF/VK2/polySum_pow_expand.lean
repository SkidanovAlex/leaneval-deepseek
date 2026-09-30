import Mathlib
import Submission.Work.BMF.kdr_defs
import Submission.Work.BMF.VK2.mean_value_box_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Expansion of the `s`-th power of the polynomial Weyl sum

`polySum m α X = Σ_{1 ≤ h ≤ X} e(Σ_j α j h^{j+1})` is the polynomial exponential sum,
and its `s`-th power expands, by the multinomial theorem, as a sum over `s`-tuples
`u : Fin s → Finset.Icc 1 X` of the additive character of the moment vector

`Σ_j α j · (mvMom m u j)`.

The moment vector `mvMom m u j = Σ_i (u i)^{j+1}` collects the power sums of the tuple `u`,
which is exactly the quantity appearing in the Vinogradov mean-value count.
-/

namespace Work.BMF.VK2

open scoped BigOperators
open Finset

/-- `eC` is additive: `eC (a + b) = eC a * eC b`. -/
lemma eC_add' (a b : ℝ) : eC (a + b) = eC a * eC b := by
  unfold eC
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `eC 0 = 1`. -/
lemma eC_zero' : eC 0 = 1 := by
  simp [eC]

/-- The product of additive characters is the character of the sum. -/
lemma prod_eC {ι : Type*} (t : Finset ι) (a : ι → ℝ) :
    ∏ i ∈ t, eC (a i) = eC (∑ i ∈ t, a i) := by
  classical
  induction t using Finset.induction with
  | empty => simp [eC_zero']
  | insert x t hx ih =>
      rw [Finset.prod_insert hx, Finset.sum_insert hx, ih, eC_add']

/-- The product of additive characters over a finite type is the character of the sum. -/
lemma prod_eC_univ {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    ∏ i, eC (a i) = eC (∑ i, a i) :=
  prod_eC Finset.univ a

/-- The phase of an `s`-tuple of integers is the pairing of `α` with its moment vector. -/
lemma sum_phase_eq {m s X : ℕ} (α : Fin m → ℝ) (u : Fin s → Finset.Icc 1 X) :
    ∑ i : Fin s, phase m α (u i).1 = ∑ j : Fin m, α j * ((mvMom m u j : ℤ) : ℝ) := by
  simp only [phase]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.mul_sum]
  congr 1
  rw [mvMom]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem polySum_pow_expand (m s X : ℕ) (α : Fin m → ℝ) :
    (polySum m α (X : ℝ)) ^ s
      = ∑ u : Fin s → Finset.Icc 1 X,
          eC (∑ j : Fin m, α j * (mvMom m u j : ℝ)) := by
  have hbase : polySum m α (X : ℝ) = ∑ a : ↥(Finset.Icc 1 X), eC (phase m α a.1) := by
    simp only [polySum, Nat.floor_natCast]
    exact (Finset.sum_coe_sort (Finset.Icc 1 X) (fun h => eC (phase m α h))).symm
  rw [hbase, Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro u _
  rw [prod_eC_univ, sum_phase_eq]

end Work.BMF.VK2
