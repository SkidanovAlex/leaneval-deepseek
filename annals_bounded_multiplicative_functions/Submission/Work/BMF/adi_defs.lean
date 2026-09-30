import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.adi_lagrange

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Shared notation for the ADI (approximate dilation invariance) descent

`Tay j x` is the degree-`j` Taylor polynomial of `t ↦ log (t/x)` at `t = x`.  The descent
peels off, at each degree `j`, a multiple `(T_j/2π) · Tay_j` of this polynomial together with
a lattice-valued polynomial `μ_j t^j`; at the end the `Tay_j` combine into `log` up to an error
with small derivative.
-/

namespace Work.BMF

open Polynomial Finset

/-- The degree-`j` Taylor polynomial of `log (t/x)` at `t = x`:
`∑_{m=1}^{j} (-1)^{m-1} (t - x)^m / (m x^m)`. -/
noncomputable def Tay (j : ℕ) (x : ℝ) : ℝ[X] :=
  ∑ m ∈ Finset.Icc 1 j, C ((-1 : ℝ) ^ (m - 1) / ((m : ℝ) * x ^ m)) * (X - C x) ^ m

/-- Coefficient of a dilate. -/
theorem coeff_dil (a : ℝ) (P : ℝ[X]) (n : ℕ) : (dil a P).coeff n = P.coeff n * a ^ n := by
  unfold dil
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [add_comp, coeff_add, coeff_add, hp, hq]
      ring
  | monomial m c =>
      have h1 : ((monomial m c).comp (C a * X)) = C (c * a ^ m) * X ^ m := by
        rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, pow_comp, X_comp, mul_pow, ← C_pow,
          C_mul]
        ring
      rw [h1, coeff_C_mul, coeff_X_pow, ← C_mul_X_pow_eq_monomial, coeff_C_mul, coeff_X_pow]
      by_cases h : m = n
      · subst h; ring
      · simp [if_neg (Ne.symm h)]

theorem natDegree_dil_le (a : ℝ) (P : ℝ[X]) : (dil a P).natDegree ≤ P.natDegree := by
  unfold dil
  refine le_trans (natDegree_comp_le) ?_
  have h1 : (C a * X : ℝ[X]).natDegree ≤ 1 := by
    refine le_trans (natDegree_mul_le) ?_
    rw [natDegree_C, zero_add, natDegree_X]
  have h2 : P.natDegree * (C a * X : ℝ[X]).natDegree ≤ P.natDegree * 1 :=
    Nat.mul_le_mul_left _ h1
  simpa using h2

theorem dil_add (a : ℝ) (P Q : ℝ[X]) : dil a (P + Q) = dil a P + dil a Q := by
  unfold dil; rw [add_comp]

theorem dil_sub (a : ℝ) (P Q : ℝ[X]) : dil a (P - Q) = dil a P - dil a Q := by
  unfold dil; rw [sub_comp]

theorem dil_C_mul (a c : ℝ) (P : ℝ[X]) : dil a (C c * P) = C c * dil a P := by
  unfold dil; rw [mul_comp, C_comp]

theorem dil_X_pow (a : ℝ) (m : ℕ) : dil a (X ^ m) = C (a ^ m) * X ^ m := by
  unfold dil; rw [pow_comp, X_comp, mul_pow, ← C_pow]

theorem dil_C (a c : ℝ) : dil a (C c) = C c := by
  unfold dil; rw [C_comp]

section TayLemmas

theorem tay_eval (j : ℕ) (x t : ℝ) :
    (Tay j x).eval t =
      ∑ m ∈ Finset.Icc 1 j, (-1 : ℝ) ^ (m - 1) * (t - x) ^ m / ((m : ℝ) * x ^ m) := by
  rw [Tay, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [eval_mul, eval_C, eval_pow, eval_sub, eval_X, eval_C, div_mul_eq_mul_div]

theorem tay_natDegree_le (j : ℕ) (x : ℝ) : (Tay j x).natDegree ≤ j := by
  rw [Tay]
  refine natDegree_finset_sum_le _ _ ?_
  intro m hm
  have hmj : m ≤ j := (Finset.mem_Icc.mp hm).2
  refine le_trans (natDegree_mul_le) ?_
  rw [natDegree_C, zero_add]
  refine le_trans (natDegree_pow_le) ?_
  have h1 : (X - C x : ℝ[X]).natDegree ≤ 1 := by
    refine le_trans (natDegree_sub_le _ _) ?_
    rw [natDegree_X, natDegree_C]
    norm_num
  calc m * (X - C x : ℝ[X]).natDegree ≤ m * 1 := Nat.mul_le_mul_left _ h1
    _ = m := Nat.mul_one _
    _ ≤ j := hmj

theorem tay_derivative_eval (j : ℕ) {x : ℝ} (hx : x ≠ 0) (t : ℝ) :
    (Tay j x).derivative.eval t =
      ∑ m ∈ Finset.Icc 1 j, (-1 : ℝ) ^ (m - 1) * (t - x) ^ (m - 1) / x ^ m := by
  rw [Tay, Polynomial.derivative_sum, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm1 : (m : ℝ) ≠ 0 := by
    have h1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    exact_mod_cast (by omega : m ≠ 0)
  rw [derivative_C_mul, derivative_pow, derivative_sub, derivative_X, derivative_C, sub_zero,
    mul_one]
  rw [eval_mul, eval_C, eval_mul, eval_C, eval_pow, eval_sub, eval_X, eval_C]
  field_simp

theorem tay_coeff_top {j : ℕ} (hj : 1 ≤ j) {x : ℝ} (hx : 0 < x) :
    (Tay j x).coeff j = (-1 : ℝ) ^ (j - 1) / ((j : ℝ) * x ^ j) := by
  rw [Tay, coeff_finset_sum]
  rw [Finset.sum_eq_single j]
  · rw [coeff_C_mul]
    have hdeg : (X - C x : ℝ[X]).natDegree = 1 := natDegree_X_sub_C x
    have hmonic : ((X - C x : ℝ[X]) ^ j).Monic := (monic_X_sub_C x).pow j
    have hnd : ((X - C x : ℝ[X]) ^ j).natDegree = j := by
      rw [(monic_X_sub_C x).natDegree_pow j, hdeg, mul_one]
    have hc : ((X - C x : ℝ[X]) ^ j).coeff j = 1 := by
      have h2 := hmonic.coeff_natDegree
      rwa [hnd] at h2
    rw [hc, mul_one]
  · intro m hm hmj
    rw [coeff_C_mul]
    have hmj' : m < j := lt_of_le_of_ne (Finset.mem_Icc.mp hm).2 hmj
    have hmonic : ((X - C x : ℝ[X]) ^ m).Monic := (monic_X_sub_C x).pow m
    have hnd : ((X - C x : ℝ[X]) ^ m).natDegree = m := by
      rw [(monic_X_sub_C x).natDegree_pow m, natDegree_X_sub_C, mul_one]
    rw [coeff_eq_zero_of_natDegree_lt (by rw [hnd]; exact hmj'), mul_zero]
  · intro hj'
    exact absurd (Finset.mem_Icc.mpr ⟨hj, le_rfl⟩) hj'

end TayLemmas

end Work.BMF
