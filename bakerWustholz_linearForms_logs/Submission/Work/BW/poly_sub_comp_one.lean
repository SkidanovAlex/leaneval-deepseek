import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Polynomial

/-- The `(deg q - 1)`-th Hasse derivative of `q` is the linear polynomial
`q.coeff (deg q - 1) + deg(q) * leadingCoeff(q) * X`; evaluating at `-1` gives
`q.coeff (deg q - 1) - deg(q) * leadingCoeff(q)`. -/
private lemma hasseDeriv_pred_eval (q : Polynomial ℚ) (hq : 1 ≤ q.natDegree) :
    (hasseDeriv (q.natDegree - 1) q).eval (-1) =
      q.coeff (q.natDegree - 1) - (q.natDegree : ℚ) * q.leadingCoeff := by
  have h2 : (hasseDeriv (q.natDegree - 1) q).natDegree < 2 := by
    rw [natDegree_hasseDeriv]; omega
  rw [eval_eq_sum_range' h2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one, mul_one]
  rw [hasseDeriv_coeff, hasseDeriv_coeff]
  simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.zero_add]
  have hn1 : 1 + (q.natDegree - 1) = q.natDegree := by omega
  have hchoose : (q.natDegree).choose (q.natDegree - 1) = q.natDegree := by
    nth_rewrite 1 [show q.natDegree = (q.natDegree - 1) + 1 by omega]
    rw [Nat.choose_succ_self_right]
    omega
  rw [hn1, hchoose, coeff_natDegree]
  ring

theorem poly_sub_comp_one (q : Polynomial ℚ) (hq : 1 ≤ q.natDegree) :
    (q - q.comp (Polynomial.X - Polynomial.C 1)).natDegree = q.natDegree - 1 ∧
    (q - q.comp (Polynomial.X - Polynomial.C 1)).leadingCoeff =
      (q.natDegree : ℚ) * q.leadingCoeff := by
  have hq0 : q ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hq
    omega
  have hcomp_eq : q.comp (X - C 1) = taylor (-1) q := by
    rw [taylor_apply]
    congr 1
    simp [sub_eq_add_neg]
  have hcomp_nd : (q.comp (X - C 1)).natDegree = q.natDegree := by
    rw [hcomp_eq, natDegree_taylor]
  have hcomp_lc : (q.comp (X - C 1)).leadingCoeff = q.leadingCoeff := by
    rw [hcomp_eq, leadingCoeff_taylor]
  have hcomp_coeff : (q.comp (X - C 1)).coeff (q.natDegree - 1) =
      q.coeff (q.natDegree - 1) - (q.natDegree : ℚ) * q.leadingCoeff := by
    rw [hcomp_eq, taylor_coeff]
    exact hasseDeriv_pred_eval q hq
  have hle : (q - q.comp (X - C 1)).natDegree ≤ q.natDegree - 1 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    have hNn : q.natDegree ≤ N := by omega
    rcases lt_or_eq_of_le hNn with h | h
    · rw [coeff_sub,
        coeff_eq_zero_of_natDegree_lt (by omega : q.natDegree < N),
        coeff_eq_zero_of_natDegree_lt (by rw [hcomp_nd]; omega :
          (q.comp (X - C 1)).natDegree < N),
        sub_zero]
    · subst h
      have hc : (q.comp (X - C 1)).coeff q.natDegree = (q.comp (X - C 1)).leadingCoeff := by
        rw [← hcomp_nd]; exact coeff_natDegree
      rw [coeff_sub, coeff_natDegree, hc, hcomp_lc, sub_self]
  have hcoeff : (q - q.comp (X - C 1)).coeff (q.natDegree - 1) =
      (q.natDegree : ℚ) * q.leadingCoeff := by
    rw [coeff_sub, hcomp_coeff]
    ring
  have hne : (q - q.comp (X - C 1)).coeff (q.natDegree - 1) ≠ 0 := by
    rw [hcoeff]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (by omega : q.natDegree ≠ 0))
      (by rw [Ne, leadingCoeff_eq_zero]; exact hq0)
  have hnd := natDegree_eq_of_le_of_coeff_ne_zero hle hne
  exact ⟨hnd, by rw [← coeff_natDegree, hnd]; exact hcoeff⟩

end Work.BW
