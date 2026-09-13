import Mathlib

namespace Commons.Analysis.Sigma2

open scoped BigOperators

private lemma sum_sub_mul_factor {ι : Type*} [Fintype ι] (e df t : ι → ℝ) (c : ℝ) :
    (∑ j, (e j - c * df j) * t j) = (∑ j, e j * t j) - c * (∑ j, df j * t j) := by
  simp only [sub_mul]
  rw [Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma sum_ite_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ι → ℝ) (i : ι) :
    (∑ j, (if j = i then (1 : ℝ) else 0) * t j) = t i := by
  simp

private lemma sum_one_mul {ι : Type*} [Fintype ι] (t : ι → ℝ) :
    (∑ j, (1 : ℝ) * t j) = ∑ j, t j := by
  simp

open scoped BigOperators in
theorem proj_inner_eq (lam : Fin 4 → ℝ) (i : Fin 4) (t : Fin 4 → ℝ)
    (ht : (∑ j : Fin 4, ((∑ k : Fin 4, lam k) - lam j) * t j) = 0) :
    let S : ℝ := ∑ k : Fin 4, lam k
    let f : ℝ := S - lam i
    let D : ℝ := 3 * S ^ 2 - 2
    let df : Fin 4 → ℝ := fun j => S - lam j
    let e : Fin 4 → ℝ := fun j => if j = i then 1 else 0
    let E : Fin 4 → ℝ := fun j => e j - (f / D) * df j
    let L : Fin 4 → ℝ := fun j => 1 - (3 * S / D) * df j
    ((∑ j : Fin 4, E j * t j) = t i) ∧ ((∑ j : Fin 4, L j * t j) = ∑ j : Fin 4, t j) := by
  dsimp only
  constructor
  · rw [sum_sub_mul_factor]
    simp only [sum_ite_mul, ht, mul_zero, sub_zero]
  · rw [sum_sub_mul_factor]
    simp only [sum_one_mul, ht, mul_zero, sub_zero]

end Commons.Analysis.Sigma2
