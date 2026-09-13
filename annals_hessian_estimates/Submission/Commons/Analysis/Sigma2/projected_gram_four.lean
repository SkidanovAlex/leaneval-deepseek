import Mathlib
import Submission.Commons.Analysis.Sigma2.linearized_grad_sq
import Submission.Commons.Analysis.Sigma2.sigma1_sq_ge_two

namespace Commons.Analysis.Sigma2

open scoped BigOperators

/-- Projected Gram matrix identities for the linearized σ₂ equation in dimension 4.

For an eigenvalue tuple `lam : Fin 4 → ℝ` with `σ₂(lam) = 1`, writing `S = σ₁`,
`f = S - lam i`, `D = 3 S² - 2`, `df j = S - lam j`, `e j = [j = i]`,
`E j = e j - (f/D) df j` and `L j = 1 - (3S/D) df j`, the three Gram entries
`∑ E·E`, `∑ L·L` and `∑ E·L` take the closed values displayed.  All three follow
from the four moment identities `∑ df = 3S`, `∑ df² = D`, `∑ e = 1`, `∑ e·df = f`
(the second is `linearized_grad_sq`) together with `D > 0`, which follows from
`σ₁² = ∑ lam² + 2 ≥ 2`. -/
theorem projected_gram_four (lam : Fin 4 → ℝ)
    (hmono : ∀ ⦃i j : Fin 4⦄, i ≤ j → lam j ≤ lam i)
    (hσ2 : (∑ j : Fin 4, ∑ i : Fin 4, if i < j then lam i * lam j else 0) = 1)
    (hσ1 : 0 < ∑ i : Fin 4, lam i) (i : Fin 4) :
    let S : ℝ := ∑ k : Fin 4, lam k
    let f : ℝ := S - lam i
    let D : ℝ := 3 * S ^ 2 - 2
    let df : Fin 4 → ℝ := fun j => S - lam j
    let e : Fin 4 → ℝ := fun j => if j = i then 1 else 0
    let E : Fin 4 → ℝ := fun j => e j - (f / D) * df j
    let L : Fin 4 → ℝ := fun j => 1 - (3 * S / D) * df j
    ((∑ j : Fin 4, E j * E j) = 1 - f ^ 2 / D) ∧
      ((∑ j : Fin 4, L j * L j) = 1 - 6 / D) ∧
        ((∑ j : Fin 4, E j * L j) = 1 - 3 * S * f / D) := by
  classical
  simp only []
  set S : ℝ := ∑ k : Fin 4, lam k with hS
  set f : ℝ := S - lam i with hf
  set D : ℝ := 3 * S ^ 2 - 2 with hD
  set g : Fin 4 → ℝ := (fun j : Fin 4 => S - lam j) with hg
  set e : Fin 4 → ℝ := (fun j : Fin 4 => if j = i then (1:ℝ) else 0) with he
  set E : Fin 4 → ℝ := (fun j : Fin 4 => e j - (f / D) * g j) with hE
  set L : Fin 4 → ℝ := (fun j : Fin 4 => 1 - (3 * S / D) * g j) with hL
  -- `∑ df = 3 S`
  have hb : ∑ j : Fin 4, g j = 3 * S := by
    have hsub : ∑ j : Fin 4, g j = ∑ j : Fin 4, (S - lam j) := by
      apply Finset.sum_congr rfl; intro j _; simp only [hg]
    rw [hsub, Finset.sum_sub_distrib]
    have h1 : ∑ j : Fin 4, (S : ℝ) = 4 * S := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; norm_num
    rw [h1, ← hS]; ring
  -- `∑ df² = D`
  have hc : ∑ j : Fin 4, g j * g j = D := by
    have hlg := Commons.Analysis.Sigma2.linearized_grad_sq lam hσ2
    rw [← hS] at hlg
    rw [hD]
    rw [show (∑ j : Fin 4, g j * g j) = ∑ j : Fin 4, (S - lam j)^2 by
      apply Finset.sum_congr rfl; intro j _; simp only [hg]; ring]
    exact hlg
  -- `∑ e = 1`
  have hd : ∑ j : Fin 4, e j = 1 := by
    have hh : (∑ j : Fin 4, e j) = ∑ j : Fin 4, (if j = i then (1:ℝ) else 0) := by
      apply Finset.sum_congr rfl; intro j _; simp only [he]
    rw [hh, Finset.sum_ite_eq']; simp
  -- `∑ e · df = f`
  have heg : ∑ j : Fin 4, e j * g j = f := by
    have hcongr : ∑ j : Fin 4, e j * g j = ∑ j : Fin 4, (if j = i then g j else 0) := by
      apply Finset.sum_congr rfl; intro j _
      simp only [he]; by_cases h : j = i <;> simp [h]
    rw [hcongr, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true, hg, hf]
  -- `∑ e² = 1`
  have hee : ∑ j : Fin 4, e j * e j = 1 := by
    have hcongr : ∑ j : Fin 4, e j * e j = ∑ j : Fin 4, e j := by
      apply Finset.sum_congr rfl; intro j _
      simp only [he]; by_cases h : j = i <;> simp [h]
    rw [hcongr, hd]
  -- `D > 0`
  have hDpos : 0 < D := by
    have h2 := Commons.Analysis.Sigma2.sigma1_sq_ge_two lam hσ2
    rw [← hS] at h2
    rw [hD]; nlinarith
  have hDne : D ≠ 0 := ne_of_gt hDpos
  have h4 : ∑ _j : Fin 4, (1:ℝ) = 4 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; norm_num
  refine ⟨?_, ?_, ?_⟩
  -- `∑ E·E`
  · have expand : ∑ j : Fin 4, E j * E j
        = ∑ j : Fin 4, (e j * e j - 2 * (f / D) * (e j * g j) + (f / D) ^ 2 * (g j * g j)) := by
      apply Finset.sum_congr rfl; intro j _
      simp only [hE]; ring
    rw [expand, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    rw [hee, heg, hc]
    field_simp; ring
  -- `∑ L·L`
  · have expand : ∑ j : Fin 4, L j * L j
        = ∑ j : Fin 4, ((1:ℝ) - 2 * (3 * S / D) * g j + (3 * S / D) ^ 2 * (g j * g j)) := by
      apply Finset.sum_congr rfl; intro j _
      simp only [hL]; ring
    rw [expand, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    rw [h4, hb, hc]
    field_simp
    rw [hD]; ring
  -- `∑ E·L`
  · have expand : ∑ j : Fin 4, E j * L j
        = ∑ j : Fin 4, (e j - (3 * S / D) * (e j * g j) - (f / D) * g j
            + (f / D) * (3 * S / D) * (g j * g j)) := by
      apply Finset.sum_congr rfl; intro j _
      simp only [hE, hL]; ring
    rw [expand, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [hd, heg, hb, hc]
    field_simp; ring

end Commons.Analysis.Sigma2
