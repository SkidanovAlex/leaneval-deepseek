import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Lagrange interpolation (base tool for the ADI descent)

If `Q` has degree `≤ n` and `v : Fin (n+1) → ℝ` is injective, `Q` is recovered from its
values at the nodes `v r` by the Lagrange formula.  We record the polynomial form and the
two consequences used in the ADI argument (evaluation form, top-coefficient form).
-/

namespace Work.BMF

open Polynomial Finset

/-- A sum of polynomials each of `natDegree ≤ n` again has `natDegree ≤ n`. -/
theorem natDegree_finset_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ[X]) {n : ℕ}
    (h : ∀ i ∈ s, (f i).natDegree ≤ n) : (∑ i ∈ s, f i).natDegree ≤ n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
      · exact h a (Finset.mem_insert_self a s)
      · exact ih (fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Coefficient extraction commutes with finite sums. -/
theorem coeff_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ[X]) (n : ℕ) :
    (∑ i ∈ s, f i).coeff n = ∑ i ∈ s, (f i).coeff n :=
  Polynomial.finsetSum_coeff s f n

/-- The Lagrange basis polynomial at node `r`. -/
noncomputable def lagrangeBasis {n : ℕ} (v : Fin (n + 1) → ℝ) (r : Fin (n + 1)) : ℝ[X] :=
  (∏ m ∈ Finset.univ.erase r, (X - C (v m))) * C ((∏ m ∈ Finset.univ.erase r, (v r - v m))⁻¹)

theorem lagrangeBasis_monic {n : ℕ} (v : Fin (n + 1) → ℝ) (r : Fin (n + 1)) :
    (∏ m ∈ Finset.univ.erase r, (X - C (v m))).Monic :=
  monic_prod_of_monic _ _ fun m _ => monic_X_sub_C (v m)

theorem lagrangeBasis_natDegree {n : ℕ} (v : Fin (n + 1) → ℝ) (r : Fin (n + 1)) :
    (∏ m ∈ Finset.univ.erase r, (X - C (v m))).natDegree = n := by
  rw [natDegree_prod_of_monic _ _ fun m _ => monic_X_sub_C (v m)]
  simp [Finset.card_erase_of_mem (Finset.mem_univ r)]

theorem lagrangeBasis_coeff_top {n : ℕ} (v : Fin (n + 1) → ℝ) (r : Fin (n + 1)) :
    (∏ m ∈ Finset.univ.erase r, (X - C (v m))).coeff n = 1 := by
  have h := (lagrangeBasis_monic v r).coeff_natDegree
  rwa [lagrangeBasis_natDegree v r] at h

theorem lagrangeBasis_coeff {n : ℕ} (v : Fin (n + 1) → ℝ) (r : Fin (n + 1)) :
    (lagrangeBasis v r).coeff n = (∏ m ∈ Finset.univ.erase r, (v r - v m))⁻¹ := by
  unfold lagrangeBasis
  rw [coeff_mul_C, lagrangeBasis_coeff_top, one_mul]

theorem prod_erase_ne_zero {n : ℕ} {v : Fin (n + 1) → ℝ} (hv : Function.Injective v)
    (r : Fin (n + 1)) : (∏ m ∈ Finset.univ.erase r, (v r - v m)) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro m hm
  have hm' : m ≠ r := (Finset.mem_erase.mp hm).1
  exact sub_ne_zero.mpr fun h => hm' (hv h).symm

/-- **Lagrange interpolation, polynomial form.** -/
theorem lagrange_eq {n : ℕ} {v : Fin (n + 1) → ℝ} (hv : Function.Injective v) {Q : ℝ[X]}
    (hdeg : Q.natDegree ≤ n) :
    Q = ∑ r : Fin (n + 1), C (Q.eval (v r)) * lagrangeBasis v r := by
  classical
  set L : ℝ[X] := ∑ r : Fin (n + 1), C (Q.eval (v r)) * lagrangeBasis v r with hL
  have hLdeg : L.natDegree ≤ n := by
    rw [hL]
    refine natDegree_finset_sum_le _ _ ?_
    intro r _
    refine le_trans (natDegree_mul_le) ?_
    rw [natDegree_C]
    have : (lagrangeBasis v r).natDegree ≤ n := by
      unfold lagrangeBasis
      refine le_trans (natDegree_mul_le) ?_
      rw [natDegree_C, add_zero, lagrangeBasis_natDegree]
    omega
  have hzero : Q - L = 0 := by
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero (Q - L) hv ?_ ?_
    · intro i
      rw [eval_sub]
      have hLi : L.eval (v i) = Q.eval (v i) := by
        rw [hL, Polynomial.eval_finsetSum]
        rw [Finset.sum_eq_single i]
        · have hne := prod_erase_ne_zero hv i
          simp only [eval_mul, eval_C]
          unfold lagrangeBasis
          simp only [eval_mul, eval_C, eval_prod, eval_sub, eval_X, eval_C]
          rw [← mul_assoc, mul_inv_cancel_right₀ hne]
        · intro b _ hbi
          simp only [eval_mul, eval_C]
          unfold lagrangeBasis
          rw [eval_mul, eval_C, eval_prod]
          simp only [eval_sub, eval_X, eval_C]
          have hz : (∏ m ∈ Finset.univ.erase b, (v i - v m)) = 0 := by
            rw [Finset.prod_eq_zero_iff]
            exact ⟨i, by rw [Finset.mem_erase]; exact ⟨Ne.symm hbi, Finset.mem_univ i⟩, sub_self _⟩
          rw [hz, zero_mul, mul_zero]
        · intro hi
          exact absurd (Finset.mem_univ i) hi
      rw [hLi, sub_self]
    · rw [Fintype.card_fin]
      refine lt_of_le_of_lt (natDegree_sub_le Q L) ?_
      rw [max_lt_iff]
      exact ⟨Nat.lt_succ_of_le hdeg, Nat.lt_succ_of_le hLdeg⟩
  exact sub_eq_zero.mp hzero

/-- **Lagrange interpolation, evaluation form.** -/
theorem lagrange_eval {n : ℕ} {v : Fin (n + 1) → ℝ} (hv : Function.Injective v) {Q : ℝ[X]}
    (hdeg : Q.natDegree ≤ n) (x : ℝ) :
    Q.eval x = ∑ r : Fin (n + 1),
      Q.eval (v r) * (∏ m ∈ Finset.univ.erase r, (x - v m)) *
        (∏ m ∈ Finset.univ.erase r, (v r - v m))⁻¹ := by
  conv_lhs => rw [lagrange_eq hv hdeg]
  rw [Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [eval_mul, eval_C]
  unfold lagrangeBasis
  rw [eval_mul, eval_C, eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  ring

/-- **Lagrange interpolation, top-coefficient form.** -/
theorem lagrange_coeff_top {n : ℕ} {v : Fin (n + 1) → ℝ} (hv : Function.Injective v) {Q : ℝ[X]}
    (hdeg : Q.natDegree ≤ n) :
    Q.coeff n = ∑ r : Fin (n + 1), Q.eval (v r) * (∏ m ∈ Finset.univ.erase r, (v r - v m))⁻¹ := by
  conv_lhs => rw [lagrange_eq hv hdeg]
  rw [coeff_finset_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [coeff_C_mul, lagrangeBasis_coeff]

end Work.BMF
