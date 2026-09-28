import Mathlib
import Submission.Work.HP.Defs

namespace Work.HP.HP2

open Polynomial Finset

/-- The linear polynomial `C a + X * C b` has degree at most `1`. -/
theorem natDegree_linear_le (a b : ℝ) : (C a + X * C b : ℝ[X]).natDegree ≤ 1 := by
  have h1 : (C a : ℝ[X]).natDegree ≤ 1 := by rw [natDegree_C]; norm_num
  have h2 : (X * C b : ℝ[X]).natDegree ≤ 1 := by
    calc (X * C b : ℝ[X]).natDegree ≤ X.natDegree + (C b).natDegree := natDegree_mul_le
      _ = 1 := by rw [natDegree_X, natDegree_C]
  calc (C a + X * C b : ℝ[X]).natDegree
      ≤ max (C a : ℝ[X]).natDegree (X * C b : ℝ[X]).natDegree := natDegree_add_le _ _
    _ ≤ 1 := max_le h1 h2

/-- The coefficient of `X^(d+e)` in a product, when the two factors have degree at most
`d` and `e` respectively, is the product of the top coefficients. -/
theorem coeff_mul_of_natDegree_le {p q : ℝ[X]} {d e : ℕ} (hp : p.natDegree ≤ d)
    (hq : q.natDegree ≤ e) : (p * q).coeff (d + e) = p.coeff d * q.coeff e := by
  rw [coeff_mul]
  refine Finset.sum_eq_single (d, e) ?_ ?_
  · rintro ⟨i, j⟩ hij hne
    simp only [HasAntidiagonal.mem_antidiagonal] at hij
    by_cases h : i < d
    · have hje : e < j := by omega
      have : q.coeff j = 0 := coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hq hje)
      simp [this]
    · have hge : d ≤ i := not_lt.mp h
      have hi : i ≠ d := by
        intro hid
        apply hne
        have : j = e := by omega
        simp [hid, this]
      have hdi : d < i := lt_of_le_of_ne hge (Ne.symm hi)
      have : p.coeff i = 0 := coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp hdi)
      simp [this]
  · intro hmem
    have : (d, e) ∈ HasAntidiagonal.antidiagonal (d + e) :=
      HasAntidiagonal.mem_antidiagonal.mpr rfl
    exact absurd this hmem

/-- The top coefficient of a product of polynomials, with variable degree bounds. -/
theorem coeff_prod_of_natDegree_le_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℝ[X]) (d : ι → ℕ) (h : ∀ i ∈ s, (f i).natDegree ≤ d i) :
    (∏ i ∈ s, f i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (f i).coeff (d i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have ha' : (f a).natDegree ≤ d a := h a (mem_insert_self a s)
    have hs' : (∏ i ∈ s, f i).natDegree ≤ ∑ i ∈ s, d i :=
      (natDegree_prod_le s f).trans (sum_le_sum (fun i hi => h i (mem_insert_of_mem hi)))
    rw [prod_insert ha, sum_insert ha, coeff_mul_of_natDegree_le ha' hs',
      ih (fun i hi => h i (mem_insert_of_mem hi)), prod_insert ha]

/-- The degree-`n` coefficient of `(C a + X * C b)^n` is `b^n`. -/
theorem coeff_linear_pow (a b : ℝ) (n : ℕ) :
    ((C a + X * C b : ℝ[X]) ^ n).coeff n = b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hlin := natDegree_linear_le a b
    have hpow : ((C a + X * C b : ℝ[X]) ^ n).natDegree ≤ n :=
      (natDegree_pow_le_of_le n hlin).trans (le_of_eq (Nat.mul_one n))
    have hc : (C a + X * C b : ℝ[X]).coeff 1 = b := by
      rw [coeff_add, coeff_C, show (X * C b : ℝ[X]) = C b * X from mul_comm _ _, coeff_C_mul_X]
      simp
    rw [pow_succ, coeff_mul_of_natDegree_le hpow hlin, ih, hc, pow_succ]

theorem exists_fibre_poly (m D : ℕ) (F : Work.HP.Mon D m → ℝ) (z e : Fin (m + 1) → ℝ) :
    ∃ p : Polynomial ℝ, p.natDegree ≤ D ∧
      p.coeff D = ∑ μ : Work.HP.Mon D m, F μ * Work.HP.veronese D m e μ ∧
      ∀ t : ℝ, p.eval t = ∑ μ : Work.HP.Mon D m,
        F μ * Work.HP.veronese D m (fun i => z i + t * e i) μ := by
  refine ⟨∑ μ : Mon D m, C (F μ) * ∏ i, (C (z i) + X * C (e i)) ^ (μ.1 i : ℕ),
    ?_, ?_, ?_⟩
  · -- degree bound
    refine natDegree_sum_le_of_forall_le _ _ (fun μ _ => ?_)
    calc (C (F μ) * ∏ i, (C (z i) + X * C (e i)) ^ (μ.1 i : ℕ) : ℝ[X]).natDegree
        ≤ (C (F μ) : ℝ[X]).natDegree
            + (∏ i, (C (z i) + X * C (e i)) ^ (μ.1 i : ℕ) : ℝ[X]).natDegree := natDegree_mul_le
      _ ≤ 0 + D := by
            refine add_le_add (le_of_eq (natDegree_C (F μ))) ?_
            calc (∏ i, (C (z i) + X * C (e i)) ^ (μ.1 i : ℕ) : ℝ[X]).natDegree
                ≤ ∑ i, ((C (z i) + X * C (e i)) ^ (μ.1 i : ℕ) : ℝ[X]).natDegree :=
                  natDegree_prod_le _ _
              _ ≤ ∑ i : Fin (m + 1), (μ.1 i : ℕ) :=
                  sum_le_sum (fun i _ =>
                    (natDegree_pow_le_of_le _ (natDegree_linear_le _ _)).trans
                      (le_of_eq (Nat.mul_one _)))
              _ = D := μ.2
      _ = D := by norm_num
  · -- top coefficient
    rw [finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro μ _
    rw [coeff_C_mul]
    congr 1
    have hbound : ∀ i ∈ (Finset.univ : Finset (Fin (m + 1))),
        ((C (z i) + X * C (e i) : ℝ[X]) ^ (μ.1 i : ℕ)).natDegree ≤ (μ.1 i : ℕ) :=
      fun i _ => (natDegree_pow_le_of_le _ (natDegree_linear_le _ _)).trans
        (le_of_eq (Nat.mul_one _))
    have key := coeff_prod_of_natDegree_le_sum (Finset.univ : Finset (Fin (m + 1)))
      (fun i : Fin (m + 1) => (C (z i) + X * C (e i) : ℝ[X]) ^ (μ.1 i : ℕ))
      (fun i => (μ.1 i : ℕ)) hbound
    rw [show (∑ i : Fin (m + 1), (μ.1 i : ℕ)) = D from μ.2] at key
    rw [key]
    rw [show veronese D m e μ = ∏ i, e i ^ (μ.1 i : ℕ) from rfl]
    exact Finset.prod_congr rfl (fun i _ => coeff_linear_pow (z i) (e i) (μ.1 i : ℕ))
  · -- evaluation
    intro t
    rw [eval_finsetSum]
    apply Finset.sum_congr rfl
    intro μ _
    rw [eval_mul, eval_C]
    congr 1
    rw [eval_prod]
    rw [show veronese D m (fun i => z i + t * e i) μ = ∏ i, (z i + t * e i) ^ (μ.1 i : ℕ) from rfl]
    apply Finset.prod_congr rfl
    intro i _
    rw [eval_pow]
    congr 1
    simp only [eval_add, eval_mul, eval_X, eval_C]

end Work.HP.HP2
