import Mathlib
import Submission.Work.HP.Q44Setup

/-!
# `|wCoeff v e m| ≤ 10000 · ∏ B_j^{e_j}`

If `v : Fin 3 → (Fin 5 → ℤ)` is a triple of integer vectors whose `(j,i)`-entry is bounded
by `B j` (with `B j ≥ 1`), then every coefficient of the polynomial `verPoly v m` is bounded
by `10000 · ∏_j B_j^{e_j}`.

The proof bounds the coefficient of a product of linear forms: a product of `n` linear forms
in `3` variables has `e`-coefficient of absolute value at most `3^n · ∏_j B_j^{e_j}`, by
induction on the number of factors, using that `(Σ_j c_j X_j · Q).coeff e` is a sum of at most
`3` terms `c_j · Q.coeff (e - single j 1)`.
-/

set_option autoImplicit false

noncomputable section

open MvPolynomial Finset

namespace Work.HP.Q44Child

/-- Exponent bookkeeping: if `B j` is a factor of the weight `∏_i B_i^{e_i}` with positive
multiplicity, then pulling it out of the product multiplies the exponent of `j` by one less. -/
lemma pow_prod_tsub_single (B : Fin 3 → ℝ) (e : Fin 3 →₀ ℕ) (j : Fin 3) (hj : j ∈ e.support) :
    B j * ∏ i : Fin 3, B i ^ ((e - Finsupp.single j 1 : Fin 3 →₀ ℕ) i)
      = ∏ i : Fin 3, B i ^ (e i) := by
  set s : Fin 3 →₀ ℕ := Finsupp.single j 1 with hs
  set e' : Fin 3 →₀ ℕ := e - s with he'
  have hdec : e' + s = e := by
    rw [he', hs]
    ext i
    rw [Finsupp.add_apply, Finsupp.tsub_apply]
    by_cases h : i = j
    · subst h
      simp only [Finsupp.single_eq_same]
      have : e i ≠ 0 := by simpa [Finsupp.mem_support_iff] using hj
      omega
    · rw [Finsupp.single_eq_of_ne h]
      simp
  have hsingle : (∏ i : Fin 3, B i ^ (s i)) = B j := by
    rw [hs, ← Finsupp.prod_pow (Finsupp.single j 1 : Fin 3 →₀ ℕ) (fun i => B i)]
    rw [Finsupp.prod_single_index (h := fun i b => B i ^ b) (by simp)]
    simp
  calc B j * ∏ i : Fin 3, B i ^ (e' i)
      = (∏ i : Fin 3, B i ^ (e' i)) * B j := by ring
    _ = (∏ i : Fin 3, B i ^ (e' i)) * (∏ i : Fin 3, B i ^ (s i)) := by rw [hsingle]
    _ = ∏ i : Fin 3, (B i ^ (e' i) * B i ^ (s i)) := by rw [Finset.prod_mul_distrib]
    _ = ∏ i : Fin 3, B i ^ ((e' + s) i) := by
          refine Finset.prod_congr rfl (fun i _ => ?_)
          rw [Finsupp.add_apply, pow_add]
    _ = ∏ i : Fin 3, B i ^ (e i) := by rw [hdec]

/-- The key coefficient bound: the `e`-coefficient of a product of `n` linear forms
`Σ_j c_{k,j} X_j` (with `|c_{k,j}| ≤ B_j`, `B_j ≥ 0`) is at most `3^n · ∏_j B_j^{e_j}`. -/
theorem abs_coeff_prod_linForm_le {ι : Type*} (s : Finset ι) (c : ι → Fin 3 → ℤ)
    (B : Fin 3 → ℝ) (hB : ∀ j, 0 ≤ B j) (hc : ∀ k j, |(c k j : ℝ)| ≤ B j) :
    ∀ e : Fin 3 →₀ ℕ,
    |((∏ k ∈ s, (∑ j : Fin 3, MvPolynomial.C (c k j) * MvPolynomial.X j)).coeff e : ℝ)|
      ≤ (3 : ℝ) ^ s.card * ∏ j : Fin 3, B j ^ (e j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro e
      simp only [Finset.prod_empty, Finset.card_empty, pow_zero, one_mul]
      rw [MvPolynomial.coeff_one]
      by_cases he : e = 0
      · subst he
        simp
      · have hne : ¬ (0 = e) := fun h => he h.symm
        simp only [hne, ite_false, Int.cast_zero, abs_zero]
        exact Finset.prod_nonneg (fun j _ => pow_nonneg (hB j) _)
  | insert a s' ha ih =>
      intro e
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
      set Q : MvPolynomial (Fin 3) ℤ :=
        ∏ k ∈ s', (∑ j : Fin 3, MvPolynomial.C (c k j) * MvPolynomial.X j) with hQ
      have hih : ∀ e' : Fin 3 →₀ ℕ,
          |(Q.coeff e' : ℝ)| ≤ (3 : ℝ) ^ s'.card * ∏ j : Fin 3, B j ^ (e' j) := by
        intro e'; rw [hQ]; exact ih e'
      have hcoeff : ((((∑ j : Fin 3, MvPolynomial.C (c a j) * MvPolynomial.X j) * Q).coeff e : ℤ) : ℝ)
          = ∑ j : Fin 3,
              (c a j : ℝ) * (if j ∈ e.support then (Q.coeff (e - Finsupp.single j 1) : ℝ) else 0) := by
        have hZ : ((∑ j : Fin 3, MvPolynomial.C (c a j) * MvPolynomial.X j) * Q).coeff e
            = ∑ j : Fin 3,
                c a j * (if j ∈ e.support then Q.coeff (e - Finsupp.single j 1) else 0) := by
          rw [Finset.sum_mul, MvPolynomial.coeff_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [mul_assoc, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_mul']
        rw [hZ]; push_cast
        refine Finset.sum_congr rfl (fun j _ => ?_); split <;> simp
      rw [hcoeff]
      calc |∑ j : Fin 3,
              (c a j : ℝ) * (if j ∈ e.support then (Q.coeff (e - Finsupp.single j 1) : ℝ) else 0)|
          ≤ ∑ j : Fin 3, |(c a j : ℝ) *
              (if j ∈ e.support then (Q.coeff (e - Finsupp.single j 1) : ℝ) else 0)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j : Fin 3, |(c a j : ℝ)| *
              (if j ∈ e.support then |(Q.coeff (e - Finsupp.single j 1) : ℝ)| else 0) := by
            apply Finset.sum_le_sum; intro j _
            rw [abs_mul]
            by_cases h : j ∈ e.support <;> simp [h]
        _ ≤ ∑ j : Fin 3, B j *
              (if j ∈ e.support then |(Q.coeff (e - Finsupp.single j 1) : ℝ)| else 0) := by
            apply Finset.sum_le_sum; intro j _
            apply mul_le_mul_of_nonneg_right (hc a j)
            by_cases h : j ∈ e.support <;> simp [h]
        _ ≤ ∑ j : Fin 3, B j * (if j ∈ e.support then
              (3 : ℝ) ^ s'.card * ∏ i : Fin 3,
                B i ^ ((e - Finsupp.single j 1 : Fin 3 →₀ ℕ) i) else 0) := by
            apply Finset.sum_le_sum; intro j _
            apply mul_le_mul_of_nonneg_left _ (hB j)
            by_cases h : j ∈ e.support
            · simp only [h, ite_true]; exact hih (e - Finsupp.single j 1)
            · simp [h]
        _ = ∑ j ∈ Finset.univ.filter (fun j : Fin 3 => j ∈ e.support), B j *
              ((3 : ℝ) ^ s'.card * ∏ i : Fin 3,
                B i ^ ((e - Finsupp.single j 1 : Fin 3 →₀ ℕ) i)) := by
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl; intro j _
            by_cases h : j ∈ e.support <;> simp [h]
        _ = ∑ j ∈ Finset.univ.filter (fun j : Fin 3 => j ∈ e.support),
              ((3 : ℝ) ^ s'.card * ∏ i : Fin 3, B i ^ (e i)) := by
            apply Finset.sum_congr rfl; intro j hj
            rw [Finset.mem_filter] at hj
            rw [← mul_assoc, mul_comm (B j) ((3 : ℝ) ^ s'.card), mul_assoc,
              pow_prod_tsub_single B e j hj.2]
        _ = ((Finset.univ.filter (fun j : Fin 3 => j ∈ e.support)).card : ℝ) *
              ((3 : ℝ) ^ s'.card * ∏ i : Fin 3, B i ^ (e i)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 3 * ((3 : ℝ) ^ s'.card * ∏ i : Fin 3, B i ^ (e i)) := by
            apply mul_le_mul_of_nonneg_right _ _
            · have hcardle : (Finset.univ.filter (fun j : Fin 3 => j ∈ e.support)).card ≤ 3 := by
                simpa using
                  Finset.card_le_univ (Finset.univ.filter (fun j : Fin 3 => j ∈ e.support))
              exact_mod_cast hcardle
            · exact mul_nonneg (pow_nonneg (by norm_num) _)
                (Finset.prod_nonneg (fun i _ => pow_nonneg (hB i) _))
        _ = (3 : ℝ) ^ (s'.card + 1) * ∏ i : Fin 3, B i ^ (e i) := by
            rw [pow_succ]; ring

/-- `verPoly v m` as a product of `∑_i m_i = 4` linear forms. -/
lemma verPoly_eq_prod_sigma (v : Fin 3 → (Fin 5 → ℤ)) (m : Work.HP.Mon 4 4) :
    (∏ k : (Σ i : Fin 5, Fin (m.1 i : ℕ)), Work.HP.linForm v k.1)
      = Work.HP.verPoly v m := by
  rw [Work.HP.verPoly, Fintype.prod_sigma]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [show (∏ y : Fin (m.1 i : ℕ),
        Work.HP.linForm v ((⟨i, y⟩ : (Σ j : Fin 5, Fin (m.1 j : ℕ))).1))
      = ∏ _y : Fin (m.1 i : ℕ), Work.HP.linForm v i from by
        apply Finset.prod_congr rfl; intro y _; rfl]
  rw [Finset.prod_const]
  simp

/-- The number of linear-form factors attached to `m` is `4`. -/
lemma card_sigma_mon (m : Work.HP.Mon 4 4) :
    (Finset.univ : Finset (Σ i : Fin 5, Fin (m.1 i : ℕ))).card = 4 := by
  rw [Finset.card_univ, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact m.2

theorem abs_wCoeff_le (v : Fin 3 → (Fin 5 → ℤ)) (B : Fin 3 → ℝ)
    (hB : ∀ j, 1 ≤ B j) (hv : ∀ (i : Fin 5) (j : Fin 3), |(v j i : ℝ)| ≤ B j)
    (e : Fin 3 →₀ ℕ) (m : Work.HP.Mon 4 4) :
    |(Work.HP.wCoeff v e m : ℝ)| ≤ 10000 * ∏ j : Fin 3, B j ^ (e j) := by
  have hB0 : ∀ j, 0 ≤ B j := fun j => le_trans zero_le_one (hB j)
  have hprod_nonneg : 0 ≤ ∏ j : Fin 3, B j ^ (e j) :=
    Finset.prod_nonneg (fun j _ => pow_nonneg (hB0 j) _)
  have hmain := abs_coeff_prod_linForm_le
    (s := (Finset.univ : Finset (Σ i : Fin 5, Fin (m.1 i : ℕ))))
    (c := fun k j => v j k.1) (B := B) hB0 (fun k j => hv k.1 j) e
  have hA : (∏ k ∈ (Finset.univ : Finset (Σ i : Fin 5, Fin (m.1 i : ℕ))),
        (∑ j : Fin 3, MvPolynomial.C (v j k.1) * MvPolynomial.X j))
      = Work.HP.verPoly v m := by
    rw [← verPoly_eq_prod_sigma v m]
    apply Finset.prod_congr rfl; intro k _
    rw [Work.HP.linForm]
  rw [hA, card_sigma_mon m, show (3 : ℝ) ^ 4 = 81 from by norm_num] at hmain
  unfold Work.HP.wCoeff
  calc |((Work.HP.verPoly v m).coeff e : ℝ)| ≤ 81 * ∏ j : Fin 3, B j ^ (e j) := hmain
    _ ≤ 10000 * ∏ j : Fin 3, B j ^ (e j) := by
        apply mul_le_mul_of_nonneg_right (by norm_num : (81 : ℝ) ≤ 10000) hprod_nonneg

end Work.HP.Q44Child
