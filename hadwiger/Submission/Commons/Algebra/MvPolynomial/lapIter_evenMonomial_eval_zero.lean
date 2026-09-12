import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial

open scoped BigOperators
open MvPolynomial
open Finsupp
open Nat

namespace Commons.Algebra.MvPolynomial

abbrev P (n : ℕ) := MvPolynomial (Fin n) ℝ

-- ============================================================
-- Section A : lapFun and iterate linearity
-- ============================================================

private noncomputable def lapFun (n : ℕ) : P n → P n :=
  fun Q => ∑ i : Fin n, pderiv (R := ℝ) i (pderiv (R := ℝ) i Q)

private noncomputable def ev0 (n : ℕ) : P n → ℝ :=
  fun p => MvPolynomial.eval (fun _ : Fin n => (0 : ℝ)) p

private lemma lapFun_add (n : ℕ) (x y : P n) : lapFun n (x + y) = lapFun n x + lapFun n y := by
  classical
  simp [lapFun, Finset.sum_add_distrib]

private lemma lapFun_smul (n : ℕ) (a : ℝ) (x : P n) : lapFun n (a • x) = a • lapFun n x := by
  classical
  simp [lapFun, Finset.smul_sum]

private lemma lapFun_zero (n : ℕ) : lapFun n 0 = 0 := by simp [lapFun]

private lemma lapFun_sum (n : ℕ) {ι : Type*} (s : Finset ι) (f : ι → P n) :
    lapFun n (∑ i ∈ s, f i) = ∑ i ∈ s, lapFun n (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [lapFun_zero]
  · intro a s' has' ih
    simp [has', Finset.sum_insert, lapFun_add, ih]

private lemma lapFun_iterate_add (n : ℕ) (k : ℕ) (x y : P n) :
    (lapFun n)^[k] (x + y) = (lapFun n)^[k] x + (lapFun n)^[k] y := by
  revert x y
  induction k with
  | zero => intro x y; simp
  | succ k ih =>
      intro x y
      rw [Function.iterate_succ_apply]
      rw [lapFun_add]
      exact ih (lapFun n x) (lapFun n y)

private lemma lapFun_iterate_smul (n : ℕ) (k : ℕ) (a : ℝ) (x : P n) :
    (lapFun n)^[k] (a • x) = a • (lapFun n)^[k] x := by
  revert a x
  induction k with
  | zero => intro a x; simp
  | succ k ih =>
      intro a x
      rw [Function.iterate_succ_apply]
      rw [lapFun_smul]
      exact ih a (lapFun n x)

private lemma lapFun_iterate_sum (n : ℕ) (k : ℕ) {ι : Type*} (s : Finset ι) (f : ι → P n) :
    (lapFun n)^[k] (∑ i ∈ s, f i) = ∑ i ∈ s, (lapFun n)^[k] (f i) := by
  classical
  revert f
  induction k with
  | zero => intro f; simp
  | succ k ih =>
      intro f
      rw [Function.iterate_succ_apply]
      rw [lapFun_sum]
      rw [ih (fun i => lapFun n (f i))]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Function.iterate_succ_apply]

private lemma ev0_add (n : ℕ) (x y : P n) : ev0 n (x + y) = ev0 n x + ev0 n y := by
  simp [ev0]
private lemma ev0_smul (n : ℕ) (a : ℝ) (x : P n) : ev0 n (a • x) = a • ev0 n x := by
  simp [ev0, smul_eq_C_mul]
private lemma ev0_sum (n : ℕ) {ι : Type*} (s : Finset ι) (f : ι → P n) :
    ev0 n (∑ i ∈ s, f i) = ∑ i ∈ s, ev0 n (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [ev0]
  · intro a s' has' ih
    simp [has', Finset.sum_insert, ev0_add, ih]

-- ============================================================
-- Section B : derivative of even monomial
-- ============================================================

private lemma two_smul_apply (n : ℕ) (β : Fin n →₀ ℕ) (i : Fin n) :
    ((2 • β : Fin n →₀ ℕ) i) = 2 * β i := by
  simp

private lemma tsub_single_apply (n : ℕ) (β : Fin n →₀ ℕ) (i : Fin n) :
    (((2 • β : Fin n →₀ ℕ) - single i (1 : ℕ)) i) = 2 * β i - 1 := by
  rw [Finsupp.tsub_apply]
  rw [two_smul_apply]
  simp

private lemma exp_tsub_tsub (n : ℕ) (β : Fin n →₀ ℕ) (i : Fin n) :
    (((2 • β : Fin n →₀ ℕ) - single i (1 : ℕ)) - single i (1 : ℕ)) =
      2 • (β - single i (1 : ℕ)) := by
  ext j
  by_cases hji : j = i
  · subst j
    simp only [Finsupp.tsub_apply, two_smul_apply, nsmul_eq_mul]
    simp only [Finsupp.single_eq_same]
    omega
  · rw [Finsupp.tsub_apply, Finsupp.tsub_apply]
    simp [Finsupp.single_eq_of_ne hji]

private lemma pderiv2_even_monomial (n : ℕ) (β : Fin n →₀ ℕ) (i : Fin n) :
    pderiv (R := ℝ) i (pderiv (R := ℝ) i (monomial (2 • β) (1 : ℝ))) =
      monomial (2 • (β - single i (1 : ℕ)))
        ((((2 * β i : ℕ) : ℝ) * (((2 * β i - 1 : ℕ) : ℕ) : ℝ))) := by
  classical
  rw [MvPolynomial.pderiv_monomial, MvPolynomial.pderiv_monomial]
  rw [exp_tsub_tsub]
  simp only [one_mul, two_smul_apply, tsub_single_apply]

private lemma lapFun_even_monomial (n : ℕ) (β : Fin n →₀ ℕ) :
    lapFun n (monomial (2 • β) (1 : ℝ)) =
      ∑ i ∈ β.support, monomial (2 • (β - single i (1 : ℕ)))
        ((((2 * β i : ℕ) : ℝ) * (((2 * β i - 1 : ℕ) : ℕ) : ℝ))) := by
  classical
  unfold lapFun
  rw [← Finset.sum_subset (s₁ := β.support) (s₂ := Finset.univ)]
  · apply Finset.sum_congr rfl
    intro i hi
    exact pderiv2_even_monomial n β i
  · intro i hi
    simp
  · intro i hi hi'
    rw [pderiv2_even_monomial]
    have hβ0 : β i = 0 := by
      by_contra h
      exact hi' (Finsupp.mem_support_iff.mpr (by simpa using h))
    simp [hβ0]

private lemma monomial_smul_coeff {n : ℕ} (s : Fin n →₀ ℕ) (a : ℝ) :
    (monomial s a : P n) = a • (monomial s (1 : ℝ) : P n) := by
  rw [smul_eq_C_mul, MvPolynomial.C_mul_monomial, mul_one]

-- ============================================================
-- Section C : arithmetic identities
-- ============================================================

private lemma dF_odd_rec (k : ℕ) (hk : 1 ≤ k) :
    Nat.doubleFactorial (2 * k - 1) = (2 * k - 1) * Nat.doubleFactorial (2 * k - 3) := by
  have h1 : Nat.doubleFactorial (2 * k - 1) = Nat.doubleFactorial ((2 * k - 2) + 1) := by
    congr 1
    omega
  rw [h1, Nat.doubleFactorial_add_one]
  congr 1
  omega

private lemma term_identity_nat (n : ℕ) (β : Fin n →₀ ℕ) (i : Fin n) (hi : 1 ≤ β i) :
    (2 * β i) * (2 * β i - 1) * (∏ j : Fin n, Nat.doubleFactorial (2 * (β - (single i (1 : ℕ) : Fin n →₀ ℕ)) j - 1))
      = (2 * β i) * (∏ j : Fin n, Nat.doubleFactorial (2 * β j - 1)) := by
  classical
  let e : Fin n →₀ ℕ := single i (1 : ℕ)
  let f := fun j : Fin n => Nat.doubleFactorial (2 * β j - 1)
  let g := fun j : Fin n => Nat.doubleFactorial (2 * (β - e) j - 1)
  have he : e = single i (1 : ℕ) := rfl
  have hf : ∀ j : Fin n, j ≠ i → f j = g j := by
    intro j hj
    have hje : (β - e) j = β j := by
      rw [he]
      rw [Finsupp.tsub_apply]
      rw [Finsupp.single_eq_of_ne hj]
      rw [Nat.sub_zero]
    change Nat.doubleFactorial (2 * β j - 1) = Nat.doubleFactorial (2 * (β - e) j - 1)
    rw [hje]
  have hgi : g i = Nat.doubleFactorial (2 * β i - 3) := by
    have hie : (β - e) i = β i - 1 := by
      rw [he]
      rw [Finsupp.tsub_apply]
      simp only [Finsupp.single_eq_same]
    calc
      g i = Nat.doubleFactorial (2 * (β - e) i - 1) := rfl
      _ = Nat.doubleFactorial (2 * (β i - 1) - 1) := by rw [hie]
      _ = Nat.doubleFactorial (2 * β i - 3) := by congr 1; omega
  have hfi : f i = Nat.doubleFactorial (2 * β i - 1) := by rfl
  have hprod : (∏ j : Fin n, g j) = g i * (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, g j) := by
    rw [Finset.mul_prod_erase (s := (Finset.univ : Finset (Fin n))) (f := g) (a := i) (by simp)]
  have hprod' : (∏ j : Fin n, f j) = f i * (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, f j) := by
    rw [Finset.mul_prod_erase (s := (Finset.univ : Finset (Fin n))) (f := f) (a := i) (by simp)]
  have herase : (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, g j)
      = (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, f j) := by
    apply Finset.prod_congr rfl
    intro j hj
    exact (hf j (Finset.mem_erase.mp hj).1).symm
  calc
    (2 * β i) * (2 * β i - 1) * (∏ j : Fin n, g j)
        = (2 * β i) * (2 * β i - 1) * (g i * (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, g j)) := by
            rw [hprod]
    _ = (2 * β i) * (2 * β i - 1) * (Nat.doubleFactorial (2 * β i - 3)
            * (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, g j)) := by
            rw [hgi]
    _ = (2 * β i) * (Nat.doubleFactorial (2 * β i - 1))
            * (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, g j) := by
            rw [dF_odd_rec (β i) (by omega : 1 ≤ β i)]
            ring
    _ = (2 * β i) * (f i * (∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, f j)) := by
            rw [← hfi]
            rw [herase]
            ring
    _ = (2 * β i) * (∏ j : Fin n, f j) := by
            rw [← hprod']

private lemma term_identity_real (n : ℕ) (β : Fin n →₀ ℕ) (i : Fin n) (hi : i ∈ β.support) :
    (((2 * β i : ℕ) : ℝ) * (((2 * β i - 1 : ℕ) : ℕ) : ℝ)) *
        (∏ j : Fin n, ((Nat.doubleFactorial (2 * (β - (single i (1 : ℕ) : Fin n →₀ ℕ)) j - 1) : ℕ) : ℝ))
      = ((2 * β i : ℕ) : ℝ) * (∏ j : Fin n, ((Nat.doubleFactorial (2 * β j - 1) : ℕ) : ℝ)) := by
  have hne : β i ≠ 0 := Finsupp.mem_support_iff.mp hi
  have hi1 : 1 ≤ β i := by omega
  exact_mod_cast term_identity_nat n β i hi1

private lemma sum_sub_single (n : ℕ) (β : Fin n →₀ ℕ) (i : Fin n) (hi : β i ≠ 0) :
    (∑ j : Fin n, (β - (Finsupp.single i (1 : ℕ) : Fin n →₀ ℕ)) j) = (∑ j : Fin n, β j) - 1 := by
  classical
  let e : Fin n →₀ ℕ := Finsupp.single i (1 : ℕ)
  have hie : (β - e) i = β i - 1 := by
    rw [Finsupp.tsub_apply]
    simp [e]
  have hje : ∀ j : Fin n, j ≠ i → (β - e) j = β j := by
    intro j hj
    rw [Finsupp.tsub_apply]
    simp [e, Finsupp.single_eq_of_ne hj]
  calc
    (∑ j : Fin n, (β - e) j)
        = (∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, (β - e) j) + (β - e) i := by
            rw [← Finset.sum_erase_add (s := (Finset.univ : Finset (Fin n)))
                  (f := fun j => (β - e) j) (a := i) (Finset.mem_univ i)]
    _ = (∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, β j) + (β i - 1) := by
            congr 1
            · apply Finset.sum_congr rfl
              intro j hj
              exact hje j (Finset.mem_erase.mp hj).1
    _ = (∑ j : Fin n, β j) - 1 := by
            have hsum : (∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, β j) + β i = ∑ j : Fin n, β j := by
              exact Finset.sum_erase_add (s := (Finset.univ : Finset (Fin n)))
                  (f := fun j => β j) (a := i) (Finset.mem_univ i)
            omega

private lemma sum_two_support (n : ℕ) (β : Fin n →₀ ℕ) :
    (∑ i ∈ β.support, (2 * β i : ℕ)) = 2 * (∑ j : Fin n, β j) := by
  classical
  calc
    (∑ i ∈ β.support, (2 * β i : ℕ)) = ∑ i : Fin n, (2 * β i : ℕ) := by
        rw [Finset.sum_subset (s₁ := β.support) (s₂ := Finset.univ)]
        · intro i hi
          simp
        · intro i hi hi'
          have hβ0 : β i = 0 := by
            by_contra h
            exact hi' (Finsupp.mem_support_iff.mpr (by simpa using h))
          simp [hβ0]
    _ = 2 * (∑ j : Fin n, β j) := by
        rw [← Finset.mul_sum]

private lemma sum_two_support_real (n : ℕ) (β : Fin n →₀ ℕ) :
    (∑ i ∈ β.support, ((2 * β i : ℕ) : ℝ)) = ((2 * (∑ j : Fin n, β j) : ℕ) : ℝ) := by
  exact_mod_cast sum_two_support n β

private lemma step_arith (n t : ℕ) (β : Fin n →₀ ℕ) (hβ0 : (∑ i : Fin n, β i) = t + 1) :
    (∑ i ∈ β.support,
        ((((2 * β i : ℕ) : ℝ) * (((2 * β i - 1 : ℕ) : ℕ) : ℝ)) *
          ((Nat.factorial t : ℝ) * (2 : ℝ)^t *
            (∏ j : Fin n, ((Nat.doubleFactorial (2 * (β - (single i (1 : ℕ) : Fin n →₀ ℕ)) j - 1) : ℕ) : ℝ)))))
      = (Nat.factorial (t + 1) : ℝ) * (2 : ℝ)^(t+1) *
          (∏ i : Fin n, ((Nat.doubleFactorial (2 * β i - 1) : ℕ) : ℝ)) := by
  classical
  let B : ℝ := ∏ i : Fin n, ((Nat.doubleFactorial (2 * β i - 1) : ℕ) : ℝ)
  have hterm : ∀ i ∈ β.support,
      (((2 * β i : ℕ) : ℝ) * (((2 * β i - 1 : ℕ) : ℕ) : ℝ)) *
          ((Nat.factorial t : ℝ) * (2 : ℝ)^t *
            (∏ j : Fin n, ((Nat.doubleFactorial (2 * (β - (single i (1 : ℕ) : Fin n →₀ ℕ)) j - 1) : ℕ) : ℝ)))
        = (Nat.factorial t : ℝ) * (2 : ℝ)^t * ((2 * β i : ℕ) : ℝ) * B := by
      intro i hi
      have htr := term_identity_real n β i hi
      dsimp [B]
      have htr' : (((2 * β i : ℕ) : ℝ) * (((2 * β i - 1 : ℕ) : ℕ) : ℝ)) *
            (∏ j : Fin n, ((Nat.doubleFactorial (2 * (β - (single i (1 : ℕ) : Fin n →₀ ℕ)) j - 1) : ℕ) : ℝ))
          = ((2 * β i : ℕ) : ℝ) * (∏ i : Fin n, ((Nat.doubleFactorial (2 * β i - 1) : ℕ) : ℝ)) := htr
      calc
        (((2 * β i : ℕ) : ℝ) * (((2 * β i - 1 : ℕ) : ℕ) : ℝ)) *
            ((Nat.factorial t : ℝ) * (2 : ℝ)^t *
              (∏ j : Fin n, ((Nat.doubleFactorial (2 * (β - (single i (1 : ℕ) : Fin n →₀ ℕ)) j - 1) : ℕ) : ℝ)))
            = ((Nat.factorial t : ℝ) * (2 : ℝ)^t) *
                ((((2 * β i : ℕ) : ℝ) * (((2 * β i - 1 : ℕ) : ℕ) : ℝ)) *
                  (∏ j : Fin n, ((Nat.doubleFactorial (2 * (β - (single i (1 : ℕ) : Fin n →₀ ℕ)) j - 1) : ℕ) : ℝ))) := by ring
        _ = ((Nat.factorial t : ℝ) * (2 : ℝ)^t) *
                (((2 * β i : ℕ) : ℝ) * (∏ i : Fin n, ((Nat.doubleFactorial (2 * β i - 1) : ℕ) : ℝ))) := by
                rw [htr']
        _ = (Nat.factorial t : ℝ) * (2 : ℝ)^t * ((2 * β i : ℕ) : ℝ) *
                (∏ i : Fin n, ((Nat.doubleFactorial (2 * β i - 1) : ℕ) : ℝ)) := by ring
  calc
    (∑ i ∈ β.support,
        ((((2 * β i : ℕ) : ℝ) * (((2 * β i - 1 : ℕ) : ℕ) : ℝ)) *
          ((Nat.factorial t : ℝ) * (2 : ℝ)^t *
            (∏ j : Fin n, ((Nat.doubleFactorial (2 * (β - (single i (1 : ℕ) : Fin n →₀ ℕ)) j - 1) : ℕ) : ℝ)))))
        = ∑ i ∈ β.support, ((Nat.factorial t : ℝ) * (2 : ℝ)^t * ((2 * β i : ℕ) : ℝ) * B) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hterm i hi
    _ = ∑ i ∈ β.support, (((Nat.factorial t : ℝ) * (2 : ℝ)^t * B) * ((2 * β i : ℕ) : ℝ)) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
    _ = ((Nat.factorial t : ℝ) * (2 : ℝ)^t * B) * (∑ i ∈ β.support, ((2 * β i : ℕ) : ℝ)) := by
            rw [← Finset.mul_sum]
    _ = ((Nat.factorial t : ℝ) * (2 : ℝ)^t * B) * ((2 * (∑ j : Fin n, β j) : ℕ) : ℝ) := by
            rw [sum_two_support_real]
    _ = ((Nat.factorial t : ℝ) * (2 : ℝ)^t * B) * ((2 * (t + 1) : ℕ) : ℝ) := by
            rw [hβ0]
    _ = (Nat.factorial (t + 1) : ℝ) * (2 : ℝ)^(t+1) * B := by
            dsimp [B]
            have h2 : ((2 * (t + 1) : ℕ) : ℝ) = 2 * ((t + 1 : ℕ) : ℝ) := by norm_num
            rw [h2]
            rw [Nat.factorial_succ]
            norm_num
            ring

-- ============================================================
-- Section D : the main recursion
-- ============================================================

private lemma coord_le_sum (n : ℕ) (β : Fin n →₀ ℕ) (i : Fin n) :
    β i ≤ ∑ j : Fin n, β j := by
  classical
  have h := Finset.single_le_sum (s := (Finset.univ : Finset (Fin n)))
    (f := fun j : Fin n => β j • (1 : ℕ))
    (by intro j hj; exact Nat.zero_le _) (a := i) (Finset.mem_univ i)
  simpa using h

private lemma beta_eq_zero_of_sum_zero {n : ℕ} (β : Fin n →₀ ℕ)
    (hw : (∑ i : Fin n, β i) = 0) : β = 0 := by
  ext i
  by_contra h
  have hpos : 0 < β i := Nat.pos_of_ne_zero h
  have hle : β i ≤ ∑ j : Fin n, β j := coord_le_sum n β i
  omega

private lemma sum_beta_sub_single {n t : ℕ} (β : Fin n →₀ ℕ) (i : Fin n)
    (hw : (∑ j : Fin n, β j) = t + 1) (hi : i ∈ β.support) :
    (∑ j : Fin n, (β - (single i (1 : ℕ) : Fin n →₀ ℕ)) j) = t := by
  have hne : β i ≠ 0 := Finsupp.mem_support_iff.mp hi
  rw [sum_sub_single n β i hne]
  omega

private theorem main {n : ℕ} : ∀ (m : ℕ) (β : Fin n →₀ ℕ),
    (∑ i : Fin n, β i) = m →
    ev0 n ((lapFun n)^[m] (monomial (2 • β) (1 : ℝ))) =
      (Nat.factorial m : ℝ) * (2 : ℝ)^m *
        (∏ i : Fin n, ((Nat.doubleFactorial (2 * β i - 1) : ℕ) : ℝ)) := by
  intro m
  induction m with
  | zero =>
      intro β hw
      have hβ0 : β = 0 := beta_eq_zero_of_sum_zero β hw
      simp [ev0, hβ0]
  | succ t ih =>
      intro β hw
      have hw' : (∑ i : Fin n, β i) = t + 1 := by omega
      calc
        ev0 n ((lapFun n)^[succ t] (monomial (2 • β) (1 : ℝ)))
            = ev0 n ((lapFun n)^[t] (lapFun n (monomial (2 • β) (1 : ℝ)))) := by
                rw [Function.iterate_succ_apply]
        _ = ev0 n ((lapFun n)^[t]
              (∑ i ∈ β.support, monomial (2 • (β - single i (1 : ℕ)))
                ((((2 * β i : ℕ) : ℝ) * (((2 * β i - 1 : ℕ) : ℕ) : ℝ))))) := by
                rw [lapFun_even_monomial]
        _ = ev0 n (∑ i ∈ β.support, (lapFun n)^[t]
              (monomial (2 • (β - single i (1 : ℕ)))
                ((((2 * β i : ℕ) : ℝ) * (((2 * β i - 1 : ℕ) : ℕ) : ℝ))))) := by
                rw [lapFun_iterate_sum]
        _ = (∑ i ∈ β.support, ev0 n ((lapFun n)^[t]
              (monomial (2 • (β - single i (1 : ℕ)))
                ((((2 * β i : ℕ) : ℝ) * (((2 * β i - 1 : ℕ) : ℕ) : ℝ)))))) := by
                rw [ev0_sum]
        _ = (∑ i ∈ β.support,
              ((((2 * β i : ℕ) : ℝ) * (((2 * β i - 1 : ℕ) : ℕ) : ℝ))) •
                ev0 n ((lapFun n)^[t] (monomial (2 • (β - single i (1 : ℕ))) (1 : ℝ)))) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [monomial_smul_coeff]
                rw [lapFun_iterate_smul]
                rw [ev0_smul]
        _ = (∑ i ∈ β.support,
              ((((2 * β i : ℕ) : ℝ) * (((2 * β i - 1 : ℕ) : ℕ) : ℝ))) •
                ((Nat.factorial t : ℝ) * (2 : ℝ)^t *
                  (∏ j : Fin n, ((Nat.doubleFactorial (2 * (β - single i (1 : ℕ)) j - 1) : ℕ) : ℝ)))) := by
                apply Finset.sum_congr rfl
                intro i hi
                congr 1
                exact ih (β - single i (1 : ℕ)) (sum_beta_sub_single β i hw' hi)
        _ = (∑ i ∈ β.support,
              ((((2 * β i : ℕ) : ℝ) * (((2 * β i - 1 : ℕ) : ℕ) : ℝ))) *
                ((Nat.factorial t : ℝ) * (2 : ℝ)^t *
                  (∏ j : Fin n, ((Nat.doubleFactorial (2 * (β - single i (1 : ℕ)) j - 1) : ℕ) : ℝ)))) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [smul_eq_mul]
        _ = (Nat.factorial (t + 1) : ℝ) * (2 : ℝ)^(t + 1) *
              (∏ i : Fin n, ((Nat.doubleFactorial (2 * β i - 1) : ℕ) : ℝ)) := by
                exact step_arith n t β hw'
        _ = (Nat.factorial (succ t) : ℝ) * (2 : ℝ)^(succ t) *
              (∏ i : Fin n, ((Nat.doubleFactorial (2 * β i - 1) : ℕ) : ℝ)) := by
                norm_num

-- ============================================================
-- Section E : product form and final theorem
-- ============================================================

private lemma univ_indicator_two_smul {n : ℕ} (β : Fin n →₀ ℕ) :
    (Finsupp.indicator (Finset.univ : Finset (Fin n)) (fun i _ => 2 * β i)) = (2 • β) := by
  ext i
  simp [Finsupp.indicator_apply, Finsupp.coe_nsmul]

private lemma prod_even_eq_monomial {n : ℕ} (β : Fin n →₀ ℕ) :
    (∏ i : Fin n, (X i : MvPolynomial (Fin n) ℝ) ^ (2 * β i)) =
      monomial (2 • β) (1 : ℝ) := by
  classical
  rw [MvPolynomial.prod_X_pow]
  rw [univ_indicator_two_smul]

theorem lapIter_evenMonomial_eval_zero
    {n : ℕ} {m : ℕ} (β : Fin n →₀ ℕ)
    (hw : (Finset.univ.sum (fun i : Fin n => β i)) = m) :
    MvPolynomial.eval (fun _ : Fin n => (0 : ℝ))
      ((fun Q : MvPolynomial (Fin n) ℝ =>
          Finset.univ.sum (fun i : Fin n => MvPolynomial.pderiv i (MvPolynomial.pderiv i Q)))^[m]
        (Finset.univ.prod (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℝ) ^ (2 * β i)))) =
      (Nat.factorial m : ℝ) * (2 : ℝ) ^ m * (Finset.univ.prod
        (fun i : Fin n => ((Nat.doubleFactorial (2 * β i - 1) : ℕ) : ℝ))) := by
  classical
  rw [prod_even_eq_monomial]
  change ev0 n ((lapFun n)^[m] (monomial (2 • β) (1 : ℝ))) =
      (Nat.factorial m : ℝ) * (2 : ℝ) ^ m *
        (Finset.univ.prod (fun i : Fin n => ((Nat.doubleFactorial (2 * β i - 1) : ℕ) : ℝ)))
  exact main m β hw

end Commons.Algebra.MvPolynomial