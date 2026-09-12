import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum.Ineq

namespace Commons.Analysis.MvPolynomial

set_option autoImplicit false

open scoped BigOperators

noncomputable section

/-- All coefficients of a real multivariate polynomial are nonnegative. -/
private def CoeffNonneg {σ : Type*} (p : MvPolynomial σ ℝ) : Prop :=
  ∀ m : σ →₀ ℕ, 0 ≤ p.coeff m

/-- Nonnegativity of coefficients is preserved by addition. -/
private lemma coeffNonneg_add {σ : Type*} (p q : MvPolynomial σ ℝ)
    (hp : CoeffNonneg p) (hq : CoeffNonneg q) : CoeffNonneg (p + q) := by
  intro m
  change 0 ≤ p.coeff m + q.coeff m
  exact add_nonneg (hp m) (hq m)

/-- Nonnegativity of coefficients is preserved by multiplication. -/
private lemma coeffNonneg_mul {σ : Type*} (p q : MvPolynomial σ ℝ)
    (hp : CoeffNonneg p) (hq : CoeffNonneg q) : CoeffNonneg (p * q) := by
  classical
  intro m
  rw [MvPolynomial.coeff_mul]
  exact Finset.sum_nonneg (fun x hx => mul_nonneg (hp x.1) (hq x.2))

/-- Nonnegative constants have nonnegative coefficients. -/
private lemma coeffNonneg_C {σ : Type*} (a : ℝ) (ha : 0 ≤ a) :
    CoeffNonneg (MvPolynomial.C a : MvPolynomial σ ℝ) := by
  classical
  intro m
  rw [MvPolynomial.coeff_C]
  split_ifs with h <;> simp [ha]

/-- Variables have nonnegative coefficients. -/
private lemma coeffNonneg_X {σ : Type*} (i : σ) :
    CoeffNonneg (MvPolynomial.X i : MvPolynomial σ ℝ) := by
  classical
  intro m
  rw [MvPolynomial.coeff_X]
  split_ifs with h <;> norm_num

/-- Nonnegativity of coefficients is preserved by powers. -/
private lemma coeffNonneg_pow {σ : Type*} (p : MvPolynomial σ ℝ)
    (hp : CoeffNonneg p) (k : ℕ) : CoeffNonneg (p ^ k) := by
  classical
  induction k with
  | zero =>
      simpa using (coeffNonneg_C (σ := σ) (1 : ℝ) (by norm_num))
  | succ k ih =>
      rw [pow_succ]
      exact coeffNonneg_mul (p ^ k) p ih hp

/-- A finite product of polynomials with nonnegative coefficients has nonnegative
coefficients. -/
private lemma coeffNonneg_prod {σ α : Type*} (s : Finset α) (h : α → MvPolynomial σ ℝ)
    (hh : ∀ i ∈ s, CoeffNonneg (h i)) : CoeffNonneg (∏ i ∈ s, h i) := by
  classical
  revert hh
  induction s using Finset.induction_on with
  | empty =>
      intro hh
      simpa using (coeffNonneg_C (σ := σ) (1 : ℝ) (by norm_num))
  | insert a s ha ih =>
      intro hh
      rw [Finset.prod_insert ha]
      exact coeffNonneg_mul (h a) (∏ i ∈ s, h i)
        (hh a (Finset.mem_insert_self a s))
        (ih (fun i hi => hh i (Finset.mem_insert_of_mem hi)))

/-- A finite product of powers of polynomials with nonnegative coefficients has
nonnegative coefficients. -/
private lemma coeffNonneg_prod_pow {σ α : Type*} (s : Finset α)
    (f : α → MvPolynomial σ ℝ) (e : α → ℕ)
    (hf : ∀ i ∈ s, CoeffNonneg (f i)) : CoeffNonneg (∏ i ∈ s, f i ^ e i) := by
  refine coeffNonneg_prod s (fun i => f i ^ e i) ?_
  intro i hi
  exact coeffNonneg_pow (f i) (hf i hi) (e i)

/-- Substituting each variable by a polynomial with nonnegative coefficients sends a
monomial with a nonnegative coefficient to a polynomial with nonnegative coefficients. -/
private lemma coeffNonneg_bind₁_monomial {σ τ : Type*} (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ i, CoeffNonneg (f i)) (v : σ →₀ ℕ) (a : ℝ) (ha : 0 ≤ a) :
    CoeffNonneg (MvPolynomial.bind₁ f (MvPolynomial.monomial v a)) := by
  classical
  intro m
  have hmain : (MvPolynomial.bind₁ f) (MvPolynomial.monomial v a)
      = MvPolynomial.C a * v.prod (fun n e => (f n) ^ e) := by
    rw [MvPolynomial.monomial_eq]
    rw [map_mul, MvPolynomial.bind₁_C_right]
    congr 1
    change (MvPolynomial.bind₁ f) (∏ x ∈ v.support, MvPolynomial.X x ^ (v x))
        = ∏ x ∈ v.support, (f x) ^ (v x)
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro x hx
    rw [map_pow, MvPolynomial.bind₁_X_right]
  have hprod : CoeffNonneg (v.prod fun n e => (f n) ^ e) := by
    change CoeffNonneg (∏ x ∈ v.support, (f x) ^ (v x))
    exact coeffNonneg_prod_pow v.support f (fun i => v i) (fun i hi => hf i)
  rw [hmain]
  rw [MvPolynomial.coeff_C_mul]
  exact mul_nonneg ha (hprod m)

/-- Substituting each variable by a polynomial with nonnegative coefficients preserves
nonnegativity of all coefficients. -/
private lemma coeffNonneg_bind₁ {σ τ : Type*} (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ i, CoeffNonneg (f i)) (p : MvPolynomial σ ℝ) (hp : CoeffNonneg p) :
    CoeffNonneg (MvPolynomial.bind₁ f p) := by
  classical
  intro m
  have hmain : (MvPolynomial.bind₁ f) p
      = ∑ v ∈ p.support, (MvPolynomial.bind₁ f) (MvPolynomial.monomial v (p.coeff v)) := by
    calc
      (MvPolynomial.bind₁ f) p
          = (MvPolynomial.bind₁ f) (∑ v ∈ p.support, MvPolynomial.monomial v (p.coeff v)) := by
              congr 1
              exact MvPolynomial.as_sum p
      _ = ∑ v ∈ p.support, (MvPolynomial.bind₁ f) (MvPolynomial.monomial v (p.coeff v)) := by
              rw [map_sum]
  rw [hmain]
  rw [MvPolynomial.coeff_sum]
  exact Finset.sum_nonneg (fun v hv => (coeffNonneg_bind₁_monomial f hf v (p.coeff v) (hp v)) m)

/-- If `p` has nonnegative coefficients and every `w i` is nonnegative, then the
substitution `X_i ↦ X_i + C (w i)` preserves nonnegativity of all coefficients. -/
theorem coeff_nonneg_bind_add (n : ℕ) (p : MvPolynomial (Fin n) ℝ) (w : Fin n → ℝ)
    (hp : ∀ m : Fin n →₀ ℕ, 0 ≤ p.coeff m) (hw : ∀ i : Fin n, 0 ≤ w i) :
    ∀ m : Fin n →₀ ℕ,
      0 ≤ (MvPolynomial.bind₁ (fun i : Fin n => MvPolynomial.X i + MvPolynomial.C (w i)) p).coeff m := by
  classical
  let f : Fin n → MvPolynomial (Fin n) ℝ :=
    fun i => MvPolynomial.X i + MvPolynomial.C (w i)
  have hf : ∀ i, CoeffNonneg (f i) := by
    intro i
    exact coeffNonneg_add (MvPolynomial.X i) (MvPolynomial.C (w i))
      (coeffNonneg_X (σ := Fin n) i) (coeffNonneg_C (w i) (hw i))
  intro m
  change 0 ≤ ((MvPolynomial.bind₁ f) p).coeff m
  exact (coeffNonneg_bind₁ f hf p hp) m

end

end Commons.Analysis.MvPolynomial