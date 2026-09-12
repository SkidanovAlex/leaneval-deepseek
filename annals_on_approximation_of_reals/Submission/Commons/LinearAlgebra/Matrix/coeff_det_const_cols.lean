import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace Commons.LinearAlgebra.Matrix

open Polynomial
open scoped BigOperators

/-- Coefficient of `X^k` in a product of polynomials all of which except possibly
the factor at index `i₀` are constants (natDegree zero): only the constant
coefficients of those factors and the coefficient of `X^k` in the factor at `i₀`
survive. -/
lemma coeff_det_const_cols_prod_special {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℝ[X]) (i₀ : ι) (hi₀ : i₀ ∈ s) (k : ℕ)
    (hconst : ∀ i ∈ s, i ≠ i₀ → (f i).natDegree = 0) :
    (s.prod f).coeff k = (s.erase i₀).prod (fun i => (f i).coeff 0) * (f i₀).coeff k := by
  calc
    (s.prod f).coeff k
      = (((s.erase i₀).prod f) * f i₀).coeff k := by
          rw [← Finset.prod_erase_mul s f hi₀]
      _ = (((s.erase i₀).prod (fun i => C ((f i).coeff 0))) * f i₀).coeff k := by
          rw [show (s.erase i₀).prod f = (s.erase i₀).prod (fun i => C ((f i).coeff 0)) by
            apply Finset.prod_congr rfl
            intro i hi
            exact Polynomial.eq_C_of_natDegree_eq_zero (hconst i (Finset.mem_of_mem_erase hi)
              (Finset.ne_of_mem_erase hi))]
      _ = ((C (((s.erase i₀).prod fun i => (f i).coeff 0)) * f i₀)).coeff k := by
          rw [show (s.erase i₀).prod (fun i => C ((f i).coeff 0)) =
                  C ((s.erase i₀).prod (fun i => (f i).coeff 0)) by
            rw [map_prod C (fun i => (f i).coeff 0) (s.erase i₀)]]
      _ = ((s.erase i₀).prod (fun i => (f i).coeff 0)) * (f i₀).coeff k := by
          rw [Polynomial.coeff_C_mul]

/-- Variant of `coeff_det_const_cols_prod_special` for products over a whole
finite type, with `i₀` the single possibly non-constant index. -/
lemma coeff_det_const_cols_univ_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℝ[X]) (c : ι) (k : ℕ)
    (hconst : ∀ i, i ≠ c → (f i).natDegree = 0) :
    (∏ i : ι, f i).coeff k =
      ((Finset.univ : Finset ι).erase c).prod (fun i => (f i).coeff 0) * (f c).coeff k := by
  simpa using
    coeff_det_const_cols_prod_special (s := (Finset.univ : Finset ι)) (f := f) (i₀ := c)
      (hi₀ := Finset.mem_univ c) (k := k)
      (hconst := fun i _ hne => hconst i hne)

/-- For a permutation term of the Leibniz determinant formula, the coefficient of
`X^k` in the product of the polynomial matrix entries is the product of the real
matrix entries, because among the columns only column `c` is not constant, and it
is met by exactly one row index. -/
lemma coeff_det_const_cols_perm_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ[X]) (N : Matrix ι ι ℝ) (c : ι) (k : ℕ)
    (hN : ∀ i j, N i j = (M i j).coeff (if j = c then k else 0))
    (hconst : ∀ i j, j ≠ c → (M i j).natDegree = 0)
    (σ : Equiv.Perm ι) :
    (∏ i : ι, M (σ i) i).coeff k = ∏ i : ι, N (σ i) i := by
  classical
  calc
    (∏ i : ι, M (σ i) i).coeff k
      = (((Finset.univ : Finset ι).erase c).prod (fun i => (M (σ i) i).coeff 0)) *
          (M (σ c) c).coeff k := by
          exact coeff_det_const_cols_univ_prod (fun i => M (σ i) i) c k (fun i hi => hconst (σ i) i hi)
      _ = (((Finset.univ : Finset ι).erase c).prod (fun i => N (σ i) i)) * N (σ c) c := by
          rw [show ((Finset.univ : Finset ι).erase c).prod (fun i => (M (σ i) i).coeff 0) =
                  ((Finset.univ : Finset ι).erase c).prod (fun i => N (σ i) i) by
                apply Finset.prod_congr rfl
                intro i hi
                rw [hN (σ i) i, if_neg (Finset.ne_of_mem_erase hi)],
              show (M (σ c) c).coeff k = N (σ c) c by
                rw [hN (σ c) c, if_pos rfl]]
      _ = ∏ i : ι, N (σ i) i := by
          rw [Finset.prod_erase_mul (Finset.univ) (fun i => N (σ i) i) (Finset.mem_univ c)]

/-- If all columns of a real-polynomial matrix except column `c` are constant
polynomials (natDegree zero), then the coefficient of `X^k` in the determinant is
the determinant of the real matrix `N` whose entries are the coefficient of `X^k`
in column `c` and the constant coefficient everywhere else. -/
theorem coeff_det_const_cols {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ[X]) (N : Matrix ι ι ℝ) (c : ι) (k : ℕ)
    (hN : ∀ i j, N i j = (M i j).coeff (if j = c then k else 0))
    (hconst : ∀ i j, j ≠ c → (M i j).natDegree = 0) :
    (M.det).coeff k = N.det := by
  classical
  calc
    (M.det).coeff k
      = ∑ σ : Equiv.Perm ι, (((Equiv.Perm.sign σ : ℤ) : ℝ[X]) * ∏ i : ι, M (σ i) i).coeff k := by
          rw [Matrix.det_apply']
          simp
      _ = ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
            (∏ i : ι, M (σ i) i).coeff k := by
          apply Finset.sum_congr rfl
          intro σ _
          rw [← Polynomial.C_eq_intCast (Equiv.Perm.sign σ : ℤ)]
          simp
      _ = ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i : ι, N (σ i) i := by
          apply Finset.sum_congr rfl
          intro σ _
          congr 1
          exact coeff_det_const_cols_perm_prod M N c k hN hconst σ
      _ = N.det := by
          rw [Matrix.det_apply']

end Commons.LinearAlgebra.Matrix