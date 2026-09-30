import Mathlib
import Submission.Work.BW.DefsMult

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Scaling of a weighted homogeneous polynomial under `X_v ↦ λ_{v.1} * x_v`

The multidegree weighting `mdeg N` assigns weight `e_i` to both variables of the `i`-th
factor of `(P¹)^{N+1}`, so that the weight of an exponent vector `dd` is its `i`-th
partial degree `∑_j dd (i,j)` in the monomial `∏_v X_v ^ (dd v)`.

Consequently, substituting `x_v ↦ λ_{v.1} * x_v` into a polynomial that is weighted
homogeneous of multidegree `d` multiplies its value by `∏_i λ_i ^ (d i)`.
-/

namespace Work.BW

open MvPolynomial

/-- The multidegree of `dd` at `i` is the sum of its multiplicities in the `i`-th factor. -/
private lemma mapDomain_fst_apply {N : ℕ} (d : Fin (N + 1) × Fin 2 →₀ ℕ) (i : Fin (N + 1)) :
    (d.mapDomain Prod.fst) i = ∑ j : Fin 2, d (i, j) := by
  rw [Finsupp.mapDomain_apply, Finsupp.sum]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_subset (Finset.subset_univ d.support)]
  · rw [Fintype.sum_prod_type]
    simp [Finset.sum_add_distrib, Finset.sum_ite_eq']
  · intro x _ hx; rw [Finsupp.notMem_support_iff.mp hx]; simp

/-- The `mdeg N`-weight of an exponent vector is the pushforward of its multiplicities
along the first projection. -/
private lemma weight_mdeg_eq_mapDomain {N : ℕ} (d : Fin (N + 1) × Fin 2 →₀ ℕ) :
    Finsupp.weight (mdeg N) d = d.mapDomain Prod.fst := by
  ext i
  rw [Finsupp.weight_eq_sum]
  simp only [mdeg, Finsupp.mapDomain_apply]
  simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, Finsupp.sum,
    Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_subset (Finset.subset_univ d.support)]
  intro x _ hx; rw [Finsupp.notMem_support_iff.mp hx]; simp

/-- The product `∏_i λ_i ^ (D i)` can be computed over the support of `D`. -/
private lemma finsupp_prod_pow_eq_prod {N : ℕ} (lam : Fin (N + 1) → ℂ) (D : Fin (N + 1) →₀ ℕ) :
    D.prod (fun i e => lam i ^ e) = ∏ i : Fin (N + 1), lam i ^ (D i) := by
  rw [Finsupp.prod]
  exact Finset.prod_subset (Finset.subset_univ D.support)
    (fun x _ hx => by rw [Finsupp.notMem_support_iff.mp hx, pow_zero])

/-- Evaluating a weighted homogeneous polynomial at the scaled point `λ · x`
multiplies its value by the weight `∏_i λ_i ^ (d i)`. -/
theorem eval_scale_of_isWeightedHomogeneous {N : ℕ} {G : MR N} {d : Fin (N + 1) →₀ ℕ}
    (hG : MvPolynomial.IsWeightedHomogeneous (mdeg N) G d) (lam : Fin (N + 1) → ℂ)
    (x : Fin (N + 1) × Fin 2 → ℂ) :
    MvPolynomial.eval (fun v : Fin (N + 1) × Fin 2 => lam v.1 * x v) G =
      (∏ i : Fin (N + 1), lam i ^ (d i)) * MvPolynomial.eval x G := by
  rw [MvPolynomial.as_sum G, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun dd hdd => ?_
  have hwt : Finsupp.weight (mdeg N) dd = d := hG (Finsupp.mem_support_iff.mp hdd)
  rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
  have hD : dd.mapDomain Prod.fst = d := (weight_mdeg_eq_mapDomain dd).symm.trans hwt
  have h3 : dd.prod (fun v e => (lam v.1 * x v) ^ e)
      = (∏ i : Fin (N + 1), lam i ^ (d i)) * dd.prod (fun v e => x v ^ e) := by
    have h1 : dd.prod (fun v e => (lam v.1 * x v) ^ e)
        = dd.prod (fun v e => (lam v.1) ^ e * (x v) ^ e) :=
      Finsupp.prod_congr (fun v _ => by rw [mul_pow])
    rw [h1, Finsupp.prod_mul]
    congr 1
    rw [← hD, ← finsupp_prod_pow_eq_prod lam (dd.mapDomain Prod.fst)]
    exact (Finsupp.prod_mapDomain_index (fun i => pow_zero (lam i))
      (fun i a b => pow_add (lam i) a b)).symm
  rw [h3]; ring

end Work.BW
