import Mathlib
import Submission.Work.BW.DefsB
import Submission.Work.BW.bwScale
import Submission.Work.BW.homPiece_finrank

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Evaluating a multihomogeneous polynomial at a torus-scaled point

`MR N = ℂ[X_{i,0},X_{i,1} : i ≤ N]` is the homogeneous coordinate ring of `(P¹)^{N+1}`, and
`homPiece N d` is the multihomogeneous piece of multidegree `d` (both variables `X_{i,0},X_{i,1}`
have weight `eᵢ`).  The torus acts by `X_{i,j} ↦ lamᵢ X_{i,j}` (`scaleEnd N lam`).

The main result: if `p` is multihomogeneous of multidegree `d`, then at any point `x` of the
affine chart,
`eval (fun (i,j) => lamᵢ * x (i,j)) p = (∏ᵢ lamᵢ^{dᵢ}) * eval x p`.
-/

namespace Work.BW

open MvPolynomial

variable {N : ℕ}

/-- The weight product `∏_{v} lam_{v.1} ^ (m v)` attached to an exponent vector `m` is `wtPow`
at the weighted degree of `m` (the `i`-th coordinate of the weighted degree is `m (i,0)+m (i,1)`,
so `∏_{v} lam_{v.1}^{m v} = ∏_i lam_i^{m (i,0)+m (i,1)}`). -/
lemma prod_lam_pow_eq_wtPow_weight (lam : Fin (N + 1) → ℂ)
    (m : (Fin (N + 1) × Fin 2) →₀ ℕ) :
    (∏ v : Fin (N + 1) × Fin 2, lam v.1 ^ (m v)) =
      wtPow N lam (Finsupp.weight (mdeg N) m) := by
  rw [wtPow, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fin.prod_univ_two, ← pow_add, weight_mdeg_apply]

/-- The same weight product restricted to the support of `m`. -/
lemma prod_lam_pow_support_eq_wtPow_weight (lam : Fin (N + 1) → ℂ)
    (m : (Fin (N + 1) × Fin 2) →₀ ℕ) :
    (∏ v ∈ m.support, lam v.1 ^ (m v)) =
      wtPow N lam (Finsupp.weight (mdeg N) m) := by
  rw [← prod_lam_pow_eq_wtPow_weight lam m]
  exact (Finset.prod_subset (Finset.subset_univ _) fun x _ hx => by
    rw [Finsupp.notMem_support_iff.mp hx, pow_zero])

/-- The scaling endomorphism `X_{i,j} ↦ lamᵢ X_{i,j}` applied to the monomial `c X^m`:
it picks up the weight product `∏_v lam_{v.1}^{m v}` of the exponent vector. -/
lemma scaleEnd_monomial (lam : Fin (N + 1) → ℂ) (m : (Fin (N + 1) × Fin 2) →₀ ℕ) (c : ℂ) :
    scaleEnd N lam (MvPolynomial.monomial m c) =
      MvPolynomial.C (c * wtPow N lam (Finsupp.weight (mdeg N) m)) *
        MvPolynomial.monomial m 1 := by
  rw [scaleEnd, MvPolynomial.aeval_monomial, MvPolynomial.monic_monomial_eq,
    MvPolynomial.algebraMap_eq]
  have hkey : (m.prod fun i k => (MvPolynomial.C (lam i.1) * MvPolynomial.X i) ^ k : MR N) =
      MvPolynomial.C (wtPow N lam (Finsupp.weight (mdeg N) m)) *
        (m.prod fun n e => MvPolynomial.X n ^ e : MR N) := by
    have h1 : (m.prod fun i k => (MvPolynomial.C (lam i.1) * MvPolynomial.X i) ^ k : MR N) =
        ∏ i ∈ m.support, (MvPolynomial.C (lam i.1) * MvPolynomial.X i) ^ (m i) := by
      simp [Finsupp.prod]
    have h2 : (m.prod fun n e => MvPolynomial.X n ^ e : MR N) =
        ∏ i ∈ m.support, MvPolynomial.X i ^ (m i) := by
      simp [Finsupp.prod]
    rw [h1, h2]
    have h3 : (∏ i ∈ m.support, (MvPolynomial.C (lam i.1) * MvPolynomial.X i) ^ (m i) : MR N) =
        (∏ i ∈ m.support, MvPolynomial.C ((lam i.1) ^ (m i))) *
          (∏ i ∈ m.support, MvPolynomial.X i ^ (m i)) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => by rw [mul_pow, MvPolynomial.C_pow]
    rw [h3]
    have h4 : (∏ i ∈ m.support, MvPolynomial.C ((lam i.1) ^ (m i)) : MR N) =
        MvPolynomial.C (∏ i ∈ m.support, lam i.1 ^ (m i)) := by rw [map_prod]
    rw [h4, prod_lam_pow_support_eq_wtPow_weight]
  rw [hkey, ← mul_assoc, ← MvPolynomial.C_mul]

/-- A multihomogeneous polynomial of multidegree `d` is an eigenvector of the scaling
endomorphism, with eigenvalue `wtPow N lam d`. -/
lemma scaleEnd_eq_of_mem_homPiece (lam : Fin (N + 1) → ℂ) {d : Fin (N + 1) →₀ ℕ}
    {p : MR N} (hp : p ∈ homPiece N d) :
    scaleEnd N lam p = MvPolynomial.C (wtPow N lam d) * p := by
  have hpH : p.IsWeightedHomogeneous (mdeg N) d := hp
  refine MvPolynomial.IsWeightedHomogeneous.induction_on
    (w := mdeg N) (m := d)
    (motive := fun p _ => scaleEnd N lam p = MvPolynomial.C (wtPow N lam d) * p)
    ?_ ?_ ?_ hpH
  · simp
  · intro p q hp hq ihp ihq
    rw [map_add, ihp, ihq, mul_add]
  · intro m r hm
    rw [scaleEnd_monomial, hm, MvPolynomial.C_mul_monomial, mul_one]
    rw [MvPolynomial.C_mul_monomial, mul_comm r]

theorem eval_scale_homPiece {N : ℕ} (d : Fin (N + 1) →₀ ℕ) (p : MR N) (hp : p ∈ homPiece N d)
    (lam : Fin (N + 1) → ℂ) (x : Fin (N + 1) × Fin 2 → ℂ) :
    MvPolynomial.eval (fun v : Fin (N + 1) × Fin 2 => lam v.1 * x v) p =
      wtPow N lam d * MvPolynomial.eval x p := by
  have h1 : MvPolynomial.eval (fun v : Fin (N + 1) × Fin 2 => lam v.1 * x v) p =
      MvPolynomial.eval x (scaleEnd N lam p) := by
    rw [← MvPolynomial.aeval_eq_eval (fun v : Fin (N + 1) × Fin 2 => lam v.1 * x v),
      ← MvPolynomial.aeval_eq_eval x]
    have hcomp : (MvPolynomial.aeval x).comp (scaleEnd N lam)
        = MvPolynomial.aeval (fun v : Fin (N + 1) × Fin 2 => lam v.1 * x v) := by
      rw [scaleEnd, MvPolynomial.comp_aeval]
      congr 1
      funext v
      simp
    rw [← hcomp]
    rfl
  rw [h1, scaleEnd_eq_of_mem_homPiece lam hp, map_mul, MvPolynomial.eval_C]

end Work.BW
