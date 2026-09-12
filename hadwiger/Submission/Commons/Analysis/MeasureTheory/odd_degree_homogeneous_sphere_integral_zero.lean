import Mathlib
import Submission.Commons.Analysis.MeasureTheory.integral_odd_zero

noncomputable section
open Set Function MeasureTheory Metric
open scoped Classical

namespace Commons.Analysis.MeasureTheory

private lemma finsupp_prod_neg_pow {σ : Type*} (d : σ →₀ ℕ) (v : σ → ℝ) :
    d.prod (fun i e => (-(v i)) ^ e) =
      (-1 : ℝ) ^ (d.degree : ℕ) * d.prod (fun i e => (v i) ^ e) := by
  calc
    d.prod (fun i e => (-(v i)) ^ e)
        = ∏ i ∈ d.support, (-(v i)) ^ (d i) := rfl
    _ = ∏ i ∈ d.support, ((-1 : ℝ) * v i) ^ (d i) := by
          apply Finset.prod_congr rfl
          intro i hi
          congr 1
          ring
    _ = ∏ i ∈ d.support, ((-1 : ℝ) ^ (d i)) * (v i) ^ (d i) := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [mul_pow]
    _ = (∏ i ∈ d.support, (-1 : ℝ) ^ (d i)) * (∏ i ∈ d.support, (v i) ^ (d i)) := by
          rw [Finset.prod_mul_distrib]
    _ = (-1 : ℝ) ^ (∑ i ∈ d.support, d i) * (∏ i ∈ d.support, (v i) ^ (d i)) := by
          congr 1
          exact Finset.prod_pow_eq_pow_sum d.support d (-1 : ℝ)
    _ = (-1 : ℝ) ^ (d.degree : ℕ) * d.prod (fun i e => (v i) ^ e) := by
          rw [Finsupp.degree_apply]
          rfl

private lemma eval_eq_sum {σ : Type*} (P : MvPolynomial σ ℝ) (f : σ → ℝ) :
    MvPolynomial.eval f P =
      ∑ d ∈ P.support, P.coeff d * d.prod (fun i e => f i ^ e) := by
  conv_lhs => rw [MvPolynomial.as_sum P]
  rw [MvPolynomial.eval_sum]
  refine Finset.sum_congr rfl ?_
  intro d hd
  rw [MvPolynomial.eval_monomial]

private lemma eval_homogeneous_neg {σ : Type*} (P : MvPolynomial σ ℝ) {k : ℕ}
    (hP : P ∈ MvPolynomial.homogeneousSubmodule σ ℝ k) (v : σ → ℝ) :
    MvPolynomial.eval (fun i => -v i) P = (-1 : ℝ) ^ k * MvPolynomial.eval v P := by
  calc
    MvPolynomial.eval (fun i => -v i) P
        = ∑ d ∈ P.support, P.coeff d * d.prod (fun i e => (-v i) ^ e) := eval_eq_sum P (fun i => -v i)
    _ = ∑ d ∈ P.support, P.coeff d * ((-1 : ℝ) ^ k * d.prod (fun i e => (v i) ^ e)) := by
            apply Finset.sum_congr rfl
            intro d hd
            have hdc : P.coeff d ≠ 0 := Finsupp.mem_support_iff.mp hd
            have hdeg : d.degree = k := by
              rw [Finsupp.degree_eq_weight_one]
              exact hP hdc
            rw [finsupp_prod_neg_pow d v, hdeg]
    _ = (-1 : ℝ) ^ k * ∑ d ∈ P.support, P.coeff d * d.prod (fun i e => (v i) ^ e) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro d hd
            ring
    _ = (-1 : ℝ) ^ k * MvPolynomial.eval v P := by
            rw [eval_eq_sum P v]

/-- The integral over the unit sphere of an odd-degree homogeneous polynomial is zero:
substituting `x ↦ -x` changes the integrand into its negative, while the sphere measure
is invariant under the antipodal map. -/
theorem odd_degree_homogeneous_sphere_integral_zero
    {n : ℕ} {k : ℕ} (hkodd : Odd k)
    (P : MvPolynomial (Fin n) ℝ)
    (hP : P ∈ MvPolynomial.homogeneousSubmodule (Fin n) ℝ k) :
    (∫ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        MvPolynomial.eval (fun i : Fin n => (θ : EuclideanSpace ℝ (Fin n)) i) P
      ∂MeasureTheory.volume.toSphere) = 0 := by
  classical
  by_cases hn : Nonempty (Fin n)
  · haveI : Nonempty (Fin n) := hn
    refine integral_odd_zero (V := EuclideanSpace ℝ (Fin n))
      (g := fun θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
        MvPolynomial.eval (fun i : Fin n => (θ : EuclideanSpace ℝ (Fin n)) i) P) ?_
    intro θ
    calc
      MvPolynomial.eval (fun i : Fin n =>
          ((⟨-θ.1, by simpa [mem_sphere_zero_iff_norm, norm_neg] using
            (mem_sphere_zero_iff_norm.mp θ.2)⟩ :
            Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : EuclideanSpace ℝ (Fin n)) i) P
          = MvPolynomial.eval (fun i : Fin n => -((θ : EuclideanSpace ℝ (Fin n)) i)) P := rfl
      _ = (-1 : ℝ) ^ k * MvPolynomial.eval (fun i : Fin n => (θ : EuclideanSpace ℝ (Fin n)) i) P :=
            eval_homogeneous_neg P hP (fun i : Fin n => (θ : EuclideanSpace ℝ (Fin n)) i)
      _ = - MvPolynomial.eval (fun i : Fin n => (θ : EuclideanSpace ℝ (Fin n)) i) P := by
            rw [hkodd.neg_one_pow]
            ring
  · haveI : IsEmpty (Fin n) := not_nonempty_iff.mp hn
    have hPzero : P = 0 := by
      apply MvPolynomial.ext
      intro d
      by_contra hc
      have hdegk : (Finsupp.weight (1 : Fin n → ℕ)) d = k := hP hc
      have hdzero : d = 0 := by
        apply Finsupp.ext
        intro i
        exact False.elim (isEmptyElim i)
      have hw0 : (Finsupp.weight (R := ℕ) (1 : Fin n → ℕ)) 0 = 0 := by simp
      rw [hdzero] at hdegk
      have hk0 : k = 0 := hdegk.symm.trans hw0
      rcases hkodd with ⟨m, hm⟩
      omega
    simp [hPzero]

end Commons.Analysis.MeasureTheory
