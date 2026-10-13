import Mathlib
import Submission.Work.WilE1.Setup

set_option autoImplicit false

namespace Work.WilE1

open MvPolynomial

/-- Abstract first-order Taylor expansion, in a commutative `ℂ`-algebra `B`, of the evaluation
`p ↦ p(f)` where `f i = algebraMap ℂ B (x i) + t i` and the `t i` are infinitesimal with respect
to an ideal `J` (their pairwise products lie in `J`): the difference between `p(f)` and the
first-order expansion of `p` around `x` lies in `J`. -/
theorem taylor_abstract {k : ℕ} {B : Type*} [CommRing B] [Algebra ℂ B]
    (x : Fin k → ℂ) (t : Fin k → B) (J : Ideal B) (ht : ∀ i j, t i * t j ∈ J)
    (p : MvPolynomial (Fin k) ℂ) :
    MvPolynomial.aeval (fun i => algebraMap ℂ B (x i) + t i) p -
        algebraMap ℂ B (MvPolynomial.aeval x p) -
        ∑ i, t i * algebraMap ℂ B (MvPolynomial.aeval x (MvPolynomial.pderiv i p)) ∈ J := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      have h0 : MvPolynomial.aeval (fun i => algebraMap ℂ B (x i) + t i) (MvPolynomial.C a) -
          algebraMap ℂ B (MvPolynomial.aeval x (MvPolynomial.C a)) -
          ∑ i, t i * algebraMap ℂ B
            (MvPolynomial.aeval x (MvPolynomial.pderiv i (MvPolynomial.C a))) = 0 := by
        simp
      rw [h0]
      exact J.zero_mem
  | add p q hp hq =>
      have h0 : MvPolynomial.aeval (fun i => algebraMap ℂ B (x i) + t i) (p + q) -
            algebraMap ℂ B (MvPolynomial.aeval x (p + q)) -
            ∑ i, t i * algebraMap ℂ B (MvPolynomial.aeval x (MvPolynomial.pderiv i (p + q)))
          = (MvPolynomial.aeval (fun i => algebraMap ℂ B (x i) + t i) p -
              algebraMap ℂ B (MvPolynomial.aeval x p) -
              ∑ i, t i * algebraMap ℂ B (MvPolynomial.aeval x (MvPolynomial.pderiv i p)))
            + (MvPolynomial.aeval (fun i => algebraMap ℂ B (x i) + t i) q -
              algebraMap ℂ B (MvPolynomial.aeval x q) -
              ∑ i, t i * algebraMap ℂ B (MvPolynomial.aeval x (MvPolynomial.pderiv i q))) := by
        simp only [map_add, Finset.sum_add_distrib, mul_add]
        ring
      rw [h0]
      exact J.add_mem hp hq
  | mul_X p n hp =>
      have hβ : ∀ i : Fin k,
          algebraMap ℂ B (MvPolynomial.aeval x
              (MvPolynomial.pderiv i (MvPolynomial.X n : MvPolynomial (Fin k) ℂ)))
            = if n = i then 1 else 0 := by
        intro i
        by_cases h : n = i
        · rw [h]; simp
        · rw [MvPolynomial.pderiv_X_of_ne h]; simp [h]
      have hterm : ∀ i : Fin k,
          t i * algebraMap ℂ B
              (MvPolynomial.aeval x (MvPolynomial.pderiv i (p * MvPolynomial.X n)))
            = t i * algebraMap ℂ B (MvPolynomial.aeval x (MvPolynomial.pderiv i p))
                * algebraMap ℂ B (x n)
              + (if n = i then t i * algebraMap ℂ B (MvPolynomial.aeval x p) else 0) := by
        intro i
        rw [MvPolynomial.pderiv_mul]
        simp only [map_add, map_mul, MvPolynomial.aeval_X, hβ i]
        by_cases h : n = i
        · simp [h]; ring
        · simp [h]; ring
      have h1 : MvPolynomial.aeval (fun i => algebraMap ℂ B (x i) + t i) (p * MvPolynomial.X n)
          = MvPolynomial.aeval (fun i => algebraMap ℂ B (x i) + t i) p
              * (algebraMap ℂ B (x n) + t n) := by
        simp [map_mul, MvPolynomial.aeval_X]
      have h2 : algebraMap ℂ B (MvPolynomial.aeval x (p * MvPolynomial.X n))
          = algebraMap ℂ B (MvPolynomial.aeval x p) * algebraMap ℂ B (x n) := by
        simp [map_mul, MvPolynomial.aeval_X]
      have h3 : (∑ i, t i * algebraMap ℂ B
            (MvPolynomial.aeval x (MvPolynomial.pderiv i (p * MvPolynomial.X n))))
          = (∑ i, t i * algebraMap ℂ B (MvPolynomial.aeval x (MvPolynomial.pderiv i p)))
              * algebraMap ℂ B (x n)
            + t n * algebraMap ℂ B (MvPolynomial.aeval x p) := by
        rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib,
          Finset.sum_mul, Finset.sum_ite_eq]
        simp
      rw [h1, h2, h3]
      have step : MvPolynomial.aeval (fun i => algebraMap ℂ B (x i) + t i) p
              * (algebraMap ℂ B (x n) + t n)
            - algebraMap ℂ B (MvPolynomial.aeval x p) * algebraMap ℂ B (x n)
            - ((∑ i, t i * algebraMap ℂ B (MvPolynomial.aeval x (MvPolynomial.pderiv i p)))
                * algebraMap ℂ B (x n)
              + t n * algebraMap ℂ B (MvPolynomial.aeval x p))
          = (∑ i, t i * algebraMap ℂ B (MvPolynomial.aeval x (MvPolynomial.pderiv i p))) * t n
            + (MvPolynomial.aeval (fun i => algebraMap ℂ B (x i) + t i) p
              - algebraMap ℂ B (MvPolynomial.aeval x p)
              - ∑ i, t i * algebraMap ℂ B (MvPolynomial.aeval x (MvPolynomial.pderiv i p)))
              * (algebraMap ℂ B (x n) + t n) := by
        ring
      rw [step]
      apply J.add_mem
      · rw [Finset.sum_mul]
        apply Ideal.sum_mem
        intro i _
        have hc : t i * algebraMap ℂ B (MvPolynomial.aeval x (MvPolynomial.pderiv i p)) * t n
            = algebraMap ℂ B (MvPolynomial.aeval x (MvPolynomial.pderiv i p))
                * (t i * t n) := by
          ring
        rw [hc]
        exact Ideal.mul_mem_left J _ (ht i n)
      · exact J.mul_mem_right (algebraMap ℂ B (x n) + t n) hp

theorem TaylorTwo {k : ℕ} (x : Fin k → ℂ) (p : MvPolynomial (Fin k) ℂ) :
    p - MvPolynomial.C (MvPolynomial.aeval x p) -
        ∑ i, (MvPolynomial.X i - MvPolynomial.C (x i)) *
          MvPolynomial.C (MvPolynomial.aeval x (MvPolynomial.pderiv i p))
      ∈ (Ideal.span (Set.range fun i =>
          (MvPolynomial.X i - MvPolynomial.C (x i) : MvPolynomial (Fin k) ℂ)))^2 := by
  have ht : ∀ i j : Fin k,
      (fun i => MvPolynomial.X i - MvPolynomial.C (x i)) i
        * (fun i => MvPolynomial.X i - MvPolynomial.C (x i)) j
      ∈ (Ideal.span (Set.range fun i =>
          (MvPolynomial.X i - MvPolynomial.C (x i) : MvPolynomial (Fin k) ℂ)))^2 := by
    intro i j
    rw [sq]
    exact Ideal.mul_mem_mul
      (Ideal.subset_span (Set.mem_range_self i)) (Ideal.subset_span (Set.mem_range_self j))
  have h := taylor_abstract x (fun i => MvPolynomial.X i - MvPolynomial.C (x i))
    ((Ideal.span (Set.range fun i =>
        (MvPolynomial.X i - MvPolynomial.C (x i) : MvPolynomial (Fin k) ℂ)))^2) ht p
  have hfam : (fun i => algebraMap ℂ (MvPolynomial (Fin k) ℂ) (x i)
        + (MvPolynomial.X i - MvPolynomial.C (x i))) = fun i => MvPolynomial.X i := by
    funext i
    simp
  have hF : MvPolynomial.aeval (fun i => algebraMap ℂ (MvPolynomial (Fin k) ℂ) (x i)
        + (MvPolynomial.X i - MvPolynomial.C (x i))) p = p := by
    rw [hfam, MvPolynomial.aeval_X_left_apply]
  have halg : ∀ r : ℂ, algebraMap ℂ (MvPolynomial (Fin k) ℂ) r = MvPolynomial.C r :=
    fun r => rfl
  rw [hF] at h
  simp only [halg] at h
  exact h

end Work.WilE1
