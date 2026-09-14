import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.PDeriv

namespace Commons.Algebra.MvPolynomial

open scoped BigOperators

theorem pderiv_bind1 {R : Type*} [CommSemiring R] {σ τ : Type*} [Fintype σ]
    (f : σ → MvPolynomial τ R) (j : τ) (p : MvPolynomial σ R) :
    MvPolynomial.pderiv j (MvPolynomial.bind₁ f p) =
      ∑ i : σ, (MvPolynomial.pderiv j (f i)) * (MvPolynomial.bind₁ f (MvPolynomial.pderiv i p)) := by
  classical
  let ρ : MvPolynomial σ R →ₐ[R] MvPolynomial τ R := MvPolynomial.bind₁ f
  let d : σ → MvPolynomial τ R := fun i => MvPolynomial.pderiv j (f i)
  change MvPolynomial.pderiv j (ρ p) = ∑ i : σ, d i * ρ (MvPolynomial.pderiv i p)
  induction p using MvPolynomial.induction_on with
  | C a =>
      simp [d]
  | add p q hp hq =>
      simp [map_add, hp, hq, d, Finset.sum_add_distrib, mul_add]
  | mul_X p n hp =>
      have hdn : MvPolynomial.pderiv j (ρ (MvPolynomial.X n)) = d n := by
        simp [d, ρ]
      have hXterm : ∀ x : σ, ρ (MvPolynomial.pderiv x (MvPolynomial.X n)) =
          if x = n then (1 : MvPolynomial τ R) else 0 := by
        intro x
        by_cases h : x = n
        · subst h
          simp
        · have hn : n ≠ x := Ne.symm h
          rw [MvPolynomial.pderiv_X_of_ne hn]
          simp [h]
      have hXsum : (∑ x : σ, d x * ρ (MvPolynomial.pderiv x (MvPolynomial.X n))) = d n := by
        calc
          (∑ x : σ, d x * ρ (MvPolynomial.pderiv x (MvPolynomial.X n)))
              = ∑ x : σ, if x = n then d x else 0 := by
                  refine Finset.sum_congr rfl ?_
                  intro x hx
                  by_cases h : x = n
                  · subst h; simp
                  · simp [h]
          _ = d n := by simp
      have hRHS : (∑ x : σ, d x * ρ (MvPolynomial.pderiv x (p * MvPolynomial.X n)))
          = (∑ x : σ, d x * ρ (MvPolynomial.pderiv x p)) * ρ (MvPolynomial.X n) + ρ p * d n := by
        calc
          (∑ x : σ, d x * ρ (MvPolynomial.pderiv x (p * MvPolynomial.X n)))
              = ∑ x : σ, d x * ρ (MvPolynomial.pderiv x p * MvPolynomial.X n +
                    p * MvPolynomial.pderiv x (MvPolynomial.X n)) := by
                  refine Finset.sum_congr rfl ?_
                  intro x hx
                  rw [MvPolynomial.pderiv_mul]
          _ = ∑ x : σ, d x * (ρ (MvPolynomial.pderiv x p) * ρ (MvPolynomial.X n) +
                ρ p * ρ (MvPolynomial.pderiv x (MvPolynomial.X n))) := by
                  refine Finset.sum_congr rfl ?_
                  intro x hx
                  simp [map_add, map_mul]
          _ = ∑ x : σ, (d x * ρ (MvPolynomial.pderiv x p) * ρ (MvPolynomial.X n) +
                d x * ρ p * ρ (MvPolynomial.pderiv x (MvPolynomial.X n))) := by
                  refine Finset.sum_congr rfl ?_
                  intro x hx
                  rw [mul_add]
                  congr 1 <;> ring
          _ = (∑ x : σ, d x * ρ (MvPolynomial.pderiv x p) * ρ (MvPolynomial.X n)) +
                (∑ x : σ, d x * ρ p * ρ (MvPolynomial.pderiv x (MvPolynomial.X n))) := by
                  rw [Finset.sum_add_distrib]
          _ = (∑ x : σ, d x * ρ (MvPolynomial.pderiv x p)) * ρ (MvPolynomial.X n) + ρ p * d n := by
                  rw [← Finset.sum_mul]
                  rw [show (∑ x : σ, d x * ρ p * ρ (MvPolynomial.pderiv x (MvPolynomial.X n)))
                      = ρ p * ∑ x : σ, d x * ρ (MvPolynomial.pderiv x (MvPolynomial.X n)) by
                        calc
                          (∑ x : σ, d x * ρ p * ρ (MvPolynomial.pderiv x (MvPolynomial.X n)))
                              = ∑ x : σ, ρ p * (d x * ρ (MvPolynomial.pderiv x (MvPolynomial.X n))) := by
                                  refine Finset.sum_congr rfl ?_
                                  intro x hx; ring
                          _ = ρ p * ∑ x : σ, d x * ρ (MvPolynomial.pderiv x (MvPolynomial.X n)) := by
                                  rw [Finset.mul_sum]]
                  rw [hXsum]
      calc
        MvPolynomial.pderiv j (ρ (p * MvPolynomial.X n))
            = MvPolynomial.pderiv j (ρ p * ρ (MvPolynomial.X n)) := by simp [map_mul]
        _ = MvPolynomial.pderiv j (ρ p) * ρ (MvPolynomial.X n) +
              ρ p * MvPolynomial.pderiv j (ρ (MvPolynomial.X n)) := by
              rw [MvPolynomial.pderiv_mul]
        _ = (∑ x : σ, d x * ρ (MvPolynomial.pderiv x p)) * ρ (MvPolynomial.X n) + ρ p * d n := by
              rw [hp, hdn]
        _ = ∑ x : σ, d x * ρ (MvPolynomial.pderiv x (p * MvPolynomial.X n)) := by
              rw [hRHS]

end Commons.Algebra.MvPolynomial