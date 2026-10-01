import Mathlib
import Submission.Work.Analysis.Complex.cpow_nat_eq_exp

namespace Work.Analysis.Complex

/-- The expansion of the squared norm of a finite sum of complex numbers as a double sum:
`‖∑ f x‖² = re (∑ x ∑ y f x * conj (f y))`. -/
lemma normSq_finset_sum_star {α : Type*} (s : Finset α) (f : α → ℂ) :
    ‖∑ x ∈ s, f x‖ ^ 2 = (∑ x ∈ s, ∑ y ∈ s, f x * (starRingEnd ℂ) (f y)).re := by
  have h : (∑ x ∈ s, ∑ y ∈ s, f x * (starRingEnd ℂ) (f y))
      = (∑ x ∈ s, f x) * (starRingEnd ℂ) (∑ x ∈ s, f x) := by
    rw [map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mul_sum]
  rw [h, Complex.sq_norm, ← Complex.ofReal_re (Complex.normSq (∑ x ∈ s, f x)),
    ← Complex.mul_conj]

/-- Termwise identification of the product `f m * conj (f n)` for the Dirichlet-polynomial
terms `f k = a k * k ^ (I t)`. -/
lemma dirichletPoly_term_star (a : ℕ → ℂ) (t : ℝ) (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (a m * (m : ℂ) ^ ((t : ℂ) * Complex.I)) *
        (starRingEnd ℂ) (a n * (n : ℂ) ^ ((t : ℂ) * Complex.I))
      = (a m * (starRingEnd ℂ) (a n)) *
          Complex.exp (Complex.I * (((t : ℝ) * (Real.log (m : ℝ) - Real.log (n : ℝ)) : ℝ) : ℂ)) := by
  have hstar : (starRingEnd ℂ) (Complex.exp (Complex.I * ((t * Real.log (n : ℝ) : ℝ) : ℂ)))
      = Complex.exp (-(Complex.I * ((t * Real.log (n : ℝ) : ℝ) : ℂ))) := by
    rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hexp : Complex.exp (Complex.I * ((t * Real.log (m : ℝ) : ℝ) : ℂ)) *
        Complex.exp (-(Complex.I * ((t * Real.log (n : ℝ) : ℝ) : ℂ)))
      = Complex.exp (Complex.I * (((t : ℝ) * (Real.log (m : ℝ) - Real.log (n : ℝ)) : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [map_mul, cpow_nat_eq_exp m hm t, cpow_nat_eq_exp n hn t, hstar,
    mul_mul_mul_comm, hexp]

lemma dirichletPoly_normsq_expansion (a : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    ‖∑ n ∈ Finset.Icc 1 N, a n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2
      = (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          (a m * (starRingEnd ℂ) (a n)) *
            Complex.exp (Complex.I * (((t : ℝ) * (Real.log (m : ℝ) - Real.log (n : ℝ)) : ℝ) : ℂ))).re := by
  rw [normSq_finset_sum_star (Finset.Icc 1 N)
    (fun n => a n * (n : ℂ) ^ ((t : ℂ) * Complex.I))]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  exact dirichletPoly_term_star a t m n (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hn).1

end Work.Analysis.Complex
