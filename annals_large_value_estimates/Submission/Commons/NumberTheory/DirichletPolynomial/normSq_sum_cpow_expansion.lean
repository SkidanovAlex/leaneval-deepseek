import Mathlib.Analysis.SpecialFunctions.Pow.Complex

namespace Commons.NumberTheory.DirichletPolynomial

open scoped BigOperators

/-! ## Auxiliary facts about complex powers on the positive real axis -/

/-- Conjugation reverses the sign of the imaginary exponent of a positive real. -/
private lemma conj_cpow_I_of_pos {x : ℝ} (hx : 0 < x) (s : ℝ) :
    (starRingEnd ℂ) ((x : ℂ) ^ (Complex.I * (s : ℂ)))
      = (x : ℂ) ^ (Complex.I * ((-s : ℝ) : ℂ)) := by
  have harg : (x : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]
    exact Real.pi_ne_zero.symm
  have hc := Complex.cpow_conj (x : ℂ) (Complex.I * (s : ℂ)) harg
  rw [Complex.conj_ofReal] at hc
  have hexp : (starRingEnd ℂ) (Complex.I * (s : ℂ)) = Complex.I * ((-s : ℝ) : ℂ) := by
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  rw [hexp] at hc
  exact hc.symm

/-- Additivity of the exponent of a positive real base. -/
private lemma cpow_I_mul_cpow_I {x : ℝ} (hx : 0 < x) (s u : ℝ) :
    (x : ℂ) ^ (Complex.I * (s : ℂ)) * (x : ℂ) ^ (Complex.I * (u : ℂ))
      = (x : ℂ) ^ (Complex.I * (s : ℂ) + Complex.I * (u : ℂ)) := by
  have hxne : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  exact (Complex.cpow_add (x := (x : ℂ)) (Complex.I * (s : ℂ)) (Complex.I * (u : ℂ)) hxne).symm

private lemma mul_rearr (A B C D : ℂ) : (A * B) * (C * D) = A * C * (B * D) := by ring

/-- Pointwise expansion of the squared norm of a finite sum of "Dirichlet monomials"
`c i * x ^ (I * t i)` for a positive real `x`. -/
private lemma normSq_sum_cpow_expansion_pointwise {ι : Type*} (S : Finset ι) (t : ι → ℝ)
    (c : ι → ℂ) {x : ℝ} (hx : 0 < x) :
    ((‖∑ i ∈ S, c i * (x : ℂ) ^ (Complex.I * (t i : ℂ))‖ ^ 2 : ℝ) : ℂ)
      = ∑ i ∈ S, ∑ j ∈ S, (starRingEnd ℂ) (c i) * c j *
          ((x : ℂ) ^ (Complex.I * ((t j - t i : ℝ) : ℂ))) := by
  have hconj : (starRingEnd ℂ) (∑ i ∈ S, c i * (x : ℂ) ^ (Complex.I * (t i : ℂ)))
      = ∑ i ∈ S, (starRingEnd ℂ) (c i) * (x : ℂ) ^ (Complex.I * ((-(t i) : ℝ) : ℂ)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_mul, conj_cpow_I_of_pos hx (t i)]
  have hnorm : ((‖∑ i ∈ S, c i * (x : ℂ) ^ (Complex.I * (t i : ℂ))‖ ^ 2 : ℝ) : ℂ)
      = (starRingEnd ℂ) (∑ i ∈ S, c i * (x : ℂ) ^ (Complex.I * (t i : ℂ)))
          * (∑ i ∈ S, c i * (x : ℂ) ^ (Complex.I * (t i : ℂ))) := by
    rw [show ((‖∑ i ∈ S, c i * (x : ℂ) ^ (Complex.I * (t i : ℂ))‖ ^ 2 : ℝ) : ℂ)
          = ((Complex.normSq (∑ i ∈ S, c i * (x : ℂ) ^ (Complex.I * (t i : ℂ))) : ℝ) : ℂ) by
        rw [Complex.normSq_eq_norm_sq]]
    rw [← Complex.mul_conj, mul_comm]
  rw [hnorm, hconj, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have h1 := cpow_I_mul_cpow_I hx (-(t i)) (t j)
  have h2 : Complex.I * (((-(t i) : ℝ)) : ℂ) + Complex.I * ((t j : ℝ) : ℂ)
      = Complex.I * ((t j - t i : ℝ) : ℂ) := by
    push_cast
    ring
  rw [mul_rearr, h1, h2]

/-- Expansion of the sum of squared norms of the "Dirichlet polynomials"
`∑_{i ∈ S} c i * n ^ (I * t i)` over `n ∈ Icc N (2*N)`. -/
theorem normSq_sum_cpow_expansion {ι : Type*} (S : Finset ι) (N : ℕ) (hN : 1 ≤ N)
    (t : ι → ℝ) (c : ι → ℂ) :
    ∑ n ∈ Finset.Icc N (2 * N), ‖∑ i ∈ S, c i * (n : ℂ) ^ (Complex.I * (t i : ℂ))‖ ^ 2
      = (∑ i ∈ S, ∑ j ∈ S, (starRingEnd ℂ) (c i) * c j *
          (∑ n ∈ Finset.Icc N (2 * N), (n : ℂ) ^ (Complex.I * ((t j - t i : ℝ) : ℂ)))).re := by
  have hcomplex :
      ((∑ n ∈ Finset.Icc N (2 * N),
          ‖∑ i ∈ S, c i * (n : ℂ) ^ (Complex.I * (t i : ℂ))‖ ^ 2 : ℝ) : ℂ)
        = ∑ i ∈ S, ∑ j ∈ S, (starRingEnd ℂ) (c i) * c j *
            (∑ n ∈ Finset.Icc N (2 * N), (n : ℂ) ^ (Complex.I * ((t j - t i : ℝ) : ℂ))) := by
    rw [Complex.ofReal_sum]
    trans ∑ n ∈ Finset.Icc N (2 * N), ∑ i ∈ S, ∑ j ∈ S,
        (starRingEnd ℂ) (c i) * c j * (n : ℂ) ^ (Complex.I * ((t j - t i : ℝ) : ℂ))
    · refine Finset.sum_congr rfl (fun n hn => ?_)
      have hnpos : (0 : ℝ) < (n : ℝ) := by
        have hNn : N ≤ n := (Finset.mem_Icc.mp hn).1
        have h1n : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans hN hNn
        linarith
      exact normSq_sum_cpow_expansion_pointwise S t c hnpos
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← Finset.mul_sum]
  have hre := congrArg Complex.re hcomplex
  simp only [Complex.ofReal_re] at hre
  exact hre

end Commons.NumberTheory.DirichletPolynomial