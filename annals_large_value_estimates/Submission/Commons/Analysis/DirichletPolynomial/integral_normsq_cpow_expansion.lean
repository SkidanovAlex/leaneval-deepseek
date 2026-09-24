import Mathlib

namespace Commons.Analysis.DirichletPolynomial

open scoped BigOperators
open MeasureTheory

/-! ## Auxiliary facts about complex powers on the positive real axis -/

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

private lemma cpow_I_mul_cpow_I {x : ℝ} (hx : 0 < x) (s u : ℝ) :
    (x : ℂ) ^ (Complex.I * (s : ℂ)) * (x : ℂ) ^ (Complex.I * (u : ℂ))
      = (x : ℂ) ^ (Complex.I * (s : ℂ) + Complex.I * (u : ℂ)) := by
  have hxne : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  exact (Complex.cpow_add (x := (x : ℂ)) (Complex.I * (s : ℂ)) (Complex.I * (u : ℂ)) hxne).symm

private lemma mul_rearr (A B C D : ℂ) : (A * B) * (C * D) = A * C * (B * D) := by ring

/-- Pointwise expansion of the squared norm of a finite sum of "Dirichlet monomials"
`c i * x ^ (I * t i)` for `x > 0`. -/
private lemma normSq_sum_cpow_expansion {ι : Type*} (S : Finset ι) (t : ι → ℝ) (c : ι → ℂ)
    {x : ℝ} (hx : 0 < x) :
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

/-! ## Integrability of the individual summands -/

private lemma continuousOn_ofReal_cpow (w : ℂ) :
    ContinuousOn (fun x : ℝ => (x : ℂ) ^ w) (Set.Ioi 0) :=
  ContinuousOn.cpow_const (b := w) Complex.continuous_ofReal.continuousOn
    (fun _ hx => Complex.ofReal_mem_slitPlane.2 hx)

private lemma intervalIntegrable_ofReal_cpow (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (w : ℂ) :
    IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ w) volume a b := by
  refine ContinuousOn.intervalIntegrable ((continuousOn_ofReal_cpow w).mono ?_)
  intro x hx
  rw [Set.uIcc_of_le hab] at hx
  exact lt_of_lt_of_le ha hx.1

theorem integral_normsq_cpow_expansion {ι : Type*} (S : Finset ι) (a b : ℝ) (ha : 0 < a)
    (hab : a ≤ b) (t : ι → ℝ) (c : ι → ℂ) :
    (∫ x in a..b, ((‖∑ i ∈ S, c i * (x : ℂ) ^ (Complex.I * (t i : ℂ))‖ ^ 2 : ℝ) : ℂ))
      = ∑ i ∈ S, ∑ j ∈ S, (starRingEnd ℂ) (c i) * c j *
          (∫ x in a..b, (x : ℂ) ^ (Complex.I * ((t j - t i : ℝ) : ℂ))) := by
  classical
  have hsub : Set.uIcc a b ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact lt_of_lt_of_le ha hx.1
  have hInt : ∀ w : ℂ, IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ w) volume a b :=
    fun w => intervalIntegrable_ofReal_cpow a b ha hab w
  rw [intervalIntegral.integral_congr
    (fun x hx => normSq_sum_cpow_expansion S t c (hsub hx))]
  -- integrability of the inner sums
  have houter : ∀ i ∈ S, IntervalIntegrable
      (fun x : ℝ => ∑ j ∈ S, (starRingEnd ℂ) (c i) * c j *
        (x : ℂ) ^ (Complex.I * ((t j - t i : ℝ) : ℂ))) volume a b := by
    intro i _
    refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_finsetSum S (fun j _ => ?_)
    exact (((continuousOn_ofReal_cpow (Complex.I * ((t j - t i : ℝ) : ℂ))).mono hsub).const_mul
      ((starRingEnd ℂ) (c i) * c j))
  rw [intervalIntegral.integral_finsetSum
    (f := fun i x => ∑ j ∈ S, (starRingEnd ℂ) (c i) * c j *
        (x : ℂ) ^ (Complex.I * ((t j - t i : ℝ) : ℂ))) houter]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [intervalIntegral.integral_finsetSum
    (f := fun j x => (starRingEnd ℂ) (c i) * c j *
        (x : ℂ) ^ (Complex.I * ((t j - t i : ℝ) : ℂ)))
    (fun j _ => (hInt (Complex.I * ((t j - t i : ℝ) : ℂ))).const_mul
      ((starRingEnd ℂ) (c i) * c j))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [intervalIntegral.integral_const_mul]

end Commons.Analysis.DirichletPolynomial
