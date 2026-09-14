import Mathlib
import Submission.Commons.Algebra.MvPolynomial.coeff_pderivIter

namespace Commons.Algebra.MvPolynomial

open scoped BigOperators

/-- The factorial factor appearing in `coeff_pderivIter` is bounded by the box bound `d`:
if `(J + e) i ≤ d i.1` for every `i : Fin m × Fin N`, then
`∏ i, ((J+e) i).descFactorial (e i) ≤ ∏ h, (d h) ^ (∑ k, e (h,k))`. -/
lemma prod_descFactorial_pderivIter_le {m N : ℕ} (e J : (Fin m × Fin N) →₀ ℕ)
    (d : Fin m → ℕ) (hle : ∀ i : Fin m × Fin N, (J + e) i ≤ d i.1) :
    (∏ i : Fin m × Fin N, ((J + e) i).descFactorial (e i))
      ≤ ∏ h : Fin m, (d h) ^ (∑ k : Fin N, e (h, k)) := by
  classical
  rw [Fintype.prod_prod_type]
  refine Finset.prod_le_prod (fun h _ => Nat.zero_le _) (fun h _ => ?_)
  calc ∏ k : Fin N, ((J + e) (h, k)).descFactorial (e (h, k))
      ≤ ∏ k : Fin N, (d h) ^ (e (h, k)) := by
        refine Finset.prod_le_prod (fun k _ => Nat.zero_le _) (fun k _ => ?_)
        calc ((J + e) (h, k)).descFactorial (e (h, k))
            ≤ ((J + e) (h, k)) ^ (e (h, k)) := Nat.descFactorial_le_pow _ _
          _ ≤ (d h) ^ (e (h, k)) := Nat.pow_le_pow_left (hle (h, k)) _
    _ = (d h) ^ (∑ k : Fin N, e (h, k)) := Finset.prod_pow_eq_pow_sum _ _ _

theorem coeff_pderivIter_norm_le {m N : ℕ} (F : MvPolynomial (Fin m × Fin N) ℂ)
    (d : Fin m → ℕ) (Bd : ℝ) (hBd : 0 ≤ Bd)
    (hcoeff : ∀ J, ‖F.coeff J‖ ≤ Bd)
    (hdeg : ∀ J ∈ F.support, ∀ h : Fin m, ∑ k : Fin N, J (h, k) ≤ d h)
    (e : (Fin m × Fin N) →₀ ℕ) (J : (Fin m × Fin N) →₀ ℕ) :
    ‖(Commons.Algebra.MvPolynomial.pderivIter e F).coeff J‖
      ≤ Bd * ∏ h : Fin m, (d h : ℝ) ^ (∑ k : Fin N, e (h, k)) := by
  classical
  have hRHS : (0 : ℝ) ≤ ∏ h : Fin m, (d h : ℝ) ^ (∑ k : Fin N, e (h, k)) :=
    Finset.prod_nonneg (fun h _ => pow_nonneg (Nat.cast_nonneg _) _)
  rw [Commons.Algebra.MvPolynomial.coeff_pderivIter]
  by_cases hmem : J + e ∈ F.support
  · have hle : ∀ i : Fin m × Fin N, (J + e) i ≤ d i.1 := by
      intro i
      have hsum := hdeg (J + e) hmem i.1
      calc (J + e) i = (J + e) (i.1, i.2) := rfl
        _ ≤ ∑ k : Fin N, (J + e) (i.1, k) :=
            Finset.single_le_sum (s := Finset.univ) (f := fun k : Fin N => (J + e) (i.1, k))
              (fun k _ => Nat.zero_le _) (Finset.mem_univ i.2)
        _ ≤ d i.1 := hsum
    have hprod := prod_descFactorial_pderivIter_le e J d hle
    have hc : ‖F.coeff (J + e)‖ ≤ Bd := hcoeff _
    rw [norm_mul, Complex.norm_natCast]
    calc ‖F.coeff (J + e)‖ * ((∏ i : Fin m × Fin N, ((J + e) i).descFactorial (e i) : ℕ) : ℝ)
        ≤ Bd * ((∏ i : Fin m × Fin N, ((J + e) i).descFactorial (e i) : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)
      _ ≤ Bd * ∏ h : Fin m, (d h : ℝ) ^ (∑ k : Fin N, e (h, k)) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hprod) hBd
  · rw [MvPolynomial.notMem_support_iff.mp hmem, zero_mul, norm_zero]
    exact mul_nonneg hBd hRHS

end Commons.Algebra.MvPolynomial
