import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Partial sums of polynomials over `ℚ`

For every polynomial `Q` over `ℚ`, the partial sums `t ↦ ∑_{s < t} Q(s)` are again given by a
polynomial in `t` (Faulhaber's formula, obtained here from Mathlib's Bernoulli polynomials).
-/

namespace Work.RB

open Polynomial

/-- Faulhaber's formula: `t ↦ ∑_{s < t} s ^ e` is a polynomial in `t`. -/
theorem exists_sum_pow_poly (e : ℕ) :
    ∃ F : Polynomial ℚ, ∀ t : ℕ, F.eval (t : ℚ) = ∑ s ∈ Finset.range t, (s : ℚ) ^ e := by
  refine ⟨(Polynomial.bernoulli (e+1) - Polynomial.C ((Polynomial.bernoulli (e+1)).eval 0)) *
      Polynomial.C (((e+1 : ℕ) : ℚ)⁻¹), ?_⟩
  intro t
  rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_C]
  have h := bernoulli_succ_eval t e
  rw [show _root_.bernoulli e.succ = (Polynomial.bernoulli (e+1)).eval 0 from
      (Polynomial.bernoulli_eval_zero (e+1)).symm] at h
  rw [h]
  rw [show (((e:ℚ)) + 1) = ((e+1 : ℕ) : ℚ) by push_cast; ring]
  have hne : (((e+1 : ℕ)) : ℚ) ≠ 0 := by positivity
  field_simp
  ring

/-- Partial sums of a polynomial over `ℚ` are again polynomial. -/
theorem exists_partial_sum_poly (Q : Polynomial ℚ) :
    ∃ R : Polynomial ℚ, ∀ t : ℕ, R.eval (t : ℚ) = ∑ s ∈ Finset.range t, Q.eval (s : ℚ) := by
  classical
  choose F hF using exists_sum_pow_poly
  refine ⟨Q.sum (fun e c => Polynomial.C c * F e), ?_⟩
  intro t
  rw [Polynomial.sum_def, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  have step : ∀ e ∈ Q.support, Q.coeff e * (F e).eval (t:ℚ) =
      ∑ s ∈ Finset.range t, Q.coeff e * (s:ℚ)^e := by
    intro e _; rw [hF e t, Finset.mul_sum]
  rw [Finset.sum_congr rfl step, Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro s _
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]

/-- Shifted partial sums: for `t ≥ M`, `∑_{M ≤ s < t} Q(s)` is polynomial in `t`. -/
theorem exists_partial_sum_poly_shift (Q : Polynomial ℚ) (M : ℕ) :
    ∃ R : Polynomial ℚ, ∀ t : ℕ, M ≤ t →
      R.eval (t : ℚ) = ∑ k ∈ Finset.range (t - M), Q.eval ((M + k : ℕ) : ℚ) := by
  obtain ⟨R0, hR0⟩ := exists_partial_sum_poly Q
  refine ⟨R0 - Polynomial.C (R0.eval (M:ℚ)), ?_⟩
  intro t ht
  rw [Polynomial.eval_sub, Polynomial.eval_C, hR0 t, hR0 M]
  have hsplit : ∑ s ∈ Finset.range t, Q.eval (s:ℚ) =
      (∑ s ∈ Finset.range M, Q.eval (s:ℚ)) +
        ∑ k ∈ Finset.range (t-M), Q.eval ((M+k : ℕ):ℚ) := by
    rw [← Finset.sum_range_add_sum_Ico (fun s => Q.eval (s:ℚ)) ht]
    congr 1
    rw [Finset.sum_Ico_eq_sum_range]
  rw [hsplit]
  ring

end Work.RB
