import Mathlib
import Submission.Subspace.PderivDiv
import Submission.Subspace.UBounds

/-!
# Bounds for the divided iterated derivative

The `ν!`-divided derivative `∂^ν P / ν!` has coefficients bounded by
`max |coeff P| * 2 ^ (N * deg P)`, *not* by `max |coeff P| * deg P ^ |ν|`; this is what makes the
`A`-bounds of the subspace theorem work without a `log (degree)` loss.  This file records

* `support_pderivIterDiv_eq_support`: dividing by `ν!` does not change the support;
* `coeff_pderivIterDiv_norm_le`: the coefficient bound;
* `aeval_pderivIterDiv_int`: the divided derivative of an integer polynomial is again an
  integer polynomial, so its value at an integral point is an integer.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

open scoped BigOperators

namespace Submission.Subspace

open MvPolynomial

variable {m N : ℕ}

/-- `ν! = ∏ i, (ν i)!` is positive. -/
lemma facOf_pos {σ : Type*} [Fintype σ] (e : σ →₀ ℕ) : 0 < facOf e := by
  rw [facOf]
  exact Finset.prod_pos fun i _ => Nat.factorial_pos _

/-- Over a field, dividing the iterated derivative by `ν!` does not change its support. -/
lemma support_pderivIterDiv_eq_support {K : Type*} [Field K] [CharZero K]
    (e : (Fin m × Fin N) →₀ ℕ) (F : MvPolynomial (Fin m × Fin N) K) :
    (pderivIterDiv e F).support = (Commons.Algebra.MvPolynomial.pderivIter e F).support := by
  rw [pderivIterDiv_eq_inv_mul]
  ext J
  rw [MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul,
    mul_ne_zero_iff]
  constructor
  · intro h; exact h.2
  · intro h
    exact ⟨inv_ne_zero (Nat.cast_ne_zero.mpr (facOf_pos e).ne'), h⟩

/-- The product of the binomial coefficients occurring in the divided derivative is at most
`2 ^ (∑ i, (J + e) i)`. -/
theorem prod_choose_le_two_pow_sum {m N : ℕ} (e J : (Fin m × Fin N) →₀ ℕ) :
    (∏ i : Fin m × Fin N, (((J + e) i).choose (e i) : ℕ))
      ≤ 2 ^ (∑ i : Fin m × Fin N, (J + e) i) := by
  classical
  calc (∏ i : Fin m × Fin N, (((J + e) i).choose (e i) : ℕ))
      ≤ ∏ i : Fin m × Fin N, 2 ^ ((J + e) i) :=
        Finset.prod_le_prod (fun i _ => Nat.zero_le _)
          (fun i _ => Nat.choose_le_two_pow ((J + e) i) (e i))
    _ = 2 ^ (∑ i : Fin m × Fin N, (J + e) i) := Finset.prod_pow_eq_pow_sum _ _ _

/-- **Coefficient bound for the divided iterated derivative.**  If `F` has coefficients bounded
by `Bd` and block-degrees `d h`, then the coefficients of `∂^e F / e!` are bounded by
`Bd * 2 ^ (N * ∑ h, d h)`. -/
theorem coeff_pderivIterDiv_norm_le {m N : ℕ} (F : MvPolynomial (Fin m × Fin N) ℂ)
    (d : Fin m → ℕ) (Bd : ℝ) (hBd : 0 ≤ Bd)
    (hcoeff : ∀ J, ‖F.coeff J‖ ≤ Bd)
    (hdeg : ∀ J ∈ F.support, ∀ h : Fin m, ∑ k : Fin N, J (h, k) ≤ d h)
    (e J : (Fin m × Fin N) →₀ ℕ) :
    ‖(pderivIterDiv e F).coeff J‖ ≤ Bd * 2 ^ (N * ∑ h : Fin m, d h) := by
  classical
  rw [coeff_pderivIterDiv]
  by_cases hmem : J + e ∈ F.support
  · have h1 : ‖F.coeff (J + e)‖ ≤ Bd := hcoeff _
    have hsum : (∑ i : Fin m × Fin N, (J + e) i) ≤ N * ∑ h : Fin m, d h := by
      rw [Fintype.sum_prod_type]
      have hblock : ∑ h : Fin m, ∑ k : Fin N, (J + e) (h, k) ≤ ∑ h : Fin m, d h :=
        Finset.sum_le_sum (fun h _ => hdeg (J + e) hmem h)
      rcases Nat.eq_zero_or_pos N with hN | hN
      · subst hN
        simpa using hblock
      · calc ∑ h : Fin m, ∑ k : Fin N, (J + e) (h, k)
            ≤ ∑ h : Fin m, d h := hblock
          _ = 1 * ∑ h : Fin m, d h := (one_mul _).symm
          _ ≤ (N : ℕ) * ∑ h : Fin m, d h := Nat.mul_le_mul_right _ (by omega)
    have h2 : ‖((((∏ i : Fin m × Fin N, ((J + e) i).choose (e i)) : ℕ)) : ℂ)‖
        ≤ (2 : ℝ) ^ (N * ∑ h : Fin m, d h) := by
      rw [Complex.norm_natCast]
      have hle : (∏ i : Fin m × Fin N, ((J + e) i).choose (e i))
          ≤ 2 ^ (∑ i : Fin m × Fin N, (J + e) i) := prod_choose_le_two_pow_sum e J
      calc (((∏ i : Fin m × Fin N, ((J + e) i).choose (e i) : ℕ)) : ℝ)
          ≤ (((2 ^ (∑ i : Fin m × Fin N, (J + e) i) : ℕ)) : ℝ) := by exact_mod_cast hle
        _ = (2 : ℝ) ^ (∑ i : Fin m × Fin N, (J + e) i) := by push_cast; ring
        _ ≤ (2 : ℝ) ^ (N * ∑ h : Fin m, d h) := pow_le_pow_right₀ (by norm_num) hsum
    calc ‖F.coeff (J + e) * (((∏ i : Fin m × Fin N, ((J + e) i).choose (e i)) : ℕ) : ℂ)‖
        = ‖F.coeff (J + e)‖ * ‖((((∏ i : Fin m × Fin N, ((J + e) i).choose (e i)) : ℕ)) : ℂ)‖ :=
          norm_mul _ _
      _ ≤ Bd * 2 ^ (N * ∑ h : Fin m, d h) := mul_le_mul h1 h2 (norm_nonneg _) hBd
  · rw [MvPolynomial.notMem_support_iff.mp hmem, zero_mul, norm_zero]
    exact mul_nonneg hBd (by positivity)

/-- The divided iterated derivative of an integer polynomial takes integer values at integral
points. -/
theorem aeval_pderivIterDiv_int {S : Type*} [CommRing S] [Algebra ℤ S]
    (F : MvPolynomial (Fin m × Fin N) ℤ) (e : (Fin m × Fin N) →₀ ℕ) (x : Fin m × Fin N → ℤ) :
    ∃ n : ℤ, MvPolynomial.aeval (fun q : Fin m × Fin N => algebraMap ℤ S (x q))
      (pderivIterDiv e (F.map (algebraMap ℤ S))) = algebraMap ℤ S n := by
  refine ⟨MvPolynomial.aeval x (pderivIterDiv e F), ?_⟩
  rw [pderivIterDiv_map]
  have h1 : MvPolynomial.aeval (fun q : Fin m × Fin N => algebraMap ℤ S (x q))
      ((pderivIterDiv e F).map (algebraMap ℤ S)) =
      MvPolynomial.aeval (fun q : Fin m × Fin N => algebraMap ℤ S (x q))
        (pderivIterDiv e F) :=
    MvPolynomial.aeval_map_algebraMap S _ _
  rw [h1, MvPolynomial.aeval_eq_eval₂Hom]
  have h2 := MvPolynomial.map_aeval (R := ℤ) (σ := Fin m × Fin N)
    (g := x) (φ := algebraMap ℤ S) (p := pderivIterDiv e F)
  rw [show (algebraMap ℤ S).comp (algebraMap ℤ ℤ) = (algebraMap ℤ S) from by
    ext n; simp] at h2
  exact h2.symm

end Submission.Subspace
