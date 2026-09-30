import Mathlib
import Submission.Work.BW.DefsAC

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Chain rule for `∂/∂Y₀` along the substitution `Y₀ ↦ a Y₀ + c`:
`∂/∂Y₀ (f(a Y₀ + c)) = a · f'(a Y₀ + c)`. -/
private lemma pderiv0_aeval_scaled_derivative {r : ℕ} (a c : ℂ) (f : Polynomial ℂ) :
    MvPolynomial.pderiv (0 : Fin (r + 1))
        (Polynomial.aeval (MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C c) f)
      = MvPolynomial.C a *
        Polynomial.aeval (MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C c)
          (Polynomial.derivative f) := by
  rw [Derivation.comp_aeval_eq]
  have hP : MvPolynomial.pderiv (0 : Fin (r + 1))
      (MvPolynomial.C a * MvPolynomial.X (0 : Fin (r + 1)) + MvPolynomial.C c)
      = MvPolynomial.C a := by
    rw [map_add, MvPolynomial.pderiv_C, add_zero, MvPolynomial.pderiv_C_mul,
      MvPolynomial.pderiv_X_self, mul_one]
  rw [hP, smul_eq_mul, mul_comm]

/-- Iterated chain rule: `(∂/∂Y₀)^[k] (f(a Y₀ + c)) = a^k · f^{(k)}(a Y₀ + c)`. -/
private lemma pderiv0_iterate_aeval_scaled_derivative {r : ℕ} (a c : ℂ) (p : Polynomial ℂ)
    (k : ℕ) :
    (MvPolynomial.pderiv (0 : Fin (r + 1)))^[k]
        (Polynomial.aeval (MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C c) p)
      = (MvPolynomial.C a)^k *
        Polynomial.aeval (MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C c)
          ((Polynomial.derivative)^[k] p) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, MvPolynomial.pderiv_mul,
      pderiv0_aeval_scaled_derivative]
    rw [show (MvPolynomial.pderiv (0 : Fin (r + 1))) ((MvPolynomial.C a)^k) = 0 from by
          rw [← map_pow]; exact MvPolynomial.pderiv_C]
    rw [zero_mul, zero_add, ← mul_assoc, ← pow_succ, Function.iterate_succ_apply']

/-- Over `ℂ`: iterating `∂/∂Y₀` on the value of a polynomial at `a Y₀ + c` gives
`k! a^k` times the value of the `k`-th Hasse derivative. -/
private lemma pderiv0_iterate_aeval_scaled_aux {r : ℕ} (a c : ℂ) (p : Polynomial ℂ) (k : ℕ) :
    (MvPolynomial.pderiv (0 : Fin (r + 1)))^[k]
        (Polynomial.aeval (MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C c) p)
      = ((k.factorial : ℂ) * a ^ k) •
        Polynomial.aeval (MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C c)
          (Polynomial.hasseDeriv k p) := by
  rw [pderiv0_iterate_aeval_scaled_derivative]
  -- `derivative^[k] = k! • hasseDeriv k`.
  rw [show (Polynomial.derivative)^[k] p = (k.factorial : ℂ) • Polynomial.hasseDeriv k p from by
        rw [← congr_fun (Polynomial.factorial_smul_hasseDeriv (R := ℂ) k) p]
        simp only [LinearMap.smul_apply]
        simp [Algebra.smul_def]]
  rw [map_smul]
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul]
  rw [← mul_assoc, ← map_pow, ← map_mul, mul_comm (a ^ k) (k.factorial : ℂ)]

theorem pderiv0_pow_aeval_scaled {r : ℕ} (a c : ℂ) (q : Polynomial ℚ) (k : ℕ) :
    (MvPolynomial.pderiv (0 : Fin (r + 1)))^[k]
        (Polynomial.aeval (MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C c) q)
      = ((k.factorial : ℂ) * a ^ k) •
        Polynomial.aeval (MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C c)
          (Polynomial.hasseDeriv k q) := by
  have hφ : (algebraMap ℂ (MvPolynomial (Fin (r + 1)) ℂ)).comp (algebraMap ℚ ℂ)
      = algebraMap ℚ (MvPolynomial (Fin (r + 1)) ℂ) := by
    ext x; simp
  -- Reinterpret the `ℚ`-coefficient data as `ℂ`-coefficient data.
  have hq := Polynomial.aeval_eq_aeval_map (R := ℚ) (S := MvPolynomial (Fin (r + 1)) ℂ)
      (T := ℂ) hφ q (MvPolynomial.C a * MvPolynomial.X (0 : Fin (r + 1)) + MvPolynomial.C c)
  have hh := Polynomial.aeval_eq_aeval_map (R := ℚ) (S := MvPolynomial (Fin (r + 1)) ℂ)
      (T := ℂ) hφ (Polynomial.hasseDeriv k q)
      (MvPolynomial.C a * MvPolynomial.X (0 : Fin (r + 1)) + MvPolynomial.C c)
  rw [hq, hh, ← Polynomial.hasseDeriv_map (algebraMap ℚ ℂ) k q]
  exact pderiv0_iterate_aeval_scaled_aux a c (q.map (algebraMap ℚ ℂ)) k

end Work.BW
