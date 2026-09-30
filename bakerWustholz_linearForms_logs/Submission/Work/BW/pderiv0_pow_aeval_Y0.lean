import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Over `ℂ`: iterating `∂/∂Y₀` on the value of a polynomial in `Y₀ + c` gives the value of the
`k`-th iterated (ordinary) derivative, and `derivative^[k] = k! • hasseDeriv k`. -/
theorem pderiv0_iterate_aeval_Y0_aux {r : ℕ} (c : ℂ) (p : Polynomial ℂ) (k : ℕ) :
    (MvPolynomial.pderiv (0 : Fin (r + 1)))^[k]
        (Polynomial.aeval (MvPolynomial.X 0 + MvPolynomial.C c) p)
      = (k.factorial : ℂ) •
        Polynomial.aeval (MvPolynomial.X 0 + MvPolynomial.C c) (Polynomial.hasseDeriv k p) := by
  -- Chain rule: `∂/∂Y₀` on `p(Y₀ + c)` is `p'(Y₀ + c)`, since `∂/∂Y₀ (Y₀ + c) = 1`.
  have key : ∀ f : Polynomial ℂ,
      MvPolynomial.pderiv (0 : Fin (r + 1))
          (Polynomial.aeval (MvPolynomial.X 0 + MvPolynomial.C c) f)
        = Polynomial.aeval (MvPolynomial.X 0 + MvPolynomial.C c) (Polynomial.derivative f) := by
    intro f
    rw [Derivation.comp_aeval_eq]
    simp
  -- Iterating the chain rule.
  have hiter : ∀ k : ℕ,
      (MvPolynomial.pderiv (0 : Fin (r + 1)))^[k]
          (Polynomial.aeval (MvPolynomial.X 0 + MvPolynomial.C c) p)
        = Polynomial.aeval (MvPolynomial.X 0 + MvPolynomial.C c) ((Polynomial.derivative)^[k] p) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Function.iterate_succ_apply', ih, key, Function.iterate_succ_apply']
  rw [hiter k]
  -- `derivative^[k] = k! • hasseDeriv k`.
  rw [show (Polynomial.derivative)^[k] p = (k.factorial : ℂ) • Polynomial.hasseDeriv k p from by
    rw [← congr_fun (Polynomial.factorial_smul_hasseDeriv (R := ℂ) k) p]
    simp only [LinearMap.smul_apply]
    simp [Algebra.smul_def]]
  simp

/-- Iterated `∂/∂Y₀` on a polynomial in `Y₀` alone equals `k!` times the `k`-th Hasse derivative,
evaluated at `Y₀ + c`. -/
theorem pderiv0_pow_aeval_Y0 {r : ℕ} (c : ℂ) (q : Polynomial ℚ) (k : ℕ) :
    (MvPolynomial.pderiv (0 : Fin (r + 1)))^[k]
        (Polynomial.aeval (MvPolynomial.X 0 + MvPolynomial.C c) q)
      = (k.factorial : ℂ) •
        Polynomial.aeval (MvPolynomial.X 0 + MvPolynomial.C c) (Polynomial.hasseDeriv k q) := by
  have hφ : (algebraMap ℂ (MvPolynomial (Fin (r + 1)) ℂ)).comp (algebraMap ℚ ℂ)
      = algebraMap ℚ (MvPolynomial (Fin (r + 1)) ℂ) := by
    ext x; simp
  -- Reinterpret the `ℚ`-coefficient data as `ℂ`-coefficient data.
  have hq := Polynomial.aeval_eq_aeval_map (R := ℚ) (S := MvPolynomial (Fin (r + 1)) ℂ)
      (T := ℂ) hφ q (MvPolynomial.X (0 : Fin (r + 1)) + MvPolynomial.C c)
  have hh := Polynomial.aeval_eq_aeval_map (R := ℚ) (S := MvPolynomial (Fin (r + 1)) ℂ)
      (T := ℂ) hφ (Polynomial.hasseDeriv k q)
      (MvPolynomial.X (0 : Fin (r + 1)) + MvPolynomial.C c)
  rw [hq, hh, ← Polynomial.hasseDeriv_map (algebraMap ℚ ℂ) k q]
  exact pderiv0_iterate_aeval_Y0_aux c (q.map (algebraMap ℚ ℂ)) k

end Work.BW
