import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div

namespace Commons.Algebra.Polynomial

section Generic

variable {R : Type*} [CommRing R]

/-- The "power rule" in the form `t * (t^m)' = m * t^m`, valid when `t' = 1`. -/
theorem deriv_pow_mul_self (t : Polynomial R) (ht : t.derivative = 1) (m : ℕ) :
    t * (t ^ m).derivative = (m : Polynomial R) * t ^ m := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Polynomial.derivative_mul, ht, mul_one, mul_add, ← mul_assoc, ih, ← pow_succ']
    push_cast
    ring

/-- The key algebraic identity behind `eulerOperator_factor`. -/
theorem euler_key (t u v : Polynomial R) (m n : ℕ) (ht : t.derivative = 1) :
    t * ((t ^ m * u).derivative * (t ^ n * v) - (t ^ m * u) * (t ^ n * v).derivative)
      - ((m : Polynomial R) - (n : Polynomial R)) * ((t ^ m * u) * (t ^ n * v))
    = t ^ (m + n + 1) * (u.derivative * v - u * v.derivative) := by
  have h1 : t * (t ^ m * u).derivative - (m : Polynomial R) * (t ^ m * u)
      = t ^ (m + 1) * u.derivative := by
    rw [Polynomial.derivative_mul, mul_add, ← mul_assoc t (t ^ m).derivative u,
      ← mul_assoc t (t ^ m) u.derivative]
    rw [deriv_pow_mul_self t ht m, ← pow_succ']
    ring
  have h2 : t * (t ^ n * v).derivative - (n : Polynomial R) * (t ^ n * v)
      = t ^ (n + 1) * v.derivative := by
    rw [Polynomial.derivative_mul, mul_add, ← mul_assoc t (t ^ n).derivative v,
      ← mul_assoc t (t ^ n) v.derivative]
    rw [deriv_pow_mul_self t ht n, ← pow_succ']
    ring
  have hrw : t * ((t ^ m * u).derivative * (t ^ n * v) - (t ^ m * u) * (t ^ n * v).derivative)
      - ((m : Polynomial R) - (n : Polynomial R)) * ((t ^ m * u) * (t ^ n * v))
      = (t * (t ^ m * u).derivative - (m : Polynomial R) * (t ^ m * u)) * (t ^ n * v)
        - (t ^ m * u) * (t * (t ^ n * v).derivative - (n : Polynomial R) * (t ^ n * v)) := by
    ring
  rw [hrw, h1, h2]
  have hA : t ^ (m + 1) * t ^ n = t ^ (m + n + 1) := by rw [← pow_add, Nat.add_right_comm]
  have hB : t ^ m * t ^ (n + 1) = t ^ (m + n + 1) := by rw [← pow_add, Nat.add_assoc]
  calc t ^ (m + 1) * u.derivative * (t ^ n * v) - (t ^ m * u) * (t ^ (n + 1) * v.derivative)
      = (t ^ (m + 1) * t ^ n) * (u.derivative * v)
          - (t ^ m * t ^ (n + 1)) * (u * v.derivative) := by ring
    _ = t ^ (m + n + 1) * (u.derivative * v)
          - t ^ (m + n + 1) * (u * v.derivative) := by rw [hA, hB]
    _ = t ^ (m + n + 1) * (u.derivative * v - u * v.derivative) := by ring

end Generic

theorem eulerOperator_factor {K : Type*} [Field K] (p q : Polynomial K) (α : K) :
    ∃ r : Polynomial K,
      (Polynomial.X - Polynomial.C α) * (p.derivative * q - p * q.derivative)
        - Polynomial.C ((((Polynomial.rootMultiplicity α p : ℤ) - (Polynomial.rootMultiplicity α q : ℤ)) : ℤ) : K)
            * (p * q)
      = (Polynomial.X - Polynomial.C α) ^
          (Polynomial.rootMultiplicity α p + Polynomial.rootMultiplicity α q + 1) * r := by
  obtain ⟨u, hu⟩ := Polynomial.pow_rootMultiplicity_dvd p α
  obtain ⟨v, hv⟩ := Polynomial.pow_rootMultiplicity_dvd q α
  generalize hm : Polynomial.rootMultiplicity α p = m at *
  generalize hn : Polynomial.rootMultiplicity α q = n at *
  refine ⟨u.derivative * v - u * v.derivative, ?_⟩
  have ht : (Polynomial.X - Polynomial.C α).derivative = 1 := by
    rw [Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C, sub_zero]
  have hc : Polynomial.C ((((m : ℤ) - (n : ℤ)) : ℤ) : K)
      = (m : Polynomial K) - (n : Polynomial K) := by
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast, Polynomial.C_sub,
      Polynomial.C_eq_natCast, Polynomial.C_eq_natCast]
  rw [hc, hu, hv]
  exact euler_key (Polynomial.X - Polynomial.C α) u v m n ht

end Commons.Algebra.Polynomial