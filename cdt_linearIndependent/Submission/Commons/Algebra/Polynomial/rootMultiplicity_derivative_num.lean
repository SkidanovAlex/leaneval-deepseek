import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.Algebra.Polynomial

/-- The algebraic identity behind the quotient-rule numerator.  If `v = (X - C a)^m * w` with
`m ≥ 1`, then
`u' * v - u * v' = (X - C a)^(m-1) * ((X - C a) * u' * w - C m * u * w - (X - C a) * u * w')`. -/
lemma derivative_num_eq_pow_pred_mul {K : Type*} [Field K] (u v w : Polynomial K) (a : K)
    (m : ℕ) (hm : 1 ≤ m) (hv : v = (Polynomial.X - Polynomial.C a) ^ m * w) :
    u.derivative * v - u * v.derivative
      = (Polynomial.X - Polynomial.C a) ^ (m - 1) *
        ((Polynomial.X - Polynomial.C a) * u.derivative * w
          - Polynomial.C (m : K) * u * w
          - (Polynomial.X - Polynomial.C a) * u * w.derivative) := by
  have hpow : (Polynomial.X - Polynomial.C a : Polynomial K) ^ m
      = (Polynomial.X - Polynomial.C a) ^ (m - 1) * (Polynomial.X - Polynomial.C a) := by
    conv_lhs => rw [← Nat.sub_add_cancel hm]
    rw [pow_succ]
  have hdv : v.derivative
      = Polynomial.C (m : K) * (Polynomial.X - Polynomial.C a) ^ (m - 1) * w
        + (Polynomial.X - Polynomial.C a) ^ m * w.derivative := by
    rw [hv, Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.derivative_X_sub_C]
    simp
  rw [hdv, hv, hpow]
  ring

/-- **The multiplicity of the quotient-rule numerator.**  Let `u, v ∈ K[X]` be coprime over a field
`K` of characteristic zero, let `a : K`, suppose `u` does not vanish at `a`
(`rootMultiplicity a u = 0`) and that `v` has a root of multiplicity `m ≥ 1` at `a`.  Then the
quotient-rule numerator `u' * v - u * v'` has multiplicity exactly `m - 1` at `a`.

Indeed, writing `v = (X - C a) ^ m * v₁` with `v₁ a ≠ 0`, one computes
`u' * v - u * v' = (X - C a) ^ (m - 1) * ((m * u * v₁) + (X - C a) * (...))`, and the first factor
in parentheses does not vanish at `a` because `m ≠ 0` and `u`, `v₁` do not vanish there. -/
theorem rootMultiplicity_derivative_num {K : Type*} [Field K] [CharZero K] (u v : Polynomial K)
    (hcop : IsCoprime u v) (a : K) (hu : u.rootMultiplicity a = 0)
    (hv : 1 ≤ v.rootMultiplicity a) :
    (u.derivative * v - u * v.derivative).rootMultiplicity a = v.rootMultiplicity a - 1 := by
  -- `v` is nonzero because it has a root of positive multiplicity.
  have hv_ne : v ≠ 0 := by rintro rfl; simp at hv
  -- Factor `v = (X - C a)^m * w` with `(X - C a) ∤ w`.
  obtain ⟨w, hvw, hwndvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd v hv_ne a
  -- The bracket that survives after extracting `(X - C a)^(m-1)`.
  set M : Polynomial K := (Polynomial.X - Polynomial.C a) * u.derivative * w
      - Polynomial.C (v.rootMultiplicity a : K) * u * w
      - (Polynomial.X - Polynomial.C a) * u * w.derivative with hM
  have hN : u.derivative * v - u * v.derivative
      = M * (Polynomial.X - Polynomial.C a) ^ (v.rootMultiplicity a - 1) := by
    rw [hM, derivative_num_eq_pow_pred_mul u v w a (v.rootMultiplicity a) hv hvw]
    ring
  -- The bracket evaluates at `a` to `-m * u(a) * w(a)`, a nonzero element.
  have hMeval : M.eval a = -((v.rootMultiplicity a : K) * u.eval a * w.eval a) := by
    rw [hM]; simp
  -- `u(a) ≠ 0`: otherwise `u = 0` and coprimality would make `v` a unit, hence rootless.
  have hu_eval : u.eval a ≠ 0 := by
    intro h
    have hu0 : u = 0 :=
      (Polynomial.rootMultiplicity_eq_zero_iff.mp hu) (by rw [Polynomial.IsRoot.def]; exact h)
    have hunit : IsUnit v := by
      rw [hu0] at hcop
      exact isCoprime_zero_left.mp hcop
    have hv_eval_ne : v.eval a ≠ 0 := (hunit.map (Polynomial.evalRingHom a)).ne_zero
    have hv_root : v.IsRoot a :=
      (Polynomial.rootMultiplicity_pos'.mp (by omega : 0 < v.rootMultiplicity a)).2
    exact hv_eval_ne (by rwa [Polynomial.IsRoot.def] at hv_root)
  -- `w(a) ≠ 0` because `(X - C a) ∤ w`.
  have hw_eval : w.eval a ≠ 0 := by
    intro h
    exact hwndvd (Polynomial.dvd_iff_isRoot.mpr (by rw [Polynomial.IsRoot.def]; exact h))
  have hm_cast : (v.rootMultiplicity a : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hMeval_ne : M.eval a ≠ 0 := by
    rw [hMeval]
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero hm_cast hu_eval) hw_eval)
  have hM_ne : M ≠ 0 := by
    intro h; rw [h] at hMeval_ne; simp at hMeval_ne
  have hMroot : M.rootMultiplicity a = 0 :=
    Polynomial.rootMultiplicity_eq_zero (by rw [Polynomial.IsRoot.def]; exact hMeval_ne)
  calc (u.derivative * v - u * v.derivative).rootMultiplicity a
      = (M * (Polynomial.X - Polynomial.C a) ^ (v.rootMultiplicity a - 1)).rootMultiplicity a := by
        rw [hN]
    _ = M.rootMultiplicity a + (v.rootMultiplicity a - 1) :=
        Polynomial.rootMultiplicity_mul_X_sub_C_pow (p := M) hM_ne
    _ = v.rootMultiplicity a - 1 := by rw [hMroot, zero_add]

end Commons.Algebra.Polynomial