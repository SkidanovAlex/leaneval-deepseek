import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open _root_.Polynomial

namespace Commons.RingTheory.Polynomial

theorem isRoot_eq_of_sub_mem_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R]
    {f : Polynomial R} {x y : R} (hx : f.IsRoot x) (hy : f.IsRoot y)
    (hxy : x - y ∈ IsLocalRing.maximalIdeal R) (hu : IsUnit (f.derivative.eval y)) : x = y := by
  -- Write `f - C (f.eval y) = (X - C y) * q`, using that `y` is a root of `f - C (f.eval y)`.
  obtain ⟨q, hq⟩ : (X - C y) ∣ (f - C (f.eval y)) := by
    rw [dvd_iff_isRoot]
    simp [IsRoot.def, hy.eq_zero]
  -- Differentiate: `f.derivative = q + (X - C y) * q.derivative`, hence `q.eval y = f.derivative.eval y`.
  have hderiv : f.derivative = q + (X - C y) * q.derivative := by
    have h := congrArg derivative hq
    simpa only [derivative_sub, derivative_C, sub_zero, derivative_mul, derivative_X,
      one_mul] using h
  have hqy : q.eval y = f.derivative.eval y := by
    have h := congrArg (Polynomial.eval y) hderiv
    simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero] at h
    exact h.symm
  -- Evaluate the factorization at `x`: `f.eval x - f.eval y = (x - y) * q.eval x`.
  have hx_eval : f.eval x - f.eval y = (x - y) * q.eval x := by
    have h := congrArg (Polynomial.eval x) hq
    simpa only [eval_sub, eval_mul, eval_X, eval_C] using h
  -- Taylor-type remainder: `q.eval x = q.eval y + (x - y) * r = f.derivative.eval y + (x - y) * r`.
  obtain ⟨r, hr⟩ := Polynomial.sub_dvd_eval_sub x y q
  have hqx : q.eval x = f.derivative.eval y + (x - y) * r := by
    have h := sub_eq_iff_eq_add.mp hr
    rw [hqy, add_comm] at h
    exact h
  -- Using `f.eval x = f.eval y = 0`:
  have hmain : (x - y) * (f.derivative.eval y + (x - y) * r) = 0 := by
    have h1 : (x - y) * q.eval x = 0 := by
      rw [← hx_eval]
      simp [hx.eq_zero, hy.eq_zero]
    rwa [hqx] at h1
  -- `(x - y) * r` lies in the maximal ideal, so `f.derivative.eval y + (x - y) * r` is a unit.
  have hz : (x - y) * r ∈ IsLocalRing.maximalIdeal R := by
    rw [mul_comm]
    exact Ideal.mul_mem_left _ r hxy
  have huz : IsUnit (f.derivative.eval y + (x - y) * r) := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    rw [← IsLocalRing.notMem_maximalIdeal] at hu
    intro hmem
    exact hu (by
      have h2 := (IsLocalRing.maximalIdeal R).sub_mem hmem hz
      simpa using h2)
  have hxy0 : x - y = 0 := (IsUnit.mul_left_eq_zero huz).1 hmain
  exact sub_eq_zero.mp hxy0

end Commons.RingTheory.Polynomial