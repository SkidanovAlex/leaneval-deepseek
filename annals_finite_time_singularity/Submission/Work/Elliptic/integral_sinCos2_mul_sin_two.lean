import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-! ## Auxiliary trigonometric evaluations

We compute `∫_0^{π/2} sin θ cos²θ · sin(2nθ) dθ` by writing `sin θ cos²θ = (sin θ + sin 3θ)/4`
and expanding the product of two sines with the product-to-sum identity.  The building blocks
below are the antiderivative of `cos (aθ)` on `[0, π/2]` and the values of `sin` at odd
half-integer multiples of `π`. -/

/-- `sin ((2m+1)π/2) = (-1)^m`. -/
lemma sin_odd_pi_half (m : ℕ) : Real.sin ((2*(m:ℝ)+1) * π/2) = (-1:ℝ)^m := by
  rw [show (2*(m:ℝ)+1)*π/2 = (m:ℝ)*π + π/2 by ring]
  rw [Real.sin_add, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
  ring

/-- `sin ((2m-1)π/2) = -(-1)^m`. -/
lemma sin_two_m_sub_one (m : ℕ) : Real.sin ((2*(m:ℝ)-1)*π/2) = -(-1:ℝ)^m := by
  have h : (2*(m:ℝ)-1)*π/2 = ((2*(m:ℝ)+1)*π/2) - π := by ring
  rw [h, Real.sin_sub, Real.cos_pi, Real.sin_pi, sin_odd_pi_half]
  ring

/-- `sin ((2m+3)π/2) = -(-1)^m`. -/
lemma sin_two_m_add_three (m : ℕ) : Real.sin ((2*(m:ℝ)+3)*π/2) = -(-1:ℝ)^m := by
  have h : (2*(m:ℝ)+3)*π/2 = (2*((m+1:ℕ):ℝ)+1)*π/2 := by push_cast; ring
  rw [h, sin_odd_pi_half (m+1), pow_succ]
  ring

/-- `sin ((2m+5)π/2) = (-1)^m`. -/
lemma sin_two_m_add_five (m : ℕ) : Real.sin ((2*(m:ℝ)+5)*π/2) = (-1:ℝ)^m := by
  have h : (2*(m:ℝ)+5)*π/2 = (2*((m+2:ℕ):ℝ)+1)*π/2 := by push_cast; ring
  rw [h, sin_odd_pi_half (m+2), pow_add]
  ring

/-- The product-to-sum rewriting of the integrand: writing `sin θ cos²θ = (sin θ + sin 3θ)/4`
and expanding `sin x sin y = (cos (x-y) - cos (x+y))/2` gives
`sin θ cos²θ · sin (2bθ) = ((cos ((2b-1)θ) - cos ((2b+1)θ)) + (cos ((2b-3)θ) - cos ((2b+3)θ)))/8`. -/
lemma sinCos2_mul_sin_eq (b θ : ℝ) :
    sinCos2 θ * Real.sin (2*b*θ)
      = (1/8) * ((Real.cos ((2*b-1)*θ) - Real.cos ((2*b+1)*θ))
          + (Real.cos ((2*b-3)*θ) - Real.cos ((2*b+3)*θ))) := by
  have hs : sinCos2 θ = (1/4)*(Real.sin θ + Real.sin (3*θ)) := by
    have h : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by linarith [Real.sin_sq_add_cos_sq θ]
    rw [sinCos2, Real.sin_three_mul, h]; ring
  have e1 : Real.cos (θ - 2*b*θ) = Real.cos ((2*b-1)*θ) := by
    rw [show θ - 2*b*θ = -((2*b-1)*θ) by ring, Real.cos_neg]
  have e2 : Real.cos (θ + 2*b*θ) = Real.cos ((2*b+1)*θ) := by
    rw [show θ + 2*b*θ = (2*b+1)*θ by ring]
  have e3 : Real.cos (3*θ - 2*b*θ) = Real.cos ((2*b-3)*θ) := by
    rw [show 3*θ - 2*b*θ = -((2*b-3)*θ) by ring, Real.cos_neg]
  have e4 : Real.cos (3*θ + 2*b*θ) = Real.cos ((2*b+3)*θ) := by
    rw [show 3*θ + 2*b*θ = (2*b+3)*θ by ring]
  have h2 : Real.sin θ * Real.sin (2*b*θ)
      = (1/2)*(Real.cos ((2*b-1)*θ) - Real.cos ((2*b+1)*θ)) := by
    have := Real.two_mul_sin_mul_sin θ (2*b*θ)
    rw [e1, e2] at this
    linarith
  have h3 : Real.sin (3*θ) * Real.sin (2*b*θ)
      = (1/2)*(Real.cos ((2*b-3)*θ) - Real.cos ((2*b+3)*θ)) := by
    have := Real.two_mul_sin_mul_sin (3*θ) (2*b*θ)
    rw [e3, e4] at this
    linarith
  rw [hs, mul_assoc, add_mul, h2, h3]
  ring

/-- `∫_0^{π/2} cos (aθ) dθ = sin (aπ/2)/a` for `a ≠ 0`. -/
lemma integral_cos_mul (a : ℝ) (ha : a ≠ 0) :
    ∫ θ in (0:ℝ)..(π/2), Real.cos (a * θ) = Real.sin (a * π/2) / a := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun θ => Real.sin (a*θ)/a)
    (f' := fun θ => Real.cos (a*θ))]
  · rw [mul_div_assoc]; simp
  · intro x _
    have h1 : HasDerivAt (fun θ : ℝ => Real.sin (a*θ)) (Real.cos (a*x) * a) x :=
      (Real.hasDerivAt_sin (a*x)).comp x (hasDerivAt_const_mul (x := x) a)
    refine (h1.div_const a).congr_deriv ?_
    field_simp
  · exact (by fun_prop : Continuous fun θ : ℝ => Real.cos (a*θ)).intervalIntegrable _ _

/-- Linearity of the interval integral applied to the four-cosine combination produced by
`sinCos2_mul_sin_eq`. -/
lemma integral_cos_sub_sum (a1 a2 a3 a4 : ℝ) (h1 : a1 ≠ 0) (h2 : a2 ≠ 0) (h3 : a3 ≠ 0)
    (h4 : a4 ≠ 0) :
    ∫ θ in (0:ℝ)..(π/2),
        ((Real.cos (a1*θ) - Real.cos (a2*θ)) + (Real.cos (a3*θ) - Real.cos (a4*θ)))
      = Real.sin (a1*π/2)/a1 - Real.sin (a2*π/2)/a2
        + Real.sin (a3*π/2)/a3 - Real.sin (a4*π/2)/a4 := by
  have i1 : IntervalIntegrable (fun θ => Real.cos (a1*θ)) volume (0:ℝ) (π/2) :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun θ => Real.cos (a2*θ)) volume (0:ℝ) (π/2) :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun θ => Real.cos (a3*θ)) volume (0:ℝ) (π/2) :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have i4 : IntervalIntegrable (fun θ => Real.cos (a4*θ)) volume (0:ℝ) (π/2) :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (i1.sub i2) (i3.sub i4),
      intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_sub i3 i4,
      integral_cos_mul a1 h1, integral_cos_mul a2 h2, integral_cos_mul a3 h3,
      integral_cos_mul a4 h4]
  ring

theorem integral_sinCos2_mul_sin_two (n : ℕ) (hn : 1 ≤ n) :
    ∫ θ in Work.Spaces.Iθ, Work.Elliptic.sinCos2 θ * Real.sin (2 * (n : ℝ) * θ)
      = (-1 : ℝ) ^ n * (4 * (n : ℝ)) / ((4 * (n : ℝ) ^ 2 - 1) * (4 * (n : ℝ) ^ 2 - 9)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  push_cast
  have hIθ : (∫ θ in Work.Spaces.Iθ, sinCos2 θ * Real.sin (2 * ((m:ℝ)+1) * θ))
      = ∫ θ in (0:ℝ)..(π/2), sinCos2 θ * Real.sin (2 * ((m:ℝ)+1) * θ) := by
    change ∫ θ in Set.Icc 0 (π/2), sinCos2 θ * Real.sin (2*((m:ℝ)+1)*θ) = _
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ π/2)]
  rw [hIθ]
  have hpoint : ∀ θ : ℝ, sinCos2 θ * Real.sin (2*((m:ℝ)+1)*θ)
      = (1/8) * ((Real.cos ((2*(m:ℝ)+1)*θ) - Real.cos ((2*(m:ℝ)+3)*θ))
          + (Real.cos ((2*(m:ℝ)-1)*θ) - Real.cos ((2*(m:ℝ)+5)*θ))) := by
    intro θ
    have h := sinCos2_mul_sin_eq ((m:ℝ)+1) θ
    have e1 : (2*((m:ℝ)+1)-1)*θ = (2*(m:ℝ)+1)*θ := by ring
    have e2 : (2*((m:ℝ)+1)+1)*θ = (2*(m:ℝ)+3)*θ := by ring
    have e3 : (2*((m:ℝ)+1)-3)*θ = (2*(m:ℝ)-1)*θ := by ring
    have e4 : (2*((m:ℝ)+1)+3)*θ = (2*(m:ℝ)+5)*θ := by ring
    rw [h, e1, e2, e3, e4]
  rw [intervalIntegral.integral_congr (fun θ _ => hpoint θ)]
  rw [intervalIntegral.integral_const_mul]
  have ha3 : (2*(m:ℝ)-1) ≠ 0 := by
    intro h
    have h2 : (2 * m : ℕ) = 1 := by
      have h' : ((2 * m : ℕ) : ℝ) = 1 := by push_cast; linarith
      exact_mod_cast h'
    omega
  rw [integral_cos_sub_sum (2*(m:ℝ)+1) (2*(m:ℝ)+3) (2*(m:ℝ)-1) (2*(m:ℝ)+5)
      (by positivity) (by positivity) ha3 (by positivity)]
  rw [sin_odd_pi_half m, sin_two_m_add_three m, sin_two_m_sub_one m, sin_two_m_add_five m]
  rw [show (-1:ℝ)^m.succ = -(-1:ℝ)^m by rw [pow_succ]; ring]
  set p : ℝ := (-1:ℝ)^m with hp
  have key : (1/8) * (p/(2*(m:ℝ)+1) - (-p)/(2*(m:ℝ)+3) + (-p)/(2*(m:ℝ)-1)
        - p/(2*(m:ℝ)+5))
      = -p * (4*((m:ℝ)+1)) / ((4*((m:ℝ)+1)^2-1)*(4*((m:ℝ)+1)^2-9)) := by
    have h5 : (4*((m:ℝ)+1)^2-1) ≠ 0 := by
      have : 4*((m:ℝ)+1)^2-1 = (2*(m:ℝ)+1)*(2*(m:ℝ)+3) := by ring
      rw [this]; exact mul_ne_zero (by positivity) (by positivity)
    have h6 : (4*((m:ℝ)+1)^2-9) ≠ 0 := by
      have : 4*((m:ℝ)+1)^2-9 = (2*(m:ℝ)-1)*(2*(m:ℝ)+5) := by ring
      rw [this]; exact mul_ne_zero ha3 (by positivity)
    field_simp
    ring
  exact key

end Work.Elliptic
