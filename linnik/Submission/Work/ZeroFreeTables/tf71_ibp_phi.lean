import Mathlib

open MeasureTheory

namespace Work.ZeroFreeTables

/-- The "profile" function P(u) appearing in the integration-by-parts identity. -/
noncomputable def Pf (θ u : ℝ) : ℝ :=
  (θ - u / 2 - Real.sin θ * Real.cos θ) * Real.cos u + Real.cos θ ^ 2 * (2 * θ - u)
    + (Real.cos θ ^ 2 + 1 / 2) * Real.sin u - 2 * Real.sin θ * Real.cos θ

/-- P'(u). -/
noncomputable def Pd (θ u : ℝ) : ℝ :=
  Real.cos θ ^ 2 * Real.cos u - (θ - u / 2 - Real.sin θ * Real.cos θ) * Real.sin u
    - Real.cos θ ^ 2

/-- P''(u). -/
noncomputable def Pdd (θ u : ℝ) : ℝ :=
  (1 / 2 - Real.cos θ ^ 2) * Real.sin u - (θ - u / 2 - Real.sin θ * Real.cos θ) * Real.cos u

/-- The target function Q(u) = P(u) + P''(u). -/
noncomputable def Qf (θ u : ℝ) : ℝ :=
  Real.cos θ ^ 2 * (2 * θ - u) + Real.sin u - 2 * Real.sin θ * Real.cos θ

/-- The antiderivative F(u) = f'(u) P(u) - f(u) P'(u), f(u) = cos(c u). -/
noncomputable def FF (θ c u : ℝ) : ℝ :=
  -(c * Real.sin (c * u)) * Pf θ u - Real.cos (c * u) * Pd θ u

/-- The integrand of the difference of the two sides. -/
noncomputable def PhiF (θ c u : ℝ) : ℝ :=
  (1 - c ^ 2) * (Real.cos (c * u) * Pf θ u) - Real.cos (c * u) * Qf θ u

lemma Qf_eq (θ u : ℝ) : Qf θ u = Pf θ u + Pdd θ u := by
  simp only [Qf, Pf, Pdd]; ring

lemma hasDerivAt_sin_mul (c u : ℝ) :
    HasDerivAt (fun u : ℝ => Real.sin (c * u)) (c * Real.cos (c * u)) u := by
  have hc := (Real.hasDerivAt_sin (c * u)).comp u ((hasDerivAt_id u).const_mul c)
  refine hc.congr_deriv ?_
  ring

lemma hasDerivAt_cos_mul (c u : ℝ) :
    HasDerivAt (fun u : ℝ => Real.cos (c * u)) (-(c * Real.sin (c * u))) u := by
  have hc := (Real.hasDerivAt_cos (c * u)).comp u ((hasDerivAt_id u).const_mul c)
  refine hc.congr_deriv ?_
  ring

lemma hasDerivAt_Pf (θ u : ℝ) : HasDerivAt (Pf θ) (Pd θ u) u := by
  unfold Pf Pd
  have hlin : HasDerivAt (fun u : ℝ => θ - u / 2 - Real.sin θ * Real.cos θ) (-(1 / 2)) u := by
    have h : HasDerivAt (fun u : ℝ => θ - u / 2) (-(1 / 2)) u :=
      ((hasDerivAt_id u).div_const 2).const_sub θ
    exact h.sub_const (Real.sin θ * Real.cos θ)
  have h1 : HasDerivAt (fun u : ℝ => (θ - u / 2 - Real.sin θ * Real.cos θ) * Real.cos u)
      ((-(1 / 2)) * Real.cos u + (θ - u / 2 - Real.sin θ * Real.cos θ) * (-Real.sin u)) u :=
    hlin.mul (Real.hasDerivAt_cos u)
  have h2 : HasDerivAt (fun u : ℝ => Real.cos θ ^ 2 * (2 * θ - u)) (Real.cos θ ^ 2 * (-1)) u := by
    have h : HasDerivAt (fun u : ℝ => 2 * θ - u) (-1) u :=
      (hasDerivAt_id u).const_sub (2 * θ)
    exact h.const_mul (Real.cos θ ^ 2)
  have h3 : HasDerivAt (fun u : ℝ => (Real.cos θ ^ 2 + 1 / 2) * Real.sin u)
      ((Real.cos θ ^ 2 + 1 / 2) * Real.cos u) u :=
    (Real.hasDerivAt_sin u).const_mul (Real.cos θ ^ 2 + 1 / 2)
  have h4 : HasDerivAt (fun u : ℝ => 2 * Real.sin θ * Real.cos θ) 0 u :=
    hasDerivAt_const u (2 * Real.sin θ * Real.cos θ)
  have hsum := ((h1.add h2).add h3).sub h4
  refine hsum.congr_deriv ?_
  ring

lemma hasDerivAt_Pd (θ u : ℝ) : HasDerivAt (Pd θ) (Pdd θ u) u := by
  unfold Pd Pdd
  have hlin : HasDerivAt (fun u : ℝ => θ - u / 2 - Real.sin θ * Real.cos θ) (-(1 / 2)) u := by
    have h : HasDerivAt (fun u : ℝ => θ - u / 2) (-(1 / 2)) u :=
      ((hasDerivAt_id u).div_const 2).const_sub θ
    exact h.sub_const (Real.sin θ * Real.cos θ)
  have hsin : HasDerivAt (fun u : ℝ => (θ - u / 2 - Real.sin θ * Real.cos θ) * Real.sin u)
      ((-(1 / 2)) * Real.sin u + (θ - u / 2 - Real.sin θ * Real.cos θ) * Real.cos u) u :=
    hlin.mul (Real.hasDerivAt_sin u)
  have hcos : HasDerivAt (fun u : ℝ => Real.cos θ ^ 2 * Real.cos u)
      (Real.cos θ ^ 2 * (-Real.sin u)) u :=
    (Real.hasDerivAt_cos u).const_mul (Real.cos θ ^ 2)
  have hcst : HasDerivAt (fun u : ℝ => Real.cos θ ^ 2) 0 u := hasDerivAt_const u (Real.cos θ ^ 2)
  have hsum := (hcos.sub hsin).sub hcst
  refine hsum.congr_deriv ?_
  ring

lemma hasDerivAt_FF (θ c u : ℝ) : HasDerivAt (FF θ c) (PhiF θ c u) u := by
  unfold FF PhiF
  have hsin := hasDerivAt_sin_mul c u
  have hcos := hasDerivAt_cos_mul c u
  have hPf := hasDerivAt_Pf θ u
  have hPd := hasDerivAt_Pd θ u
  have hA : HasDerivAt (fun u : ℝ => -(c * Real.sin (c * u))) (-(c * (c * Real.cos (c * u)))) u :=
    (hsin.const_mul c).neg
  have hA' : HasDerivAt (fun u : ℝ => -(c * Real.sin (c * u)) * Pf θ u)
      ((-(c * (c * Real.cos (c * u)))) * Pf θ u + (-(c * Real.sin (c * u))) * Pd θ u) u :=
    hA.mul hPf
  have hB' : HasDerivAt (fun u : ℝ => Real.cos (c * u) * Pd θ u)
      ((-(c * Real.sin (c * u))) * Pd θ u + Real.cos (c * u) * Pdd θ u) u :=
    hcos.mul hPd
  have hsum := hA'.sub hB'
  refine hsum.congr_deriv ?_
  rw [Qf_eq]; ring

lemma Pf_two (θ : ℝ) : Pf θ (2 * θ) = 0 := by
  unfold Pf
  rw [Real.sin_two_mul, Real.cos_two_mul]
  ring_nf

lemma Pd_two (θ : ℝ) : Pd θ (2 * θ) = 0 := by
  unfold Pd
  rw [Real.sin_two_mul, Real.cos_two_mul]
  have h := Real.sin_sq_add_cos_sq θ
  ring_nf
  nlinarith [h]

lemma Pd_zero (θ : ℝ) : Pd θ 0 = 0 := by
  unfold Pd
  simp

lemma FF_two (θ c : ℝ) : FF θ c (2 * θ) = 0 := by
  unfold FF
  rw [Pf_two, Pd_two]
  ring

lemma FF_zero (θ c : ℝ) : FF θ c 0 = 0 := by
  unfold FF
  rw [Pd_zero]
  simp

theorem tf71_ibp_phi (θ c : ℝ) :
    (1 - c^2) * (∫ u in (0:ℝ)..(2*θ), Real.cos (c*u) *
        ((θ - u/2 - Real.sin θ * Real.cos θ) * Real.cos u + Real.cos θ ^ 2 * (2*θ - u)
          + (Real.cos θ ^ 2 + 1/2) * Real.sin u - 2 * Real.sin θ * Real.cos θ))
      = ∫ u in (0:ℝ)..(2*θ), Real.cos (c*u) *
          (Real.cos θ ^ 2 * (2*θ - u) + Real.sin u - 2 * Real.sin θ * Real.cos θ) := by
  show (1 - c^2) * (∫ u in (0:ℝ)..(2*θ), Real.cos (c*u) * Pf θ u)
      = ∫ u in (0:ℝ)..(2*θ), Real.cos (c*u) * Qf θ u
  have hPhi : ∫ u in (0:ℝ)..(2*θ), PhiF θ c u = 0 := by
    have hderiv : ∀ x ∈ Set.uIcc (0:ℝ) (2*θ), HasDerivAt (FF θ c) (PhiF θ c x) x :=
      fun x _ => hasDerivAt_FF θ c x
    have hcont : Continuous (PhiF θ c) := by unfold PhiF Pf Qf; fun_prop
    have hint : IntervalIntegrable (PhiF θ c) volume (0:ℝ) (2*θ) :=
      hcont.intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    rw [FF_two, FF_zero]
    ring
  have hlin : ∫ u in (0:ℝ)..(2*θ), PhiF θ c u
      = (1 - c^2) * (∫ u in (0:ℝ)..(2*θ), Real.cos (c*u) * Pf θ u)
        - ∫ u in (0:ℝ)..(2*θ), Real.cos (c*u) * Qf θ u := by
    have hc1 : Continuous (fun u : ℝ => (1 - c^2) * (Real.cos (c*u) * Pf θ u)) := by
      unfold Pf; fun_prop
    have hc2 : Continuous (fun u : ℝ => Real.cos (c*u) * Qf θ u) := by
      unfold Qf; fun_prop
    have h1 : IntervalIntegrable (fun u : ℝ => (1 - c^2) * (Real.cos (c*u) * Pf θ u))
        volume (0:ℝ) (2*θ) := hc1.intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun u : ℝ => Real.cos (c*u) * Qf θ u)
        volume (0:ℝ) (2*θ) := hc2.intervalIntegrable _ _
    have hfun : PhiF θ c
        = (fun u : ℝ => (1 - c^2) * (Real.cos (c*u) * Pf θ u) - Real.cos (c*u) * Qf θ u) := by
      ext u; rfl
    rw [hfun, intervalIntegral.integral_sub h1 h2, intervalIntegral.integral_const_mul]
  rw [hlin] at hPhi
  linarith

end Work.ZeroFreeTables
