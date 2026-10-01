import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Commons.Analysis.Integral.extremal_cosine_integral

open Real
open MeasureTheory

namespace Commons.Analysis.Integral

lemma hasDerivAt_exp_neg_mul (a x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-(a * y))) (-(a * Real.exp (-(a * x)))) x := by
  have h1 : HasDerivAt (fun y : ℝ => -(a * y)) (-a) x := by
    simpa only [neg_mul] using (hasDerivAt_const_mul (x := x) (-a))
  have h := (Real.hasDerivAt_exp (-(a * x))).comp x h1
  have hval : Real.exp (-(a*x)) * -a = -(a * Real.exp (-(a*x))) := by ring
  rw [hval] at h
  simpa [Function.comp_def] using h

theorem extremal_cosine_reflected_integral {θ lam : ℝ} (hθ0 : Real.pi / 2 < θ) (hθ1 : θ < Real.pi) (hlam : 0 < lam) :
    let ζ : ℝ := -(lam * Real.tan θ)
    let γ : ℝ := θ / ζ
    let f : ℝ → ℝ := fun x => lam * (1 + Real.tan θ ^ 2) *
      (lam * (1 + Real.tan θ ^ 2) * (γ - x / 2) * Real.cos (ζ * x) + lam * (2 * γ - x)
        - Real.sin (2 * θ - ζ * x) / Real.sin (2 * θ)
        + 2 * (1 + Real.sin (θ - ζ * x) / Real.sin θ))
    f 0 = lam * (1 + Real.tan θ ^ 2) * (3 - θ * Real.tan θ - 3 * θ * (Real.cos θ / Real.sin θ)) ∧
    (∫ x in (0:ℝ)..(2 * γ), f x) = 2 * (1 + Real.tan θ ^ 2) * (1 - θ * (Real.cos θ / Real.sin θ)) ^ 2 ∧
    (∫ x in (0:ℝ)..(2 * γ), Real.exp (-(lam * x)) * f x)
      = 2 * Real.tan θ ^ 2 + 3 - 3 * θ * Real.tan θ - 3 * θ * (Real.cos θ / Real.sin θ) := by
  dsimp only
  set ζ : ℝ := -(lam * Real.tan θ) with hζ
  set γ : ℝ := θ / ζ with hγ
  set A : ℝ := lam * (1 + Real.tan θ ^ 2) with hA
  have hθ0' : 0 < θ := by linarith [Real.pi_pos]
  have hcos_neg : Real.cos θ < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt hθ0 (by linarith [Real.pi_pos])
  have hsin_pos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0' hθ1
  have hsin_ne : Real.sin θ ≠ 0 := ne_of_gt hsin_pos
  have hcos_ne : Real.cos θ ≠ 0 := ne_of_lt hcos_neg
  have htan_neg : Real.tan θ < 0 := by
    rw [Real.tan_eq_sin_div_cos]; exact div_neg_of_pos_of_neg hsin_pos hcos_neg
  have htan_ne : Real.tan θ ≠ 0 := ne_of_lt htan_neg
  have hζ_ne : ζ ≠ 0 := by
    rw [hζ]; exact neg_ne_zero.mpr (mul_ne_zero (ne_of_gt hlam) htan_ne)
  have hsin2θ_neg : Real.sin (2 * θ) < 0 := by
    rw [Real.sin_two_mul]
    exact mul_neg_of_pos_of_neg (by linarith [hsin_pos]) hcos_neg
  have hsin2θ_ne : Real.sin (2 * θ) ≠ 0 := ne_of_lt hsin2θ_neg
  have hA_pos : 0 < A := by rw [hA]; positivity
  have hζγ : ζ * γ = θ := by rw [hγ]; field_simp
  refine ⟨?_, ?_, ?_⟩
  · have h1 : A * γ + lam * (2 * γ) - Real.sin (2 * θ) / Real.sin (2 * θ)
        + 2 * (1 + Real.sin θ / Real.sin θ) = γ * (A + 2 * lam) + 3 := by
      rw [div_self hsin2θ_ne, div_self hsin_ne]; ring
    have h2 : γ * (A + 2 * lam) = -θ * Real.tan θ - 3 * θ * (Real.cos θ / Real.sin θ) := by
      rw [hA, hγ, hζ, Real.tan_eq_sin_div_cos]
      field_simp
      ring
    simp only [mul_zero, zero_div, Real.cos_zero, mul_one, sub_zero]
    rw [h1, h2]
    ring
  · let GH : ℝ → ℝ := fun x => (A * ((γ - x/2)*Real.sin (ζ*x)/ζ - Real.cos (ζ*x)/(2*ζ^2)) + lam*(2*γ*x - x^2/2)) - Real.cos (2*θ - ζ*x)/(ζ*Real.sin (2*θ)) + 2*x + 2*Real.cos (θ - ζ*x)/(ζ*Real.sin θ)
    let F : ℝ → ℝ := fun x => A * GH x
    have hInner : ∀ x, HasDerivAt (fun y : ℝ => (γ - y/2)*Real.sin (ζ*y)/ζ - Real.cos (ζ*y)/(2*ζ^2))
        ((γ - x/2)*Real.cos (ζ*x)) x := by
      intro x
      have hlin : HasDerivAt (fun y : ℝ => γ - y/2) (-1/2) x := by
        have h := (hasDerivAt_id x).div_const 2
        have key : HasDerivAt (fun y : ℝ => γ - y/2) (0 - 1/2) x :=
          (hasDerivAt_const (x := x) γ).sub h
        have hval : (0:ℝ) - 1/2 = -1/2 := by norm_num
        rw [hval] at key
        exact key
      have ha : HasDerivAt (fun y : ℝ => (γ - y/2)*Real.sin (ζ*y)/ζ)
          (((-1/2)*Real.sin (ζ*x) + (γ - x/2)*(ζ*Real.cos (ζ*x)))/ζ) x :=
        (hlin.mul (hasDerivAt_sin_mul ζ x)).div_const ζ
      have hb : HasDerivAt (fun y : ℝ => Real.cos (ζ*y)/(2*ζ^2))
          ((-(ζ*Real.sin (ζ*x)))/(2*ζ^2)) x :=
        (hasDerivAt_cos_mul ζ x).div_const (2*ζ^2)
      have h := ha.sub hb
      have hval : (((-1/2)*Real.sin (ζ*x) + (γ - x/2)*(ζ*Real.cos (ζ*x)))/ζ
          - (-(ζ*Real.sin (ζ*x)))/(2*ζ^2)) = (γ - x/2)*Real.cos (ζ*x) := by
        field_simp
        ring
      rw [hval] at h
      exact h
    have hFderiv : ∀ x, HasDerivAt F (A * (A * (γ - x / 2) * Real.cos (ζ * x) + lam * (2 * γ - x)
        - Real.sin (2 * θ - ζ * x) / Real.sin (2 * θ)
        + 2 * (1 + Real.sin (θ - ζ * x) / Real.sin θ))) x := by
      intro x
      have h1 : HasDerivAt (fun y : ℝ => A * ((γ - y/2)*Real.sin (ζ*y)/ζ - Real.cos (ζ*y)/(2*ζ^2)))
          (A*((γ - x/2)*Real.cos (ζ*x))) x := (hInner x).const_mul A
      have h2 : HasDerivAt (fun y : ℝ => lam*(2*γ*y - y^2/2)) (lam*(2*γ - x)) x := by
        have h := ((hasDerivAt_id x).const_mul (2*γ)).sub (((hasDerivAt_id x).pow 2).div_const 2)
        have key : HasDerivAt (fun y : ℝ => (2*γ)*y - y^2/2) ((2*γ)*1 - (2*x^(2-1)*1)/2) x := h
        have hval : (2*γ)*1 - (2*x^(2-1)*1)/2 = 2*γ - x := by ring
        rw [hval] at key
        exact key.const_mul lam
      have h3 : HasDerivAt (fun y : ℝ => -(Real.cos (2*θ - ζ*y)/(ζ*Real.sin (2*θ))))
          (-(Real.sin (2*θ - ζ*x)/Real.sin (2*θ))) x := by
        have h := (hasDerivAt_cos_sub_mul ζ (2*θ) x).div_const (ζ*Real.sin (2*θ))
        have hval : (ζ*Real.sin (2*θ - ζ*x))/(ζ*Real.sin (2*θ)) = Real.sin (2*θ - ζ*x)/Real.sin (2*θ) := by
          field_simp
        rw [hval] at h
        exact h.neg
      have h4 : HasDerivAt (fun y : ℝ => 2*y) (2:ℝ) x := by
        simpa using (hasDerivAt_id x).const_mul (2:ℝ)
      have h5 : HasDerivAt (fun y : ℝ => 2*Real.cos (θ - ζ*y)/(ζ*Real.sin θ))
          (2*Real.sin (θ - ζ*x)/Real.sin θ) x := by
        have h := ((hasDerivAt_cos_sub_mul ζ θ x).const_mul (2:ℝ)).div_const (ζ*Real.sin θ)
        have hval : 2*(ζ*Real.sin (θ - ζ*x))/(ζ*Real.sin θ) = 2*Real.sin (θ - ζ*x)/Real.sin θ := by
          field_simp
        rw [hval] at h
        exact h
      have hGH := (((h1.add h2).add h3).add h4).add h5
      exact (hGH.const_mul A).congr_deriv (by ring)
    have hint : IntervalIntegrable (fun x : ℝ => A * (A * (γ - x / 2) * Real.cos (ζ * x) + lam * (2 * γ - x)
        - Real.sin (2 * θ - ζ * x) / Real.sin (2 * θ)
        + 2 * (1 + Real.sin (θ - ζ * x) / Real.sin θ))) volume 0 (2*γ) := by
      apply Continuous.intervalIntegrable
      fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := F)
        (f' := fun x => A * (A * (γ - x / 2) * Real.cos (ζ * x) + lam * (2 * γ - x)
          - Real.sin (2 * θ - ζ * x) / Real.sin (2 * θ)
          + 2 * (1 + Real.sin (θ - ζ * x) / Real.sin θ)))
        (fun x _ => hFderiv x) hint]
    simp only [F, GH]
    have hζ2γ : ζ * (2*γ) = 2*θ := by rw [hγ]; field_simp
    have hcos2 : (θ:ℝ) - 2*θ = -θ := by ring
    rw [hζ2γ, hcos2]
    simp only [sub_self, mul_zero, zero_div, Real.sin_zero, Real.cos_zero, Real.cos_neg, pow_two,
      sub_zero, zero_sub, add_zero]
    rw [hA, hγ, hζ]
    rw [Real.cos_two_mul, Real.sin_two_mul, Real.tan_eq_sin_div_cos]
    field_simp
    ring_nf
    field_simp
    ring_nf
    nlinarith [Real.sin_sq_add_cos_sq θ]
  · set p : ℝ := 1/2 with hp
    set q : ℝ := (2*θ*(Real.cos θ/Real.sin θ) - Real.cos (2*θ) - 3)/(2*lam) with hq
    set rr : ℝ := Real.tan θ/2 with hrr
    set s : ℝ := (θ - Real.sin θ*Real.cos θ + (3/2)*(Real.cos θ/Real.sin θ))/lam with hs
    set be : ℝ := -2*γ - 1/lam with hbe
    set R : ℝ → ℝ := fun x => ((p*x+q)*Real.cos (ζ*x) + (rr*x+s)*Real.sin (ζ*x)) + (x+be) with hR
    set Rd : ℝ → ℝ := fun x => ((p*Real.cos (ζ*x) + (p*x+q)*(-(ζ*Real.sin (ζ*x))))
        + (rr*Real.sin (ζ*x) + (rr*x+s)*(ζ*Real.cos (ζ*x)))) + 1 with hRd
    set g : ℝ → ℝ := fun x => A*(γ-x/2)*Real.cos (ζ*x) + lam*(2*γ-x)
        - Real.sin (2*θ-ζ*x)/Real.sin (2*θ) + 2 + 2*Real.sin (θ-ζ*x)/Real.sin θ with hg
    set G : ℝ → ℝ := fun x => A*(Real.exp (-(lam*x)) * R x) with hG
    have ha : ζ*rr - lam*p = -A/2 := by rw [hp, hrr, hζ, hA]; ring
    have hf : 1 - lam*be = 2*lam*γ + 2 := by rw [hbe]; field_simp; ring
    have hb : p + ζ*s - lam*q = A*γ + 1 := by
      rw [hq, hp, hs, hA, hγ, hζ, Real.tan_eq_sin_div_cos, Real.cos_two_mul]
      field_simp
      ring_nf
      linear_combination (norm := ring_nf) (2*Real.cos θ * Real.sin θ) * (Real.sin_sq_add_cos_sq θ)
    have hc : -ζ*p - lam*rr = 0 := by rw [hrr, hp, hζ]; ring
    have hd : rr - ζ*q - lam*s = Real.cos (2*θ)/Real.sin (2*θ) - 2*Real.cos θ/Real.sin θ := by
      rw [hs, hrr, hq, hζ, Real.tan_eq_sin_div_cos, Real.sin_two_mul, Real.cos_two_mul]
      field_simp
      ring_nf
      nlinarith [Real.sin_sq_add_cos_sq θ]
    have hRderiv : ∀ x, HasDerivAt R (Rd x) x := by
      intro x
      have hp1 : HasDerivAt (fun y : ℝ => p*y + q) p x := by
        simpa using (hasDerivAt_const_mul (x:=x) p).add_const q
      have hp2 : HasDerivAt (fun y : ℝ => rr*y + s) rr x := by
        simpa using (hasDerivAt_const_mul (x:=x) rr).add_const s
      have hlin : HasDerivAt (fun y : ℝ => y + be) 1 x := by
        simpa using (hasDerivAt_id x).add_const be
      have hpr := (hp1.mul (hasDerivAt_cos_mul ζ x)).add (hp2.mul (hasDerivAt_sin_mul ζ x))
      have hsum := hpr.add hlin
      rw [hR, hRd]
      exact hsum
    have expand2 : ∀ x, Rd x - lam * R x = ((ζ*rr - lam*p)*x + (p + ζ*s - lam*q))*Real.cos (ζ*x)
        + ((-ζ*p - lam*rr)*x + (rr - ζ*q - lam*s))*Real.sin (ζ*x) + (-lam)*x + (1 - lam*be) := by
      intro x; rw [hR, hRd]; ring
    have expandg : ∀ x, g x = ((-A/2)*x + (A*γ + 1))*Real.cos (ζ*x)
        + (Real.cos (2*θ)/Real.sin (2*θ) - 2*Real.cos θ/Real.sin θ)*Real.sin (ζ*x) + (-lam)*x + (2*lam*γ + 2) := by
      intro x; rw [hg]; simp only [Real.sin_sub]; field_simp; ring
    have hode : ∀ x, Rd x - lam * R x = g x := by
      intro x
      rw [expand2 x, expandg x, ha, hb, hc, hd, hf]
      ring
    have hGderiv : ∀ x, HasDerivAt G (Real.exp (-(lam*x)) * (A * (A * (γ - x / 2) * Real.cos (ζ * x) + lam * (2 * γ - x)
        - Real.sin (2 * θ - ζ * x) / Real.sin (2 * θ)
        + 2 * (1 + Real.sin (θ - ζ * x) / Real.sin θ)))) x := by
      intro x
      have hprod := (hasDerivAt_exp_neg_mul lam x).mul (hRderiv x)
      have hAc := hprod.const_mul A
      refine hAc.congr_deriv ?_
      have h1 : -(lam*Real.exp (-(lam*x)))*R x + Real.exp (-(lam*x))*Rd x
          = Real.exp (-(lam*x)) * (Rd x - lam*R x) := by ring
      rw [h1, hode x, hg]
      ring
    have hintG : IntervalIntegrable (fun x => Real.exp (-(lam*x)) * (A * (A * (γ - x / 2) * Real.cos (ζ * x) + lam * (2 * γ - x)
        - Real.sin (2 * θ - ζ * x) / Real.sin (2 * θ) + 2 * (1 + Real.sin (θ - ζ * x) / Real.sin θ)))) volume 0 (2*γ) := by
      apply Continuous.intervalIntegrable; fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := G)
        (f' := fun x => Real.exp (-(lam*x)) * (A * (A * (γ - x / 2) * Real.cos (ζ * x) + lam * (2 * γ - x)
          - Real.sin (2 * θ - ζ * x) / Real.sin (2 * θ) + 2 * (1 + Real.sin (θ - ζ * x) / Real.sin θ))))
        (fun x _ => hGderiv x) hintG]
    simp only [hG]
    have hζ2γ : ζ * (2*γ) = 2*θ := by rw [hγ]; field_simp
    have hR2γ : R (2*γ) = 0 := by
      simp only [hR]
      rw [hζ2γ, hp, hq, hrr, hs, hbe, hγ, hζ]
      rw [Real.cos_two_mul, Real.sin_two_mul, Real.tan_eq_sin_div_cos]
      field_simp
      ring_nf
      linear_combination (norm := ring_nf) (-4*Real.cos θ^2 * Real.sin θ) * (Real.sin_sq_add_cos_sq θ)
    have hR0 : R 0 = q + be := by simp only [hR, mul_zero, Real.cos_zero, Real.sin_zero]; ring
    rw [hR2γ, hR0]
    simp only [mul_zero, neg_zero, Real.exp_zero, one_mul, zero_sub]
    have hend : -(A*(q+be)) = 2*Real.tan θ ^ 2 + 3 - 3 * θ * Real.tan θ - 3 * θ * (Real.cos θ / Real.sin θ) := by
      rw [hA, hq, hbe, hγ, hζ, Real.tan_eq_sin_div_cos, Real.cos_two_mul]
      field_simp
      ring_nf
      linear_combination (norm := ring_nf) (2*Real.cos θ^2 * Real.sin θ) * (Real.sin_sq_add_cos_sq θ)
    rw [hend]

end Commons.Analysis.Integral
