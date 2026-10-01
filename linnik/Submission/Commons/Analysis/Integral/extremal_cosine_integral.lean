import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Real
open MeasureTheory

namespace Commons.Analysis.Integral

lemma hasDerivAt_cos_mul (a x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.cos (a * y)) (-(a * Real.sin (a * x))) x := by
  simpa [Function.comp_def, mul_comm] using
    (Real.hasDerivAt_cos (a * x)).comp x (hasDerivAt_const_mul (x := x) a)

lemma hasDerivAt_sin_mul (a x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sin (a * y)) (a * Real.cos (a * x)) x := by
  simpa [Function.comp_def, mul_comm] using
    (Real.hasDerivAt_sin (a * x)).comp x (hasDerivAt_const_mul (x := x) a)

lemma hasDerivAt_exp_mul (a x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (a * y)) (a * Real.exp (a * x)) x := by
  simpa [Function.comp_def, mul_comm] using
    (Real.hasDerivAt_exp (a * x)).comp x (hasDerivAt_const_mul (x := x) a)

lemma hasDerivAt_cos_sub_mul (a c x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.cos (c - a * y)) (a * Real.sin (c - a * x)) x := by
  have h1 : HasDerivAt (fun y : ℝ => c - a * y) (-a) x := by
    simpa using (hasDerivAt_const_mul (x := x) a).const_sub c
  simpa [Function.comp_def, mul_comm] using
    (Real.hasDerivAt_cos (c - a * x)).comp x h1

theorem extremal_cosine_integral {θ lam : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    let ζ : ℝ := lam * Real.tan θ
    let γ : ℝ := θ / ζ
    let f : ℝ → ℝ := fun x => lam * (1 + Real.tan θ ^ 2) *
      (lam * (1 + Real.tan θ ^ 2) * (γ - x / 2) * Real.cos (ζ * x) + lam * (2 * γ - x)
        + Real.sin (2 * θ - ζ * x) / Real.sin (2 * θ)
        - 2 * (1 + Real.sin (θ - ζ * x) / Real.sin θ))
    f 0 = lam * (1 + Real.tan θ ^ 2) * (θ * Real.tan θ + 3 * θ * (Real.cos θ / Real.sin θ) - 3) ∧
    (∫ x in (0:ℝ)..(2 * γ), f x) = 2 * (1 + Real.tan θ ^ 2) * (1 - θ * (Real.cos θ / Real.sin θ)) ^ 2 ∧
    (∫ x in (0:ℝ)..(2 * γ), Real.exp (lam * x) * f x)
      = 2 * Real.tan θ ^ 2 + 3 - 3 * θ * Real.tan θ - 3 * θ * (Real.cos θ / Real.sin θ) := by
  dsimp only
  set ζ : ℝ := lam * Real.tan θ with hζ
  set γ : ℝ := θ / ζ with hγ
  set A : ℝ := lam * (1 + Real.tan θ ^ 2) with hA
  have hcos_pos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩
  have hsin_pos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  have hsin_ne : Real.sin θ ≠ 0 := ne_of_gt hsin_pos
  have hcos_ne : Real.cos θ ≠ 0 := ne_of_gt hcos_pos
  have htan_pos : 0 < Real.tan θ := Real.tan_pos_of_pos_of_lt_pi_div_two hθ0 hθ1
  have htan_ne : Real.tan θ ≠ 0 := ne_of_gt htan_pos
  have hζ_ne : ζ ≠ 0 := by rw [hζ]; exact mul_ne_zero (ne_of_gt hlam) htan_ne
  have hsin2θ_pos : 0 < Real.sin (2 * θ) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hsin2θ_ne : Real.sin (2 * θ) ≠ 0 := ne_of_gt hsin2θ_pos
  have hA_pos : 0 < A := by rw [hA]; positivity
  have hζγ : ζ * γ = θ := by rw [hγ]; field_simp
  refine ⟨?_, ?_, ?_⟩
  · have h1 : A * γ + lam * (2 * γ) + Real.sin (2 * θ) / Real.sin (2 * θ)
        - 2 * (1 + Real.sin θ / Real.sin θ) = γ * (A + 2 * lam) - 3 := by
      rw [div_self hsin2θ_ne, div_self hsin_ne]; ring
    have h2 : γ * (A + 2 * lam) = θ * Real.tan θ + 3 * θ * (Real.cos θ / Real.sin θ) := by
      rw [hA, hγ, hζ, Real.tan_eq_sin_div_cos]
      field_simp
      ring
    simp only [mul_zero, zero_div, Real.cos_zero, mul_one, sub_zero]
    rw [h1, h2]
  ·
    let GH : ℝ → ℝ := fun x => ((A * ((γ - x/2)*Real.sin (ζ*x)/ζ - Real.cos (ζ*x)/(2*ζ^2)) + lam*(2*γ*x - x^2/2)) + Real.cos (2*θ - ζ*x)/(ζ*Real.sin (2*θ))) - 2*x - 2*Real.cos (θ - ζ*x)/(ζ*Real.sin θ)
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
        + Real.sin (2 * θ - ζ * x) / Real.sin (2 * θ)
        - 2 * (1 + Real.sin (θ - ζ * x) / Real.sin θ))) x := by
      intro x
      have h1 : HasDerivAt (fun y : ℝ => A * ((γ - y/2)*Real.sin (ζ*y)/ζ - Real.cos (ζ*y)/(2*ζ^2)))
          (A*((γ - x/2)*Real.cos (ζ*x))) x := (hInner x).const_mul A
      have h2 : HasDerivAt (fun y : ℝ => lam*(2*γ*y - y^2/2)) (lam*(2*γ - x)) x := by
        have h := ((hasDerivAt_id x).const_mul (2*γ)).sub (((hasDerivAt_id x).pow 2).div_const 2)
        have key : HasDerivAt (fun y : ℝ => (2*γ)*y - y^2/2) ((2*γ)*1 - (2*x^(2-1)*1)/2) x := h
        have hval : (2*γ)*1 - (2*x^(2-1)*1)/2 = 2*γ - x := by ring
        rw [hval] at key
        exact key.const_mul lam
      have h3 : HasDerivAt (fun y : ℝ => Real.cos (2*θ - ζ*y)/(ζ*Real.sin (2*θ)))
          (Real.sin (2*θ - ζ*x)/Real.sin (2*θ)) x := by
        have h := (hasDerivAt_cos_sub_mul ζ (2*θ) x).div_const (ζ*Real.sin (2*θ))
        have hval : (ζ*Real.sin (2*θ - ζ*x))/(ζ*Real.sin (2*θ)) = Real.sin (2*θ - ζ*x)/Real.sin (2*θ) := by
          field_simp
        rw [hval] at h
        exact h
      have h4 : HasDerivAt (fun y : ℝ => 2*y) (2:ℝ) x := by
        simpa using (hasDerivAt_id x).const_mul (2:ℝ)
      have h5 : HasDerivAt (fun y : ℝ => 2*Real.cos (θ - ζ*y)/(ζ*Real.sin θ))
          (2*Real.sin (θ - ζ*x)/Real.sin θ) x := by
        have h := ((hasDerivAt_cos_sub_mul ζ θ x).const_mul (2:ℝ)).div_const (ζ*Real.sin θ)
        have hval : 2*(ζ*Real.sin (θ - ζ*x))/(ζ*Real.sin θ) = 2*Real.sin (θ - ζ*x)/Real.sin θ := by
          field_simp
        rw [hval] at h
        exact h
      have hGH := (((h1.add h2).add h3).sub h4).sub h5
      have hF := hGH.const_mul A
      have hval : A * ((((A*((γ - x/2)*Real.cos (ζ*x)) + lam*(2*γ - x)) + Real.sin (2*θ - ζ*x)/Real.sin (2*θ)) - 2)
          - 2*Real.sin (θ - ζ*x)/Real.sin θ)
          = A * (A * (γ - x / 2) * Real.cos (ζ * x) + lam * (2 * γ - x)
            + Real.sin (2 * θ - ζ * x) / Real.sin (2 * θ)
            - 2 * (1 + Real.sin (θ - ζ * x) / Real.sin θ)) := by ring
      rw [hval] at hF
      exact hF
    have hint : IntervalIntegrable (fun x : ℝ => A * (A * (γ - x / 2) * Real.cos (ζ * x) + lam * (2 * γ - x)
        + Real.sin (2 * θ - ζ * x) / Real.sin (2 * θ)
        - 2 * (1 + Real.sin (θ - ζ * x) / Real.sin θ))) volume 0 (2*γ) := by
      apply Continuous.intervalIntegrable
      fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := F)
        (f' := fun x => A * (A * (γ - x / 2) * Real.cos (ζ * x) + lam * (2 * γ - x)
          + Real.sin (2 * θ - ζ * x) / Real.sin (2 * θ)
          - 2 * (1 + Real.sin (θ - ζ * x) / Real.sin θ)))
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
  ·
    set p : ℝ := -1/2 with hp
    set q : ℝ := (2*θ*(Real.cos θ/Real.sin θ) - Real.cos (2*θ) - 3)/(2*lam) with hq
    set rr : ℝ := -Real.tan θ/2 with hrr
    set s : ℝ := (θ - Real.sin θ*Real.cos θ + (3/2)*(Real.cos θ/Real.sin θ))/lam with hs
    set al : ℝ := -1 with hal
    set be : ℝ := 2*γ - 1/lam with hbe
    set R : ℝ → ℝ := fun x => ((p*x+q)*Real.cos (ζ*x) + (rr*x+s)*Real.sin (ζ*x)) + (al*x+be) with hR
    set Rd : ℝ → ℝ := fun x => ((p*Real.cos (ζ*x) + (p*x+q)*(-(ζ*Real.sin (ζ*x))))
        + (rr*Real.sin (ζ*x) + (rr*x+s)*(ζ*Real.cos (ζ*x)))) + al with hRd
    set g : ℝ → ℝ := fun x => A*(γ-x/2)*Real.cos (ζ*x) + lam*(2*γ-x)
        + Real.sin (2*θ-ζ*x)/Real.sin (2*θ) - 2 - 2*Real.sin (θ-ζ*x)/Real.sin θ with hg
    set G : ℝ → ℝ := fun x => A*(Real.exp (lam*x) * R x) with hG
    have ha : lam*p + ζ*rr = -A/2 := by rw [hp, hrr, hζ, hA]; ring
    have he : lam*al = -lam := by rw [hal]; ring
    have hf : lam*be + al = 2*lam*γ - 2 := by rw [hbe, hal]; field_simp; ring
    have hb : lam*q + p + ζ*s = A*γ - 1 := by
      rw [hq, hp, hal, hs, hA, hγ, hζ, Real.tan_eq_sin_div_cos, Real.cos_two_mul]
      field_simp
      ring_nf
      linear_combination (norm := ring_nf) (-2*Real.cos θ * Real.sin θ) * (Real.sin_sq_add_cos_sq θ)
    have hc : lam*rr - ζ*p = 0 := by rw [hrr, hp, hζ]; ring
    have hd : lam*s + rr - ζ*q = 2*Real.cos θ/Real.sin θ - Real.cos (2*θ)/Real.sin (2*θ) := by
      rw [hs, hrr, hq, hζ, Real.tan_eq_sin_div_cos, Real.sin_two_mul, Real.cos_two_mul]
      field_simp
      ring_nf
      linear_combination (norm := ring_nf) (Real.sin_sq_add_cos_sq θ)
    have hRderiv : ∀ x, HasDerivAt R (Rd x) x := by
      intro x
      have hp1 : HasDerivAt (fun y : ℝ => p*y + q) p x := by
        simpa using (hasDerivAt_const_mul (x:=x) p).add_const q
      have hp2 : HasDerivAt (fun y : ℝ => rr*y + s) rr x := by
        simpa using (hasDerivAt_const_mul (x:=x) rr).add_const s
      have hlin : HasDerivAt (fun y : ℝ => al*y + be) al x := by
        simpa using (hasDerivAt_const_mul (x:=x) al).add_const be
      have hpr := (hp1.mul (hasDerivAt_cos_mul ζ x)).add (hp2.mul (hasDerivAt_sin_mul ζ x))
      have hsum := hpr.add hlin
      rw [hR, hRd]
      exact hsum
    have expand2 : ∀ x, lam * R x + Rd x = ((lam*p + ζ*rr)*x + (lam*q + p + ζ*s))*Real.cos (ζ*x)
        + ((lam*rr - ζ*p)*x + (lam*s + rr - ζ*q))*Real.sin (ζ*x) + (lam*al)*x + (lam*be + al) := by
      intro x; rw [hR, hRd]; ring
    have expandg : ∀ x, g x = ((-A/2)*x + (A*γ - 1))*Real.cos (ζ*x)
        + (2*Real.cos θ/Real.sin θ - Real.cos (2*θ)/Real.sin (2*θ))*Real.sin (ζ*x) + (-lam)*x + (2*lam*γ - 2) := by
      intro x; rw [hg]; simp only [Real.sin_sub]; field_simp; ring
    have hode : ∀ x, lam * R x + Rd x = g x := by
      intro x
      rw [expand2 x, expandg x, ha, hb, hc, hd, he, hf]
      ring
    have hGderiv : ∀ x, HasDerivAt G (Real.exp (lam*x) * (A * (A * (γ - x / 2) * Real.cos (ζ * x) + lam * (2 * γ - x)
        + Real.sin (2 * θ - ζ * x) / Real.sin (2 * θ)
        - 2 * (1 + Real.sin (θ - ζ * x) / Real.sin θ)))) x := by
      intro x
      have hprod := (hasDerivAt_exp_mul lam x).mul (hRderiv x)
      have hAc := hprod.const_mul A
      have hval : A * (lam*Real.exp (lam*x)*R x + Real.exp (lam*x)*Rd x) = Real.exp (lam*x)*(A*g x) := by
        have h1 : lam*Real.exp (lam*x)*R x + Real.exp (lam*x)*Rd x = Real.exp (lam*x)*(lam*R x + Rd x) := by ring
        rw [h1, hode x]; ring
      rw [hval] at hAc
      have hval2 : Real.exp (lam*x)*(A*g x) = Real.exp (lam*x)*(A * (A * (γ - x / 2) * Real.cos (ζ * x) + lam * (2 * γ - x)
          + Real.sin (2 * θ - ζ * x) / Real.sin (2 * θ)
          - 2 * (1 + Real.sin (θ - ζ * x) / Real.sin θ))) := by
        congr 1; rw [hg]; ring
      rw [hval2] at hAc
      rw [hG]
      exact hAc
    have hintG : IntervalIntegrable (fun x => Real.exp (lam*x) * (A * (A * (γ - x / 2) * Real.cos (ζ * x) + lam * (2 * γ - x)
        + Real.sin (2 * θ - ζ * x) / Real.sin (2 * θ) - 2 * (1 + Real.sin (θ - ζ * x) / Real.sin θ)))) volume 0 (2*γ) := by
      apply Continuous.intervalIntegrable; fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := G)
        (f' := fun x => Real.exp (lam*x) * (A * (A * (γ - x / 2) * Real.cos (ζ * x) + lam * (2 * γ - x)
          + Real.sin (2 * θ - ζ * x) / Real.sin (2 * θ) - 2 * (1 + Real.sin (θ - ζ * x) / Real.sin θ))))
        (fun x _ => hGderiv x) hintG]
    simp only [hG]
    have hζ2γ : ζ * (2*γ) = 2*θ := by rw [hγ]; field_simp
    have hR2γ : R (2*γ) = 0 := by
      simp only [hR]
      rw [hζ2γ, hp, hal, hq, hrr, hs, hbe, hγ, hζ]
      rw [Real.cos_two_mul, Real.sin_two_mul, Real.tan_eq_sin_div_cos]
      field_simp
      ring_nf
      linear_combination (norm := ring_nf) (-4*Real.cos θ^2 * Real.sin θ) * (Real.sin_sq_add_cos_sq θ)
    have hR0 : R 0 = q + be := by simp only [hR, mul_zero, Real.cos_zero, Real.sin_zero]; ring
    rw [hR2γ, hR0]
    simp only [mul_zero, Real.exp_zero, one_mul, zero_sub]
    have hend : -(A*(q+be)) = 2*Real.tan θ ^ 2 + 3 - 3 * θ * Real.tan θ - 3 * θ * (Real.cos θ / Real.sin θ) := by
      rw [hA, hq, hbe, hγ, hζ, Real.tan_eq_sin_div_cos, Real.cos_two_mul]
      field_simp
      ring_nf
      linear_combination (norm := ring_nf) (2*Real.cos θ^2 * Real.sin θ) * (Real.sin_sq_add_cos_sq θ)
    rw [hend]
end Commons.Analysis.Integral