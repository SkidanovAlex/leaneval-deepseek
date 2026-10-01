import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open Real MeasureTheory

namespace Commons.Analysis.Integral

private lemma hasDerivAt_cosh_mul (a x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.cosh (a * y)) (a * Real.sinh (a * x)) x := by
  simpa [Function.comp_def, mul_comm] using
    (Real.hasDerivAt_cosh (a * x)).comp x (hasDerivAt_const_mul (x := x) a)

private lemma hasDerivAt_sinh_mul (a x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sinh (a * y)) (a * Real.cosh (a * x)) x := by
  simpa [Function.comp_def, mul_comm] using
    (Real.hasDerivAt_sinh (a * x)).comp x (hasDerivAt_const_mul (x := x) a)

private lemma hasDerivAt_cosh_sub_mul (a c x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.cosh (c - a * y)) (-(a * Real.sinh (c - a * x))) x := by
  have h1 : HasDerivAt (fun y : ℝ => c - a * y) (-a) x := by
    simpa using (hasDerivAt_const_mul (x := x) a).const_sub c
  simpa [Function.comp_def, mul_comm] using
    (Real.hasDerivAt_cosh (c - a * x)).comp x h1

private lemma hasDerivAt_exp_mul (a x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (a * y)) (a * Real.exp (a * x)) x := by
  simpa [Function.comp_def, mul_comm] using
    (Real.hasDerivAt_exp (a * x)).comp x (hasDerivAt_const_mul (x := x) a)

theorem extremal_cosh_integral {θ lam : ℝ} (hθ0 : 0 < θ) (hlam : 0 < lam) :
    let ρ : ℝ := lam * Real.tanh θ
    let γ : ℝ := θ / ρ
    let f : ℝ → ℝ := fun x => lam * (1 - Real.tanh θ ^ 2) *
      (lam * (1 - Real.tanh θ ^ 2) * (γ - x / 2) * Real.cosh (ρ * x) + lam * (2 * γ - x)
        + Real.sinh (2 * θ - ρ * x) / Real.sinh (2 * θ)
        - 2 * (1 + Real.sinh (θ - ρ * x) / Real.sinh θ))
    f 0 = lam * (1 - Real.tanh θ ^ 2) * (3 * θ * (Real.cosh θ / Real.sinh θ) - θ * Real.tanh θ - 3) ∧
    (∫ x in (0:ℝ)..(2 * γ), f x) = 2 * (1 - Real.tanh θ ^ 2) * (1 - θ * (Real.cosh θ / Real.sinh θ)) ^ 2 ∧
    (∫ x in (0:ℝ)..(2 * γ), Real.exp (lam * x) * f x)
      = 3 - 2 * Real.tanh θ ^ 2 + 3 * θ * Real.tanh θ - 3 * θ * (Real.cosh θ / Real.sinh θ) := by
  dsimp only
  set ζ : ℝ := lam * Real.tanh θ with hζ
  set γ : ℝ := θ / ζ with hγ
  set A : ℝ := lam * (1 - Real.tanh θ ^ 2) with hA
  have hsinh_pos : 0 < Real.sinh θ := Real.sinh_pos_iff.mpr hθ0
  have hsinh_ne : Real.sinh θ ≠ 0 := ne_of_gt hsinh_pos
  have hcosh_pos : 0 < Real.cosh θ := Real.cosh_pos θ
  have hcosh_ne : Real.cosh θ ≠ 0 := ne_of_gt hcosh_pos
  have htanh_pos : 0 < Real.tanh θ := by
    rw [Real.tanh_eq_sinh_div_cosh]; positivity
  have htanh_ne : Real.tanh θ ≠ 0 := ne_of_gt htanh_pos
  have htanh_sq_lt : Real.tanh θ ^ 2 < 1 := by
    nlinarith [Real.tanh_lt_one θ, htanh_pos]
  have hζ_ne : ζ ≠ 0 := by rw [hζ]; exact mul_ne_zero (ne_of_gt hlam) htanh_ne
  have hsinh2θ_pos : 0 < Real.sinh (2 * θ) := Real.sinh_pos_iff.mpr (by linarith)
  have hsinh2θ_ne : Real.sinh (2 * θ) ≠ 0 := ne_of_gt hsinh2θ_pos
  have hA_pos : 0 < A := by rw [hA]; exact mul_pos hlam (by linarith)
  have hζγ : ζ * γ = θ := by rw [hγ]; field_simp
  refine ⟨?_, ?_, ?_⟩
  · -- f 0
    have h1 : A * γ + lam * (2 * γ) + Real.sinh (2 * θ) / Real.sinh (2 * θ)
        - 2 * (1 + Real.sinh θ / Real.sinh θ) = γ * (A + 2 * lam) - 3 := by
      rw [div_self hsinh2θ_ne, div_self hsinh_ne]; ring
    have h2 : γ * (A + 2 * lam) = 3 * θ * (Real.cosh θ / Real.sinh θ) - θ * Real.tanh θ := by
      rw [hA, hγ, hζ, Real.tanh_eq_sinh_div_cosh]
      field_simp
      ring
    simp only [mul_zero, zero_div, Real.cosh_zero, mul_one, sub_zero]
    rw [h1, h2]
  · -- first integral
    let GH : ℝ → ℝ := fun x =>
      ((A*((γ - x/2)*Real.sinh (ζ*x)/ζ + Real.cosh (ζ*x)/(2*ζ^2)) + lam*(2*γ*x - x^2/2))
        + (-(Real.cosh (2*θ - ζ*x))/(ζ*Real.sinh (2*θ)))) - 2*x
        + 2*Real.cosh (θ - ζ*x)/(ζ*Real.sinh θ)
    let F : ℝ → ℝ := fun x => A * GH x
    have hInner : ∀ x, HasDerivAt (fun y : ℝ => (γ - y/2)*Real.sinh (ζ*y)/ζ + Real.cosh (ζ*y)/(2*ζ^2))
        ((γ - x/2)*Real.cosh (ζ*x)) x := by
      intro x
      have hlin : HasDerivAt (fun y : ℝ => γ - y/2) (-1/2) x := by
        have h := (hasDerivAt_id x).div_const 2
        have key : HasDerivAt (fun y : ℝ => γ - y/2) (0 - 1/2) x :=
          (hasDerivAt_const (x := x) γ).sub h
        have hval : (0:ℝ) - 1/2 = -1/2 := by norm_num
        rw [hval] at key
        exact key
      have ha : HasDerivAt (fun y : ℝ => (γ - y/2)*Real.sinh (ζ*y)/ζ)
          (((-1/2)*Real.sinh (ζ*x) + (γ - x/2)*(ζ*Real.cosh (ζ*x)))/ζ) x :=
        (hlin.mul (hasDerivAt_sinh_mul ζ x)).div_const ζ
      have hb : HasDerivAt (fun y : ℝ => Real.cosh (ζ*y)/(2*ζ^2))
          ((ζ*Real.sinh (ζ*x))/(2*ζ^2)) x :=
        (hasDerivAt_cosh_mul ζ x).div_const (2*ζ^2)
      have h := ha.add hb
      have hval : (((-1/2)*Real.sinh (ζ*x) + (γ - x/2)*(ζ*Real.cosh (ζ*x)))/ζ
          + (ζ*Real.sinh (ζ*x))/(2*ζ^2)) = (γ - x/2)*Real.cosh (ζ*x) := by
        field_simp
        ring
      rw [hval] at h
      exact h
    have hFderiv : ∀ x, HasDerivAt F (A * (A * (γ - x / 2) * Real.cosh (ζ * x) + lam * (2 * γ - x)
        + Real.sinh (2 * θ - ζ * x) / Real.sinh (2 * θ)
        - 2 * (1 + Real.sinh (θ - ζ * x) / Real.sinh θ))) x := by
      intro x
      have h1 : HasDerivAt (fun y : ℝ => A * ((γ - y/2)*Real.sinh (ζ*y)/ζ + Real.cosh (ζ*y)/(2*ζ^2)))
          (A*((γ - x/2)*Real.cosh (ζ*x))) x := (hInner x).const_mul A
      have h2 : HasDerivAt (fun y : ℝ => lam*(2*γ*y - y^2/2)) (lam*(2*γ - x)) x := by
        have h := ((hasDerivAt_id x).const_mul (2*γ)).sub (((hasDerivAt_id x).pow 2).div_const 2)
        have key : HasDerivAt (fun y : ℝ => (2*γ)*y - y^2/2) ((2*γ)*1 - (2*x^(2-1)*1)/2) x := h
        have hval : (2*γ)*1 - (2*x^(2-1)*1)/2 = 2*γ - x := by ring
        rw [hval] at key
        exact key.const_mul lam
      have h3 : HasDerivAt (fun y : ℝ => -(Real.cosh (2*θ - ζ*y))/(ζ*Real.sinh (2*θ)))
          (Real.sinh (2*θ - ζ*x)/Real.sinh (2*θ)) x := by
        have h := ((hasDerivAt_cosh_sub_mul ζ (2*θ) x).neg).div_const (ζ*Real.sinh (2*θ))
        have hval : (-( -(ζ*Real.sinh (2*θ - ζ*x))))/(ζ*Real.sinh (2*θ))
            = Real.sinh (2*θ - ζ*x)/Real.sinh (2*θ) := by
          field_simp
        rw [hval] at h
        exact h
      have h4 : HasDerivAt (fun y : ℝ => 2*y) (2:ℝ) x := by
        simpa using (hasDerivAt_id x).const_mul (2:ℝ)
      have h5 : HasDerivAt (fun y : ℝ => 2*Real.cosh (θ - ζ*y)/(ζ*Real.sinh θ))
          (-(2*Real.sinh (θ - ζ*x)/Real.sinh θ)) x := by
        have h := ((hasDerivAt_cosh_sub_mul ζ θ x).const_mul (2:ℝ)).div_const (ζ*Real.sinh θ)
        have hval : 2*(-(ζ*Real.sinh (θ - ζ*x)))/(ζ*Real.sinh θ)
            = -(2*Real.sinh (θ - ζ*x)/Real.sinh θ) := by
          field_simp
        rw [hval] at h
        exact h
      have hGH := (((h1.add h2).add h3).sub h4).add h5
      have hF := hGH.const_mul A
      have hval : A * (((A*((γ - x/2)*Real.cosh (ζ*x)) + lam*(2*γ - x))
            + Real.sinh (2*θ - ζ*x)/Real.sinh (2*θ)) - 2 + (-(2*Real.sinh (θ - ζ*x)/Real.sinh θ)))
          = A * (A * (γ - x / 2) * Real.cosh (ζ * x) + lam * (2 * γ - x)
            + Real.sinh (2 * θ - ζ * x) / Real.sinh (2 * θ)
            - 2 * (1 + Real.sinh (θ - ζ * x) / Real.sinh θ)) := by ring
      rw [hval] at hF
      exact hF
    have hint : IntervalIntegrable (fun x : ℝ => A * (A * (γ - x / 2) * Real.cosh (ζ * x) + lam * (2 * γ - x)
        + Real.sinh (2 * θ - ζ * x) / Real.sinh (2 * θ)
        - 2 * (1 + Real.sinh (θ - ζ * x) / Real.sinh θ))) volume 0 (2*γ) := by
      apply Continuous.intervalIntegrable
      fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := F)
        (f' := fun x => A * (A * (γ - x / 2) * Real.cosh (ζ * x) + lam * (2 * γ - x)
          + Real.sinh (2 * θ - ζ * x) / Real.sinh (2 * θ)
          - 2 * (1 + Real.sinh (θ - ζ * x) / Real.sinh θ)))
        (fun x _ => hFderiv x) hint]
    simp only [F, GH]
    have hζ2γ : ζ * (2*γ) = 2*θ := by rw [hγ]; field_simp
    have hcos2 : (θ:ℝ) - 2*θ = -θ := by ring
    rw [hζ2γ, hcos2]
    simp only [sub_self, mul_zero, zero_div, Real.sinh_zero, Real.cosh_zero, Real.cosh_neg,
      pow_two, sub_zero, add_zero]
    rw [hA, hγ, hζ]
    rw [Real.cosh_two_mul, Real.sinh_two_mul, Real.tanh_eq_sinh_div_cosh]
    field_simp
    ring_nf
    field_simp
    ring_nf
    nlinarith [Real.cosh_sq_sub_sinh_sq θ]
  · -- second integral, exp-weighted
    set p : ℝ := -1/2 with hp
    set q : ℝ := (θ * (Real.cosh θ / Real.sinh θ) - Real.sinh θ ^ 2 - 2) / lam with hq
    set rr : ℝ := Real.tanh θ / 2 with hrr
    set s : ℝ := (-θ + Real.sinh θ * Real.cosh θ + (3/2) * (Real.cosh θ / Real.sinh θ)) / lam with hs
    set al : ℝ := -1 with hal
    set be : ℝ := 2 * γ - 1 / lam with hbe
    set R : ℝ → ℝ := fun x => ((p*x+q)*Real.cosh (ζ*x) + (rr*x+s)*Real.sinh (ζ*x)) + (al*x+be) with hR
    set Rd : ℝ → ℝ := fun x => ((p*Real.cosh (ζ*x) + (p*x+q)*(ζ*Real.sinh (ζ*x)))
        + (rr*Real.sinh (ζ*x) + (rr*x+s)*(ζ*Real.cosh (ζ*x)))) + al with hRd
    set g : ℝ → ℝ := fun x => A*(γ-x/2)*Real.cosh (ζ*x) + lam*(2*γ-x)
        + Real.sinh (2*θ-ζ*x)/Real.sinh (2*θ) - 2 - 2*Real.sinh (θ-ζ*x)/Real.sinh θ with hg
    set G : ℝ → ℝ := fun x => A*(Real.exp (lam*x) * R x) with hG
    have ha : lam*p + ζ*rr = -A/2 := by rw [hp, hrr, hζ, hA]; ring
    have he : lam*al = -lam := by rw [hal]; ring
    have hf : lam*be + al = 2*lam*γ - 2 := by rw [hbe, hal]; field_simp; ring
    have hb : lam*q + p + ζ*s = A*γ - 1 := by
      rw [hq, hp, hs, hA, hγ, hζ, Real.tanh_eq_sinh_div_cosh]
      field_simp
      ring
    have hc : lam*rr + ζ*p = 0 := by rw [hrr, hp, hζ]; ring
    have hd : lam*s + rr + ζ*q = 2*Real.cosh θ/Real.sinh θ - Real.cosh (2*θ)/Real.sinh (2*θ) := by
      rw [hs, hrr, hq, hζ, Real.tanh_eq_sinh_div_cosh, Real.sinh_two_mul, Real.cosh_two_mul]
      field_simp
      ring_nf
      linear_combination (norm := ring_nf) (2*Real.sinh θ^2) * (Real.cosh_sq_sub_sinh_sq θ)
    have hRderiv : ∀ x, HasDerivAt R (Rd x) x := by
      intro x
      have hp1 : HasDerivAt (fun y : ℝ => p*y + q) p x := by
        simpa using (hasDerivAt_const_mul (x:=x) p).add_const q
      have hp2 : HasDerivAt (fun y : ℝ => rr*y + s) rr x := by
        simpa using (hasDerivAt_const_mul (x:=x) rr).add_const s
      have hlin : HasDerivAt (fun y : ℝ => al*y + be) al x := by
        simpa using (hasDerivAt_const_mul (x:=x) al).add_const be
      have hpr := (hp1.mul (hasDerivAt_cosh_mul ζ x)).add (hp2.mul (hasDerivAt_sinh_mul ζ x))
      have hsum := hpr.add hlin
      rw [hR, hRd]
      exact hsum
    have expand2 : ∀ x, lam * R x + Rd x = ((lam*p + ζ*rr)*x + (lam*q + p + ζ*s))*Real.cosh (ζ*x)
        + ((lam*rr + ζ*p)*x + (lam*s + rr + ζ*q))*Real.sinh (ζ*x) + (lam*al)*x + (lam*be + al) := by
      intro x; rw [hR, hRd]; ring
    have expandg : ∀ x, g x = ((-A/2)*x + (A*γ - 1))*Real.cosh (ζ*x)
        + (2*Real.cosh θ/Real.sinh θ - Real.cosh (2*θ)/Real.sinh (2*θ))*Real.sinh (ζ*x)
        + (-lam)*x + (2*lam*γ - 2) := by
      intro x; rw [hg]; simp only [Real.sinh_sub]; field_simp; ring
    have hode : ∀ x, lam * R x + Rd x = g x := by
      intro x
      rw [expand2 x, expandg x, ha, hb, hc, hd, he, hf]
      ring
    have hGderiv : ∀ x, HasDerivAt G (Real.exp (lam*x) * (A * (A * (γ - x / 2) * Real.cosh (ζ * x) + lam * (2 * γ - x)
        + Real.sinh (2 * θ - ζ * x) / Real.sinh (2 * θ)
        - 2 * (1 + Real.sinh (θ - ζ * x) / Real.sinh θ)))) x := by
      intro x
      have hprod := (hasDerivAt_exp_mul lam x).mul (hRderiv x)
      have hAc := hprod.const_mul A
      have hval : A * ((lam*Real.exp (lam*x))*R x + Real.exp (lam*x)*Rd x) = Real.exp (lam*x)*(A*g x) := by
        have h1 : (lam*Real.exp (lam*x))*R x + Real.exp (lam*x)*Rd x = Real.exp (lam*x)*(lam*R x + Rd x) := by ring
        rw [h1, hode x]; ring
      rw [hval] at hAc
      have hval2 : Real.exp (lam*x)*(A*g x) = Real.exp (lam*x)*(A * (A * (γ - x / 2) * Real.cosh (ζ * x) + lam * (2 * γ - x)
          + Real.sinh (2 * θ - ζ * x) / Real.sinh (2 * θ)
          - 2 * (1 + Real.sinh (θ - ζ * x) / Real.sinh θ))) := by
        congr 1; rw [hg]; ring
      rw [hval2] at hAc
      rw [hG]
      exact hAc
    have hintG : IntervalIntegrable (fun x => Real.exp (lam*x) * (A * (A * (γ - x / 2) * Real.cosh (ζ * x) + lam * (2 * γ - x)
        + Real.sinh (2 * θ - ζ * x) / Real.sinh (2 * θ) - 2 * (1 + Real.sinh (θ - ζ * x) / Real.sinh θ)))) volume 0 (2*γ) := by
      apply Continuous.intervalIntegrable; fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := G)
        (f' := fun x => Real.exp (lam*x) * (A * (A * (γ - x / 2) * Real.cosh (ζ * x) + lam * (2 * γ - x)
          + Real.sinh (2 * θ - ζ * x) / Real.sinh (2 * θ) - 2 * (1 + Real.sinh (θ - ζ * x) / Real.sinh θ))))
        (fun x _ => hGderiv x) hintG]
    simp only [hG]
    have hζ2γ : ζ * (2*γ) = 2*θ := by rw [hγ]; field_simp
    have hR2γ : R (2*γ) = 0 := by
      simp only [hR]
      rw [hζ2γ, hp, hal, hq, hrr, hs, hbe, hγ, hζ]
      rw [Real.cosh_two_mul, Real.sinh_two_mul, Real.tanh_eq_sinh_div_cosh]
      field_simp
      ring_nf
      linear_combination (norm := ring_nf) (Real.sinh θ + Real.sinh θ^3) * (Real.cosh_sq_sub_sinh_sq θ)
    have hR0 : R 0 = q + be := by simp only [hR, mul_zero, Real.cosh_zero, Real.sinh_zero]; ring
    rw [hR2γ, hR0]
    simp only [mul_zero, Real.exp_zero, one_mul, zero_sub]
    have hend : -(A*(q+be)) = 3 - 2*Real.tanh θ ^ 2 + 3 * θ * Real.tanh θ - 3 * θ * (Real.cosh θ / Real.sinh θ) := by
      rw [hA, hq, hbe, hγ, hζ, Real.tanh_eq_sinh_div_cosh]
      field_simp
      ring_nf
      linear_combination (norm := ring_nf) (Real.sinh θ^3) * (Real.cosh_sq_sub_sinh_sq θ)
    rw [hend]

end Commons.Analysis.Integral