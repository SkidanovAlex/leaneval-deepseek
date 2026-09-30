import Mathlib
import Submission.Work.BMF.parseval.Defs
import Submission.Work.BMF.cpow_theta_identity

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open scoped BigOperators
open MeasureTheory intervalIntegral

noncomputable section

lemma two_add_I_mul_ne_zero (t : ℝ) : (2 + Complex.I*(t:ℂ)) ≠ 0 := by
  intro h
  have h' := congrArg Complex.re h
  norm_num at h'

lemma intervalIntegrable_ofReal_cpow {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (r : ℂ) :
    IntervalIntegrable (fun x : ℝ => (x:ℂ)^r) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro x hx
  rw [Set.uIcc_of_le hab] at hx
  exact (Complex.continuousAt_ofReal_cpow_const x r
    (Or.inr (ne_of_gt (lt_of_lt_of_le ha hx.1)))).continuousWithinAt

lemma integral_ofReal_cpow {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {r : ℂ} (hr : r ≠ -1) :
    ∫ x in a..b, (x:ℂ)^r = ((b:ℂ)^(r+1) - (a:ℂ)^(r+1))/(r+1) :=
  (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => by
      rw [Set.uIcc_of_le hab] at hx
      exact hasDerivAt_ofReal_cpow_const' (ne_of_gt (lt_of_lt_of_le ha hx.1)) hr)
    (intervalIntegrable_ofReal_cpow ha hab r)).trans (div_sub_div_same _ _ _)

lemma Phi_integral_value (t : ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ u in a..b, Phi t u
      = (((1+b : ℝ) : ℂ)^(2 + Complex.I*(t:ℂ)) - ((1+a : ℝ) : ℂ)^(2 + Complex.I*(t:ℂ)))
          / ((1 + Complex.I*(t:ℂ)) * (2 + Complex.I*(t:ℂ)))
        - ((b - a : ℝ) : ℂ) / (1 + Complex.I*(t:ℂ)) := by
  have hk : (1 + Complex.I*(t:ℂ)) ≠ 0 := one_add_I_mul_ne_zeroD t
  have hk2 : (2 + Complex.I*(t:ℂ)) ≠ 0 := two_add_I_mul_ne_zero t
  set c : ℂ := 1 + Complex.I*(t:ℂ) with hc
  have hcne : c ≠ -1 := by
    intro h; have h' := congrArg Complex.re h; rw [hc] at h'; norm_num at h'
  have hc1 : c + 1 = 2 + Complex.I*(t:ℂ) := by rw [hc]; ring
  have hpt : ∀ w : ℝ, Phi t (w - 1) = ((w : ℂ)^c - 1) / c := by
    intro w
    have h1 : (1 + (w - 1) : ℝ) = w := by ring
    unfold Phi
    rw [h1, hc]
  have hshift : (∫ u in a..b, Phi t u) = ∫ w in (a+1)..(b+1), Phi t (w-1) := by
    rw [← intervalIntegral.integral_comp_add_right (fun w : ℝ => Phi t (w-1)) 1]
    apply intervalIntegral.integral_congr
    intro u _
    simp
  have hI1 : (∫ w in (a+1)..(b+1), (w:ℂ)^c)
      = (((b+1 : ℝ):ℂ)^(c+1) - ((a+1 : ℝ):ℂ)^(c+1))/(c+1) :=
    integral_ofReal_cpow (by linarith) (by linarith) hcne
  have hI2 : (∫ w in (a+1)..(b+1), (1:ℂ)) = ((b - a : ℝ):ℂ) := by
    rw [intervalIntegral.integral_const, Complex.real_smul, mul_one]
    push_cast
    ring
  calc ∫ u in a..b, Phi t u
      = ∫ w in (a+1)..(b+1), ((w:ℂ)^c - 1)/c := by
          rw [hshift]
          apply intervalIntegral.integral_congr
          intro w _
          exact hpt w
    _ = (1/c) * ∫ w in (a+1)..(b+1), ((w:ℂ)^c - 1) := by
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro w _
          ring
    _ = (1/c) * ((((b+1:ℝ):ℂ)^(c+1) - ((a+1:ℝ):ℂ)^(c+1))/(c+1) - ((b-a:ℝ):ℂ)) := by
          rw [intervalIntegral.integral_sub (intervalIntegrable_ofReal_cpow (by linarith) (by linarith) c)
                (continuous_const.intervalIntegrable _ _), hI1, hI2]
    _ = (((1+b : ℝ) : ℂ)^(2 + Complex.I*(t:ℂ)) - ((1+a : ℝ) : ℂ)^(2 + Complex.I*(t:ℂ)))
          / ((1 + Complex.I*(t:ℂ)) * (2 + Complex.I*(t:ℂ)))
        - ((b - a : ℝ) : ℂ) / (1 + Complex.I*(t:ℂ)) := by
          rw [show (b + 1 : ℝ) = 1 + b by ring, show (a + 1 : ℝ) = 1 + a by ring]
          rw [hc1, hc]
          field_simp [hk, hk2] <;> ring

lemma Phi_integral_continuous (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    Continuous (fun t : ℝ => ∫ u in a..b, Phi t u) := by
  rw [show (fun t : ℝ => ∫ u in a..b, Phi t u)
      = (fun t : ℝ => (((1+b : ℝ):ℂ)^(2 + Complex.I*(t:ℂ)) - ((1+a : ℝ):ℂ)^(2 + Complex.I*(t:ℂ)))
            / ((1 + Complex.I*(t:ℂ)) * (2 + Complex.I*(t:ℂ)))
          - ((b - a : ℝ):ℂ) / (1 + Complex.I*(t:ℂ))) by
        funext t
        exact Phi_integral_value t ha hab]
  apply Continuous.sub
  · apply Continuous.div
    · apply Continuous.sub
      · exact Continuous.const_cpow (by fun_prop : Continuous (fun t : ℝ => (2:ℂ) + Complex.I*(t:ℂ)))
          (Or.inl (by simp only [Complex.ofReal_ne_zero]; exact ne_of_gt (by linarith)))
      · exact Continuous.const_cpow (by fun_prop : Continuous (fun t : ℝ => (2:ℂ) + Complex.I*(t:ℂ)))
          (Or.inl (by simp only [Complex.ofReal_ne_zero]; exact ne_of_gt (by linarith)))
    · fun_prop
    · intro t
      exact mul_ne_zero (one_add_I_mul_ne_zeroD t) (two_add_I_mul_ne_zero t)
  · exact Continuous.div continuous_const (by fun_prop) (fun t => one_add_I_mul_ne_zeroD t)

lemma cpow_mul_one_add_div (x y : ℝ) (hx : 0 < x) (hy : 0 ≤ y) (c : ℂ) :
    (x:ℂ)^c * ((1 + y/x : ℝ):ℂ)^c = ((x+y:ℝ):ℂ)^c := by
  have h1 : (x + y : ℝ) = x * (1 + y/x) := by field_simp
  have h2 : (0:ℝ) ≤ 1 + y/x := by positivity
  rw [h1, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (a := x) (b := 1 + y/x) hx.le h2]

lemma cpow_two_mul_div (x y : ℝ) (hx : 0 < x) (t : ℝ) :
    (x:ℂ)^(2 + Complex.I*(t:ℂ)) * ((y/x : ℝ):ℂ)
      = (y:ℂ) * (x:ℂ)^(1 + Complex.I*(t:ℂ)) := by
  have hx0 : (x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hd : (x:ℂ) * ((y/x : ℝ):ℂ) = (y:ℂ) := by
    rw [← Complex.ofReal_mul]; congr 1; field_simp
  conv_lhs => rw [show (2:ℂ) + Complex.I*(t:ℂ) = (1 + Complex.I*(t:ℂ)) + 1 by ring,
                   Complex.cpow_add _ _ hx0, Complex.cpow_one]
  rw [mul_assoc, hd, mul_comm]

lemma window_kernel_identity (t : ℝ) {x h : ℝ} (hx : 0 < x) (hh : 0 < h) :
    (x:ℂ)^(2 + Complex.I*(t:ℂ)) * (∫ u in (h/x)..(3*h/x), Phi t u)
      - ((x:ℂ)+(h:ℂ))^(2 + Complex.I*(t:ℂ)) * (∫ u in (0:ℝ)..(2*h/(x+h)), Phi t u)
      = (2*h : ℂ) * (((x:ℂ)+(h:ℂ))^(1 + Complex.I*(t:ℂ)) - (x:ℂ)^(1 + Complex.I*(t:ℂ)))
          / (1 + Complex.I*(t:ℂ)) := by
  have hk : (1 + Complex.I*(t:ℂ)) ≠ 0 := one_add_I_mul_ne_zeroD t
  have hk2 : (2 + Complex.I*(t:ℂ)) ≠ 0 := two_add_I_mul_ne_zero t
  have hxh : (0:ℝ) < x + h := by linarith
  have hab1 : h/x ≤ 3*h/x := by
    have h0 : (0:ℝ) ≤ h/x := by positivity
    have h3 : (3:ℝ)*h/x = 3*(h/x) := by ring
    rw [h3]; linarith
  have hhC' : ((h:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
  have h1 : (∫ u in (h/x)..(3*h/x), Phi t u)
      = ((((1+3*h/x : ℝ):ℂ)^(2+Complex.I*(t:ℂ)) - ((1+h/x : ℝ):ℂ)^(2+Complex.I*(t:ℂ)))
          / ((1+Complex.I*(t:ℂ))*(2+Complex.I*(t:ℂ)))
        - ((3*h/x - h/x : ℝ):ℂ)/(1+Complex.I*(t:ℂ))) :=
    Phi_integral_value t (a := h/x) (b := 3*h/x) (by positivity) hab1
  have h2 : (∫ u in (0:ℝ)..(2*h/(x+h)), Phi t u)
      = ((((1+2*h/(x+h) : ℝ):ℂ)^(2+Complex.I*(t:ℂ)) - ((1+0 : ℝ):ℂ)^(2+Complex.I*(t:ℂ)))
          / ((1+Complex.I*(t:ℂ))*(2+Complex.I*(t:ℂ)))
        - ((2*h/(x+h) - 0 : ℝ):ℂ)/(1+Complex.I*(t:ℂ))) :=
    Phi_integral_value t (a := 0) (b := 2*h/(x+h)) (le_refl 0) (by positivity)
  have pA : (x:ℂ)^(2 + Complex.I*(t:ℂ)) * ((1+3*h/x : ℝ):ℂ)^(2 + Complex.I*(t:ℂ))
      = ((x+3*h:ℝ):ℂ)^(2 + Complex.I*(t:ℂ)) :=
    cpow_mul_one_add_div x (3*h) hx (by positivity) _
  have pB : (x:ℂ)^(2 + Complex.I*(t:ℂ)) * ((1+h/x : ℝ):ℂ)^(2 + Complex.I*(t:ℂ))
      = ((x:ℂ)+(h:ℂ))^(2 + Complex.I*(t:ℂ)) := by
    rw [show ((x:ℂ)+(h:ℂ)) = ((x+h:ℝ):ℂ) by push_cast; ring]
    exact cpow_mul_one_add_div x h hx (by positivity) _
  have pC : ((x:ℂ)+(h:ℂ))^(2 + Complex.I*(t:ℂ)) * ((1+2*h/(x+h) : ℝ):ℂ)^(2 + Complex.I*(t:ℂ))
      = ((x+3*h:ℝ):ℂ)^(2 + Complex.I*(t:ℂ)) := by
    have hca := cpow_mul_one_add_div (x+h) (2*h) hxh (by positivity) (2 + Complex.I*(t:ℂ))
    rw [show (x+h) + 2*h = x + 3*h by ring] at hca
    rw [show ((x:ℂ)+(h:ℂ)) = ((x+h:ℝ):ℂ) by push_cast; ring]
    exact hca
  have pD : (x:ℂ)^(2 + Complex.I*(t:ℂ)) * ((2*h/x : ℝ):ℂ)
      = (2*h:ℂ) * (x:ℂ)^(1 + Complex.I*(t:ℂ)) := by
    rw [cpow_two_mul_div x (2*h) hx t]
    norm_num [Complex.ofReal_mul]
  have pE : ((x:ℂ)+(h:ℂ))^(2 + Complex.I*(t:ℂ)) * ((2*h/(x+h) : ℝ):ℂ)
      = (2*h:ℂ) * ((x:ℂ)+(h:ℂ))^(1 + Complex.I*(t:ℂ)) := by
    have hcb := cpow_two_mul_div (x+h) (2*h) hxh t
    rw [show ((x:ℂ)+(h:ℂ)) = ((x+h:ℝ):ℂ) by push_cast; ring]
    rw [hcb]
    norm_num [Complex.ofReal_mul]
  have hgoal : (x:ℂ)^(2 + Complex.I*(t:ℂ)) * (∫ u in (h/x)..(3*h/x), Phi t u)
      - ((x:ℂ)+(h:ℂ))^(2 + Complex.I*(t:ℂ)) * (∫ u in (0:ℝ)..(2*h/(x+h)), Phi t u)
      = ((x:ℂ)^(2+Complex.I*(t:ℂ)) * ((1+3*h/x : ℝ):ℂ)^(2+Complex.I*(t:ℂ))
          - (x:ℂ)^(2+Complex.I*(t:ℂ)) * ((1+h/x : ℝ):ℂ)^(2+Complex.I*(t:ℂ)))
            / ((1+Complex.I*(t:ℂ))*(2+Complex.I*(t:ℂ)))
        - ((x:ℂ)^(2+Complex.I*(t:ℂ)) * ((3*h/x - h/x : ℝ):ℂ))/(1+Complex.I*(t:ℂ))
        - ( (((x:ℂ)+(h:ℂ))^(2+Complex.I*(t:ℂ)) * ((1+2*h/(x+h) : ℝ):ℂ)^(2+Complex.I*(t:ℂ))
              - ((x:ℂ)+(h:ℂ))^(2+Complex.I*(t:ℂ)) * 1)
                / ((1+Complex.I*(t:ℂ))*(2+Complex.I*(t:ℂ)))
            - (((x:ℂ)+(h:ℂ))^(2+Complex.I*(t:ℂ)) * ((2*h/(x+h) : ℝ):ℂ))/(1+Complex.I*(t:ℂ)) ) := by
    rw [h1, h2]
    simp only [add_zero, sub_zero, Complex.ofReal_one, Complex.one_cpow]
    ring
  rw [hgoal]
  rw [show (3*h/x - h/x : ℝ) = 2*h/x by ring]
  rw [pA, pB, pC, pD, pE]
  field_simp [hhC', hk, hk2] <;> ring

theorem window_decomposition (a : ℕ → ℂ) {X h T x : ℝ} (hX : 1 ≤ X) (hx : X ≤ x) (hx2 : x ≤ 2*X)
    (hh : 0 < h) (hT : 0 < T) :
    perronP a X h T x
      = (1/(4*Real.pi*h^2)) *
        ( (∫ t in (-T)..T, dirP a X t * ((x:ℂ)^(2 + Complex.I*(t:ℂ))) * (∫ u in (h/x)..(3*h/x), Phi t u))
        - (∫ t in (-T)..T, dirP a X t * (((x+h):ℂ)^(2 + Complex.I*(t:ℂ))) * (∫ u in (0:ℝ)..(2*h/(x+h)), Phi t u)) ) := by
  have hxpos : 0 < x := by linarith
  have hxhpos : 0 < x + h := by linarith
  have hdir : Continuous (fun t : ℝ => dirP a X t) := by
    unfold dirP
    apply continuous_finsetSum
    intro n hn
    have hn0 : (n : ℂ) ≠ 0 := by
      have h1 := one_le_of_mem_natIccD hX hn
      exact_mod_cast (by omega : n ≠ 0)
    exact Continuous.mul continuous_const
      ((by fun_prop : Continuous (fun t : ℝ => -(1 + Complex.I*(t:ℂ)))).const_cpow (Or.inl hn0))
  have hab1 : h/x ≤ 3*h/x := by
    have h0 : (0:ℝ) ≤ h/x := by positivity
    have h3 : (3:ℝ)*h/x = 3*(h/x) := by ring
    rw [h3]; linarith
  have hhC' : ((h:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
  have hc1 : Continuous (fun t : ℝ => ∫ u in (h/x)..(3*h/x), Phi t u) :=
    Phi_integral_continuous (h/x) (3*h/x) (by positivity) hab1
  have hc2 : Continuous (fun t : ℝ => ∫ u in (0:ℝ)..(2*h/(x+h)), Phi t u) :=
    Phi_integral_continuous 0 (2*h/(x+h)) (le_refl 0) (by positivity)
  have hxp : Continuous (fun t : ℝ => (x:ℂ)^(2 + Complex.I*(t:ℂ))) :=
    (by fun_prop : Continuous (fun t : ℝ => (2:ℂ) + Complex.I*(t:ℂ))).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hxpos.ne'))
  have hxhC : ((x:ℂ)+(h:ℂ)) ≠ 0 := by
    rw [← Complex.ofReal_add]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hxhpos)
  have hxhp : Continuous (fun t : ℝ => ((x:ℂ)+(h:ℂ))^(2 + Complex.I*(t:ℂ))) :=
    (by fun_prop : Continuous (fun t : ℝ => (2:ℂ) + Complex.I*(t:ℂ))).const_cpow (Or.inl hxhC)
  have hf1c : Continuous (fun t : ℝ => dirP a X t * ((x:ℂ)^(2 + Complex.I*(t:ℂ))) * (∫ u in (h/x)..(3*h/x), Phi t u)) :=
    (hdir.mul hxp).mul hc1
  have hf2c : Continuous (fun t : ℝ => dirP a X t * (((x:ℂ)+(h:ℂ))^(2 + Complex.I*(t:ℂ))) * (∫ u in (0:ℝ)..(2*h/(x+h)), Phi t u)) :=
    (hdir.mul hxhp).mul hc2
  have hi1 : IntervalIntegrable (fun t : ℝ => dirP a X t * ((x:ℂ)^(2 + Complex.I*(t:ℂ))) * (∫ u in (h/x)..(3*h/x), Phi t u)) volume (-T) T :=
    hf1c.intervalIntegrable (-T) T
  have hi2 : IntervalIntegrable (fun t : ℝ => dirP a X t * (((x:ℂ)+(h:ℂ))^(2 + Complex.I*(t:ℂ))) * (∫ u in (0:ℝ)..(2*h/(x+h)), Phi t u)) volume (-T) T :=
    hf2c.intervalIntegrable (-T) T
  set B : ℝ → ℂ := fun t => (((x+h:ℝ):ℂ)^(1 + Complex.I*(t:ℂ)) - (x:ℂ)^(1 + Complex.I*(t:ℂ))) / ((h:ℂ) * (1 + Complex.I*(t:ℂ))) with hB
  have hperr : perronP a X h T x = (1/(2*Real.pi)) * ∫ t in (-T)..T, dirP a X t * B t := by
    rw [perronP]
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    simp only [hB]
    rw [mul_assoc, cpow_theta_identity h x t hxpos hh]
  have hpt : ∀ t : ℝ,
      dirP a X t * ((x:ℂ)^(2 + Complex.I*(t:ℂ))) * (∫ u in (h/x)..(3*h/x), Phi t u)
      - dirP a X t * (((x:ℂ)+(h:ℂ))^(2 + Complex.I*(t:ℂ))) * (∫ u in (0:ℝ)..(2*h/(x+h)), Phi t u)
      = dirP a X t * (((2:ℂ)*(h:ℂ)^2) * B t) := by
    intro t
    have hD := window_kernel_identity t hxpos hh
    have step : dirP a X t * ((x:ℂ)^(2 + Complex.I*(t:ℂ))) * (∫ u in (h/x)..(3*h/x), Phi t u)
        - dirP a X t * (((x:ℂ)+(h:ℂ))^(2 + Complex.I*(t:ℂ))) * (∫ u in (0:ℝ)..(2*h/(x+h)), Phi t u)
        = dirP a X t * (((x:ℂ)^(2 + Complex.I*(t:ℂ))) * (∫ u in (h/x)..(3*h/x), Phi t u)
            - ((x:ℂ)+(h:ℂ))^(2 + Complex.I*(t:ℂ)) * (∫ u in (0:ℝ)..(2*h/(x+h)), Phi t u)) := by ring
    rw [step, hD]
    rw [show ((x:ℂ)+(h:ℂ)) = ((x+h:ℝ):ℂ) by push_cast; ring]
    simp only [hB]
    congr 1
    field_simp [Complex.ofReal_ne_zero.mpr hh.ne', one_add_I_mul_ne_zeroD t] <;> ring
  have hsplit : (∫ t in (-T)..T, dirP a X t * ((x:ℂ)^(2 + Complex.I*(t:ℂ))) * (∫ u in (h/x)..(3*h/x), Phi t u))
        - (∫ t in (-T)..T, dirP a X t * (((x:ℂ)+(h:ℂ))^(2 + Complex.I*(t:ℂ))) * (∫ u in (0:ℝ)..(2*h/(x+h)), Phi t u))
      = ∫ t in (-T)..T, dirP a X t * (((2:ℂ)*(h:ℂ)^2) * B t) := by
    rw [← intervalIntegral.integral_sub hi1 hi2]
    apply intervalIntegral.integral_congr
    intro t _
    exact hpt t
  have hpull : (∫ t in (-T)..T, dirP a X t * (((2:ℂ)*(h:ℂ)^2) * B t))
      = ((2:ℂ)*(h:ℂ)^2) * ∫ t in (-T)..T, dirP a X t * B t := by
    rw [show (fun t => dirP a X t * (((2:ℂ)*(h:ℂ)^2) * B t))
        = (fun t => ((2:ℂ)*(h:ℂ)^2) * (dirP a X t * B t)) by funext t; ring]
    rw [intervalIntegral.integral_const_mul]
  rw [hperr]
  have hJ : (∫ t in (-T)..T, dirP a X t * ((x:ℂ)^(2 + Complex.I*(t:ℂ))) * (∫ u in (h/x)..(3*h/x), Phi t u))
          - (∫ t in (-T)..T, dirP a X t * (((x:ℂ)+(h:ℂ))^(2 + Complex.I*(t:ℂ))) * (∫ u in (0:ℝ)..(2*h/(x+h)), Phi t u))
        = ((2:ℂ)*(h:ℂ)^2) * ∫ t in (-T)..T, dirP a X t * B t := by
    rw [hsplit, hpull]
  rw [hJ, ← mul_assoc]
  congr 1
  have hpiC : ((Real.pi:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hhC : ((h:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
  push_cast <;> field_simp <;> ring


end

end Work.BMF
