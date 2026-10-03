import Mathlib

namespace Work.FIArea5.S16

open MeasureTheory intervalIntegral
open scoped Topology

/-- `iteratedDeriv 2 p = deriv (deriv p)`. -/
lemma iteratedDeriv_two_eq' (p : ℝ → ℝ) : iteratedDeriv 2 p = deriv (deriv p) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]

/-- One integration by parts on an arbitrary interval: if `u,v` are differentiable on `uIcc a b`
with derivatives `u',v'` there and those derivatives are interval integrable, then
`∫ u·v' = u b·v b − u a·v a − ∫ u'·v`. -/
lemma ibp_step_gen {q q' : ℝ → ℝ} {e e' : ℝ → ℂ} {a b : ℝ}
    (hq : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun y => (q y : ℂ)) ((q' x : ℝ) : ℂ) x)
    (he : ∀ x ∈ Set.uIcc a b, HasDerivAt e (e' x) x)
    (hqi : IntervalIntegrable (fun y => ((q' y : ℝ) : ℂ)) volume a b)
    (hei : IntervalIntegrable e' volume a b) :
    ∫ x in a..b, (q x : ℂ) * e' x
      = (q b : ℂ) * e b - (q a : ℂ) * e a - ∫ x in a..b, (q' x : ℂ) * e x :=
  intervalIntegral.integral_mul_deriv_eq_deriv_mul hq he hqi hei

/-- **Two-fold integration by parts for the Mellin transform.**  For a `C²` function `p` on
`[a,b] ⊆ (0,∞)` vanishing, together with its derivative, at the endpoints `a`, `b`, and for
`w ∈ ℂ` with `w+1 ≠ 0`, `w+2 ≠ 0`,
`(∫_a^b p(u) u^w du) · (w+1)(w+2) = ∫_a^b p''(u) u^{w+2} du`. -/
theorem mellin_ibp (p : ℝ → ℝ) (a b : ℝ) (w : ℂ) (ha : 0 < a) (hb : 0 < b)
    (hpC : ContDiff ℝ 2 p) (hpa : p a = 0) (hpb : p b = 0)
    (hdpa : deriv p a = 0) (hdpb : deriv p b = 0)
    (hw1 : w + 1 ≠ 0) (hw2 : w + 2 ≠ 0) :
    (∫ u in a..b, (p u : ℂ) * (u : ℂ) ^ w) * ((w + 1) * (w + 2))
      = ∫ u in a..b, ((iteratedDeriv 2 p u : ℝ) : ℂ) * (u : ℂ) ^ (w + 2) := by
  -- every point of the interval is positive
  have hpos : ∀ x ∈ Set.uIcc a b, 0 < x := by
    intro x hx
    rcases Set.mem_uIcc.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · linarith
    · linarith
  have hq1 : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun y : ℝ => (p y : ℂ)) ((deriv p x : ℝ):ℂ) x :=
    fun x _ => (hpC.differentiable (by norm_num)).differentiableAt.hasDerivAt.ofReal_comp
  have he1 : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ (w + 1) / (w + 1)) ((x:ℂ) ^ w) x := by
    intro x hx
    have hx0 : (x:ℝ) ≠ 0 := ne_of_gt (hpos x hx)
    have hw : w ≠ -1 := by intro h; exact hw1 (by rw [h]; ring)
    exact hasDerivAt_ofReal_cpow_const' hx0 hw
  have he2 : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ (w + 2) / (w + 2)) ((x:ℂ) ^ (w+1)) x := by
    intro x hx
    have hx0 : (x:ℝ) ≠ 0 := ne_of_gt (hpos x hx)
    have hw : w + 1 ≠ -1 := by
      intro h
      exact hw2 (by rw [show w + 2 = (w+1)+1 from by ring, h]; ring)
    have h := hasDerivAt_ofReal_cpow_const' hx0 (r := w+1) hw
    simpa only [show (w + 1) + 1 = w + 2 from by ring] using h
  have hq2 : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => ((deriv p y : ℝ):ℂ)) ((iteratedDeriv 2 p x : ℝ):ℂ) x := by
    intro x hx
    rw [iteratedDeriv_two_eq']
    exact (hpC.differentiable_deriv_two.differentiableAt).hasDerivAt.ofReal_comp
  have hderiv_cont : Continuous (fun y : ℝ => ((deriv p y : ℝ):ℂ)) :=
    Complex.continuous_ofReal.comp (hpC.continuous_deriv (by norm_num))
  have hdd_cont : Continuous (fun y : ℝ => ((iteratedDeriv 2 p y : ℝ):ℂ)) :=
    Complex.continuous_ofReal.comp (hpC.continuous_iteratedDeriv' 2)
  have hpow_contOn : ∀ c : ℂ, ContinuousOn (fun y : ℝ => (y:ℂ)^c) (Set.uIcc a b) := by
    intro c
    exact (Complex.continuous_ofReal.continuousOn.cpow_const
      (fun y hy => Complex.ofReal_mem_slitPlane.mpr (hpos y hy)))
  have hqi1 : IntervalIntegrable (fun y : ℝ => ((deriv p y : ℝ):ℂ)) volume a b :=
    hderiv_cont.intervalIntegrable a b
  have hqi2 : IntervalIntegrable (fun y : ℝ => ((iteratedDeriv 2 p y : ℝ):ℂ)) volume a b :=
    hdd_cont.intervalIntegrable a b
  have hei1 : IntervalIntegrable (fun y : ℝ => (y:ℂ)^w) volume a b :=
    (hpow_contOn w).intervalIntegrable
  have hei2 : IntervalIntegrable (fun y : ℝ => (y:ℂ)^(w+1)) volume a b :=
    (hpow_contOn (w+1)).intervalIntegrable
  have hstep1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := a) (b := b)
      (u := fun y : ℝ => (p y : ℂ)) (v := fun y : ℝ => (y:ℂ)^(w+1)/(w+1))
      (u' := fun y : ℝ => ((deriv p y : ℝ):ℂ)) (v' := fun y : ℝ => (y:ℂ)^w)
      hq1 he1 hqi1 hei1
  have hstep2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := a) (b := b)
      (u := fun y : ℝ => ((deriv p y : ℝ):ℂ)) (v := fun y : ℝ => (y:ℂ)^(w+2)/(w+2))
      (u' := fun y : ℝ => ((iteratedDeriv 2 p y : ℝ):ℂ)) (v' := fun y : ℝ => (y:ℂ)^(w+1))
      hq2 he2 hqi2 hei2
  set B : ℂ := ∫ u in a..b, ((deriv p u : ℝ):ℂ) * (u:ℂ)^(w+1) with hB
  set D : ℂ := ∫ u in a..b, ((iteratedDeriv 2 p u : ℝ):ℂ) * (u:ℂ)^(w+2) with hD
  have hconst1 : (∫ x in a..b, ((deriv p x : ℝ):ℂ) * ((x:ℂ)^(w+1)/(w+1)))
      = (w+1)⁻¹ * B := by
    rw [hB, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    ring
  have hconst2 : (∫ x in a..b, ((iteratedDeriv 2 p x : ℝ):ℂ) * ((x:ℂ)^(w+2)/(w+2)))
      = (w+2)⁻¹ * D := by
    rw [hD, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    ring
  have step1 : (∫ u in a..b, (p u : ℂ) * (u:ℂ)^w) = - ((w+1)⁻¹ * B) := by
    rw [hstep1, hpa, hpb]
    simp only [Complex.ofReal_zero, zero_mul, sub_zero, zero_sub]
    rw [hconst1]
  have step2 : B = - ((w+2)⁻¹ * D) := by
    rw [hstep2, hdpb, hdpa]
    simp only [Complex.ofReal_zero, zero_mul, sub_zero, zero_sub]
    rw [hconst2]
  have hAD : (∫ u in a..b, (p u : ℂ) * (u:ℂ)^w) = ((w+1)*(w+2))⁻¹ * D := by
    rw [step1, step2, mul_inv]
    ring
  have hc : ((w+1)*(w+2)) ≠ 0 := mul_ne_zero hw1 hw2
  have hgoal : ((w+1)*(w+2))⁻¹ * D * ((w+1)*(w+2)) = D := by
    rw [mul_assoc, mul_comm D, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  calc (∫ u in a..b, (p u : ℂ) * (u:ℂ)^w) * ((w+1)*(w+2))
      = (((w+1)*(w+2))⁻¹ * D) * ((w+1)*(w+2)) := by rw [hAD]
    _ = D := hgoal
    _ = ∫ u in a..b, ((iteratedDeriv 2 p u : ℝ):ℂ) * (u:ℂ)^(w+2) := hD

end Work.FIArea5.S16
