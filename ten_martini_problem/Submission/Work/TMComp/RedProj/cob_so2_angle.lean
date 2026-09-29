import Mathlib
import Submission.Work.TMComp.RedProj.so2_tools

/-!
# The analytic angle lift of an `S¹`-valued analytic function

If `u, v : ℝ → ℝ` are real-analytic with `u x ^ 2 + v x ^ 2 = 1`, then `z x = u x + i v x` is an
analytic, nowhere vanishing `ℂ`-valued function, and we produce a real-analytic `κ : ℝ → ℝ` with
`exp (2 π i κ x) = z x`.

Strategy.  First build a *continuous* lift by integrating the angular velocity
`s x = (u v' - v u') / (2 π)`: the function `x ↦ exp (-2 π i κ x) z x` has vanishing derivative
(because `u u' + v v' = 0` on the circle) and value `1` at `0`, so `exp (2 π i κ x) = z x`.
Then upgrade to analyticity: near any point one of the two charts `w ↦ log w`, `w ↦ log (-w)` of
the universal cover of `S¹` gives a local analytic angle lift `ℓ`; the difference `κ - ℓ` is
continuous and `ℤ`-valued, hence locally constant, so `κ` is analytic.
-/

namespace Work.TMComp.RedProj

open Complex MeasureTheory Filter
open scoped Topology

noncomputable section

/-- On the unit circle, `exp (i * im (log w)) = w`. -/
theorem cob_exp_I_im_log {w : ℂ} (hw : w ≠ 0) (hn : ‖w‖ = 1) :
    Complex.exp (((Complex.log w).im : ℂ) * Complex.I) = w := by
  have hsplit : Complex.log w = ((Complex.log w).re : ℂ) + ((Complex.log w).im : ℂ) * Complex.I :=
    (Complex.re_add_im _).symm
  have key : Complex.exp (((Complex.log w).re : ℂ))
        * Complex.exp (((Complex.log w).im : ℂ) * Complex.I) = w := by
    rw [← Complex.exp_add, ← hsplit, Complex.exp_log hw]
  rw [Complex.log_re, ← Complex.ofReal_exp, Real.exp_log (norm_pos_iff.mpr hw), hn,
    Complex.ofReal_one, one_mul] at key
  exact key

/-- If `exp (2 π i a) = exp (2 π i b)` then `a - b ∈ ℤ`. -/
theorem cob_exp_two_pi_sub_int {a b : ℝ}
    (h : Complex.exp (2 * Real.pi * a * Complex.I) = Complex.exp (2 * Real.pi * b * Complex.I)) :
    ∃ m : ℤ, a - b = (m : ℝ) := by
  have h' : Complex.exp (((2 * Real.pi * a : ℝ)) * Complex.I)
      = Complex.exp (((2 * Real.pi * b : ℝ)) * Complex.I) := by
    rw [show 2 * Real.pi * a * Complex.I = (((2 * Real.pi * a : ℝ)) : ℂ) * Complex.I by
      push_cast; ring,
      show 2 * Real.pi * b * Complex.I = (((2 * Real.pi * b : ℝ)) : ℂ) * Complex.I by
      push_cast; ring] at h
    exact h
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I] at h'
  have hcos : Real.cos (2 * Real.pi * a) = Real.cos (2 * Real.pi * b) := by
    have hre := congrArg Complex.re h'
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero] at hre
    linarith
  have hsin : Real.sin (2 * Real.pi * a) = Real.sin (2 * Real.pi * b) := by
    have him := congrArg Complex.im h'
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_add] at him
    linarith
  have h1 : Real.cos (2 * Real.pi * a - 2 * Real.pi * b) = 1 := by
    rw [Real.cos_sub, hcos, hsin]
    nlinarith [Real.cos_sq_add_sin_sq (2 * Real.pi * b)]
  have h2 : Real.cos (2 * Real.pi * (a - b)) = 1 := by
    rwa [show 2 * Real.pi * (a - b) = 2 * Real.pi * a - 2 * Real.pi * b by ring]
  obtain ⟨m, hm⟩ := (Real.cos_eq_one_iff _).mp h2
  exact ⟨m, by nlinarith [hm, Real.pi_pos]⟩

/-- Two reals all of whose values are integers and which differ by less than `1` are equal. -/
theorem cob_int_eq_of_abs_sub_lt_one {a b : ℝ} (ha : ∃ m : ℤ, a = (m : ℝ))
    (hb : ∃ k : ℤ, b = (k : ℝ)) (h : |a - b| < 1) : a = b := by
  obtain ⟨m, rfl⟩ := ha
  obtain ⟨k, rfl⟩ := hb
  have h1 : ((m - k : ℤ) : ℝ) < 1 := by
    rw [show ((m - k : ℤ) : ℝ) = (m : ℝ) - (k : ℝ) by push_cast; ring]
    exact (abs_lt.mp h).2
  have h2 : (-1 : ℤ) < m - k := by
    have h2' : (-1 : ℝ) < ((m - k : ℤ) : ℝ) := by
      rw [show ((m - k : ℤ) : ℝ) = (m : ℝ) - (k : ℝ) by push_cast; ring]
      exact (abs_lt.mp h).1
    exact_mod_cast h2'
  have h3 : (m - k : ℤ) < 1 := by exact_mod_cast h1
  have h4 : m - k = 0 := by omega
  simp [sub_eq_zero.mp h4]

/-- **Local analytic angle lift.**  Near a point `x₀` of an analytic `S¹`-valued function `z`
there is a real-analytic `ℓ` with `exp (2 π i ℓ x) = z x`. -/
theorem cob_local_lift {z : ℝ → ℂ} {x₀ : ℝ} (hz : AnalyticAt ℝ z x₀)
    (hne : ∀ x, z x ≠ 0) (hn : ∀ x, ‖z x‖ = 1) :
    ∃ ℓ : ℝ → ℝ, AnalyticAt ℝ ℓ x₀ ∧ Complex.exp (2 * Real.pi * ℓ x₀ * Complex.I) = z x₀ ∧
      ∀ᶠ x in 𝓝 x₀, Complex.exp (2 * Real.pi * ℓ x * Complex.I) = z x := by
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have hpiC : (2 : ℂ) * (Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  by_cases hc : z x₀ = -1
  · have hmem : -(z x₀) ∈ slitPlane := by rw [hc, neg_neg]; exact one_mem_slitPlane
    let ℓ : ℝ → ℝ := fun x => (Complex.log (-(z x))).im / (2 * Real.pi) + 1 / 2
    have hℓ : ∀ x, 2 * Real.pi * ℓ x * Complex.I
        = (((Complex.log (-(z x))).im : ℂ) + (Real.pi : ℂ)) * Complex.I := by
      intro x
      dsimp only [ℓ]
      push_cast
      rw [mul_add, ← mul_div_assoc, mul_div_cancel_left₀ _ hpiC]
      ring
    have hgood : ∀ x, -(z x) ∈ slitPlane → Complex.exp (2 * Real.pi * ℓ x * Complex.I) = z x := by
      intro x _
      rw [hℓ x, add_mul, Complex.exp_add, cob_exp_I_im_log (neg_ne_zero.mpr (hne x))
        (by rw [norm_neg, hn x]), Complex.exp_pi_mul_I]
      ring
    have hℓan : AnalyticAt ℝ ℓ x₀ := by
      have hzneg : AnalyticAt ℝ (fun x => -(z x)) x₀ := hz.neg
      have hlog0 : AnalyticAt ℝ (Complex.log : ℂ → ℂ) (-(z x₀)) :=
        (analyticAt_clog hmem).restrictScalars
      have hlog : AnalyticAt ℝ (fun x => Complex.log (-(z x))) x₀ :=
        AnalyticAt.comp (g := Complex.log) (f := fun x => -(z x)) hlog0 hzneg
      have him : AnalyticAt ℝ (fun x => (Complex.log (-(z x))).im) x₀ :=
        (Complex.imCLM.analyticAt _).comp hlog
      exact ((him.div_const).add analyticAt_const)
    refine ⟨ℓ, hℓan, hgood x₀ hmem, ?_⟩
    have hcont : ContinuousAt (fun x => -(z x)) x₀ := hz.continuousAt.neg
    filter_upwards [hcont.preimage_mem_nhds (Complex.isOpen_slitPlane.mem_nhds hmem)] with x hx
    exact hgood x hx
  · have hmem : z x₀ ∈ slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      by_contra hcon
      rw [not_or, not_lt, not_ne_iff] at hcon
      obtain ⟨h1, h2⟩ := hcon
      have h3 : Complex.normSq (z x₀) = 1 := by
        rw [Complex.normSq_eq_norm_sq, hn x₀]; norm_num
      rw [Complex.normSq_apply] at h3
      have h4 : (z x₀).re = -1 := by nlinarith [h1, h2, h3]
      exact hc (Complex.ext (by rw [h4]; simp) (by rw [h2]; simp))
    let ℓ : ℝ → ℝ := fun x => (Complex.log (z x)).im / (2 * Real.pi)
    have hℓ : ∀ x, 2 * Real.pi * ℓ x * Complex.I = ((Complex.log (z x)).im : ℂ) * Complex.I := by
      intro x
      dsimp only [ℓ]
      push_cast
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ hpiC]
    have hgood : ∀ x, z x ∈ slitPlane → Complex.exp (2 * Real.pi * ℓ x * Complex.I) = z x := by
      intro x _
      rw [hℓ x]
      exact cob_exp_I_im_log (hne x) (hn x)
    have hℓan : AnalyticAt ℝ ℓ x₀ := by
      have hlog0 : AnalyticAt ℝ (Complex.log : ℂ → ℂ) (z x₀) :=
        (analyticAt_clog hmem).restrictScalars
      have hlog : AnalyticAt ℝ (fun x => Complex.log (z x)) x₀ :=
        AnalyticAt.comp (g := Complex.log) (f := z) hlog0 hz
      have him : AnalyticAt ℝ (fun x => (Complex.log (z x)).im) x₀ :=
        (Complex.imCLM.analyticAt _).comp hlog
      exact him.div_const
    refine ⟨ℓ, hℓan, hgood x₀ hmem, ?_⟩
    filter_upwards [hz.continuousAt.preimage_mem_nhds
      (Complex.isOpen_slitPlane.mem_nhds hmem)] with x hx
    exact hgood x hx

/-- **Analytic angle lift.**  If `u, v : ℝ → ℝ` are real-analytic on `ℝ` and
`u x ^ 2 + v x ^ 2 = 1` for all `x`, there is a real-analytic `κ : ℝ → ℝ` with
`exp (2 π i κ x) = u x + i v x`. -/
theorem cob_so2_angle_lift (u v : ℝ → ℝ) (hu : AnalyticOnNhd ℝ u Set.univ)
    (hv : AnalyticOnNhd ℝ v Set.univ) (huv : ∀ x, u x ^ 2 + v x ^ 2 = 1) :
    ∃ κ : ℝ → ℝ, AnalyticOnNhd ℝ κ Set.univ ∧
      ∀ x, Complex.exp (2 * Real.pi * κ x * Complex.I) = (u x : ℂ) + (v x : ℂ) * Complex.I := by
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have hpiC : (2 : ℂ) * (Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hz_an : AnalyticOnNhd ℝ (fun x => (u x : ℂ) + (v x : ℂ) * Complex.I) Set.univ := by
    intro x _
    have h1 : AnalyticAt ℝ (fun y : ℝ => ((u y : ℝ) : ℂ)) x :=
      (Complex.ofRealCLM.analyticAt (u x)).comp (hu x trivial)
    have h2 : AnalyticAt ℝ (fun y : ℝ => ((v y : ℝ) : ℂ)) x :=
      (Complex.ofRealCLM.analyticAt (v x)).comp (hv x trivial)
    exact h1.add (h2.mul analyticAt_const)
  have hz_ns : ∀ x, Complex.normSq ((u x : ℂ) + (v x : ℂ) * Complex.I) = 1 := by
    intro x
    rw [Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, zero_add]
    nlinarith [huv x]
  have hz_norm : ∀ x, ‖(u x : ℂ) + (v x : ℂ) * Complex.I‖ = 1 := by
    intro x
    have h : ‖(u x : ℂ) + (v x : ℂ) * Complex.I‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, hz_ns x]
    nlinarith [norm_nonneg ((u x : ℂ) + (v x : ℂ) * Complex.I)]
  have hz_ne : ∀ x, ((u x : ℂ) + (v x : ℂ) * Complex.I) ≠ 0 := by
    intro x hx
    have := hz_norm x
    rw [hx, norm_zero] at this
    exact one_ne_zero this.symm
  let s : ℝ → ℝ := fun x => (u x * deriv v x - v x * deriv u x) / (2 * Real.pi)
  have hs_an : AnalyticOnNhd ℝ s Set.univ := by
    intro x _
    have hdu : AnalyticAt ℝ (deriv u) x := (hu x trivial).deriv
    have hdv : AnalyticAt ℝ (deriv v) x := (hv x trivial).deriv
    have h1 : AnalyticAt ℝ (fun y => u y * deriv v y) x := (hu x trivial).mul hdv
    have h2 : AnalyticAt ℝ (fun y => v y * deriv u y) x := (hv x trivial).mul hdu
    exact (h1.sub h2).div_const
  have hs_c : Continuous s := continuous_iff_continuousAt.mpr fun x => (hs_an x trivial).continuousAt
  have huu : ∀ x, u x * deriv u x + v x * deriv v x = 0 := by
    intro x
    have h3 : deriv (u ^ 2 + v ^ 2) x = 0 := by
      have h : (u ^ 2 + v ^ 2) = fun _ : ℝ => (1 : ℝ) := by
        ext y; simpa using huv y
      rw [h]; simp
    have h4 : deriv (u ^ 2 + v ^ 2) x = 2 * u x * deriv u x + 2 * v x * deriv v x := by
      have hh : HasDerivAt (u ^ 2 + v ^ 2)
          (2 * u x ^ (2 - 1) * deriv u x + 2 * v x ^ (2 - 1) * deriv v x) x :=
        (((hu x trivial).differentiableAt.hasDerivAt).pow 2).add
          (((hv x trivial).differentiableAt.hasDerivAt).pow 2)
      simpa using hh.deriv
    linarith [h3, h4]
  have hzero : ((u 0 : ℂ) + (v 0 : ℂ) * Complex.I) ≠ 0 := hz_ne 0
  set c₀ : ℝ := (Complex.log ((u 0 : ℂ) + (v 0 : ℂ) * Complex.I)).im / (2 * Real.pi) with hc₀
  have hcz : Complex.exp (2 * Real.pi * c₀ * Complex.I) = (u 0 : ℂ) + (v 0 : ℂ) * Complex.I := by
    have h1 : 2 * Real.pi * c₀ * Complex.I
        = ((Complex.log ((u 0 : ℂ) + (v 0 : ℂ) * Complex.I)).im : ℂ) * Complex.I := by
      rw [hc₀]
      push_cast
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ hpiC]
    rw [h1]
    exact cob_exp_I_im_log hzero (hz_norm 0)
  let κ : ℝ → ℝ := fun x => c₀ + ∫ t in (0 : ℝ)..x, s t
  have hκd : ∀ x, HasDerivAt κ (s x) x := by
    intro x
    exact ((hs_c.integral_hasStrictDerivAt 0 x).hasDerivAt).const_add c₀
  let G : ℝ → ℂ := fun y => Complex.exp (-(2 * Real.pi * κ y * Complex.I))
    * ((u y : ℂ) + (v y : ℂ) * Complex.I)
  have hOD : ∀ x, HasDerivAt G 0 x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => (2 : ℂ) * (Real.pi : ℂ) * ((κ y : ℝ) : ℂ))
        ((2 : ℂ) * (Real.pi : ℂ) * ((s x : ℝ) : ℂ)) x :=
      ((hκd x).ofReal_comp).const_mul ((2 : ℂ) * (Real.pi : ℂ))
    have h2 : HasDerivAt
        (fun y : ℝ => (2 : ℂ) * (Real.pi : ℂ) * ((κ y : ℝ) : ℂ) * Complex.I)
        ((2 : ℂ) * (Real.pi : ℂ) * ((s x : ℝ) : ℂ) * Complex.I) x := h1.mul_const Complex.I
    have h3 : HasDerivAt
        (fun y : ℝ => -((2 : ℂ) * (Real.pi : ℂ) * ((κ y : ℝ) : ℂ) * Complex.I))
        (-((2 : ℂ) * (Real.pi : ℂ) * ((s x : ℝ) : ℂ) * Complex.I)) x := h2.neg
    have h4 : HasDerivAt
        (fun y : ℝ => Complex.exp (-((2 : ℂ) * (Real.pi : ℂ) * ((κ y : ℝ) : ℂ) * Complex.I)))
        (Complex.exp (-((2 : ℂ) * (Real.pi : ℂ) * ((κ x : ℝ) : ℂ) * Complex.I))
          * (-((2 : ℂ) * (Real.pi : ℂ) * ((s x : ℝ) : ℂ) * Complex.I))) x :=
      (Complex.hasDerivAt_exp (x := -((2 : ℂ) * (Real.pi : ℂ) * ((κ x : ℝ) : ℂ) * Complex.I))).comp
        x h3
    have h5 : HasDerivAt (fun y : ℝ => (u y : ℂ) + (v y : ℂ) * Complex.I)
        (((deriv u x : ℝ) : ℂ) + ((deriv v x : ℝ) : ℂ) * Complex.I) x :=
      (((hu x trivial).differentiableAt.hasDerivAt).ofReal_comp).add
        ((((hv x trivial).differentiableAt.hasDerivAt).ofReal_comp).mul_const Complex.I)
    have h6 := h4.mul h5
    have hval : Complex.exp (-((2 : ℂ) * (Real.pi : ℂ) * ((κ x : ℝ) : ℂ) * Complex.I))
            * (-((2 : ℂ) * (Real.pi : ℂ) * ((s x : ℝ) : ℂ) * Complex.I))
            * ((u x : ℂ) + (v x : ℂ) * Complex.I)
          + Complex.exp (-((2 : ℂ) * (Real.pi : ℂ) * ((κ x : ℝ) : ℂ) * Complex.I))
            * (((deriv u x : ℝ) : ℂ) + ((deriv v x : ℝ) : ℂ) * Complex.I) = 0 := by
      have hsx : 2 * Real.pi * s x = u x * deriv v x - v x * deriv u x := by
        dsimp only [s]; field_simp
      have hVr : u x * deriv u x + v x * deriv v x = 0 := huu x
      have hUr : u x ^ 2 + v x ^ 2 - 1 = 0 := by linarith [huv x]
      have hdu' : deriv u x = -(2 * Real.pi * s x) * v x := by
        linear_combination (v x) * hsx + (u x) * hVr - (deriv u x) * hUr
      have hdv' : deriv v x = (2 * Real.pi * s x) * u x := by
        linear_combination -(u x) * hsx + (v x) * hVr - (deriv v x) * hUr
      have hDU : ((deriv u x : ℝ) : ℂ)
          = -(((2 * Real.pi * s x : ℝ)) : ℂ) * ((v x : ℝ) : ℂ) := by
        rw [hdu']; push_cast; ring
      have hDV : ((deriv v x : ℝ) : ℂ)
          = (((2 * Real.pi * s x : ℝ)) : ℂ) * ((u x : ℝ) : ℂ) := by
        rw [hdv']; push_cast; ring
      have hcoef : (2 : ℂ) * (Real.pi : ℂ) * ((s x : ℝ) : ℂ)
          = (((2 * Real.pi * s x : ℝ)) : ℂ) := by push_cast; ring
      have hI : Complex.I * Complex.I + 1 = 0 := by rw [Complex.I_mul_I]; ring
      rw [hcoef, hDU, hDV]
      linear_combination (-(Complex.exp (-((2 : ℂ) * (Real.pi : ℂ) * ((κ x : ℝ) : ℂ) * Complex.I))
        * ((((2 * Real.pi * s x : ℝ)) : ℂ) * ((v x : ℝ) : ℂ)))) * hI
    rw [hval] at h6
    exact h6
  have hk0 : κ 0 = c₀ := by
    dsimp only [κ]
    simp
  have hG0 : G 0 = 1 := by
    dsimp only [G]
    rw [hk0]
    rw [show ((u 0 : ℂ) + (v 0 : ℂ) * Complex.I) = Complex.exp (2 * Real.pi * c₀ * Complex.I)
      from hcz.symm]
    rw [← Complex.exp_add]
    simp
  have hconst : ∀ x, G x = G 0 := fun x =>
    is_const_of_deriv_eq_zero (fun y => (hOD y).differentiableAt) (fun y => (hOD y).deriv) x 0
  have hfinal : ∀ x, Complex.exp (2 * Real.pi * κ x * Complex.I) = (u x : ℂ) + (v x : ℂ) * Complex.I := by
    intro x
    have hx : G x = 1 := by rw [hconst x, hG0]
    dsimp only [G] at hx
    have hBA : Complex.exp (2 * Real.pi * κ x * Complex.I)
        * Complex.exp (-(2 * Real.pi * κ x * Complex.I)) = 1 := by
      rw [← Complex.exp_add]
      simp
    calc Complex.exp (2 * Real.pi * κ x * Complex.I)
        = Complex.exp (2 * Real.pi * κ x * Complex.I)
            * (Complex.exp (-(2 * Real.pi * κ x * Complex.I)) * ((u x : ℂ) + (v x : ℂ) * Complex.I)) := by
          rw [hx, mul_one]
      _ = (Complex.exp (2 * Real.pi * κ x * Complex.I)
            * Complex.exp (-(2 * Real.pi * κ x * Complex.I))) * ((u x : ℂ) + (v x : ℂ) * Complex.I) := by
          ring
      _ = ((u x : ℂ) + (v x : ℂ) * Complex.I) := by rw [hBA, one_mul]
  refine ⟨κ, ?_, hfinal⟩
  have hcκ : Continuous κ := continuous_iff_continuousAt.mpr fun x => (hκd x).differentiableAt.continuousAt
  intro x₀ _
  obtain ⟨ℓ, hℓan, hℓx₀, hℓev⟩ := cob_local_lift (hz_an x₀ trivial) hz_ne hz_norm
  have hint : ∀ᶠ x in 𝓝 x₀, ∃ k : ℤ, κ x - ℓ x = (k : ℝ) := by
    filter_upwards [hℓev] with x hlx
    exact cob_exp_two_pi_sub_int (by rw [hfinal x, hlx])
  have hd : ∃ m : ℤ, κ x₀ - ℓ x₀ = (m : ℝ) :=
    cob_exp_two_pi_sub_int (by rw [hfinal x₀, hℓx₀])
  obtain ⟨m, hm⟩ := hd
  have hclose : ∀ᶠ x in 𝓝 x₀, |(κ x - ℓ x) - (κ x₀ - ℓ x₀)| < 1 := by
    have hcont : ContinuousAt (fun x => κ x - ℓ x) x₀ := hcκ.continuousAt.sub hℓan.continuousAt
    have h3 : ∀ᶠ x in 𝓝 x₀, dist (κ x - ℓ x) (κ x₀ - ℓ x₀) < (1 : ℝ) :=
      Metric.tendsto_nhds.mp hcont.tendsto 1 one_pos
    filter_upwards [h3] with x hx
    rwa [Real.dist_eq] at hx
  have hev : ∀ᶠ x in 𝓝 x₀, κ x - ℓ x = (m : ℝ) := by
    filter_upwards [hint, hclose] with x hx hcl
    obtain ⟨k, hk⟩ := hx
    have hcl' : |(κ x - ℓ x) - (m : ℝ)| < 1 := by rw [← hm]; exact hcl
    exact cob_int_eq_of_abs_sub_lt_one ⟨k, hk⟩ ⟨m, rfl⟩ hcl'
  exact (hℓan.add analyticAt_const).congr (hev.mono fun x hx => by
    show ℓ x + (m : ℝ) = κ x
    linarith [hx])

end

end Work.TMComp.RedProj
