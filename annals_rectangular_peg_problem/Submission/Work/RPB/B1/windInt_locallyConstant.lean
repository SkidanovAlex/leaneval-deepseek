import Mathlib
import Submission.Work.RPB.B1.AreaPosDefs
import Submission.Work.RPB.B1.windInt_continuousOn

/-!
# `windInt` is locally constant off the curve

For a `C¹`, `2π`-periodic closed plane curve `u` and a point `q` off `u` we prove

`Work.RPB.B1.windInt_locallyConstant` : the winding integral

`windInt u q = (1/2π) ∮_0^{2π} Im (u'(t)/(u(t) - q))`

is constant on a neighbourhood of `q` (intersected with the complement of `Set.range u`).

The two ingredients are independent and proved here from scratch:

* `windInt_integrality_of_notMem` : `windInt u q` is an **integer**.  This is the classical lifting
  computation, done without any covering-space machinery: the primitive `Φ s = ∫_0^s u'/(u-q)`
  satisfies `HasDerivAt Φ (u' s / (u s - q)) s`, hence
  `s ↦ exp (-Φ s) * (u s - q)` has vanishing derivative and is constant.  At `s = 2π`
  periodicity gives `exp (Φ (2π)) = 1`, so `Φ (2π) = n · 2π i` (`Complex.exp_eq_one_iff`), and
  taking imaginary parts (commuting `Integral` with the continuous linear map `Complex.imCLM`)
  yields `windInt u q = n`.

  This route deliberately avoids `Submission.Work.RPB.B1.windInt_lift`: the integrality statement
  is reproved here without the `windPhase`/`windDir` lifting theory, so that the present file
  depends only on `AreaPosDefs` and `windInt_continuousOn`.

* `windInt_continuousOn` (in `Submission.Work.RPB.B1.windInt_continuousOn`) : continuity of
  `windInt u` on `(Set.range u)ᶜ`.

A continuous integer-valued function on a metric space is locally constant: on the ball of radius
`δ` (from `Metric.continuousWithinAt_iff` for `ε = 1/2`) about `q` the value changes by less than
`1/2`, but two integers differing by less than `1/2` are equal.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace Work.RPB.B1

/-- **Integrality of the winding number.** For a `C¹`, `2π`-periodic curve `u` and a point `q` off
`u`, the integral winding number `windInt u q` is an integer.

The proof uses the primitive `Φ s = ∫_0^s u'/(u - q)` and the fact that
`s ↦ exp (-Φ s) * (u s - q)` is constant, so that `exp (Φ (2π)) = 1` by periodicity. -/
theorem windInt_integrality_of_notMem (u : ℝ → ℂ) (hu : ContDiff ℝ 1 u)
    (hper : ∀ t, u (t + 2 * Real.pi) = u t) {q : ℂ} (hq : q ∉ Set.range u) :
    ∃ k : ℤ, windInt u q = (k : ℝ) := by
  have hq' : ∀ t, u t ≠ q := fun t h => hq ⟨t, h⟩
  -- the winding integrand `w`
  set w : ℝ → ℂ := fun t => deriv u t / (u t - q) with hw
  have hwcont : Continuous w := by
    rw [hw]
    exact ((hu.continuous_deriv (by norm_num)).div (hu.continuous.sub continuous_const))
      (fun t => sub_ne_zero.mpr (hq' t))
  have hwq : ∀ s, w s * (u s - q) = deriv u s := by
    intro s
    rw [hw]
    exact div_mul_cancel₀ _ (sub_ne_zero.mpr (hq' s))
  -- its primitive `Φ`
  set Phi : ℝ → ℂ := fun s => ∫ t in (0 : ℝ)..s, w t with hPhidef
  have hPhid : ∀ s, HasDerivAt Phi (w s) s := fun s =>
    intervalIntegral.integral_hasDerivAt_right (hwcont.intervalIntegrable 0 s)
      (hwcont.stronglyMeasurableAtFilter volume (nhds s)) hwcont.continuousAt
  -- the integrating factor `s ↦ exp (-Φ s) * (u s - q)` has vanishing derivative
  have hFd : ∀ s, HasDerivAt (fun s => Complex.exp (-(Phi s)) * (u s - q)) 0 s := by
    intro s
    have hg : HasDerivAt (fun x : ℝ => Complex.exp (-(Phi x)))
        (Complex.exp (-(Phi s)) * (-(w s))) s := (hPhid s).neg.cexp
    have hu' : HasDerivAt u (deriv u s) s := ((hu.differentiable (by norm_num)) s).hasDerivAt
    have hsub : HasDerivAt (u - fun x : ℝ => q) (deriv u s) s := by
      simpa only [sub_zero] using hu'.sub (hasDerivAt_const s q)
    have h2 := hg.mul hsub
    convert h2 using 1
    simp only [Pi.sub_apply]
    rw [← hwq s]
    ring
  have hconst : ∀ s, Complex.exp (-(Phi s)) * (u s - q) = u 0 - q := by
    intro s
    have hdiff : Differentiable ℝ (fun s => Complex.exp (-(Phi s)) * (u s - q)) :=
      fun s => (hFd s).differentiableAt
    have hderiv0 : ∀ s, deriv (fun s => Complex.exp (-(Phi s)) * (u s - q)) s = 0 :=
      fun s => (hFd s).deriv
    have := is_const_of_deriv_eq_zero hdiff hderiv0 s 0
    simpa [hPhidef] using this
  -- periodicity: `exp (Φ (2π)) = 1`
  have hA : Complex.exp (Phi (2 * Real.pi)) = 1 := by
    have h := hconst (2 * Real.pi)
    rw [show u (2 * Real.pi) = u 0 from by simpa using hper 0] at h
    have hne : u 0 - q ≠ 0 := sub_ne_zero.mpr (hq' 0)
    have h1 : Complex.exp (-(Phi (2 * Real.pi))) = 1 :=
      mul_right_cancel₀ hne (by rw [h, one_mul])
    rw [Complex.exp_neg] at h1
    exact inv_eq_one.mp h1
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hA
  refine ⟨n, ?_⟩
  -- the imaginary part of the primitive is the winding integral
  have hIm : (Phi (2 * Real.pi)).im = ∫ t in (0 : ℝ)..(2 * Real.pi), (w t).im := by
    have hcomm := ContinuousLinearMap.intervalIntegral_comp_comm (𝕜 := ℝ) Complex.imCLM
      (hwcont.intervalIntegrable (μ := MeasureTheory.volume) 0 (2 * Real.pi))
    simp only [Complex.imCLM_apply] at hcomm
    rw [hPhidef]
    exact hcomm.symm
  have hnim : (∫ t in (0 : ℝ)..(2 * Real.pi), (w t).im) = (n : ℝ) * (2 * Real.pi) := by
    rw [← hIm, hn, Complex.mul_im]
    simp
  have hkey : ∫ t in (0 : ℝ)..(2 * Real.pi), (deriv u t / (u t - q)).im
      = (n : ℝ) * (2 * Real.pi) := by
    simpa [hw] using hnim
  rw [windInt, hkey]
  field_simp

theorem windInt_locallyConstant (u : ℝ → ℂ) (hu : ContDiff ℝ 1 u)
    (hper : ∀ t, u (t + 2 * Real.pi) = u t) {q : ℂ} (hq : q ∉ Set.range u) :
    ∃ δ > 0, ∀ q' : ℂ, q' ∉ Set.range u → dist q' q < δ →
      Work.RPB.B1.windInt u q' = Work.RPB.B1.windInt u q := by
  have hcont : ContinuousOn (windInt u) ((Set.range u)ᶜ) := windInt_continuousOn u hu hper
  -- on a small ball the winding numbers differ by less than `1/2`
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousWithinAt_iff.mp (hcont q hq) (1/2) (by norm_num)
  refine ⟨δ, hδ, fun q' hq' hdist => ?_⟩
  -- but they are both integers, so they are equal
  obtain ⟨k, hk⟩ := windInt_integrality_of_notMem u hu hper hq
  obtain ⟨k', hk'⟩ := windInt_integrality_of_notMem u hu hper hq'
  have hd : dist (windInt u q') (windInt u q) < 1/2 := hδ' hq' hdist
  have hkk : k' = k := by
    by_contra hne
    have h1 : (1 : ℝ) ≤ |(k' : ℝ) - (k : ℝ)| := by
      have h2 := Int.one_le_abs (sub_ne_zero.mpr hne)
      calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
        _ ≤ ((|k' - k| : ℤ) : ℝ) := by exact_mod_cast h2
        _ = |(k' : ℝ) - (k : ℝ)| := by push_cast; rw [abs_sub_comm]
    rw [Real.dist_eq, hk', hk] at hd
    linarith
  rw [hk', hk, hkk]

end Work.RPB.B1
