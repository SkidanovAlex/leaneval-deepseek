import Mathlib
import Submission.Work.Smooth.SphereJordan.planeIndex

/-!
# The winding number of a closed plane curve: vanishing at infinity

From the index theory of `planeIndex.lean` we extract the property of the winding number
`windNumber γ z` of a `2π`-periodic continuous plane curve `γ` around a point `z` which gives the
non-emptiness of the "outside" of the curve:

* `windNumber_eq_zero_of_norm_gt` — the winding number vanishes at points farther from the origin
  than the whole curve.

The key ingredient is `loopIndex_eq_zero_of_avoids_ray`: a closed path avoiding a ray from the
origin has index `0`.  Its proof rotates the ray to the negative real axis, where `Complex.log` is
a continuous lift of `exp` which returns to its starting value at the end of the loop.
-/

noncomputable section

open Set
open Classical

namespace Work.Smooth.SphereJordan

/-- `-w` lies in the slit plane exactly when `w` is not a nonnegative real number. -/
theorem neg_mem_slitPlane_iff {w : ℂ} :
    -w ∈ Complex.slitPlane ↔ ∀ r : ℝ, 0 ≤ r → w ≠ (r : ℂ) := by
  constructor
  · intro h r hr hw
    rw [hw] at h
    rw [show (-((r : ℂ)) : ℂ) = ((-r : ℝ) : ℂ) by push_cast; ring] at h
    rw [Complex.ofReal_mem_slitPlane] at h
    exact absurd h (not_lt.mpr (neg_nonpos.mpr hr))
  · intro h
    by_contra hcon
    rw [Complex.slitPlane, Set.mem_setOf_eq, not_or] at hcon
    obtain ⟨hre, him⟩ := hcon
    have him' : w.im = 0 := by
      have h0 : (-w).im = 0 := not_ne_iff.mp him
      rw [Complex.neg_im] at h0
      exact neg_eq_zero.mp h0
    have hre' : 0 ≤ w.re := by
      have h0 : (-w).re ≤ 0 := not_lt.mp hre
      rw [Complex.neg_re] at h0
      exact neg_nonpos.mp h0
    refine h w.re hre' ?_
    refine Complex.ext ?_ ?_
    · simp only [Complex.ofReal_re]
    · simp only [Complex.ofReal_im, him']

variable {c : C(unitInterval, ℂ)}

/-- A constant closed path has index `0`. -/
theorem loopIndex_const (a : ℂ) (ha : a ≠ 0) :
    loopIndex (ContinuousMap.const unitInterval a) = 0 := by
  have hne : ∀ t : unitInterval, (ContinuousMap.const unitInterval a) t ≠ 0 := fun _ => ha
  have hloop : (ContinuousMap.const unitInterval a) 0 = (ContinuousMap.const unitInterval a) 1 := rfl
  refine loopIndex_eq_zero_of_lift _ hne hloop
    ⟨fun _ => Complex.log a, continuous_const⟩ (fun _ => Complex.exp_log ha) rfl

/-- **Two closed paths whose pointwise quotient lies in the slit plane have the same index.** -/
theorem loopIndex_eq_of_pointwise_div_mem_slitPlane (u v : C(unitInterval, ℂ))
    (hu : ∀ t, u t ≠ 0) (hv : ∀ t, v t ≠ 0) (hlu : u 0 = u 1) (hlv : v 0 = v 1)
    (hdiv : ∀ t, u t / v t ∈ Complex.slitPlane) : loopIndex u = loopIndex v := by
  let w : C(unitInterval, ℂ) := ⟨fun t => u t / v t, u.continuous.div v.continuous hv⟩
  have hw : ∀ t, w t ≠ 0 := fun t => div_ne_zero (hu t) (hv t)
  have hwl : w 0 = w 1 := by
    show u 0 / v 0 = u 1 / v 1
    rw [hlu, hlv]
  have hslit : ∀ t, w t ∈ Complex.slitPlane := fun t => hdiv t
  have hzero : loopIndex w = 0 := loopIndex_eq_zero_of_slitPlane w hw hwl hslit
  have hmul : loopIndex (w * v) = loopIndex w + loopIndex v := loopIndex_mul w v hw hv hwl hlv
  have hl2 : (w * v) 0 = (w * v) 1 := by
    simp only [ContinuousMap.mul_apply]; rw [hwl, hlv]
  have hcongr : loopIndex u = loopIndex (w * v) :=
    loopIndex_congr (fun t => by
      show u t = u t / v t * v t
      rw [div_mul_cancel₀ _ (hv t)]) hu (fun t => mul_ne_zero (hw t) (hv t)) hlu hl2
  rw [hcongr, hmul, hzero, zero_add]

/-- **A closed path avoiding the ray `{r * ω : r ≥ 0}` (`ω ≠ 0`) has index `0`.**

Rotating by `ω` turns the avoided ray into the positive real axis, and negating turns it into the
slit plane `ℂ \ (-∞,0]`, on which `Complex.log` is a continuous lift of `exp` which returns to its
starting value. -/
theorem loopIndex_eq_zero_of_avoids_ray (c : C(unitInterval, ℂ)) (hc : ∀ t, c t ≠ 0)
    (hloop : c 0 = c 1) {ω : ℂ} (hω : ω ≠ 0)
    (hav : ∀ (t : unitInterval) (r : ℝ), 0 ≤ r → c t ≠ (r : ℂ) * ω) : loopIndex c = 0 := by
  have hslit : ∀ t : unitInterval, -(c t / ω) ∈ Complex.slitPlane := by
    intro t
    refine (neg_mem_slitPlane_iff).mpr ?_
    intro r hr hrt
    refine hav t r hr ?_
    have h1 : c t / ω * ω = (r : ℂ) * ω := by rw [hrt]
    rwa [div_mul_cancel₀ _ hω] at h1
  refine loopIndex_eq_zero_of_lift c hc hloop
    ⟨fun t => Complex.log (-(c t / ω)) + Complex.log (-ω), ?_⟩ ?_ ?_
  · have hcont : Continuous fun t : unitInterval => -(c t / ω) := by fun_prop
    exact (hcont.clog hslit).add continuous_const
  · intro t
    show Complex.exp (Complex.log (-(c t / ω)) + Complex.log (-ω)) = c t
    rw [Complex.exp_add, Complex.exp_log (neg_ne_zero.mpr (div_ne_zero (hc t) hω)),
      Complex.exp_log (neg_ne_zero.mpr hω)]
    field_simp
  · show Complex.log (-(c 1 / ω)) + Complex.log (-ω) = Complex.log (-(c 0 / ω)) + Complex.log (-ω)
    rw [hloop]

/-- The closed path on `[0,1]` associated with a `2π`-periodic curve. -/
noncomputable def curveLoop (γ : ℝ → ℂ) (hγ : Continuous γ) : C(unitInterval, ℂ) :=
  ⟨fun t => γ (2 * Real.pi * t), hγ.comp (by fun_prop)⟩

/-- The **winding number of the `2π`-periodic curve `γ` around the point `z`**. -/
noncomputable def windNumber (γ : ℝ → ℂ) (hγ : Continuous γ) (z : ℂ) : ℤ :=
  loopIndex (curveLoop (fun t => γ t - z) (hγ.sub continuous_const))

/-- **The winding number vanishes far away from a bounded curve.** -/
theorem windNumber_eq_zero_of_norm_gt {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) {R : ℝ} (hR : ∀ t : ℝ, ‖γ t‖ ≤ R) {z : ℂ}
    (hz : R < ‖z‖) : windNumber γ hγ z = 0 := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz
    linarith [norm_nonneg (γ 0), hR 0]
  have hloop : (curveLoop (fun t => γ t - z) (hγ.sub continuous_const)) 0
      = (curveLoop (fun t => γ t - z) (hγ.sub continuous_const)) 1 := by
    have h1 : γ (2 * Real.pi * ((1 : unitInterval) : ℝ)) = γ 0 := by
      simpa using hper 0
    have h0 : 2 * Real.pi * ((0 : unitInterval) : ℝ) = 0 := by simp
    show γ (2 * Real.pi * ((0 : unitInterval) : ℝ)) - z
      = γ (2 * Real.pi * ((1 : unitInterval) : ℝ)) - z
    rw [h0, h1]
  have hne : ∀ t : unitInterval, (curveLoop (fun t => γ t - z) (hγ.sub continuous_const)) t ≠ 0 := by
    intro t
    show γ (2 * Real.pi * (t : ℝ)) - z ≠ 0
    intro h
    have h1 : γ (2 * Real.pi * (t : ℝ)) = z := sub_eq_zero.mp h
    have h2 := hR (2 * Real.pi * (t : ℝ))
    rw [h1] at h2
    linarith [h2, hz]
  refine loopIndex_eq_zero_of_avoids_ray _ hne hloop hz0 ?_
  intro t r hr
  show γ (2 * Real.pi * (t : ℝ)) - z ≠ (r : ℂ) * z
  intro h
  have hkey : γ (2 * Real.pi * (t : ℝ)) = (1 + (r : ℂ)) * z := by linear_combination h
  have hkey' : γ (2 * Real.pi * (t : ℝ)) = ((1 + r : ℝ) : ℂ) * z := by
    rw [show ((1 + r : ℝ) : ℂ) = (1 : ℂ) + (r : ℂ) by push_cast; ring]
    exact hkey
  have h2 := hR (2 * Real.pi * (t : ℝ))
  rw [hkey', norm_mul] at h2
  have hr1 : (0 : ℝ) ≤ 1 + r := by linarith
  have hn : (1 : ℝ) ≤ ‖((1 + r : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr1]
    linarith
  nlinarith [norm_nonneg z, hz, hn, h2]



/-! ## Independence of the base point

The key algebraic fact is that the Möbius map `z ↦ (z - y)/(z - x)` carries the closed segment
from `x` to `y` onto the negative real axis; its inverse carries the nonpositive real axis back
onto the segment.  Hence the quotient of two closed paths `γ - y` and `γ - x` lies in the slit
plane exactly when `γ` misses the segment from `x` to `y`, and then the two indices agree by
`loopIndex_eq_of_pointwise_div_mem_slitPlane`. -/

/-- If `z` does not lie on the closed segment from `x` to `y`, then the quotient
`(z - y)/(z - x)` lies in the slit plane `ℂ \ (-∞,0]`. -/
theorem div_sub_mem_slitPlane_of_notMem_segment {x y z : ℂ}
    (h : ∀ s : ℝ, s ∈ Set.Icc 0 1 → z ≠ (1 - s) * x + s * y) :
    (z - y) / (z - x) ∈ Complex.slitPlane := by
  by_contra hcon
  rw [Complex.slitPlane, Set.mem_setOf_eq, not_or] at hcon
  obtain ⟨hre, him⟩ := hcon
  have hre' : ((z - y) / (z - x)).re ≤ 0 := not_lt.mp hre
  have him' : ((z - y) / (z - x)).im = 0 := not_ne_iff.mp him
  set w : ℂ := (z - y) / (z - x) with hwdef
  have hwre : w.re ≤ 0 := hre'
  have hwim : w.im = 0 := him'
  have hw : w = -(((-w.re) : ℝ) : ℂ) := by
    refine Complex.ext ?_ ?_
    · simp only [Complex.neg_re, Complex.ofReal_re, neg_neg]
    · simp only [Complex.neg_im, Complex.ofReal_im, hwim, neg_zero]
  set r : ℝ := -w.re with hrdef
  have hwr : w = -((r : ℂ)) := hw
  have hr : 0 ≤ r := by rw [hrdef]; linarith
  rcases eq_or_lt_of_le hr with hr0 | hrpos
  · -- `r = 0`, so `w = 0`, hence `z = y` lies on the segment
    have hw0 : w = 0 := by rw [hwr, ← hr0]; simp
    have hzy : z = y := by
      have hmul : w * (z - x) = z - y := by
        rw [hwdef]; exact div_mul_cancel₀ _ (sub_ne_zero.mpr (by rintro rfl; exact h 0 (by norm_num) (by simp)))
      rw [hw0, zero_mul] at hmul
      exact sub_eq_zero.mp hmul.symm
    refine h 1 (by norm_num) ?_
    rw [hzy]; simp
  · -- `r > 0`: solving gives `z = (1-s) x + s y` with `s = 1/(1+r)`
    have hzx : z ≠ x := by
      rintro rfl
      exact h 0 (by norm_num) (by simp)
    have hmul : w * (z - x) = z - y := by
      rw [hwdef]; exact div_mul_cancel₀ _ (sub_ne_zero.mpr hzx)
    have hkey : ((1 : ℂ) + (r : ℂ)) * z = y + (r : ℂ) * x := by
      have h1 : w * (z - x) = z - y := hmul
      rw [hwr] at h1
      linear_combination -h1
    have hr1 : (0 : ℝ) < 1 + r := by linarith
    have h1 : ((1 : ℂ) + (r : ℂ)) = ((1 + r : ℝ) : ℂ) := by
      rw [Complex.ofReal_add, Complex.ofReal_one]
    have hsub : ((1 : ℂ) + (r : ℂ)) * (z - x) = y - x := by
      rw [mul_sub, hkey]; ring
    have hne : ((1 : ℂ) + (r : ℂ)) ≠ 0 := by rw [h1]; exact_mod_cast ne_of_gt hr1
    have hcoef : (((1 : ℂ) + (r : ℂ))⁻¹) = ((1 / (1 + r) : ℝ) : ℂ) := by
      rw [h1, ← Complex.ofReal_inv, one_div]
    have hzx' : z - x = ((1 / (1 + r) : ℝ) : ℂ) * (y - x) := by
      rw [← hcoef]
      calc z - x = ((1 : ℂ) + (r : ℂ))⁻¹ * (((1 : ℂ) + (r : ℂ)) * (z - x)) :=
            (inv_mul_cancel_left₀ hne _).symm
        _ = ((1 : ℂ) + (r : ℂ))⁻¹ * (y - x) := by rw [hsub]
    have hmain : z = (1 - ((1 / (1 + r) : ℝ) : ℂ)) * x + ((1 / (1 + r) : ℝ) : ℂ) * y := by
      calc z = x + (z - x) := by ring
        _ = x + ((1 / (1 + r) : ℝ) : ℂ) * (y - x) := by rw [hzx']
        _ = (1 - ((1 / (1 + r) : ℝ) : ℂ)) * x + ((1 / (1 + r) : ℝ) : ℂ) * y := by ring
    refine h (1 / (1 + r)) ?_ hmain
    refine ⟨le_of_lt (div_pos one_pos hr1), ?_⟩
    rw [div_le_one₀ hr1]
    linarith

/-- **The winding number does not change when the base point is moved along a segment which does
not meet the curve.**  Equivalently, the winding number is locally constant on the complement of
the trace of `γ`. -/
theorem windNumber_eq_of_segment {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi))
    {x y : ℂ} (hx : ∀ t : ℝ, γ t ≠ x) (hy : ∀ t : ℝ, γ t ≠ y)
    (hseg : ∀ (t : ℝ) (s : ℝ), s ∈ Set.Icc 0 1 → γ t ≠ (1 - s) * x + s * y) :
    windNumber γ hγ x = windNumber γ hγ y := by
  have hloop : ∀ z : ℂ, (curveLoop (fun t => γ t - z) (hγ.sub continuous_const)) 0
      = (curveLoop (fun t => γ t - z) (hγ.sub continuous_const)) 1 := by
    intro z
    show γ (2 * Real.pi * ((0 : unitInterval) : ℝ)) - z
      = γ (2 * Real.pi * ((1 : unitInterval) : ℝ)) - z
    have h1 : γ (2 * Real.pi * ((1 : unitInterval) : ℝ)) = γ 0 := by simpa using hper 0
    have h0 : 2 * Real.pi * ((0 : unitInterval) : ℝ) = 0 := by simp
    rw [h0, h1]
  have hne : ∀ (z : ℂ), (∀ t : ℝ, γ t ≠ z) →
      ∀ t : unitInterval, (curveLoop (fun t => γ t - z) (hγ.sub continuous_const)) t ≠ 0 := by
    intro z hz t
    show γ (2 * Real.pi * (t : ℝ)) - z ≠ 0
    exact sub_ne_zero.mpr (hz _)
  have hslit : ∀ t : unitInterval,
      (curveLoop (fun t => γ t - y) (hγ.sub continuous_const)) t
        / (curveLoop (fun t => γ t - x) (hγ.sub continuous_const)) t ∈ Complex.slitPlane := by
    intro t
    show (γ (2 * Real.pi * (t : ℝ)) - y) / (γ (2 * Real.pi * (t : ℝ)) - x) ∈ Complex.slitPlane
    refine div_sub_mem_slitPlane_of_notMem_segment ?_
    intro s hs
    exact hseg (2 * Real.pi * (t : ℝ)) s hs
  have h := loopIndex_eq_of_pointwise_div_mem_slitPlane
    (curveLoop (fun t => γ t - y) (hγ.sub continuous_const))
    (curveLoop (fun t => γ t - x) (hγ.sub continuous_const))
    (hne y hy) (hne x hx) (hloop y) (hloop x) hslit
  exact h.symm


/-- **Explicit local constancy of the winding number.**

If `ε` is a positive lower bound for the distance of the curve `γ` from `z`, then the winding
number about every point `w` with `‖w - z‖ < ε` agrees with the one about `z`.  (In particular the
winding number is locally constant on the complement of the trace, taking `ε` to be half the
distance from `z` to the compact trace.) -/
theorem windNumber_eq_of_norm_lt {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) {z w : ℂ} {ε : ℝ}
    (hz : ∀ t : ℝ, γ t ≠ z) (hw : ∀ t : ℝ, γ t ≠ w) (hzw : ‖w - z‖ < ε)
    (hε : ∀ t : ℝ, ε ≤ ‖γ t - z‖) :
    windNumber γ hγ z = windNumber γ hγ w := by
  refine windNumber_eq_of_segment hγ hper hz hw ?_
  intro t s hs hcon
  have h1 : γ t - z = s * (w - z) := by rw [hcon]; ring
  have h2 : ‖γ t - z‖ = s * ‖w - z‖ := by
    rw [h1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
  have h3 : s * ‖w - z‖ ≤ ‖w - z‖ := by
    have := norm_nonneg (w - z)
    nlinarith [hs.1, hs.2]
  linarith [hε t, h2 ▸ h3]

end Work.Smooth.SphereJordan
