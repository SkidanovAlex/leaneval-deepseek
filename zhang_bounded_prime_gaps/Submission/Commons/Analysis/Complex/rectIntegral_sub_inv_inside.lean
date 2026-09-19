import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Commons.Analysis.Complex.re_one_sub_mirror

open Complex MeasureTheory intervalIntegral
open scoped Real Interval Topology ComplexConjugate
set_option autoImplicit false
noncomputable section

namespace Commons.Analysis.Complex

/-! # Residue of `(s - u)⁻¹` over a rectangle boundary

We prove that the integral of `(s-u)⁻¹` along the (counterclockwise) boundary of an
axis-parallel rectangle equals `2πi` when `u` is strictly inside the rectangle.

The boundary integral is decomposed into its four side integrals.  On each side the
integrand is the derivative (in the side parameter) of `Complex.log` of the side point
minus `u`.  Three of the sides lie entirely in `Complex.slitPlane`.  The left side
crosses the branch cut of the principal logarithm at the point directly to the left of
`u`; for that side we integrate the reflected function instead, which lies in the
slitPlane, and then relate the logarithms of the reflected corners to the logarithms of
the original corners (a `+πi`/`-πi` shift, which adds up to `2πi` around the rectangle). -/

/-- Derivative of the real-affine map `t ↦ α * t + β` from `ℝ` to `ℂ`. -/
lemma rectInt_hasDerivAt_affine_sub (α β : ℂ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => α * (t : ℂ) + β) α x := by
  have hlin : HasDerivAt (fun z : ℂ => α * z) α (x : ℂ) := by
    simpa using (hasDerivAt_id (x : ℂ)).const_mul α
  exact (HasDerivAt.comp_ofReal hlin).add_const β

/-- Derivative of `Complex.log` along a horizontal side `x ↦ x + r * I - u`
(the imaginary part `r - u.im` is constant and nonzero). -/
lemma rectInt_hasDerivAt_log_horiz {r : ℝ} {u : ℂ} (hr : r ≠ u.im) :
    ∀ x : ℝ, HasDerivAt (fun x : ℝ => Complex.log (((x : ℂ) + (r : ℂ) * Complex.I) - u))
      ((((x : ℂ) + (r : ℂ) * Complex.I) - u)⁻¹) x := by
  intro x
  have hF : HasDerivAt (fun x : ℝ => ((x : ℂ) + (r : ℂ) * Complex.I) - u) 1 x := by
    have h := (rectInt_hasDerivAt_affine_sub (1 : ℂ) ((r : ℂ) * Complex.I) x).sub_const u
    refine HasDerivAt.congr_of_eventuallyEq h ?_
    exact Filter.Eventually.of_forall (by intro t; ring)
  have hslit : (((x : ℂ) + (r : ℂ) * Complex.I) - u) ∈ Complex.slitPlane := by
    change 0 < (((x : ℂ) + (r : ℂ) * Complex.I) - u).re ∨ (((x : ℂ) + (r : ℂ) * Complex.I) - u).im ≠ 0
    right
    have him : (((x : ℂ) + (r : ℂ) * Complex.I) - u).im = r - u.im := by simp
    rw [him]
    exact sub_ne_zero.mpr hr
  simpa [div_eq_mul_inv] using HasDerivAt.clog_real hF hslit

/-- Derivative of `Complex.log` along a vertical side `x ↦ s + x * I - u`
(the real part `s - u.re` is constant and positive). -/
lemma rectInt_hasDerivAt_log_vert {s : ℝ} {u : ℂ} (hs : u.re < s) :
    ∀ x : ℝ, HasDerivAt (fun x : ℝ => Complex.log (((s : ℂ) + (x : ℂ) * Complex.I) - u))
      (Complex.I * ((((s : ℂ) + (x : ℂ) * Complex.I) - u)⁻¹)) x := by
  intro x
  have hF : HasDerivAt (fun x : ℝ => ((s : ℂ) + (x : ℂ) * Complex.I) - u) Complex.I x := by
    have h := (rectInt_hasDerivAt_affine_sub Complex.I ((s : ℂ)) x).sub_const u
    refine HasDerivAt.congr_of_eventuallyEq h ?_
    exact Filter.Eventually.of_forall (by intro t; ring)
  have hslit : (((s : ℂ) + (x : ℂ) * Complex.I) - u) ∈ Complex.slitPlane := by
    change 0 < (((s : ℂ) + (x : ℂ) * Complex.I) - u).re ∨ (((s : ℂ) + (x : ℂ) * Complex.I) - u).im ≠ 0
    left
    have hrim : (((s : ℂ) + (x : ℂ) * Complex.I) - u).re = s - u.re := by simp
    rw [hrim]
    exact sub_pos.mpr hs
  simpa [div_eq_mul_inv] using HasDerivAt.clog_real hF hslit

/-- Derivative of `Complex.log` along the reflected vertical side
`x ↦ u - (s + x * I)` (the real part `u.re - s` is positive). -/
lemma rectInt_hasDerivAt_log_vert_mirror {s : ℝ} {u : ℂ} (hs : s < u.re) :
    ∀ x : ℝ, HasDerivAt (fun x : ℝ => Complex.log (u - ((s : ℂ) + (x : ℂ) * Complex.I)))
      ((-Complex.I) * ((u - ((s : ℂ) + (x : ℂ) * Complex.I))⁻¹)) x := by
  intro x
  have hF : HasDerivAt (fun x : ℝ => u - ((s : ℂ) + (x : ℂ) * Complex.I)) (-Complex.I) x := by
    have h := (rectInt_hasDerivAt_affine_sub (-Complex.I) (u - (s : ℂ)) x)
    refine HasDerivAt.congr_of_eventuallyEq h ?_
    exact Filter.Eventually.of_forall (by intro t; ring)
  have hslit : (u - ((s : ℂ) + (x : ℂ) * Complex.I)) ∈ Complex.slitPlane := by
    change 0 < (u - ((s : ℂ) + (x : ℂ) * Complex.I)).re ∨ (u - ((s : ℂ) + (x : ℂ) * Complex.I)).im ≠ 0
    left
    have hrim : (u - ((s : ℂ) + (x : ℂ) * Complex.I)).re = u.re - s := by simp
    rw [hrim]
    exact sub_pos.mpr hs
  simpa [div_eq_mul_inv] using HasDerivAt.clog_real hF hslit

/-- Integral of the derivative of the logarithm along a horizontal side. -/
lemma rectInt_horizontal_integral {a b r : ℝ} {u : ℂ} (hr : r ≠ u.im) :
    (∫ x : ℝ in a..b, (((x : ℂ) + (r : ℂ) * Complex.I) - u)⁻¹) =
      Complex.log (((b : ℂ) + (r : ℂ) * Complex.I) - u) -
        Complex.log (((a : ℂ) + (r : ℂ) * Complex.I) - u) := by
  let f : ℝ → ℂ := fun x => Complex.log (((x : ℂ) + (r : ℂ) * Complex.I) - u)
  let f' : ℝ → ℂ := fun x => (((x : ℂ) + (r : ℂ) * Complex.I) - u)⁻¹
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt f (f' x) x := by
    intro x hx
    dsimp [f, f']
    exact rectInt_hasDerivAt_log_horiz hr x
  have hcont : ContinuousOn f' (Set.uIcc a b) := by
    refine (ContinuousOn.inv₀ (s := Set.uIcc a b) ?_ ?_)
    · fun_prop
    · intro x hx
      have hpos : ((((x : ℂ) + (r : ℂ) * Complex.I) - u)).im ≠ 0 := by
        have him : (((x : ℂ) + (r : ℂ) * Complex.I) - u).im = r - u.im := by simp
        rw [him]
        exact sub_ne_zero.mpr hr
      intro hz
      have hzim : (((x : ℂ) + (r : ℂ) * Complex.I) - u).im = 0 := congrArg Complex.im hz
      exact hpos hzim
  have hint : IntervalIntegrable f' volume a b := hcont.intervalIntegrable
  calc
    ∫ x : ℝ in a..b, (((x : ℂ) + (r : ℂ) * Complex.I) - u)⁻¹
        = ∫ x : ℝ in a..b, f' x := by rfl
    _ = f b - f a := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    _ = Complex.log (((b : ℂ) + (r : ℂ) * Complex.I) - u) -
          Complex.log (((a : ℂ) + (r : ℂ) * Complex.I) - u) := by rfl

/-- Integral of the derivative of the logarithm along a vertical side with positive real part. -/
lemma rectInt_vertical_integral_mul_I {c d s : ℝ} {u : ℂ} (hs : u.re < s) :
    (∫ y : ℝ in c..d, Complex.I * ((((s : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹)) =
      Complex.log (((s : ℂ) + (d : ℂ) * Complex.I) - u) -
        Complex.log (((s : ℂ) + (c : ℂ) * Complex.I) - u) := by
  let f : ℝ → ℂ := fun x => Complex.log (((s : ℂ) + (x : ℂ) * Complex.I) - u)
  let f' : ℝ → ℂ := fun x => Complex.I * ((((s : ℂ) + (x : ℂ) * Complex.I) - u)⁻¹)
  have hderiv : ∀ x ∈ Set.uIcc c d, HasDerivAt f (f' x) x := by
    intro x hx
    dsimp [f, f']
    exact rectInt_hasDerivAt_log_vert hs x
  have hcont : ContinuousOn f' (Set.uIcc c d) := by
    refine ContinuousOn.mul continuousOn_const ?_
    refine (ContinuousOn.inv₀ (s := Set.uIcc c d) ?_ ?_)
    · fun_prop
    · intro x hx
      have hpos : 0 < (((s : ℂ) + (x : ℂ) * Complex.I) - u).re := by
        have hrim : (((s : ℂ) + (x : ℂ) * Complex.I) - u).re = s - u.re := by simp
        rw [hrim]
        exact sub_pos.mpr hs
      intro hz
      have hzre : (((s : ℂ) + (x : ℂ) * Complex.I) - u).re = 0 := congrArg Complex.re hz
      linarith
  have hint : IntervalIntegrable f' volume c d := hcont.intervalIntegrable
  calc
    ∫ y : ℝ in c..d, Complex.I * ((((s : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹)
        = ∫ x : ℝ in c..d, f' x := by rfl
    _ = f d - f c := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    _ = Complex.log (((s : ℂ) + (d : ℂ) * Complex.I) - u) -
          Complex.log (((s : ℂ) + (c : ℂ) * Complex.I) - u) := by rfl

/-- Integral along the *reflected* vertical side `y ↦ u - (s + y * I)` (used for the side
that would cross the branch cut of the principal logarithm). -/
lemma rectInt_mirror_integral_mul_negI {s c d : ℝ} {u : ℂ} (hs : s < u.re) :
    (∫ y : ℝ in c..d, (-Complex.I) * ((u - ((s : ℂ) + (y : ℂ) * Complex.I))⁻¹)) =
      Complex.log (u - ((s : ℂ) + (d : ℂ) * Complex.I)) -
        Complex.log (u - ((s : ℂ) + (c : ℂ) * Complex.I)) := by
  let f : ℝ → ℂ := fun x => Complex.log (u - ((s : ℂ) + (x : ℂ) * Complex.I))
  let f' : ℝ → ℂ := fun x => (-Complex.I) * ((u - ((s : ℂ) + (x : ℂ) * Complex.I))⁻¹)
  have hderiv : ∀ x ∈ Set.uIcc c d, HasDerivAt f (f' x) x := by
    intro x hx
    dsimp [f, f']
    exact rectInt_hasDerivAt_log_vert_mirror hs x
  have hcont : ContinuousOn f' (Set.uIcc c d) := by
    refine ContinuousOn.mul continuousOn_const ?_
    refine (ContinuousOn.inv₀ (s := Set.uIcc c d) ?_ ?_)
    · fun_prop
    · intro x hx
      have hpos : 0 < (u - ((s : ℂ) + (x : ℂ) * Complex.I)).re := by
        have hrim : (u - ((s : ℂ) + (x : ℂ) * Complex.I)).re = u.re - s := by simp
        rw [hrim]
        exact sub_pos.mpr hs
      intro hz
      have hzre : (u - ((s : ℂ) + (x : ℂ) * Complex.I)).re = 0 := congrArg Complex.re hz
      linarith
  have hint : IntervalIntegrable f' volume c d := hcont.intervalIntegrable
  calc
    ∫ y : ℝ in c..d, (-Complex.I) * ((u - ((s : ℂ) + (y : ℂ) * Complex.I))⁻¹)
        = ∫ x : ℝ in c..d, f' x := by rfl
    _ = f d - f c := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    _ = Complex.log (u - ((s : ℂ) + (d : ℂ) * Complex.I)) -
          Complex.log (u - ((s : ℂ) + (c : ℂ) * Complex.I)) := by rfl

/-- Principal logarithm under a half-turn: below the real axis it picks up `+πi`. -/
lemma rectInt_log_neg_of_im_neg {z : ℂ} (hz : z.im < 0) :
    Complex.log (-z) = Complex.log z + (Real.pi : ℂ) * Complex.I := by
  have harg : arg (-z) = arg z + π := arg_neg_eq_arg_add_pi_of_im_neg hz
  have hnorm : ‖-z‖ = ‖z‖ := by simp
  rw [Complex.log, Complex.log, hnorm, harg]
  push_cast
  ring

/-- Principal logarithm under a half-turn: above the real axis it loses `πi`. -/
lemma rectInt_log_neg_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    Complex.log (-z) = Complex.log z - (Real.pi : ℂ) * Complex.I := by
  have harg : arg (-z) = arg z - π := arg_neg_eq_arg_sub_pi_of_im_pos hz
  have hnorm : ‖-z‖ = ‖z‖ := by simp
  rw [Complex.log, Complex.log, hnorm, harg]
  push_cast
  ring


/-- Bottom side: the integral equals a difference of two logarithms. -/
lemma rectInt_bottom {z w u : ℂ} (hzim : z.im < u.im) :
    (∫ x : ℝ in z.re..w.re, (((x : ℂ) + (z.im : ℂ) * Complex.I) - u)⁻¹) =
      Complex.log (((w.re : ℂ) + (z.im : ℂ) * Complex.I) - u) -
        Complex.log (z - u) := by
  have hb := rectInt_horizontal_integral (a := z.re) (b := w.re) (r := z.im) (u := u)
    (ne_of_lt hzim)
  have hcorner : (z.re : ℂ) + (z.im : ℂ) * Complex.I = z := by
    apply Complex.ext <;> simp
  simpa [hcorner] using hb

/-- Top side: the integral equals a difference of two logarithms. -/
lemma rectInt_top {z w u : ℂ} (huim : u.im < w.im) :
    (∫ x : ℝ in z.re..w.re, (((x : ℂ) + (w.im : ℂ) * Complex.I) - u)⁻¹) =
      Complex.log (w - u) - Complex.log (((z.re : ℂ) + (w.im : ℂ) * Complex.I) - u) := by
  have ht := rectInt_horizontal_integral (a := z.re) (b := w.re) (r := w.im) (u := u)
    (ne_of_lt huim).symm
  have hcorner : (w.re : ℂ) + (w.im : ℂ) * Complex.I = w := by
    apply Complex.ext <;> simp
  simpa [hcorner] using ht

/-- Right side (multiplied by `I`): the integral equals a difference of two logarithms. -/
lemma rectInt_right_mul_I {z w u : ℂ} (hu : u.re < w.re) :
    Complex.I * (∫ y : ℝ in z.im..w.im, (((w.re : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹) =
      Complex.log (w - u) - Complex.log (((w.re : ℂ) + (z.im : ℂ) * Complex.I) - u) := by
  have hv := rectInt_vertical_integral_mul_I (c := z.im) (d := w.im) (s := w.re) (u := u) hu
  have hcorner : (w.re : ℂ) + (w.im : ℂ) * Complex.I = w := by
    apply Complex.ext <;> simp
  rw [← intervalIntegral.integral_const_mul (r := Complex.I)
    (f := fun y : ℝ => (((w.re : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹)]
  simpa [hcorner] using hv

/-- Left side (times `-I`): the side crosses the branch cut, so the two logarithms are
taken at the *reflected* points `u - z` and `u - topLeft`. -/
lemma rectInt_left_neg_mul_I {z w u : ℂ} (hu : z.re < u.re) :
    - (Complex.I * (∫ y : ℝ in z.im..w.im, (((z.re : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹)) =
      Complex.log (u - ((z.re : ℂ) + (z.im : ℂ) * Complex.I)) -
        Complex.log (u - ((z.re : ℂ) + (w.im : ℂ) * Complex.I)) := by
  let W : ℝ → ℂ := fun y => u - ((z.re : ℂ) + (y : ℂ) * Complex.I)
  have hVW : (fun y : ℝ => (((z.re : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹) =
      fun y : ℝ => - (W y)⁻¹ := by
    funext y
    have hv : (((z.re : ℂ) + (y : ℂ) * Complex.I) - u) = -(W y) := by
      dsimp [W]
      ring
    rw [hv, inv_neg]
  have hmir := rectInt_mirror_integral_mul_negI (s := z.re) (c := z.im) (d := w.im) (u := u) hu
  -- hmir : ∫ (-I) * (W y)⁻¹ = log (W d) - log (W c)
  have hmul : (-Complex.I) * (∫ y : ℝ in z.im..w.im, (W y)⁻¹) =
      Complex.log (u - ((z.re : ℂ) + (w.im : ℂ) * Complex.I)) -
        Complex.log (u - ((z.re : ℂ) + (z.im : ℂ) * Complex.I)) := by
    rw [← intervalIntegral.integral_const_mul (r := -Complex.I)
      (f := fun y : ℝ => (W y)⁻¹)]
    exact hmir
  have hIntW : (∫ y : ℝ in z.im..w.im, (W y)⁻¹) =
      Complex.I * (Complex.log (u - ((z.re : ℂ) + (w.im : ℂ) * Complex.I)) -
        Complex.log (u - ((z.re : ℂ) + (z.im : ℂ) * Complex.I))) := by
    have hinv : (-Complex.I)⁻¹ = Complex.I := by
      norm_num
    calc
      (∫ y : ℝ in z.im..w.im, (W y)⁻¹)
          = (-Complex.I)⁻¹ * ((-Complex.I) * (∫ y : ℝ in z.im..w.im, (W y)⁻¹)) := by
            rw [← mul_assoc, inv_mul_cancel₀ (by norm_num), one_mul]
      _ = Complex.I * (Complex.log (u - ((z.re : ℂ) + (w.im : ℂ) * Complex.I)) -
            Complex.log (u - ((z.re : ℂ) + (z.im : ℂ) * Complex.I))) := by
            rw [hmul, hinv]
  calc
    - (Complex.I * (∫ y : ℝ in z.im..w.im, (((z.re : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹))
        = - (Complex.I * (∫ y : ℝ in z.im..w.im, - (W y)⁻¹)) := by
          congr 1
          rw [hVW]
    _ = - (Complex.I * (- (∫ y : ℝ in z.im..w.im, (W y)⁻¹))) := by
          congr 2
          rw [intervalIntegral.integral_neg]
    _ = Complex.I * (∫ y : ℝ in z.im..w.im, (W y)⁻¹) := by ring
    _ = Complex.log (u - ((z.re : ℂ) + (z.im : ℂ) * Complex.I)) -
          Complex.log (u - ((z.re : ℂ) + (w.im : ℂ) * Complex.I)) := by
          rw [hIntW]
          have hI : Complex.I * Complex.I = -1 := by simp
          rw [← mul_assoc, hI]
          ring

/-- Residue of `(s-u)⁻¹` around the (counterclockwise) boundary of the axis-parallel
rectangle with corners `z` and `w` is `2πi` when `u` lies strictly inside. -/
theorem rectIntegral_sub_inv_inside {z w u : ℂ} (hzre : z.re < w.re) (hzim : z.im < w.im)
    (huin : z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im) :
    (∫ x : ℝ in z.re..w.re, (((x : ℂ) + (z.im : ℂ) * Complex.I) - u)⁻¹) -
        (∫ x : ℝ in z.re..w.re, (((x : ℂ) + (w.im : ℂ) * Complex.I) - u)⁻¹) +
        Complex.I • (∫ y : ℝ in z.im..w.im, (((w.re : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹) -
        Complex.I • (∫ y : ℝ in z.im..w.im, (((z.re : ℂ) + (y : ℂ) * Complex.I) - u)⁻¹) =
        (2 : ℂ) * (Real.pi : ℂ) * Complex.I := by
  rcases huin with ⟨hzre_u, huim_wre, hzim_u, huim_wim⟩
  have hb := rectInt_bottom (z := z) (w := w) (u := u) hzim_u
  have ht := rectInt_top (z := z) (w := w) (u := u) huim_wim
  have hr := rectInt_right_mul_I (z := z) (w := w) (u := u) huim_wre
  have hl := rectInt_left_neg_mul_I (z := z) (w := w) (u := u) hzre_u
  rw [smul_eq_mul, smul_eq_mul]
  rw [hb, ht, hr]
  rw [sub_eq_add_neg]
  rw [hl]
  have huz : u - ((z.re : ℂ) + (z.im : ℂ) * Complex.I) = -(z - u) := by
    have hz : (z.re : ℂ) + (z.im : ℂ) * Complex.I = z := by
      apply Complex.ext <;> simp
    rw [hz]
    ring
  have hutl : u - ((z.re : ℂ) + (w.im : ℂ) * Complex.I) =
      -(((z.re : ℂ) + (w.im : ℂ) * Complex.I) - u) := by
    ring
  have himz : (z - u).im < 0 := by
    simp
    linarith
  have himtl : 0 < (((z.re : ℂ) + (w.im : ℂ) * Complex.I) - u).im := by
    simp
    linarith
  have hloguz : Complex.log (u - ((z.re : ℂ) + (z.im : ℂ) * Complex.I)) =
      Complex.log (z - u) + (Real.pi : ℂ) * Complex.I := by
    rw [huz, rectInt_log_neg_of_im_neg himz]
  have hlogutl : Complex.log (u - ((z.re : ℂ) + (w.im : ℂ) * Complex.I)) =
      Complex.log (((z.re : ℂ) + (w.im : ℂ) * Complex.I) - u) -
        (Real.pi : ℂ) * Complex.I := by
    rw [hutl, rectInt_log_neg_of_im_pos himtl]
  rw [hloguz, hlogutl]
  ring