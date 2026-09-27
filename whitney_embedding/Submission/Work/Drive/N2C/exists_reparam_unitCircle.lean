import Mathlib
import Submission.Work.Drive.N2C.contDiff_invFun_of_strictMono
import Submission.Work.Drive.N2C.exists_int_const_of_continuous
import Submission.Work.Drive.N2C.sign_const_of_continuous_ne_zero

/-!
# Reparametrisation of a circle traversed by a unit complex curve

A smooth, `1`-periodic unit complex curve `z` which is injective on `[0,1)` and has nowhere-zero
derivative traverses the unit circle with winding `±1`; hence it admits a smooth reparametrisation
`τ` of `ℝ` onto the standard parametrisation `t ↦ exp (i (φ + 2π t))` of the unit circle.

The proof constructs the argument function `θ x = θ₀ + ∫_0^x im (deriv z s / z s)` (the "logarithmic
derivative" of `z` is purely imaginary), shows `z x = exp (θ x * I)`, that `θ (x+1) - θ x` is a
constant integer multiple `2πk` of `2π`, that `k = ±1` (strict monotonicity + the intermediate value
theorem + injectivity of `z` on `[0,1)`), and finally that `τ x := θ⁻¹ (θ 0 + 2π x)` is a smooth
bijection of `ℝ` with `z (τ x) = exp ((θ 0 + 2π x) * I)`.
-/

open MeasureTheory

namespace Work.Drive.N2C

variable {z : ℝ → ℂ}

/-! ## Elementary facts about the curve -/

/-- A complex number of `normSq` one is nonzero. -/
lemma ne_zero_of_normSq_eq_one {w : ℂ} (h : Complex.normSq w = 1) : w ≠ 0 := by
  intro hw
  rw [hw] at h
  simp at h

/-- The real and imaginary parts of `deriv z` are orthogonal to `z` at every point, because
`x ↦ normSq (z x)` is constant. -/
lemma normSq_deriv_re_im (hz : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) z)
    (hunit : ∀ x, Complex.normSq (z x) = 1) (x : ℝ) :
    (deriv z x).re * (z x).re + (deriv z x).im * (z x).im = 0 := by
  have hzd : HasDerivAt z (deriv z x) x :=
    (hz.contDiffAt.differentiableAt (by simp)).hasDerivAt
  have hre : HasDerivAt (fun y => (z y).re) (deriv z x).re x :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hzd
  have him : HasDerivAt (fun y => (z y).im) (deriv z x).im x :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hzd
  have h1 : HasDerivAt (fun y => (z y).re * (z y).re) (2 * (deriv z x).re * (z x).re) x := by
    have h := hre.mul hre
    refine h.congr_deriv ?_
    ring
  have h2 : HasDerivAt (fun y => (z y).im * (z y).im) (2 * (deriv z x).im * (z x).im) x := by
    have h := him.mul him
    refine h.congr_deriv ?_
    ring
  have h3 : HasDerivAt (fun y => (z y).re * (z y).re + (z y).im * (z y).im)
      (2 * (deriv z x).re * (z x).re + 2 * (deriv z x).im * (z x).im) x := h1.add h2
  have h4 : HasDerivAt (fun y => Complex.normSq (z y))
      (2 * (deriv z x).re * (z x).re + 2 * (deriv z x).im * (z x).im) x := by
    refine h3.congr_of_eventuallyEq ?_
    filter_upwards with y
    rw [Complex.normSq_apply]
  have h5 : deriv (fun y => Complex.normSq (z y)) x = 0 := by
    have : (fun y => Complex.normSq (z y)) = fun _ => (1 : ℝ) := funext fun y => hunit y
    rw [this]
    exact deriv_const x 1
  have := h4.deriv
  rw [h5] at this
  linarith

/-- The logarithmic derivative `deriv z x / z x` is purely imaginary. -/
lemma logDeriv_re_eq_zero (hz : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) z)
    (hunit : ∀ x, Complex.normSq (z x) = 1) (x : ℝ) :
    (deriv z x / z x).re = 0 := by
  rw [Complex.div_re, hunit x, div_one, div_one]
  exact normSq_deriv_re_im hz hunit x

/-- `deriv z x` is the logarithmic derivative times `z x`. -/
lemma deriv_eq_im_mul_I (hz : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) z)
    (hunit : ∀ x, Complex.normSq (z x) = 1) (x : ℝ) :
    deriv z x = (((deriv z x / z x).im : ℂ) * Complex.I) * z x := by
  have hz0 : z x ≠ 0 := ne_zero_of_normSq_eq_one (hunit x)
  have hw : deriv z x / z x = (((deriv z x / z x).im : ℂ)) * Complex.I := by
    conv_lhs => rw [← Complex.re_add_im (deriv z x / z x)]
    rw [logDeriv_re_eq_zero hz hunit x]
    simp
  have h2 : (deriv z x / z x) * z x = deriv z x := div_mul_cancel₀ _ hz0
  rw [hw] at h2
  exact h2.symm

/-- The logarithmic derivative never vanishes when `deriv z` never vanishes. -/
lemma logDeriv_im_ne_zero (hz : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) z)
    (hunit : ∀ x, Complex.normSq (z x) = 1) (hderiv : ∀ x, deriv z x ≠ 0) (x : ℝ) :
    (deriv z x / z x).im ≠ 0 := by
  intro him
  have hz0 : z x ≠ 0 := ne_zero_of_normSq_eq_one (hunit x)
  have hw : deriv z x / z x = 0 := by
    have : deriv z x / z x = (((deriv z x / z x).im : ℂ)) * Complex.I := by
      conv_lhs => rw [← Complex.re_add_im (deriv z x / z x)]
      rw [logDeriv_re_eq_zero hz hunit x]
      simp
    rw [this, him]
    simp
  have h2 : (deriv z x / z x) * z x = deriv z x := div_mul_cancel₀ _ hz0
  rw [hw] at h2
  exact hderiv x (by simpa using h2.symm)

/-- Smoothness of the imaginary part of the logarithmic derivative. -/
lemma contDiff_logDeriv_im (hz : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) z)
    (hne : ∀ x, z x ≠ 0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (deriv z x / z x).im) := by
  have hdz : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv z) := (contDiff_infty_iff_deriv.mp hz).2
  have hinv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (z x)⁻¹) := hz.inv hne
  have hdiv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => deriv z x * (z x)⁻¹) :=
    hdz.mul hinv
  have hfun : (fun x => deriv z x * (z x)⁻¹) = fun x => deriv z x / z x := by
    funext x; rw [div_eq_mul_inv]
  rw [hfun] at hdiv
  exact Complex.imCLM.contDiff.comp hdiv

/-! ## The argument function -/

/-- `θ x = θ₀ + ∫_0^x im (deriv z s / z s) ds`, the primitive of the logarithmic derivative. -/
noncomputable def liftArg (z : ℝ → ℂ) (θ₀ : ℝ) : ℝ → ℝ :=
  fun x => θ₀ + ∫ s in 0..x, (deriv z s / z s).im

lemma hasDerivAt_liftArg (hz : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) z) (hne : ∀ x, z x ≠ 0)
    (θ₀ : ℝ) (x : ℝ) :
    HasDerivAt (liftArg z θ₀) ((deriv z x / z x).im) x := by
  have hu : Continuous (fun x => (deriv z x / z x).im) := (contDiff_logDeriv_im hz hne).continuous
  have h1 := hu.integral_hasStrictDerivAt 0 x
  have h2 : HasDerivAt (fun x => θ₀ + ∫ s in 0..x, (deriv z s / z s).im)
      ((deriv z x / z x).im) x := h1.hasDerivAt.const_add θ₀
  change HasDerivAt (fun x => θ₀ + ∫ s in 0..x, (deriv z s / z s).im) _ x
  exact h2

lemma deriv_liftArg (hz : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) z) (hne : ∀ x, z x ≠ 0)
    (θ₀ : ℝ) (x : ℝ) :
    deriv (liftArg z θ₀) x = (deriv z x / z x).im := (hasDerivAt_liftArg hz hne θ₀ x).deriv

lemma contDiff_liftArg (hz : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) z) (hne : ∀ x, z x ≠ 0)
    (θ₀ : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (liftArg z θ₀) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun x => (hasDerivAt_liftArg hz hne θ₀ x).differentiableAt, ?_⟩
  have hfun : deriv (liftArg z θ₀) = fun x => (deriv z x / z x).im :=
    funext (fun x => deriv_liftArg hz hne θ₀ x)
  rw [hfun]
  exact contDiff_logDeriv_im hz hne

/-- The argument function really is an argument of `z`. -/
lemma exp_liftArg_eq (hz : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) z)
    (hunit : ∀ x, Complex.normSq (z x) = 1) (θ₀ : ℝ)
    (hθ₀ : Complex.exp (θ₀ * Complex.I) = z 0) :
    ∀ x, z x = Complex.exp (liftArg z θ₀ x * Complex.I) := by
  have hne : ∀ x, z x ≠ 0 := fun x => ne_zero_of_normSq_eq_one (hunit x)
  have key : ∀ y, HasDerivAt (fun t => z t * Complex.exp (-(liftArg z θ₀ t * Complex.I))) 0 y := by
    intro y
    set c : ℝ := (deriv z y / z y).im with hc
    have hdy : deriv z y = ((c : ℂ) * Complex.I) * z y := by
      rw [hc]; exact deriv_eq_im_mul_I hz hunit y
    have hθ : HasDerivAt (liftArg z θ₀) c y := by
      rw [hc]; exact hasDerivAt_liftArg hz hne θ₀ y
    have hθC : HasDerivAt (fun t => (liftArg z θ₀ t : ℂ)) ((c : ℂ)) y :=
      Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt y hθ
    have hlin : HasDerivAt (fun t => -((liftArg z θ₀ t : ℂ) * Complex.I))
        (-((c : ℂ) * Complex.I)) y := (hθC.mul_const Complex.I).neg
    have hexp : HasDerivAt (fun t => Complex.exp (-(liftArg z θ₀ t * Complex.I)))
        (Complex.exp (-(liftArg z θ₀ y * Complex.I)) * (-((c : ℂ) * Complex.I))) y := hlin.cexp
    have hzy : HasDerivAt z (deriv z y) y := (hz.contDiffAt.differentiableAt (by simp)).hasDerivAt
    refine (hzy.mul hexp).congr_deriv ?_
    rw [hdy]
    ring
  intro x
  have hconst : (fun t => z t * Complex.exp (-(liftArg z θ₀ t * Complex.I))) x
      = (fun t => z t * Complex.exp (-(liftArg z θ₀ t * Complex.I))) 0 :=
    is_const_of_deriv_eq_zero (fun y => (key y).differentiableAt) (fun y => (key y).deriv) x 0
  have hg0 : z 0 * Complex.exp (-(liftArg z θ₀ 0 * Complex.I)) = 1 := by
    have h0 : liftArg z θ₀ 0 = θ₀ := by
      simp [liftArg]
    rw [h0, Complex.exp_neg, hθ₀]
    exact mul_inv_cancel₀ (ne_zero_of_normSq_eq_one (hunit 0))
  have h1 : z x * Complex.exp (-(liftArg z θ₀ x * Complex.I)) = 1 := hconst.trans hg0
  have h2 : Complex.exp (-(liftArg z θ₀ x * Complex.I)) * Complex.exp (liftArg z θ₀ x * Complex.I)
      = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  calc z x = z x * (Complex.exp (-(liftArg z θ₀ x * Complex.I))
        * Complex.exp (liftArg z θ₀ x * Complex.I)) := by rw [h2, mul_one]
    _ = (z x * Complex.exp (-(liftArg z θ₀ x * Complex.I)))
        * Complex.exp (liftArg z θ₀ x * Complex.I) := by ring
    _ = Complex.exp (liftArg z θ₀ x * Complex.I) := by rw [h1, one_mul]

/-! ## The period change is an integer multiple of `2π` -/

/-- If `exp (a I) = exp (b I)` then `a - b` is an integer multiple of `2π`. -/
lemma exists_int_sub_of_exp_eq {a b : ℝ}
    (h : Complex.exp (a * Complex.I) = Complex.exp (b * Complex.I)) :
    ∃ n : ℤ, a - b = 2 * Real.pi * n := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  refine ⟨n, ?_⟩
  have h4 : (a : ℂ) * Complex.I = ((b + (n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
    rw [hn]; push_cast; ring
  have h3 : (a : ℂ) = ((b + (n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) :=
    mul_right_cancel₀ Complex.I_ne_zero h4
  have h3' : a = b + (n : ℝ) * (2 * Real.pi) := Complex.ofReal_inj.mp h3
  linarith

/-! ## Iterating a unit shift -/

/-- Iterating a shift `f (x+1) = f x + c` over the naturals. -/
lemma shift_nat {f : ℝ → ℝ} {c : ℝ} (h : ∀ x, f (x + 1) = f x + c) (n : ℕ) (x : ℝ) :
    f (x + n) = f x + n * c := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : (x + ↑(n + 1) : ℝ) = (x + ↑n) + 1 := by push_cast; ring
    rw [h1, h, ih]
    push_cast
    ring

/-- Iterating a shift `f (x+1) = f x + c` backwards over the naturals. -/
lemma shift_nat' {f : ℝ → ℝ} {c : ℝ} (h : ∀ x, f (x + 1) = f x + c) (n : ℕ) (x : ℝ) :
    f (x - n) = f x - n * c := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : (x - ↑(n + 1) : ℝ) + 1 = x - ↑n := by push_cast; ring
    have h2 := h (x - ↑(n + 1))
    rw [h1] at h2
    have h3 : f (x - ↑(n+1)) = f (x - ↑n) - c := by linarith
    rw [h3, ih]
    push_cast
    ring

/-- A continuous function with a shift `f (x+1) = f x + c`, `c > 0`, is surjective. -/
lemma surjective_of_continuous_shift_pos {f : ℝ → ℝ} (hf : Continuous f) {c : ℝ}
    (hc : 0 < c) (h : ∀ x, f (x + 1) = f x + c) : Function.Surjective f := by
  intro y
  rcases le_or_gt (f 0) y with hy | hy
  · obtain ⟨n, hn⟩ := exists_nat_ge ((y - f 0) / c)
    have hn' : y ≤ f 0 + n * c := by
      have := (div_le_iff₀ hc).mp hn
      linarith
    have hfn : f (0 + (n : ℝ)) = f 0 + n * c := shift_nat h n 0
    rw [zero_add] at hfn
    have hmem : y ∈ Set.Icc (f 0) (f (n:ℝ)) := ⟨hy, by rw [hfn]; exact hn'⟩
    obtain ⟨x, -, hxy⟩ := intermediate_value_Icc (Nat.cast_nonneg n) hf.continuousOn hmem
    exact ⟨x, hxy⟩
  · obtain ⟨n, hn⟩ := exists_nat_ge ((f 0 - y) / c)
    have hn' : f 0 - n * c ≤ y := by
      have := (div_le_iff₀ hc).mp hn
      linarith
    have hn0 : (-(n:ℝ)) ≤ 0 := by
      have : (0:ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hfn : f (0 - (n : ℝ)) = f 0 - n * c := shift_nat' h n 0
    rw [zero_sub] at hfn
    have hmem : y ∈ Set.Icc (f (-(n:ℝ))) (f 0) := ⟨by rw [hfn]; exact hn', hy.le⟩
    obtain ⟨x, -, hxy⟩ := intermediate_value_Icc hn0 hf.continuousOn hmem
    exact ⟨x, hxy⟩

/-- A continuous function with a nonzero shift `f (x+1) = f x + c` is surjective. -/
lemma surjective_of_continuous_shift {f : ℝ → ℝ} (hf : Continuous f) {c : ℝ} (hc : c ≠ 0)
    (h : ∀ x, f (x + 1) = f x + c) : Function.Surjective f := by
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · have hcpos : 0 < -c := by linarith
    have hgs : Function.Surjective (fun x => -f x) := by
      refine surjective_of_continuous_shift_pos hf.neg hcpos (fun x => ?_)
      rw [h x]
      ring
    intro y
    obtain ⟨x, hx⟩ := hgs (-y)
    exact ⟨x, by simpa using hx⟩
  · exact surjective_of_continuous_shift_pos hf hpos h

/-! ## The main theorem -/

theorem exists_reparam_unitCircle (z : ℝ → ℂ)
    (hz : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) z)
    (hunit : ∀ x, Complex.normSq (z x) = 1)
    (hper : ∀ x, z (x + 1) = z x)
    (hinj : Set.InjOn z (Set.Ico 0 1))
    (hderiv : ∀ x, deriv z x ≠ 0) :
    ∃ (τ : ℝ → ℝ) (φ : ℝ) (ε : ℤ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τ ∧
      (ε = 1 ∨ ε = -1) ∧
      (∀ x, τ (x + 1) = τ x + (ε : ℝ)) ∧
      Function.Surjective τ ∧
      (StrictMono τ ∨ StrictAnti τ) ∧
      (∀ x, deriv τ x ≠ 0) ∧
      (∀ x, z (τ x) = Complex.exp ((φ + 2 * Real.pi * x) * Complex.I)) := by
  have hne : ∀ x, z x ≠ 0 := fun x => ne_zero_of_normSq_eq_one (hunit x)
  have hpos2pi : (0:ℝ) < 2 * Real.pi := by positivity
  -- the base argument of `z 0`
  have hnorm0 : ‖z 0‖ = 1 := by
    have h2 := Complex.normSq_eq_norm_sq (z 0)
    nlinarith [norm_nonneg (z 0), hunit 0]
  have hθ₀ : Complex.exp ((z 0).arg * Complex.I) = z 0 := by
    simpa [hnorm0] using Complex.norm_mul_exp_arg_mul_I (z 0)
  -- the argument function
  set θ : ℝ → ℝ := liftArg z (z 0).arg with hθdef
  have hzexp : ∀ x, z x = Complex.exp (θ x * Complex.I) := by
    intro x
    rw [hθdef]
    exact exp_liftArg_eq hz hunit (z 0).arg hθ₀ x
  have hθcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ := by
    rw [hθdef]; exact contDiff_liftArg hz hne (z 0).arg
  have hθderiv : ∀ x, deriv θ x = (deriv z x / z x).im := by
    intro x; rw [hθdef]; exact deriv_liftArg hz hne _ x
  have hθne : ∀ x, deriv θ x ≠ 0 := fun x => by
    rw [hθderiv x]; exact logDeriv_im_ne_zero hz hunit hderiv x
  have hθcont : Continuous θ := hθcd.continuous
  have hθdcont : Continuous (deriv θ) := by
    have h1 : deriv θ = fun x => (deriv z x / z x).im := funext hθderiv
    rw [h1]
    exact (contDiff_logDeriv_im hz hne).continuous
  -- θ is strictly monotone
  have hmono_or_anti : StrictMono θ ∨ StrictAnti θ := by
    rcases sign_const_of_continuous_ne_zero hθdcont hθne with hpos | hneg
    · left
      have h := strictMonoOn_of_deriv_pos (convex_univ) hθcont.continuousOn (fun x _ => hpos x)
      rwa [strictMonoOn_univ] at h
    · right
      have h := strictAntiOn_of_deriv_neg (convex_univ) hθcont.continuousOn (fun x _ => hneg x)
      rwa [strictAntiOn_univ] at h
  have hinjθ : Function.Injective θ :=
    hmono_or_anti.elim StrictMono.injective StrictAnti.injective
  -- the period shift is a constant integer multiple of `2π`
  obtain ⟨k, hk⟩ : ∃ k : ℤ, ∀ x, θ (x + 1) = θ x + 2 * Real.pi * k := by
    have hconst : ∃ k : ℤ, ∀ x, θ (x + 1) - θ x = 2 * Real.pi * k := by
      refine exists_int_const_of_continuous (s := fun x => θ (x + 1) - θ x) ?_ ?_
      · exact (hθcont.comp (continuous_id.add continuous_const)).sub hθcont
      · intro x
        apply exists_int_sub_of_exp_eq
        rw [← hzexp (x + 1), ← hzexp x, hper x]
    obtain ⟨k, hk⟩ := hconst
    exact ⟨k, fun x => by linarith [hk x]⟩
  have hk_ne : k ≠ 0 := by
    intro h0
    have h01 : θ 1 = θ 0 := by simpa [h0] using hk 0
    rcases hmono_or_anti with hm | ha
    · exact absurd h01 (ne_of_gt (hm (by norm_num : (0:ℝ) < 1)))
    · exact absurd h01 (ne_of_lt (ha (by norm_num : (0:ℝ) < 1)))
  have hsurjθ : Function.Surjective θ :=
    surjective_of_continuous_shift hθcont
      (mul_ne_zero (by positivity : (2 * Real.pi : ℝ) ≠ 0) (Int.cast_ne_zero.mpr hk_ne)) hk
  -- the winding number is `± 1`
  have hk_pm : k = 1 ∨ k = -1 := by
    rcases hmono_or_anti with hm | ha
    · left
      have hkpos : 0 < k := by
        have h1 := hm (show (0:ℝ) < 1 by norm_num)
        have h01 : θ 1 = θ 0 + 2 * Real.pi * k := by simpa using hk 0
        rw [h01] at h1
        have hlt : (0:ℝ) < 2 * Real.pi * (k:ℝ) := by linarith
        have h2 : (0:ℝ) < (k:ℝ) := (mul_pos_iff_of_pos_left hpos2pi).mp hlt
        exact_mod_cast h2
      by_contra hne1
      have hk2 : (2:ℤ) ≤ k := by omega
      have hθ1 : θ 1 = θ 0 + 2 * Real.pi * k := by simpa using hk 0
      have hmem : θ 0 + 2 * Real.pi ∈ Set.Icc (θ 0) (θ 1) := by
        refine ⟨by linarith [Real.pi_pos], ?_⟩
        rw [hθ1]
        have hk2' : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk2
        nlinarith [Real.pi_pos]
      obtain ⟨x, hxmem, hxθ⟩ :=
        intermediate_value_Icc (show (0:ℝ) ≤ 1 by norm_num) hθcont.continuousOn hmem
      have hx0 : x ≠ 0 := by
        intro h; rw [h] at hxθ; linarith [Real.pi_pos]
      have hx1 : x ≠ 1 := by
        intro h
        rw [h, hθ1] at hxθ
        have hc : 2 * Real.pi * (k:ℝ) = 2 * Real.pi * 1 := by linarith
        have hk1 : k = 1 := by
          have h3 : (k:ℝ) = 1 := mul_left_cancel₀ (by positivity : (2*Real.pi:ℝ) ≠ 0) hc
          exact_mod_cast h3
        exact hne1 hk1
      have hxIco : x ∈ Set.Ico 0 1 := ⟨hxmem.1, lt_of_le_of_ne hxmem.2 hx1⟩
      have hz0mem : (0:ℝ) ∈ Set.Ico 0 1 := ⟨le_refl 0, by norm_num⟩
      have heq : z x = z 0 := by
        rw [hzexp x, hxθ, hzexp 0]
        have h1 : ↑(θ 0 + 2 * Real.pi) * Complex.I
            = ↑(θ 0) * Complex.I + (2 * ↑Real.pi) * Complex.I := by push_cast; ring
        rw [h1, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
      exact hx0 (hinj hxIco hz0mem heq)
    · right
      have hkneg : k < 0 := by
        have h1 := ha (show (0:ℝ) < 1 by norm_num)
        have h01 : θ 1 = θ 0 + 2 * Real.pi * k := by simpa using hk 0
        rw [h01] at h1
        have hlt : 2 * Real.pi * (k:ℝ) < 0 := by linarith
        have h2 : (k:ℝ) < 0 := by nlinarith [hpos2pi, hlt]
        exact_mod_cast h2
      by_contra hne1
      have hk2 : k ≤ -2 := by omega
      have hθ1 : θ 1 = θ 0 + 2 * Real.pi * k := by simpa using hk 0
      have hmem : θ 0 - 2 * Real.pi ∈ Set.Icc (θ 1) (θ 0) := by
        refine ⟨?_, by linarith [Real.pi_pos]⟩
        rw [hθ1]
        have hk2' : (k:ℝ) ≤ -2 := by exact_mod_cast hk2
        nlinarith [Real.pi_pos]
      obtain ⟨x, hxmem, hxθ⟩ := isPreconnected_Icc.intermediate_value
        (show (1:ℝ) ∈ Set.Icc 0 1 by norm_num) (show (0:ℝ) ∈ Set.Icc 0 1 by norm_num)
        hθcont.continuousOn hmem
      have hx0 : x ≠ 0 := by
        intro h; rw [h] at hxθ; linarith [Real.pi_pos]
      have hx1 : x ≠ 1 := by
        intro h
        rw [h, hθ1] at hxθ
        have hc : 2 * Real.pi * (k:ℝ) = -(2 * Real.pi) := by linarith
        have hk1 : k = -1 := by
          have h3 : (k:ℝ) = -1 := by nlinarith [Real.pi_pos]
          exact_mod_cast h3
        exact hne1 hk1
      have hxIco : x ∈ Set.Ico 0 1 := ⟨hxmem.1, lt_of_le_of_ne hxmem.2 hx1⟩
      have hz0mem : (0:ℝ) ∈ Set.Ico 0 1 := ⟨le_refl 0, by norm_num⟩
      have heq : z x = z 0 := by
        rw [hzexp x, hxθ, hzexp 0]
        have h1 : ↑(θ 0 - 2 * Real.pi) * Complex.I
            = ↑(θ 0) * Complex.I + -((2 * ↑Real.pi) * Complex.I) := by push_cast; ring
        rw [h1, Complex.exp_add, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one, mul_one]
      exact hx0 (hinj hxIco hz0mem heq)
  -- smoothness of the inverse of `θ`
  have hτcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.invFun θ) := by
    rcases hmono_or_anti with hm | ha
    · exact contDiff_invFun_of_strictMono hm hsurjθ hθcd hθne
    · have hm' : StrictMono (fun x : ℝ => -θ x) := fun x y hxy => neg_lt_neg (ha hxy)
      have hsurj' : Function.Surjective (fun x : ℝ => -θ x) := by
        intro y
        exact ⟨Function.invFun θ (-y), by
          have h := Function.rightInverse_invFun hsurjθ (-y)
          simpa using congrArg Neg.neg h⟩
      have hcd' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => -θ x) := hθcd.neg
      have h0' : ∀ y, deriv (fun x : ℝ => -θ x) y ≠ 0 := by
        intro y
        have hd : HasDerivAt (fun x : ℝ => -θ x) (-deriv θ y) y :=
          (((hθcd.contDiffAt).differentiableAt (by simp)).hasDerivAt).neg
        rw [hd.deriv]
        exact neg_ne_zero.mpr (hθne y)
      have hres := contDiff_invFun_of_strictMono hm' hsurj' hcd' h0'
      have hfun : Function.invFun θ = fun y => Function.invFun (fun x : ℝ => -θ x) (-y) := by
        funext y
        have h1 : θ (Function.invFun (fun x : ℝ => -θ x) (-y)) = y := by
          have h := Function.rightInverse_invFun hsurj' (-y)
          exact neg_injective h
        conv_lhs => rw [← h1]
        exact Function.leftInverse_invFun hinjθ _
      rw [hfun]
      exact hres.comp (by fun_prop)
  -- the reparametrisation
  set τ : ℝ → ℝ := fun x => Function.invFun θ (θ 0 + 2 * Real.pi * x) with hτdef
  have hτθ : ∀ x, θ (τ x) = θ 0 + 2 * Real.pi * x := by
    intro x; rw [hτdef]; exact Function.rightInverse_invFun hsurjθ _
  have hτcd' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) τ := by
    rw [hτdef]
    exact hτcd.comp (by fun_prop)
  refine ⟨τ, θ 0, k, hτcd', hk_pm, ?_, ?_, ?_, ?_, ?_⟩
  · -- periodicity
    intro x
    rcases hk_pm with hk1 | hkm1
    · have hθeq : θ (τ x + 1) = θ (τ (x + 1)) := by
        rw [hk (τ x), hτθ (x + 1), hτθ x, hk1]
        push_cast
        ring
      have h1 := hinjθ hθeq
      rw [← h1, hk1]
      push_cast
      ring
    · have hθeq : θ (τ x - 1) = θ (τ (x + 1)) := by
        have h := hk (τ x - 1)
        have h2 : (τ x - 1) + 1 = τ x := by ring
        rw [h2] at h
        rw [hkm1] at h
        rw [hτθ x] at h
        rw [hτθ (x + 1)]
        push_cast at h ⊢
        linarith
      have h1 := hinjθ hθeq
      rw [← h1, hkm1]
      push_cast
      ring
  · -- surjectivity
    intro y
    refine ⟨(θ y - θ 0) / (2 * Real.pi), ?_⟩
    have h1 : θ 0 + 2 * Real.pi * ((θ y - θ 0) / (2 * Real.pi)) = θ y := by
      have hπ : (2 * Real.pi : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    change Function.invFun θ (θ 0 + 2 * Real.pi * ((θ y - θ 0) / (2 * Real.pi))) = y
    rw [h1]
    exact Function.leftInverse_invFun hinjθ y
  · -- monotonicity
    rcases hmono_or_anti with hm | ha
    · left
      intro x y hxy
      have h1 : θ (τ x) < θ (τ y) := by
        rw [hτθ x, hτθ y]
        nlinarith [Real.pi_pos]
      exact (hm.lt_iff_lt).mp h1
    · right
      intro x y hxy
      have h1 : θ (τ x) < θ (τ y) := by
        rw [hτθ x, hτθ y]
        nlinarith [Real.pi_pos]
      exact (ha.lt_iff_gt).mp h1
  · -- nonzero derivative
    intro x
    have hτd : HasDerivAt τ (deriv τ x) x :=
      ((hτcd'.contDiffAt).differentiableAt (by simp)).hasDerivAt
    have hθd : HasDerivAt θ (deriv θ (τ x)) (τ x) :=
      ((hθcd.contDiffAt).differentiableAt (by simp)).hasDerivAt
    have hcomp : HasDerivAt (fun y => θ (τ y)) (deriv θ (τ x) * deriv τ x) x :=
      hθd.comp x hτd
    have hlin : HasDerivAt (fun y : ℝ => θ 0 + 2 * Real.pi * y) (2 * Real.pi) x := by
      have h := ((hasDerivAt_id x).const_mul (2 * Real.pi)).const_add (θ 0)
      simpa using h
    have hlin' : HasDerivAt (fun y => θ (τ y)) (2 * Real.pi) x :=
      hlin.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y => hτθ y))
    have huni := hcomp.unique hlin'
    intro hzero
    rw [hzero, mul_zero] at huni
    linarith [Real.pi_pos]
  · -- the reparametrisation realises the standard parametrisation
    intro x
    rw [hzexp (τ x), hτθ x]
    congr 1
    push_cast
    ring

end Work.Drive.N2C
