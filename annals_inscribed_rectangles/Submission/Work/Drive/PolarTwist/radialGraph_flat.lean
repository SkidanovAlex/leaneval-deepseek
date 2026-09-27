import Mathlib

/-!
# The radial-graph family, in flat (non-manifold) form

The last stage of the route (`ISOTOPY_TO_ELLIPSE_ROUTE.md` §3): an explicit jointly smooth family of
injective plane maps with nowhere vanishing tangent, starting at the radial graph
`x ↦ (rad x · re x, rad x · im x)` (over the standard angle of the circle) and ending at the
ellipse `z ↦ (2 re z, im z)`.

The manifold bookkeeping (`Manifold.IsSmoothEmbedding` for each slice) is separated off: see the
HANDOFF note "library gap worth filling once" — with the bridge
"injective + `C^∞` in the `Circle.exp` parametrisation + non-vanishing derivative ⟹ smooth
embedding", this flat statement yields `Work.Drive.radialGraph_isotopy`.
-/

set_option autoImplicit false

namespace Work.Drive

noncomputable section

open scoped ContDiff

/-- The circle element `Circle.exp t`, as a complex number, is `cos t + sin t · I`. -/
lemma circleExp_coe_eq (t : ℝ) :
    ((Circle.exp t : Circle) : ℂ) = (Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I := by
  rw [Circle.coe_exp, Complex.exp_ofReal_mul_I]

/-- `t ↦ ((Circle.exp t : Circle) : ℂ)` is smooth. -/
lemma contDiff_circleExp_coe :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => ((Circle.exp t : Circle) : ℂ)) := by
  have h : (fun t : ℝ => ((Circle.exp t : Circle) : ℂ))
      = fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I) := by
    funext t; exact Circle.coe_exp t
  rw [h]
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => (t : ℂ)) :=
    Complex.ofRealCLM.contDiff
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => (t : ℂ) * Complex.I) :=
    h1.mul contDiff_const
  exact Complex.contDiff_exp.comp h2

/-- The family.  `rad : Circle → ℝ` is the radius function of the starting radial graph;
the diagonal matrix `diag (1 + s, 1)` is the stretching. -/
def radialGraphFamily (rad : Circle → ℝ) : ℝ → Circle → ℝ × ℝ :=
  fun s x =>
    ((1 + s) * (((1 - s) * rad x + s) * (x : ℂ).re),
     (1 - s + s * 1) * (((1 - s) * rad x + s) * (x : ℂ).im))

lemma radialGraphFamily_zero (rad : Circle → ℝ) (x : Circle) :
    radialGraphFamily rad 0 x = (rad x * (x : ℂ).re, rad x * (x : ℂ).im) := by
  simp [radialGraphFamily]

lemma radialGraphFamily_one (rad : Circle → ℝ) (x : Circle) :
    radialGraphFamily rad 1 x = (2 * (x : ℂ).re, 1 * (x : ℂ).im) := by
  unfold radialGraphFamily
  norm_num

/-- Joint smoothness of the family along `Circle.exp`. -/
lemma contDiff_radialGraphFamily (rad : Circle → ℝ) (hrads : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => rad (Circle.exp t))) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => radialGraphFamily rad p.1 (Circle.exp p.2)) := by
  have hcoe : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => ((Circle.exp p.2 : Circle) : ℂ)) :=
    contDiff_circleExp_coe.comp contDiff_snd
  have hrad : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => rad (Circle.exp p.2)) := hrads.comp contDiff_snd
  have hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => (1 : ℝ) + p.1) := by
    fun_prop
  have hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => (1 : ℝ) - p.1) := by
    fun_prop
  have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => p.1) := contDiff_fst
  have hre : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => ((Circle.exp p.2 : Circle) : ℂ).re) :=
    Complex.reCLM.contDiff.comp hcoe
  have him : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => ((Circle.exp p.2 : Circle) : ℂ).im) :=
    Complex.imCLM.contDiff.comp hcoe
  have hradial : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => (1 - p.1) * rad (Circle.exp p.2) + p.1) := (hB.mul hrad).add hD
  have hE : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => (1 : ℝ) - p.1 + p.1 * 1) := hB.add (hD.mul contDiff_const)
  exact (hA.mul (hradial.mul hre)).prodMk (hE.mul (hradial.mul him))

/-- Each slice of the family is injective. -/
lemma radialGraphFamily_injective (rad : Circle → ℝ) (hrad : ∀ x, 0 < rad x)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    Function.Injective (radialGraphFamily rad s) := by
  intro x y hxy
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have hc1 : (0 : ℝ) < 1 + s := by linarith
  have hc2 : (0 : ℝ) < 1 - s + s * 1 := by linarith
  have h1s : (0 : ℝ) ≤ 1 - s := by linarith
  have hrx : (0 : ℝ) < (1 - s) * rad x + s := by
    rcases eq_or_lt_of_le hs0 with h | h
    · rw [← h]; simpa using hrad x
    · have hh := mul_nonneg h1s (le_of_lt (hrad x)); linarith
  have hry : (0 : ℝ) < (1 - s) * rad y + s := by
    rcases eq_or_lt_of_le hs0 with h | h
    · rw [← h]; simpa using hrad y
    · have hh := mul_nonneg h1s (le_of_lt (hrad y)); linarith
  have h1 : (1 + s) * (((1 - s) * rad x + s) * (x : ℂ).re)
      = (1 + s) * (((1 - s) * rad y + s) * (y : ℂ).re) := by
    simpa [radialGraphFamily] using congrArg Prod.fst hxy
  have h2 : (1 - s + s * 1) * (((1 - s) * rad x + s) * (x : ℂ).im)
      = (1 - s + s * 1) * (((1 - s) * rad y + s) * (y : ℂ).im) := by
    simpa [radialGraphFamily] using congrArg Prod.snd hxy
  have h1' : ((1 - s) * rad x + s) * (x : ℂ).re = ((1 - s) * rad y + s) * (y : ℂ).re :=
    mul_left_cancel₀ (ne_of_gt hc1) h1
  have h2' : ((1 - s) * rad x + s) * (x : ℂ).im = ((1 - s) * rad y + s) * (y : ℂ).im :=
    mul_left_cancel₀ (ne_of_gt hc2) h2
  have hcomplex : (((1 - s) * rad x + s : ℝ) : ℂ) * (x : ℂ)
      = (((1 - s) * rad y + s : ℝ) : ℂ) * (y : ℂ) := by
    apply Complex.ext
    · simpa [Complex.mul_re] using h1'
    · simpa [Complex.mul_im] using h2'
  have hr_eq : ((1 - s) * rad x + s : ℝ) = ((1 - s) * rad y + s : ℝ) := by
    have h := congrArg (fun z : ℂ => ‖z‖) hcomplex
    simp only [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hrx, abs_of_pos hry] at h
    exact_mod_cast h
  have hxyeq : (x : ℂ) = (y : ℂ) := by
    have h := hcomplex
    rw [hr_eq] at h
    exact mul_left_cancel₀ (by exact_mod_cast (ne_of_gt hry)) h
  exact Circle.coe_injective hxyeq

/-! ## The derivative of the family in the `Circle.exp` parametrisation -/

lemma circleExp_coe_re (t : ℝ) : ((Circle.exp t : Circle) : ℂ).re = Real.cos t := by
  rw [circleExp_coe_eq]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_one, mul_zero, sub_zero, add_zero]

lemma circleExp_coe_im (t : ℝ) : ((Circle.exp t : Circle) : ℂ).im = Real.sin t := by
  rw [circleExp_coe_eq]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_one, mul_zero, add_zero, zero_add]

lemma radialGraphFamily_exp_apply (rad : Circle → ℝ) (s t : ℝ) :
    radialGraphFamily rad s (Circle.exp t)
      = ((1 + s) * ((1 - s) * rad (Circle.exp t) + s) * Real.cos t,
         (1 - s + s * 1) * ((1 - s) * rad (Circle.exp t) + s) * Real.sin t) := by
  unfold radialGraphFamily
  rw [circleExp_coe_re, circleExp_coe_im]
  ext <;> ring

/-- The derivative of the family along `Circle.exp`, computed explicitly. -/
lemma hasDerivAt_radialGraphFamily (rad : Circle → ℝ)
    (hrads : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => rad (Circle.exp t)))
    (s t : ℝ) :
    HasDerivAt (fun u : ℝ => radialGraphFamily rad s (Circle.exp u))
      (((1 + s) * (((1 - s) * deriv (fun u : ℝ => rad (Circle.exp u)) t) * Real.cos t
            - ((1 - s) * rad (Circle.exp t) + s) * Real.sin t)),
       ((1 - s + s * 1) * (((1 - s) * deriv (fun u : ℝ => rad (Circle.exp u)) t) * Real.sin t
            + ((1 - s) * rad (Circle.exp t) + s) * Real.cos t))) t := by
  have hfun : (fun u : ℝ => radialGraphFamily rad s (Circle.exp u))
      = fun u : ℝ => ((1 + s) * ((1 - s) * rad (Circle.exp u) + s) * Real.cos u,
          (1 - s + s * 1) * ((1 - s) * rad (Circle.exp u) + s) * Real.sin u) := by
    funext u
    exact radialGraphFamily_exp_apply rad s u
  rw [hfun]
  have hd : DifferentiableAt ℝ (fun u : ℝ => rad (Circle.exp u)) t :=
    ((hrads.differentiable (by simp)).differentiableAt)
  have hρ : HasDerivAt (fun u : ℝ => (1 - s) * rad (Circle.exp u) + s)
      ((1 - s) * deriv (fun u : ℝ => rad (Circle.exp u)) t) t :=
    (hd.hasDerivAt.const_mul (1 - s)).add_const s
  have hcos : HasDerivAt Real.cos (-Real.sin t) t := Real.hasDerivAt_cos t
  have hsin : HasDerivAt Real.sin (Real.cos t) t := Real.hasDerivAt_sin t
  have h1 : HasDerivAt (fun u : ℝ => (1 + s) * ((1 - s) * rad (Circle.exp u) + s) * Real.cos u)
      ((1 + s) * (((1 - s) * deriv (fun u : ℝ => rad (Circle.exp u)) t) * Real.cos t
            - ((1 - s) * rad (Circle.exp t) + s) * Real.sin t)) t := by
    have h0 : HasDerivAt (fun _ : ℝ => (1 + s)) 0 t := hasDerivAt_const (x := t) (1 + s)
    have hres := (h0.mul hρ).mul hcos
    simp only [Pi.mul_apply] at hres
    exact hres.congr_deriv (by ring)
  have h2 : HasDerivAt
      (fun u : ℝ => (1 - s + s * 1) * ((1 - s) * rad (Circle.exp u) + s) * Real.sin u)
      ((1 - s + s * 1) * (((1 - s) * deriv (fun u : ℝ => rad (Circle.exp u)) t) * Real.sin t
            + ((1 - s) * rad (Circle.exp t) + s) * Real.cos t)) t := by
    have h0 : HasDerivAt (fun _ : ℝ => (1 - s + s * 1)) 0 t :=
      hasDerivAt_const (x := t) (1 - s + s * 1)
    have hres := (h0.mul hρ).mul hsin
    simp only [Pi.mul_apply] at hres
    exact hres.congr_deriv (by ring)
  exact h1.prodMk h2

/-- The tangent of every slice of the radial-graph family never vanishes. -/
lemma deriv_radialGraphFamily_ne_zero (rad : Circle → ℝ) (hrad : ∀ x, 0 < rad x)
    (hrads : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => rad (Circle.exp t))) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
      deriv (fun u : ℝ => radialGraphFamily rad s (Circle.exp u)) t ≠ 0 := by
  intro s hs t hzero
  have hd := (hasDerivAt_radialGraphFamily rad hrads s t).deriv
  rw [hd] at hzero
  have hc1 : (0 : ℝ) < 1 + s := by linarith [hs.1]
  have hc2 : (0 : ℝ) < 1 - s + s * 1 := by linarith [hs.2]
  have h1s : (0 : ℝ) ≤ 1 - s := by linarith [hs.2]
  have hρpos : (0 : ℝ) < (1 - s) * rad (Circle.exp t) + s := by
    rcases eq_or_lt_of_le hs.1 with h | h
    · rw [← h]; simpa using hrad (Circle.exp t)
    · have hh := mul_nonneg h1s (le_of_lt (hrad (Circle.exp t))); linarith
  have hfirst : (1 - s) * deriv (fun u : ℝ => rad (Circle.exp u)) t * Real.cos t
      - ((1 - s) * rad (Circle.exp t) + s) * Real.sin t = 0 := by
    have h' : (1 + s) * (((1 - s) * deriv (fun u : ℝ => rad (Circle.exp u)) t) * Real.cos t
        - ((1 - s) * rad (Circle.exp t) + s) * Real.sin t) = 0 := by
      have := congrArg Prod.fst hzero
      simpa using this
    nlinarith [h', hc1]
  have hsecond : (1 - s) * deriv (fun u : ℝ => rad (Circle.exp u)) t * Real.sin t
      + ((1 - s) * rad (Circle.exp t) + s) * Real.cos t = 0 := by
    have h' : (1 - s + s * 1) * (((1 - s) * deriv (fun u : ℝ => rad (Circle.exp u)) t) * Real.sin t
        + ((1 - s) * rad (Circle.exp t) + s) * Real.cos t) = 0 := by
      have := congrArg Prod.snd hzero
      simpa using this
    nlinarith [h', hc2]
  have hcs : Real.cos t ^ 2 + Real.sin t ^ 2 = 1 := Real.cos_sq_add_sin_sq t
  have hkey : ((1 - s) * deriv (fun u : ℝ => rad (Circle.exp u)) t)
      * (Real.cos t ^ 2 + Real.sin t ^ 2) = 0 := by
    linear_combination Real.cos t * hfirst + Real.sin t * hsecond
  have hρ'zero : (1 - s) * deriv (fun u : ℝ => rad (Circle.exp u)) t = 0 := by
    rw [hcs, mul_one] at hkey
    exact hkey
  have hsin0 : ((1 - s) * rad (Circle.exp t) + s) * Real.sin t = 0 := by
    rw [hρ'zero] at hfirst
    linarith
  have hcos0 : ((1 - s) * rad (Circle.exp t) + s) * Real.cos t = 0 := by
    rw [hρ'zero] at hsecond
    linarith
  have hexpand : ((1 - s) * rad (Circle.exp t) + s) ^ 2
      = (((1 - s) * rad (Circle.exp t) + s) * Real.cos t) ^ 2
        + (((1 - s) * rad (Circle.exp t) + s) * Real.sin t) ^ 2 := by
    have h' : ((1 - s) * rad (Circle.exp t) + s) ^ 2
        = ((1 - s) * rad (Circle.exp t) + s) ^ 2
          * (Real.cos t ^ 2 + Real.sin t ^ 2) := by rw [hcs, mul_one]
    rw [h']
    ring
  have hsq : ((1 - s) * rad (Circle.exp t) + s) ^ 2 = 0 := by
    rw [hexpand, hcos0, hsin0]
    ring
  exact absurd hsq (ne_of_gt (pow_pos hρpos 2))

end

end Work.Drive
