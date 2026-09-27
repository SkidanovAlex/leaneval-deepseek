import Mathlib
import Submission.Work.Drive.N2Lead.smoothArgLiftCinf

namespace Work.Drive.N2Lead

open scoped ContDiff Topology

noncomputable section

/-!
# The argument lift of a plane curve about the origin, without the injectivity hypothesis

Let `z : ℝ → ℂ` be `C^∞`, `1`-periodic and nowhere zero, with nowhere vanishing angular rate
`ω t = Im (conj (z t) * deriv z t)`.  Then there are a `C^∞` function `θ` and a nonzero integer `m`
with `deriv θ ≠ 0`, `z t = ‖z t‖ • exp (i θ t)` and `θ (t + 1) = θ t + m * 2π`.

The first part of this file is the (real, two-dimensional) engine, proved here as the auxiliary
`argLiftCinfNoInj`: this is the *whole* proof of `Work.Drive.N2Lead.smoothArgLiftCinf`
(`Submission/Work/Drive/N2Lead/smoothArgLiftCinf.lean`) with the injectivity hypothesis `hinj`
removed, i.e. its final step (`hm_one`, the only place where `hinj` is used) deleted.  The
conclusion is correspondingly weaker (the increment of `θ` over a period is an arbitrary nonzero
multiple of `2π`).

The target `smoothArgLiftComplex` is then obtained by pushing the complex curve into the unit
circle: `ψ t := (‖z t‖)⁻¹ • z t` is `C^∞` and `1`-periodic with unit modulus (`‖ψ t‖ = 1`), its
coordinates `a t = (ψ t).re`, `b t = (ψ t).im` satisfy `a ^ 2 + b ^ 2 = 1`, and the signed speed of
`(a, b)` is
`a t * deriv b t - b t * deriv a t = (conj (z t) * deriv z t).im / ‖z t‖ ^ 2`,
so the hypothesis `hω` gives the `himm` row.  The starting angle comes from `Complex.arg`.
-/

/-- The signed speed `ω x = a x * deriv b x - b x * deriv a x` of the curve `(a,b)`. -/
private def argOmega (a b : ℝ → ℝ) : ℝ → ℝ := fun x => a x * deriv b x - b x * deriv a x

/-- The candidate argument function: the starting angle plus the integral of the signed speed. -/
private def argTheta (a b : ℝ → ℝ) (t₀ : ℝ) : ℝ → ℝ :=
  fun x => t₀ + ∫ t in (0 : ℝ)..x, argOmega a b t

/-- Derivative of a `1`-periodic differentiable function at `x + 1` (periodicity of the
derivative). -/
private lemma deriv_comp_add_one {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hper : ∀ x, f (x + 1) = f x) (x : ℝ) : deriv f (x + 1) = deriv f x := by
  have h1 : HasDerivAt (fun y : ℝ => f (y + 1)) (deriv f (x + 1)) x :=
    HasDerivAt.comp_add_const x 1 (hf (x + 1)).hasDerivAt
  have h2 : (fun y : ℝ => f (y + 1)) = f := funext hper
  rw [h2] at h1
  exact h1.deriv.symm

/-- **Auxiliary (real two-dimensional form, without injectivity).**  Let `a b : ℝ → ℝ` be `C^∞`,
`1`-periodic, with `a x ^ 2 + b x ^ 2 = 1`, `(a, b) (0) = (cos t₀, sin t₀)` and with the signed speed
`ω x = a x * deriv b x - b x * deriv a x` nowhere zero.  Then `(a, b)` is the round picture of a `C^∞`
function `θ` with nonvanishing derivative, and `θ (x + 1) = θ x + m * 2π` for some nonzero integer
`m`.

This is `Work.Drive.N2Lead.smoothArgLiftCinf` with the hypothesis `hinj` deleted: the only place
where `hinj` is used is its final step (`hm_one`), so the argument is repeated verbatim except that
the increment is no longer shown to be `±2π`, only nonzero. -/
theorem argLiftCinfNoInj {a b : ℝ → ℝ}
    (ha : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a) (hb : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b)
    (hunit : ∀ x, a x ^ 2 + b x ^ 2 = 1)
    (hpera : ∀ x, a (x + 1) = a x) (hperb : ∀ x, b (x + 1) = b x)
    (h0 : ∃ t₀ : ℝ, Real.cos t₀ = a 0 ∧ Real.sin t₀ = b 0)
    (himm : ∀ x, a x * deriv b x - b x * deriv a x ≠ 0) :
    ∃ θ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ ∧ (∀ x, Real.cos (θ x) = a x) ∧
      (∀ x, Real.sin (θ x) = b x) ∧ (∀ x, deriv θ x ≠ 0) ∧
      ∃ m : ℤ, m ≠ 0 ∧ ∀ x, θ (x + 1) = θ x + (m : ℝ) * (2 * Real.pi) := by
  obtain ⟨t₀, hcos0, hsin0⟩ := h0
  have hda : Differentiable ℝ a := ha.differentiable (by simp)
  have hdb : Differentiable ℝ b := hb.differentiable (by simp)
  -- ## 1. the unit-circle relation for the derivatives
  have hrel : ∀ x, a x * deriv a x + b x * deriv b x = 0 := by
    intro x
    have hfun : (fun y : ℝ => a y ^ 2 + b y ^ 2) = fun _ : ℝ => (1 : ℝ) := funext fun y => hunit y
    have h1 : deriv (fun y : ℝ => a y ^ 2 + b y ^ 2) x = 0 := by rw [hfun]; simp
    have h2 : deriv (fun y : ℝ => a y ^ 2 + b y ^ 2) x
        = 2 * a x * deriv a x + 2 * b x * deriv b x := by
      change deriv (a ^ 2 + b ^ 2) x = 2 * a x * deriv a x + 2 * b x * deriv b x
      rw [((((hda x).hasDerivAt).pow 2).add (((hdb x).hasDerivAt).pow 2)).deriv]
      ring
    linarith
  -- ## 2. the signed speed, its continuity and its nonvanishing
  have hΩcont : Continuous (argOmega a b) := by
    have hda' : Continuous (deriv a) := ha.continuous_deriv (by simp)
    have hdb' : Continuous (deriv b) := hb.continuous_deriv (by simp)
    change Continuous ((a * deriv b) - (b * deriv a))
    exact (ha.continuous.mul hdb').sub (hb.continuous.mul hda')
  have hΩne : ∀ x, argOmega a b x ≠ 0 := fun x => by simpa only [argOmega] using himm x
  -- ## 3. the candidate lift and its derivative
  have hΘderiv : ∀ x, HasDerivAt (argTheta a b t₀) (argOmega a b x) x := by
    intro x
    have h := intervalIntegral.integral_hasDerivAt_right (hΩcont.intervalIntegrable 0 x)
      (hΩcont.stronglyMeasurableAtFilter MeasureTheory.volume (𝓝 x)) hΩcont.continuousAt
    exact h.const_add t₀
  have hΘdiff : Differentiable ℝ (argTheta a b t₀) := fun x => (hΘderiv x).differentiableAt
  have hΘcont : Continuous (argTheta a b t₀) := hΘdiff.continuous
  have hΘderivVal : ∀ x, deriv (argTheta a b t₀) x = argOmega a b x :=
    fun x => (hΘderiv x).deriv
  -- ## 3b. smoothness of the lift: its derivative is the `C^∞` function `ω`
  have hΩsm : ContDiff ℝ ∞ (argOmega a b) := by
    have hda' : ContDiff ℝ ∞ (deriv a) := ha.deriv'
    have hdb' : ContDiff ℝ ∞ (deriv b) := hb.deriv'
    change ContDiff ℝ ∞ ((a * deriv b) - (b * deriv a))
    exact (ha.mul hdb').sub (hb.mul hda')
  have hΘcd : ContDiff ℝ ∞ (argTheta a b t₀) := by
    rw [contDiff_infty_iff_deriv]
    refine ⟨hΘdiff, ?_⟩
    rw [show deriv (argTheta a b t₀) = argOmega a b from funext hΘderivVal]
    exact hΩsm
  -- ## 4. the two scalar identities for the derivatives
  have hder_a : ∀ x, deriv a x = -(b x * argOmega a b x) := by
    intro x
    simp only [argOmega]
    have h : deriv a x + b x * (a x * deriv b x - b x * deriv a x) = 0 := by
      linear_combination (norm := ring) (a x) * (hrel x) - (deriv a x) * (hunit x)
    linarith
  have hder_b : ∀ x, deriv b x = a x * argOmega a b x := by
    intro x
    simp only [argOmega]
    have h : deriv b x - a x * (a x * deriv b x - b x * deriv a x) = 0 := by
      linear_combination (norm := ring) (b x) * (hrel x) - (deriv b x) * (hunit x)
    linarith
  -- ## 5. the oscillating (Frenet) frame is constant: `cos θ = a`, `sin θ = b`
  have hcEq : ∀ x, a x * Real.cos (argTheta a b t₀ x) + b x * Real.sin (argTheta a b t₀ x) = 1 := by
    have hdiff : Differentiable ℝ
        (fun x => a x * Real.cos (argTheta a b t₀ x) + b x * Real.sin (argTheta a b t₀ x)) := by
      intro x
      have hθ : HasDerivAt (argTheta a b t₀) (argOmega a b x) x := hΘderiv x
      change DifferentiableAt ℝ (fun y => a y * Real.cos (argTheta a b t₀ y)
        + b y * Real.sin (argTheta a b t₀ y)) x
      exact (((hda x).hasDerivAt.mul hθ.cos).add ((hdb x).hasDerivAt.mul hθ.sin)).differentiableAt
    have hderiv : ∀ x, deriv
        (fun x => a x * Real.cos (argTheta a b t₀ x) + b x * Real.sin (argTheta a b t₀ x)) x
        = 0 := by
      intro x
      have hθ : HasDerivAt (argTheta a b t₀) (argOmega a b x) x := hΘderiv x
      have h1 : HasDerivAt (fun y => a y * Real.cos (argTheta a b t₀ y))
          (deriv a x * Real.cos (argTheta a b t₀ x)
            + a x * (-Real.sin (argTheta a b t₀ x) * argOmega a b x)) x :=
        (hda x).hasDerivAt.mul hθ.cos
      have h2 : HasDerivAt (fun y => b y * Real.sin (argTheta a b t₀ y))
          (deriv b x * Real.sin (argTheta a b t₀ x)
            + b x * (Real.cos (argTheta a b t₀ x) * argOmega a b x)) x :=
        (hdb x).hasDerivAt.mul hθ.sin
      have hsum : HasDerivAt
          (fun y => a y * Real.cos (argTheta a b t₀ y) + b y * Real.sin (argTheta a b t₀ y))
          ((deriv a x * Real.cos (argTheta a b t₀ x)
            + a x * (-Real.sin (argTheta a b t₀ x) * argOmega a b x))
            + (deriv b x * Real.sin (argTheta a b t₀ x)
            + b x * (Real.cos (argTheta a b t₀ x) * argOmega a b x))) x := h1.add h2
      rw [hsum.deriv, hder_a x, hder_b x]
      ring
    intro x
    have h0 := is_const_of_deriv_eq_zero hdiff hderiv x 0
    rw [h0]
    show a 0 * Real.cos (argTheta a b t₀ 0) + b 0 * Real.sin (argTheta a b t₀ 0) = 1
    simp only [argTheta, intervalIntegral.integral_same, add_zero]
    rw [hcos0, hsin0]
    nlinarith [hunit 0]
  have hsEq : ∀ x, b x * Real.cos (argTheta a b t₀ x) - a x * Real.sin (argTheta a b t₀ x) = 0 := by
    have hdiff : Differentiable ℝ
        (fun x => b x * Real.cos (argTheta a b t₀ x) - a x * Real.sin (argTheta a b t₀ x)) := by
      intro x
      have hθ : HasDerivAt (argTheta a b t₀) (argOmega a b x) x := hΘderiv x
      change DifferentiableAt ℝ (fun y => b y * Real.cos (argTheta a b t₀ y)
        - a y * Real.sin (argTheta a b t₀ y)) x
      exact (((hdb x).hasDerivAt.mul hθ.cos).sub ((hda x).hasDerivAt.mul hθ.sin)).differentiableAt
    have hderiv : ∀ x, deriv
        (fun x => b x * Real.cos (argTheta a b t₀ x) - a x * Real.sin (argTheta a b t₀ x)) x
        = 0 := by
      intro x
      have hθ : HasDerivAt (argTheta a b t₀) (argOmega a b x) x := hΘderiv x
      have h1 : HasDerivAt (fun y => b y * Real.cos (argTheta a b t₀ y))
          (deriv b x * Real.cos (argTheta a b t₀ x)
            + b x * (-Real.sin (argTheta a b t₀ x) * argOmega a b x)) x :=
        (hdb x).hasDerivAt.mul hθ.cos
      have h2 : HasDerivAt (fun y => a y * Real.sin (argTheta a b t₀ y))
          (deriv a x * Real.sin (argTheta a b t₀ x)
            + a x * (Real.cos (argTheta a b t₀ x) * argOmega a b x)) x :=
        (hda x).hasDerivAt.mul hθ.sin
      have hsum : HasDerivAt
          (fun y => b y * Real.cos (argTheta a b t₀ y) - a y * Real.sin (argTheta a b t₀ y))
          ((deriv b x * Real.cos (argTheta a b t₀ x)
            + b x * (-Real.sin (argTheta a b t₀ x) * argOmega a b x))
            - (deriv a x * Real.sin (argTheta a b t₀ x)
            + a x * (Real.cos (argTheta a b t₀ x) * argOmega a b x))) x := h1.sub h2
      rw [hsum.deriv, hder_a x, hder_b x]
      ring
    intro x
    have h0 := is_const_of_deriv_eq_zero hdiff hderiv x 0
    rw [h0]
    show b 0 * Real.cos (argTheta a b t₀ 0) - a 0 * Real.sin (argTheta a b t₀ 0) = 0
    simp only [argTheta, intervalIntegral.integral_same, add_zero]
    rw [hcos0, hsin0]
    ring
  have hcosθ : ∀ x, Real.cos (argTheta a b t₀ x) = a x := by
    intro x
    have h1 : Real.cos (argTheta a b t₀ x)
        = Real.cos (argTheta a b t₀ x) * (a x ^ 2 + b x ^ 2) := by rw [hunit x, mul_one]
    rw [h1]
    have h2 : Real.cos (argTheta a b t₀ x) * (a x ^ 2 + b x ^ 2)
        = a x * (a x * Real.cos (argTheta a b t₀ x) + b x * Real.sin (argTheta a b t₀ x))
          + b x * (b x * Real.cos (argTheta a b t₀ x) - a x * Real.sin (argTheta a b t₀ x)) := by
      ring
    rw [h2, hcEq x, hsEq x]
    ring
  have hsinθ : ∀ x, Real.sin (argTheta a b t₀ x) = b x := by
    intro x
    have h1 : Real.sin (argTheta a b t₀ x)
        = Real.sin (argTheta a b t₀ x) * (a x ^ 2 + b x ^ 2) := by rw [hunit x, mul_one]
    rw [h1]
    have h2 : Real.sin (argTheta a b t₀ x) * (a x ^ 2 + b x ^ 2)
        = b x * (a x * Real.cos (argTheta a b t₀ x) + b x * Real.sin (argTheta a b t₀ x))
          - a x * (b x * Real.cos (argTheta a b t₀ x) - a x * Real.sin (argTheta a b t₀ x)) := by
      ring
    rw [h2, hcEq x, hsEq x]
    ring
  -- ## 7. the period: `θ (x+1) - θ x` is constant and lies in `2πℤ`
  have hΩper : ∀ x, argOmega a b (x + 1) = argOmega a b x := by
    intro x
    have hA : deriv a (x + 1) = deriv a x := deriv_comp_add_one hda hpera x
    have hB : deriv b (x + 1) = deriv b x := deriv_comp_add_one hdb hperb x
    simp only [argOmega, hpera x, hperb x, hA, hB]
  have hCderiv : ∀ x, deriv (fun y => argTheta a b t₀ (y + 1) - argTheta a b t₀ y) x = 0 := by
    intro x
    have h1 : HasDerivAt (fun y => argTheta a b t₀ (y + 1)) (argOmega a b (x + 1)) x :=
      HasDerivAt.comp_add_const x 1 (hΘderiv (x + 1))
    have hsum : HasDerivAt (fun y => argTheta a b t₀ (y + 1) - argTheta a b t₀ y)
        (argOmega a b (x + 1) - argOmega a b x) x := h1.sub (hΘderiv x)
    rw [hsum.deriv, hΩper x, sub_self]
  have hCdiff : Differentiable ℝ (fun y => argTheta a b t₀ (y + 1) - argTheta a b t₀ y) := by
    intro y
    have h1 : HasDerivAt (fun z => argTheta a b t₀ (z + 1)) (argOmega a b (y + 1)) y :=
      HasDerivAt.comp_add_const y 1 (hΘderiv (y + 1))
    exact (h1.sub (hΘderiv y)).differentiableAt
  have hCconst : ∀ y, argTheta a b t₀ (y + 1) - argTheta a b t₀ y
      = argTheta a b t₀ 1 - argTheta a b t₀ 0 := by
    intro y
    have h := is_const_of_deriv_eq_zero hCdiff hCderiv y 0
    simpa using h
  have hcosC : Real.cos (argTheta a b t₀ 1 - argTheta a b t₀ 0) = 1 := by
    have ha1 : a 1 = a 0 := by simpa using hpera 0
    have hb1 : b 1 = b 0 := by simpa using hperb 0
    rw [Real.cos_sub, hcosθ 1, hcosθ 0, hsinθ 1, hsinθ 0, ha1, hb1]
    nlinarith [hunit 0]
  obtain ⟨m, hm⟩ := (Real.cos_eq_one_iff _).mp hcosC
  have hper : ∀ x, argTheta a b t₀ (x + 1) = argTheta a b t₀ x + (m : ℝ) * (2 * Real.pi) := by
    intro x
    have h := hCconst x
    linarith
  -- ## 8. the increment is a nonzero multiple of `2π`, hence exactly `±2π`
  have hm_ne : m ≠ 0 := by
    intro hm0
    have hsub : argTheta a b t₀ 1 - argTheta a b t₀ 0 = 0 := by
      rw [← hm, hm0]; ring
    obtain ⟨c, -, hcd⟩ := exists_deriv_eq_slope (argTheta a b t₀) zero_lt_one
      hΘcont.continuousOn hΘdiff.differentiableOn
    have hcz : deriv (argTheta a b t₀) c = 0 := by rw [hcd, hsub]; simp
    have hne := hΩne c
    rw [hΘderivVal c] at hcz
    exact hne hcz
  exact ⟨argTheta a b t₀, hΘcd, hcosθ, hsinθ, fun x => by rw [hΘderivVal x]; exact hΩne x,
    m, hm_ne, hper⟩

/-- **The argument lift of a plane curve about the origin, `C^∞` level, without the injectivity
hypothesis.**  Let `z : ℝ → ℂ` be `C^∞`, `1`-periodic, nowhere zero, and with nowhere vanishing
angular rate `ω t = Im (conj (z t) * deriv z t)`.  Then there are a `C^∞` function `θ` and an
integer `m ≠ 0` with `deriv θ ≠ 0`, `z t = ‖z t‖ • exp (i θ t)` (written in coordinates below) and
`θ (t + 1) = θ t + m * 2π`.

This is `Work.Drive.N2Lead.smoothArgLiftCinf` (`Submission/Work/Drive/N2Lead/smoothArgLiftCinf.lean`,
proved, `sorry`-free) with the hypothesis `hinj` (the direction curve is injective modulo the period)
**removed**; the proof is that of `smoothArgLiftCinf` with the whole final step (`hm_one`, which is
where `hinj` is used) deleted, keeping only `hm_ne`.  Concretely: put
`ψ t := (‖z t‖⁻¹ : ℂ) * z t`, `a t := (ψ t).re`, `b t := (ψ t).im`; then `a`, `b` are `C^∞`,
`1`-periodic, `a ^ 2 + b ^ 2 = 1` (as `‖ψ t‖ = 1`), and
`a t * deriv b t - b t * deriv a t = (conj (z t) * deriv z t).im / ‖z t‖ ^ 2`, so the hypothesis
`hω` gives the `himm` row of `smoothArgLiftCinf`; the starting angle comes from `Complex.arg`. -/
theorem smoothArgLiftComplex {z : ℝ → ℂ}
    (hz : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) z) (hper : ∀ t : ℝ, z (t + 1) = z t)
    (hne : ∀ t : ℝ, z t ≠ 0)
    (hω : ∀ t : ℝ, (star (z t) * deriv z t).im ≠ 0) :
    ∃ (θ : ℝ → ℝ) (m : ℤ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ ∧ m ≠ 0 ∧
      (∀ t : ℝ, deriv θ t ≠ 0) ∧
      (∀ t : ℝ, (‖z t‖ : ℂ) * (⟨Real.cos (θ t), Real.sin (θ t)⟩ : ℂ) = z t) ∧
      (∀ t : ℝ, θ (t + 1) = θ t + (m : ℝ) * (2 * Real.pi)) := by
  -- the unit direction curve `ψ = z / ‖z‖` and its coordinates `(a, b)`
  set c : ℝ → ℝ := fun t => (‖z t‖)⁻¹ with hc
  set ψ : ℝ → ℂ := fun t => (c t : ℂ) * z t with hψ
  set a : ℝ → ℝ := fun t => (ψ t).re with ha
  set b : ℝ → ℝ := fun t => (ψ t).im with hb
  -- ## smoothness of `c`, `ψ`, `a`, `b`
  have hc_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c := by
    rw [hc]
    exact (ContDiff.norm ℝ hz hne).inv (fun t => norm_ne_zero_iff.mpr (hne t))
  have hcC_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => ((c t : ℝ) : ℂ)) := by
    convert (Complex.ofRealCLM.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).comp hc_sm using 1
    ext t; simp [Complex.ofRealCLM_apply]
  have hψ_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ := by
    rw [hψ]; exact hcC_sm.mul hz
  have ha_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a := by
    rw [ha]
    convert Complex.reCLM.contDiff.comp hψ_sm using 1
    ext s; simp [Complex.reCLM_apply]
  have hb_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b := by
    rw [hb]
    convert Complex.imCLM.contDiff.comp hψ_sm using 1
    ext s; simp [Complex.imCLM_apply]
  -- ## `ψ` never vanishes and has unit modulus
  have hc_ne : ∀ t, c t ≠ 0 := by
    intro t; rw [hc]; exact inv_ne_zero (norm_ne_zero_iff.mpr (hne t))
  have hψ_ne : ∀ t, ψ t ≠ 0 := by
    intro t
    have h1 : (c t : ℂ) ≠ 0 := by exact_mod_cast hc_ne t
    rw [hψ]
    exact mul_ne_zero h1 (hne t)
  have hψnormsq : ∀ t, Complex.normSq (ψ t) = 1 := by
    intro t
    have hzt : ‖z t‖ ≠ 0 := norm_ne_zero_iff.mpr (hne t)
    rw [hψ, Complex.normSq_mul, Complex.normSq_ofReal, hc, Complex.normSq_eq_norm_sq]
    field_simp
  have hψnorm : ∀ t, ‖ψ t‖ = 1 := by
    intro t
    have h := hψnormsq t
    rw [Complex.normSq_eq_norm_sq] at h
    nlinarith [norm_nonneg (ψ t)]
  -- ## the rows of the real engine
  have hunit : ∀ t, a t ^ 2 + b t ^ 2 = 1 := by
    intro t
    have h := hψnormsq t
    rw [Complex.normSq_apply] at h
    have h' : (ψ t).re * (ψ t).re + (ψ t).im * (ψ t).im = 1 := h
    rw [ha, hb]
    simp only
    rw [pow_two, pow_two]
    exact h'
  have ha_apply : ∀ t, a t = c t * (z t).re := by
    intro t; simp [ha, hψ, Complex.mul_re]
  have hb_apply : ∀ t, b t = c t * (z t).im := by
    intro t; simp [hb, hψ, Complex.mul_im]
  have hpera : ∀ t, a (t + 1) = a t := by
    intro t
    have hc_per : c (t + 1) = c t := by rw [hc]; simp only [hper t]
    rw [ha]
    simp only [hψ, hc_per, hper t]
  have hperb : ∀ t, b (t + 1) = b t := by
    intro t
    have hc_per : c (t + 1) = c t := by rw [hc]; simp only [hper t]
    rw [hb]
    simp only [hψ, hc_per, hper t]
  have h0 : ∃ t₀ : ℝ, Real.cos t₀ = a 0 ∧ Real.sin t₀ = b 0 := by
    refine ⟨(ψ 0).arg, ?_, ?_⟩
    · exact (show Real.cos (ψ 0).arg = (ψ 0).re from by
        rw [Complex.cos_arg (hψ_ne 0), hψnorm 0, div_one])
    · exact (show Real.sin (ψ 0).arg = (ψ 0).im from by
        rw [Complex.sin_arg, hψnorm 0, div_one])
  -- ## the signed speed of `(a, b)` is `Im (conj z * z') / ‖z‖ ^ 2`
  have hzre_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => (z s).re) := by
    convert Complex.reCLM.contDiff.comp hz using 1
    ext s; simp [Complex.reCLM_apply]
  have hzim_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => (z s).im) := by
    convert Complex.imCLM.contDiff.comp hz using 1
    ext s; simp [Complex.imCLM_apply]
  have hzre_diff : Differentiable ℝ (fun s : ℝ => (z s).re) := hzre_sm.differentiable (by simp)
  have hzim_diff : Differentiable ℝ (fun s : ℝ => (z s).im) := hzim_sm.differentiable (by simp)
  have hc_diff : Differentiable ℝ c := hc_sm.differentiable (by simp)
  have hzre_deriv : ∀ t, deriv (fun s : ℝ => (z s).re) t = (deriv z t).re := by
    intro t
    have h := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) t (Complex.reCLM.hasFDerivAt (x := z t))
      ((hz.differentiable (by simp) t).hasDerivAt)
    rw [show (fun s : ℝ => (z s).re) = ⇑Complex.reCLM ∘ z from by
      funext s; simp [Complex.reCLM_apply]]
    simpa [Complex.reCLM_apply] using h.deriv
  have hzim_deriv : ∀ t, deriv (fun s : ℝ => (z s).im) t = (deriv z t).im := by
    intro t
    have h := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) t (Complex.imCLM.hasFDerivAt (x := z t))
      ((hz.differentiable (by simp) t).hasDerivAt)
    rw [show (fun s : ℝ => (z s).im) = ⇑Complex.imCLM ∘ z from by
      funext s; simp [Complex.imCLM_apply]]
    simpa [Complex.imCLM_apply] using h.deriv
  have hderiv_a : ∀ t, deriv a t = deriv c t * (z t).re + c t * (deriv z t).re := by
    intro t
    have h1 := (hc_diff t).hasDerivAt.mul (hzre_diff t).hasDerivAt
    rw [hzre_deriv t] at h1
    rw [show a = fun s : ℝ => c s * (z s).re from funext ha_apply]
    exact h1.deriv
  have hderiv_b : ∀ t, deriv b t = deriv c t * (z t).im + c t * (deriv z t).im := by
    intro t
    have h1 := (hc_diff t).hasDerivAt.mul (hzim_diff t).hasDerivAt
    rw [hzim_deriv t] at h1
    rw [show b = fun s : ℝ => c s * (z s).im from funext hb_apply]
    exact h1.deriv
  have himm : ∀ t, a t * deriv b t - b t * deriv a t ≠ 0 := by
    intro t
    rw [hderiv_b t, hderiv_a t, ha_apply t, hb_apply t]
    have hkey : c t * (z t).re * (deriv c t * (z t).im + c t * (deriv z t).im)
        - c t * (z t).im * (deriv c t * (z t).re + c t * (deriv z t).re)
        = c t ^ 2 * (star (z t) * deriv z t).im := by
      rw [Complex.mul_im]
      simp
      ring
    rw [hkey]
    exact mul_ne_zero (pow_ne_zero 2 (hc_ne t)) (hω t)
  -- ## apply the real engine and rewrite back in terms of `z`
  obtain ⟨θ, hθsm, hcos, hsin, hθderiv, m, hmne, hθper⟩ :=
    argLiftCinfNoInj ha_sm hb_sm hunit hpera hperb h0 himm
  refine ⟨θ, m, hθsm, hmne, hθderiv, ?_, hθper⟩
  intro t
  have hpair : (⟨Real.cos (θ t), Real.sin (θ t)⟩ : ℂ) = (c t : ℂ) * z t := by
    rw [hcos t, hsin t, ha_apply t, hb_apply t]
    refine Complex.ext ?_ ?_ <;> simp [Complex.mul_re, Complex.mul_im]
  rw [hpair]
  have h1 : ((‖z t‖ : ℝ) : ℂ) * ((c t : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul]
    have h2 : ‖z t‖ * c t = 1 := by
      rw [hc]; exact mul_inv_cancel₀ (norm_ne_zero_iff.mpr (hne t))
    rw [h2, Complex.ofReal_one]
  rw [← mul_assoc, h1, one_mul]

end

end Work.Drive.N2Lead
