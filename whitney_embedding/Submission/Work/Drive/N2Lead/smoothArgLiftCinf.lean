import Mathlib

namespace Work.Drive.N2Lead

open scoped ContDiff Topology

noncomputable section

/-!
# The smooth (`C^∞`) argument lift along a unit-speed closed curve

Pure real analysis: a `1`-periodic `C^∞` curve `(a,b)` in the unit circle with nowhere vanishing
`signed speed ω = a b' - b a'` and injective modulo the period is the round picture
`x ↦ (cos (θ x), sin (θ x))` of a `C^∞` function `θ` with nonvanishing derivative, advancing by
exactly one period `±2π` when `x` runs over a period.

This is the `((⊤ : ℕ∞) : WithTop ℕ∞)` (i.e. `∞`) version of
`Work.Drive.N2Lead.smoothArgLift` (which is the analytic version, `ContDiff ℝ ⊤`).  Only the
smoothness step changes: `θ := θ₀ + ∫₀ˣ ω` has derivative the `C^∞` function `ω`, so it is `C^∞`
by `contDiff_infty_iff_deriv`.  Everything else is the same argument as in the analytic file.
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

/-- **Smooth argument lift along a round-image curve (1-D, pure real analysis), at the `C^∞` level**
(level `((⊤ : ℕ∞) : WithTop ℕ∞)`, i.e. the notation `∞`, deliberately not the bare `⊤` of
`ContDiff ℝ ⊤` which means analytic).

Let `a b : ℝ → ℝ` be `C^∞`, `1`-periodic, with `a x ^ 2 + b x ^ 2 = 1` for all `x`, with
`ω x := a x * deriv b x - b x * deriv a x` nowhere zero, and with `(a,b)` injective modulo the
period.  Then `(a, b)` is the round picture `x ↦ (cos (θ x), sin (θ x))` of a `C^∞` function `θ`
with nonvanishing derivative, and `θ` advances by exactly one period `±2π` over a period.

The file `Submission/Work/Drive/N2Lead/smoothArgLift.lean` contains a *proved* version of this
statement at the analytic level (`ContDiff ℝ ⊤`); only the smoothness steps change: `θ := θ₀ + ∫₀ˣ ω`
with `θ₀` from `h0` is `C^∞` because its derivative is the `C^∞` function `ω` (induction on the
number of derivatives, or `ContDiff` of the parameter integral of a `C^∞` function).  Everything
else — the identities `cos ∘ θ = a`, `sin ∘ θ = b` via
`deriv (a * cos ∘ θ + b * sin ∘ θ) = 0`, `deriv (b * cos ∘ θ - a * sin ∘ θ) = 0` and `hunit`, and
the period argument (`θ (x+1) - θ x` is continuous with values in `(2π) • ℤ`, hence constant; `0` is
excluded by `deriv θ ≠ 0`, `|δ| ≥ 2` by `hinj` and the intermediate value property) is unchanged. -/
theorem smoothArgLiftCinf {a b : ℝ → ℝ}
    (ha : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) a) (hb : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b)
    (hunit : ∀ x, a x ^ 2 + b x ^ 2 = 1)
    (hpera : ∀ x, a (x + 1) = a x) (hperb : ∀ x, b (x + 1) = b x)
    (h0 : ∃ t₀ : ℝ, Real.cos t₀ = a 0 ∧ Real.sin t₀ = b 0)
    (himm : ∀ x, a x * deriv b x - b x * deriv a x ≠ 0)
    (hinj : ∀ x y : ℝ, a x = a y → b x = b y → ∃ k : ℤ, y = x + k) :
    ∃ θ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ ∧ (∀ x, Real.cos (θ x) = a x) ∧
      (∀ x, Real.sin (θ x) = b x) ∧ (∀ x, deriv θ x ≠ 0) ∧
      ∃ δ : ℝ, (δ = 1 ∨ δ = -1) ∧ ∀ x, θ (x + 1) = θ x + δ * (2 * Real.pi) := by
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
  have hm_one : m = 1 ∨ m = -1 := by
    rcases lt_or_gt_of_ne hm_ne with hneg | hpos
    · -- `m < 0`
      refine Or.inr ?_
      by_contra hne1
      have hm2 : m ≤ -2 := by omega
      have hmR : (m : ℝ) < -1 := by exact_mod_cast (show m < (-1 : ℤ) by omega)
      have hrepr : argTheta a b t₀ 1 - argTheta a b t₀ 0 = (m : ℝ) * (2 * Real.pi) := by
        have := hper 0; linarith
      have hcont : ContinuousOn (fun t : ℝ => argTheta a b t₀ 0 - argTheta a b t₀ t)
          (Set.Icc 0 1) := (continuous_const.sub hΘcont).continuousOn
      have hmem : 2 * Real.pi ∈ Set.Ioo
          ((fun t : ℝ => argTheta a b t₀ 0 - argTheta a b t₀ t) 0)
          ((fun t : ℝ => argTheta a b t₀ 0 - argTheta a b t₀ t) 1) := by
        constructor
        · show argTheta a b t₀ 0 - argTheta a b t₀ 0 < 2 * Real.pi
          linarith [Real.two_pi_pos]
        · show 2 * Real.pi < argTheta a b t₀ 0 - argTheta a b t₀ 1
          nlinarith [hrepr, hmR, Real.two_pi_pos]
      obtain ⟨t, ht, htu⟩ := intermediate_value_Ioo (show (0 : ℝ) ≤ 1 by norm_num) hcont hmem
      have htval : argTheta a b t₀ t = argTheta a b t₀ 0 - 2 * Real.pi := by linarith
      have hat : a t = a 0 := by
        rw [← hcosθ t, ← hcosθ 0, htval, Real.cos_sub_two_pi]
      have hbt : b t = b 0 := by
        rw [← hsinθ t, ← hsinθ 0, htval, Real.sin_sub_two_pi]
      obtain ⟨k, hk⟩ := hinj 0 t hat.symm hbt.symm
      have hk' : (k : ℝ) = t := by linarith [hk]
      have hk1 : (0 : ℤ) < k := Int.cast_pos.mp (by rw [hk']; exact ht.1)
      have hk2 : k < 1 := by
        have : (k : ℝ) < 1 := by rw [hk']; exact ht.2
        exact_mod_cast this
      omega
    · -- `0 < m`
      refine Or.inl ?_
      by_contra hne1
      have hm2 : 2 ≤ m := by omega
      have hmR : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show (1 : ℤ) < m by omega)
      have hrepr : argTheta a b t₀ 1 - argTheta a b t₀ 0 = (m : ℝ) * (2 * Real.pi) := by
        have := hper 0; linarith
      have hcont : ContinuousOn (fun t : ℝ => argTheta a b t₀ t - argTheta a b t₀ 0)
          (Set.Icc 0 1) := (hΘcont.sub continuous_const).continuousOn
      have hmem : 2 * Real.pi ∈ Set.Ioo
          ((fun t : ℝ => argTheta a b t₀ t - argTheta a b t₀ 0) 0)
          ((fun t : ℝ => argTheta a b t₀ t - argTheta a b t₀ 0) 1) := by
        constructor
        · show argTheta a b t₀ 0 - argTheta a b t₀ 0 < 2 * Real.pi
          linarith [Real.two_pi_pos]
        · show 2 * Real.pi < argTheta a b t₀ 1 - argTheta a b t₀ 0
          nlinarith [hrepr, hmR, Real.two_pi_pos]
      obtain ⟨t, ht, htu⟩ := intermediate_value_Ioo (show (0 : ℝ) ≤ 1 by norm_num) hcont hmem
      have htval : argTheta a b t₀ t = argTheta a b t₀ 0 + 2 * Real.pi := by linarith
      have hat : a t = a 0 := by
        rw [← hcosθ t, ← hcosθ 0, htval, Real.cos_add_two_pi]
      have hbt : b t = b 0 := by
        rw [← hsinθ t, ← hsinθ 0, htval, Real.sin_add_two_pi]
      obtain ⟨k, hk⟩ := hinj 0 t hat.symm hbt.symm
      have hk' : (k : ℝ) = t := by linarith [hk]
      have hk1 : (0 : ℤ) < k := Int.cast_pos.mp (by rw [hk']; exact ht.1)
      have hk2 : k < 1 := by
        have : (k : ℝ) < 1 := by rw [hk']; exact ht.2
        exact_mod_cast this
      omega
  exact ⟨argTheta a b t₀, hΘcd, hcosθ, hsinθ, fun x => by rw [hΘderivVal x]; exact hΩne x,
    (m : ℝ), hm_one.imp (fun h => by exact_mod_cast h) (fun h => by exact_mod_cast h), hper⟩

end

end Work.Drive.N2Lead
