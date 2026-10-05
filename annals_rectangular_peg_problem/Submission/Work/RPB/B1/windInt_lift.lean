import Mathlib
import Submission.Work.RPB.B1.AreaPosDefs
import Submission.Work.RPB.B1.WindLiftDefs
import Submission.Work.RPB.B1.exp_integral_of_hasDerivAt
import Submission.Work.RPB.B1.hasDerivAt_windDir
import Submission.Work.RPB.B1.eq_const_of_exp_mul_I_eq_one

/-!
# The integral formula for the argument lift, and integrality of `windInt`

For a `C¹`, `2π`-periodic, nowhere-zero plane curve `u` we prove

* `windInt u 0 = (1/2π) ∮ Im (u'/u)` is an integer, and
* for *every* continuous `θ` with `u t = ‖u t‖·e^{iθ t}` the classical identity
  `∮_0^{2π} Im (u'/u) = θ(2π) - θ(0)` holds.

The proof does **not** need a lifting theorem for the covering `ℝ → S¹`.  Instead we use the
primitive `windPhase u s = ∫_0^s Im (u'/u)` introduced in `WindLiftDefs`:

* the "unwound" curve `windDir u s = e^{-i·windPhase u s}·u s` satisfies the linear ODE
  `w' = Re(u'/u)·w` (`Submission.Work.RPB.B1.hasDerivAt_windDir`), so by
  `Submission.Work.RPB.B1.exp_integral_of_hasDerivAt` it equals `e^{Λ s}·u 0` with `Λ` real-valued;
* taking moduli gives `‖u s‖ = e^{Λ s}‖u 0‖`, and dividing the two descriptions of `u s` by the
  modulus gives the *direction identity*
  `u s/‖u s‖ = e^{i·windPhase u s}·(u 0/‖u 0‖)`;
* at `s = 2π` periodicity forces `e^{i·windPhase u (2π)} = 1`, i.e. `windPhase u (2π) ∈ 2πℤ`,
  which is the integrality of `windInt u 0`;
* given any continuous lift `θ`, the direction identity gives `e^{i(θ s - windPhase u s - θ 0)} = 1`
  for all `s`; a continuous real function with `e^{iψ} = 1` is constant
  (`Submission.Work.RPB.B1.eq_const_of_exp_mul_I_eq_one`), so the exponent vanishes identically and
  `windPhase u s = θ s - θ 0` for all `s`, in particular at `s = 2π`.
-/

set_option autoImplicit false

namespace Work.RPB.B1

/-- A real number `x` with `e^{ix} = 1` is an integer multiple of `2π`. -/
lemma exists_int_mul_two_pi_of_exp_mul_I_eq_one {x : ℝ}
    (h : Complex.exp ((x : ℂ) * Complex.I) = 1) : ∃ n : ℤ, x = n * (2 * Real.pi) :=
  Circle.exp_eq_one.mp (Circle.coe_eq_one.mp (by rw [Circle.coe_exp]; exact h))

/-- `windPhase u` is continuous (it is the primitive of a continuous integrand). -/
lemma continuous_windPhase (u : ℝ → ℂ) (hu : ContDiff ℝ 1 u) (hne : ∀ t, u t ≠ 0) :
    Continuous (windPhase u) := by
  have hcont : Continuous (fun x : ℝ => (deriv u x / u x).im) :=
    Complex.continuous_im.comp ((hu.continuous_deriv le_rfl).div hu.continuous hne)
  have h : Continuous (fun s : ℝ => windPhase u s) := by
    simpa [windPhase] using
      (intervalIntegral.continuous_primitive (μ := MeasureTheory.volume)
        (f := fun x : ℝ => (deriv u x / u x).im) (fun a b => hcont.intervalIntegrable a b) 0)
  exact h

/-- **The unwound curve is a positive multiple of `u 0`**: `windDir u s = e^{Λ s}·u 0`, where
`Λ s = ∫_0^s Re (u'/u)` is the integrated logarithmic derivative. -/
lemma windDir_eq_exp_integral_re (u : ℝ → ℂ) (hu : ContDiff ℝ 1 u) (hne : ∀ t, u t ≠ 0) :
    ∀ s, windDir u s =
      Complex.exp (((∫ x in (0 : ℝ)..s, (deriv u x / u x).re : ℝ) : ℂ)) * u 0 := by
  have hderiv : Continuous (fun x : ℝ => deriv u x / u x) :=
    (hu.continuous_deriv le_rfl).div hu.continuous hne
  have hw := hasDerivAt_windDir u hu hne
  have h := exp_integral_of_hasDerivAt (windDir u) (fun x : ℝ => (deriv u x / u x).re)
    (Complex.continuous_re.comp hderiv) (fun s => by simpa using hw s)
  intro s
  simpa using h s

/-- **The direction identity**: for a nowhere-zero `C¹` curve,
`u s / ‖u s‖ = e^{i·windPhase u s} · (u 0 / ‖u 0‖)`. -/
lemma normalized_eq_exp_windPhase (u : ℝ → ℂ) (hu : ContDiff ℝ 1 u) (hne : ∀ t, u t ≠ 0) :
    ∀ s, u s / ((‖u s‖ : ℝ) : ℂ) =
      Complex.exp ((windPhase u s : ℂ) * Complex.I) * (u 0 / ((‖u 0‖ : ℝ) : ℂ)) := by
  have hode := windDir_eq_exp_integral_re u hu hne
  have hueq : ∀ s, u s = Complex.exp ((windPhase u s : ℂ) * Complex.I) *
      (Complex.exp (((∫ x in (0 : ℝ)..s, (deriv u x / u x).re : ℝ) : ℂ)) * u 0) := by
    intro s
    have h := hode s
    rw [windDir] at h
    have hcancel : Complex.exp ((windPhase u s : ℂ) * Complex.I) *
        Complex.exp (-((windPhase u s : ℂ) * Complex.I)) = 1 := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    calc u s = 1 * u s := (one_mul _).symm
      _ = (Complex.exp ((windPhase u s : ℂ) * Complex.I) *
            Complex.exp (-((windPhase u s : ℂ) * Complex.I))) * u s := by rw [hcancel]
      _ = Complex.exp ((windPhase u s : ℂ) * Complex.I) *
            (Complex.exp (-((windPhase u s : ℂ) * Complex.I)) * u s) := by rw [mul_assoc]
      _ = Complex.exp ((windPhase u s : ℂ) * Complex.I) *
            (Complex.exp (((∫ x in (0 : ℝ)..s, (deriv u x / u x).re : ℝ) : ℂ)) * u 0) := by
            rw [h]
  intro s
  have hnorm : ‖u s‖ = Real.exp (∫ x in (0 : ℝ)..s, (deriv u x / u x).re) * ‖u 0‖ := by
    rw [hueq s, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal]
    ring
  have hD : ((Real.exp (∫ x in (0 : ℝ)..s, (deriv u x / u x).re) : ℝ) : ℂ) ≠ 0 :=
    fun h0 => ne_of_gt (Real.exp_pos _) (Complex.ofReal_eq_zero.mp h0)
  rw [hnorm, hueq s, Complex.ofReal_mul, ← Complex.ofReal_exp, mul_div_assoc]
  rw [mul_div_mul_left _ _ hD]

theorem windInt_lift (u : ℝ → ℂ) (hu : ContDiff ℝ 1 u)
    (hper : ∀ t, u (t + 2 * Real.pi) = u t) (hne : ∀ t, u t ≠ 0) :
    (∃ k : ℤ, Work.RPB.B1.windInt u 0 = (k : ℝ)) ∧
      ∀ θ : ℝ → ℝ, Continuous θ →
        (∀ t, u t = (‖u t‖ : ℂ) * Complex.exp ((θ t : ℂ) * Complex.I)) →
        ∫ t in (0 : ℝ)..(2 * Real.pi), (deriv u t / (u t)).im = θ (2 * Real.pi) - θ 0 := by
  have hdir := normalized_eq_exp_windPhase u hu hne
  constructor
  · -- integrality: periodicity forces the total unwound angle to be a multiple of `2π`
    have hper0 : u (2 * Real.pi) = u 0 := by simpa using hper 0
    have h2 := hdir (2 * Real.pi)
    rw [hper0] at h2
    have hc : u 0 / ((‖u 0‖ : ℝ) : ℂ) ≠ 0 :=
      div_ne_zero (hne 0)
        (fun h0 => norm_ne_zero_iff.mpr (hne 0) (Complex.ofReal_eq_zero.mp h0))
    have hexp1 : Complex.exp ((windPhase u (2 * Real.pi) : ℂ) * Complex.I) = 1 :=
      mul_right_cancel₀ hc (by simpa using h2.symm)
    obtain ⟨n, hn⟩ := exists_int_mul_two_pi_of_exp_mul_I_eq_one hexp1
    refine ⟨n, ?_⟩
    have hwind : Work.RPB.B1.windInt u 0 = (1 / (2 * Real.pi)) * windPhase u (2 * Real.pi) := by
      simp [windInt, windPhase]
    have hpi : (2 * Real.pi) ≠ 0 := ne_of_gt Real.two_pi_pos
    rw [hwind, hn]
    field_simp
  · -- the integral formula: any continuous lift differs from `windPhase` by a constant
    intro θ hθ hrepr
    have hc : ∀ s, Complex.exp ((θ s : ℂ) * Complex.I) = u s / ((‖u s‖ : ℝ) : ℂ) := by
      intro s
      have h2 : ((‖u s‖ : ℝ) : ℂ) ≠ 0 :=
        fun h0 => norm_ne_zero_iff.mpr (hne s) (Complex.ofReal_eq_zero.mp h0)
      rw [eq_div_iff h2, mul_comm (Complex.exp ((θ s : ℂ) * Complex.I)), ← hrepr s]
    have hexp : ∀ s, Complex.exp (((θ s - windPhase u s - θ 0 : ℝ) : ℂ) * Complex.I) = 1 := by
      intro s
      have h1 : Complex.exp ((θ s : ℂ) * Complex.I) =
          Complex.exp (((windPhase u s : ℂ) * Complex.I) + ((θ 0 : ℂ) * Complex.I)) := by
        rw [Complex.exp_add, hc 0, ← hdir s, ← hc s]
      have h2 := Complex.exp_eq_exp_iff_exp_sub_eq_one.mp h1
      convert h2 using 2
      push_cast
      ring
    have hconst := eq_const_of_exp_mul_I_eq_one
      (ψ := fun s => θ s - windPhase u s - θ 0)
      ((hθ.sub (continuous_windPhase u hu hne)).sub continuous_const) hexp
    have hkey : ∀ s, windPhase u s = θ s - θ 0 := by
      intro s
      have h := hconst s
      have h0 : θ 0 - windPhase u 0 - θ 0 = 0 := by simp
      rw [h0] at h
      linarith
    have := hkey (2 * Real.pi)
    simpa [windPhase] using this

end Work.RPB.B1
