import Mathlib

/-!
# Orthogonality of characters on `ℝ/ℤ` and the windowed Fourier coefficient identity

For absolutely summable sequences `g w : ℤ → ℂ`, an arbitrary map `Q : ℤ → ℤ` and `x : ℤ` we
prove the Fourier-coefficient (Parseval) identity

  `∫ t in 0..1, (∑' n, w n · e (t * Q n)) * (∑' y, g y · e (-(y * t))) * e (x * t)
      = ∑' n, w n * g (x + Q n)`,

where `e (s) = Complex.exp (2 * π * I * s)` is the additive character.

The integrand is the product of the two trigonometric series
`∑' n, w n · e^{2πi t (Q n)}` and `∑' y, g y · e^{2πi t (x - y)}`; expanding it as an
absolutely convergent double series `∑' p : ℤ × ℤ` and integrating term by term, the
orthogonality of the characters `t ↦ e^{2πi t m}` on `[0,1]`
(`∫_0^1 e^{2πi t m} dt = δ_{m,0}`, `winExp_integral`) selects exactly the pairs with
`Q p.1 - p.2 + x = 0`, that is `p.2 = x + Q p.1`.

The interchange of the integral with the double series is legitimised by absolute convergence:
on the probability space `volume.restrict (Ioc 0 1)` every summand is bounded by
`‖w p.1‖ * ‖g p.2‖`, which is summable on `ℤ × ℤ`.
-/

open MeasureTheory
open scoped BigOperators

set_option linter.style.haveILetI false

namespace Work.KMTAreas.A4

/-- The additive character of `ℤ` evaluated at the real point `t`: `m ↦ e^{2πi t m}`. -/
noncomputable def winExp (t : ℝ) (m : ℤ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (t * (m : ℝ)))

/-- The character `winExp t` is multiplicative in the integer index. -/
theorem winExp_add (t : ℝ) (a b : ℤ) : winExp t (a + b) = winExp t a * winExp t b := by
  rw [winExp, winExp, winExp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `winExp t (-y)` has the shape of the conjugate character occurring in the
`y`-sum of the main identity. -/
theorem winExp_neg (t : ℝ) (y : ℤ) :
    winExp t (-y) = Complex.exp (-(2 * Real.pi * Complex.I * ((y : ℝ) * t))) := by
  rw [winExp]; congr 1; push_cast; ring

/-- The character has modulus one. -/
theorem norm_winExp (t : ℝ) (m : ℤ) : ‖winExp t m‖ = 1 := by
  rw [winExp, ← Complex.norm_exp_ofReal_mul_I (2 * Real.pi * t * m)]
  congr 1
  push_cast
  ring_nf

/-- The character at the index `0` is the constant function `1`. -/
theorem winExp_zero (t : ℝ) : winExp t 0 = 1 := by simp [winExp]

/-- The character, written in the form used by `integral_exp_mul_complex`. -/
theorem winExp_eq_char (t : ℝ) (m : ℤ) :
    winExp t m = Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)) * (t : ℂ)) := by
  rw [winExp]; congr 1; push_cast; ring

/-- The character is continuous as a function of the real parameter. -/
theorem continuous_winExp (m : ℤ) : Continuous fun t : ℝ => winExp t m := by
  rw [show (fun t : ℝ => winExp t m)
      = fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * (t * (m : ℝ))) from rfl]
  fun_prop

/-- **Orthogonality of the characters on `[0,1]`**:
`∫_0^1 e^{2πi t m} dt` equals `1` for `m = 0` and `0` otherwise. -/
theorem winExp_integral (m : ℤ) :
    (∫ t in (0:ℝ)..1, winExp t m) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · rw [hm]; simp [winExp_zero, intervalIntegral.integral_const]
  · have hq : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      simp [hpi, Complex.I_ne_zero]
    have hc : (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)) ≠ 0 := by
      intro h
      rcases mul_eq_zero.mp h with h1 | h1
      · exact hq h1
      · exact hm (Int.cast_eq_zero.mp h1)
    have hc2 : 2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)
        = (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by ring
    rw [show (∫ t in (0:ℝ)..1, winExp t m) = ∫ t in (0:ℝ)..1,
        Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * (m : ℂ)) * (t : ℂ)) from
      intervalIntegral.integral_congr (fun t _ => winExp_eq_char t m)]
    rw [integral_exp_mul_complex hc]
    simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, Complex.exp_zero]
    rw [hc2, Complex.exp_int_mul_two_pi_mul_I]
    simp [hm]

/-- The same orthogonality with the interval `[0,1]` replaced by the restricted measure
`volume.restrict (Ioc 0 1)` on which the summability estimates are taken. -/
theorem winExp_integral_Ioc (m : ℤ) :
    (∫ t, winExp t m ∂(volume.restrict (Set.Ioc (0:ℝ) 1))) = if m = 0 then 1 else 0 := by
  rw [← intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num)]
  exact winExp_integral m

/-- **The Fourier coefficient identity.**  With `e (s) = e^{2πi s}`,

`∫_0^1 (∑_n w n e (t Q n)) (∑_y g y e (-(y t))) e (x t) dt = ∑_n w n g (x + Q n)`. -/
theorem winFourierCoeff (g : ℤ → ℂ) (hg : Summable fun y : ℤ => ‖g y‖)
    (w : ℤ → ℂ) (hw : Summable fun n : ℤ => ‖w n‖) (Q : ℤ → ℤ) (x : ℤ) :
    (∫ t in (0 : ℝ)..1,
        (∑' n : ℤ, w n * Complex.exp (2 * Real.pi * Complex.I * (t * (Q n : ℝ)))) *
          (∑' y : ℤ, g y * Complex.exp (-(2 * Real.pi * Complex.I * ((y : ℝ) * t)))) *
          Complex.exp (2 * Real.pi * Complex.I * ((x : ℝ) * t)))
      = ∑' n : ℤ, w n * g (x + Q n) := by
  classical
  set μ : Measure ℝ := volume.restrict (Set.Ioc (0:ℝ) 1) with hμdef
  haveI : IsFiniteMeasure μ := by
    rw [hμdef, MeasureTheory.isFiniteMeasure_restrict, Real.volume_Ioc]
    simp
  have hb : Summable (fun p : ℤ × ℤ => ‖w p.1‖ * ‖g p.2‖) :=
    Summable.mul_of_nonneg (f := fun n : ℤ => ‖w n‖) (g := fun y : ℤ => ‖g y‖) hw hg
      (fun n => norm_nonneg _) (fun y => norm_nonneg _)
  -- The pointwise expansion of the integrand as an absolutely convergent double series.
  have hpt : ∀ t : ℝ,
      (∑' n : ℤ, w n * Complex.exp (2 * Real.pi * Complex.I * (t * (Q n : ℝ)))) *
          (∑' y : ℤ, g y * Complex.exp (-(2 * Real.pi * Complex.I * ((y : ℝ) * t)))) *
          Complex.exp (2 * Real.pi * Complex.I * ((x : ℝ) * t))
        = ∑' p : ℤ × ℤ, w p.1 * g p.2 * winExp t (Q p.1 - p.2 + x) := by
    intro t
    have h1 : ∀ n : ℤ, Complex.exp (2 * Real.pi * Complex.I * (t * (Q n : ℝ)))
        = winExp t (Q n) := fun n => rfl
    have h2 : ∀ y : ℤ, Complex.exp (-(2 * Real.pi * Complex.I * ((y : ℝ) * t)))
        = winExp t (-y) := fun y => (winExp_neg t y).symm
    have h3 : Complex.exp (2 * Real.pi * Complex.I * ((x : ℝ) * t)) = winExp t x := by
      rw [winExp]; congr 1; push_cast; ring
    simp only [h1, h2, h3]
    have hWs : Summable (fun n : ℤ => w n * winExp t (Q n)) :=
      Summable.of_norm_bounded (g := fun n : ℤ => ‖w n‖) hw
        (fun n => by rw [norm_mul, norm_winExp, mul_one])
    have hGs : Summable (fun y : ℤ => g y * winExp t (-y)) :=
      Summable.of_norm_bounded (g := fun y : ℤ => ‖g y‖) hg
        (fun y => by rw [norm_mul, norm_winExp, mul_one])
    have hWnorm : Summable (fun n : ℤ => ‖w n * winExp t (Q n)‖) := by
      simpa [norm_mul, norm_winExp] using hw
    have hGnorm : Summable (fun y : ℤ => ‖g y * winExp t (-y)‖) := by
      simpa [norm_mul, norm_winExp] using hg
    have hWGs : Summable
        (fun p : ℤ × ℤ => (w p.1 * winExp t (Q p.1)) * (g p.2 * winExp t (-p.2))) :=
      summable_mul_of_summable_norm (f := fun n : ℤ => w n * winExp t (Q n))
        (g := fun y : ℤ => g y * winExp t (-y)) hWnorm hGnorm
    rw [Summable.tsum_mul_tsum (f := fun n : ℤ => w n * winExp t (Q n))
      (g := fun y : ℤ => g y * winExp t (-y)) hWs hGs hWGs,
      ← Summable.tsum_mul_right (winExp t x) hWGs]
    refine tsum_congr (fun p => ?_)
    have h4 : winExp t (Q p.1 - p.2 + x)
        = winExp t (Q p.1) * winExp t (-p.2) * winExp t x := by
      rw [show Q p.1 - p.2 + x = (Q p.1 + -p.2) + x from by ring, winExp_add, winExp_add]
    rw [h4]
    ring
  -- Integrability of every summand on the probability space `μ`.
  have hF_int : ∀ p : ℤ × ℤ,
      Integrable (fun t : ℝ => w p.1 * g p.2 * winExp t (Q p.1 - p.2 + x)) μ := by
    intro p
    refine Integrable.of_bound ?_ (‖w p.1‖ * ‖g p.2‖) ?_
    · exact ((continuous_const.mul (continuous_winExp _)).aestronglyMeasurable)
    · filter_upwards with t
      simp [norm_winExp]
  have hμuniv : μ.real Set.univ = 1 := by
    rw [hμdef]
    simp [Measure.real, Real.volume_Ioc]
  -- Summability of the integrals of the norms.
  have hF_sum : Summable
      (fun p : ℤ × ℤ => ∫ t, ‖w p.1 * g p.2 * winExp t (Q p.1 - p.2 + x)‖ ∂μ) := by
    refine Summable.of_nonneg_of_le (fun p => integral_nonneg (fun t => norm_nonneg _))
      (fun p => ?_) hb
    have hbound : ∀ᵐ t ∂μ,
        ‖(fun t => ‖w p.1 * g p.2 * winExp t (Q p.1 - p.2 + x)‖) t‖
          ≤ ‖w p.1‖ * ‖g p.2‖ := by
      filter_upwards with t
      simp [norm_winExp]
    have hint := norm_integral_le_of_norm_le_const hbound
    rw [Real.norm_of_nonneg (integral_nonneg (fun t => norm_nonneg _)), hμuniv, mul_one] at hint
    exact hint
  -- The term by term integral.
  have hterm : ∀ p : ℤ × ℤ, (∫ t, w p.1 * g p.2 * winExp t (Q p.1 - p.2 + x) ∂μ)
      = if Q p.1 - p.2 + x = 0 then w p.1 * g p.2 else 0 := by
    intro p
    rw [hμdef, MeasureTheory.integral_const_mul, winExp_integral_Ioc]
    by_cases h : Q p.1 - p.2 + x = 0
    · rw [if_pos h, if_pos h, mul_one]
    · rw [if_neg h, if_neg h, mul_zero]
  -- The surviving terms are reindexed by `n ↦ (n, x + Q n)`.
  have collapse : (∑' p : ℤ × ℤ, (if Q p.1 - p.2 + x = 0 then w p.1 * g p.2 else 0))
      = ∑' n : ℤ, w n * g (x + Q n) := by
    have hf : Summable
        (fun p : ℤ × ℤ => (if Q p.1 - p.2 + x = 0 then w p.1 * g p.2 else 0)) :=
      Summable.of_norm_bounded (g := fun p : ℤ × ℤ => ‖w p.1‖ * ‖g p.2‖) hb (fun p => by
        split_ifs with h
        · simp
        · simp only [norm_zero]
          positivity)
    rw [Summable.tsum_prod
      (f := fun p : ℤ × ℤ => (if Q p.1 - p.2 + x = 0 then w p.1 * g p.2 else 0)) hf]
    refine tsum_congr (fun n => ?_)
    show (∑' c : ℤ, if Q n - c + x = 0 then w n * g c else 0) = w n * g (x + Q n)
    rw [tsum_eq_single (x + Q n) (fun y hy => by rw [if_neg (by omega)])]
    rw [if_pos (by ring)]
  rw [intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num), ← hμdef]
  simp_rw [hpt]
  rw [← integral_tsum_of_summable_integral_norm
    (F := fun p : ℤ × ℤ => fun t : ℝ => w p.1 * g p.2 * winExp t (Q p.1 - p.2 + x))
    hF_int hF_sum]
  trans ∑' p : ℤ × ℤ, (if Q p.1 - p.2 + x = 0 then w p.1 * g p.2 else 0)
  · exact tsum_congr (fun p => hterm p)
  · exact collapse

end Work.KMTAreas.A4
