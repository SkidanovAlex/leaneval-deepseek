import Mathlib
import Submission.Work.A14D.ppc_aux

namespace Work.A14D

/-!
# `Work.A14D.deriv_evp_pureB5`

The derivative, on the open unit disc, of the evaluation of the pullback
`(B₆ ∘ y)(x) = B₆(x²/(x−1))`.

The proof is `B₆`-specific: the pullback identity `Work.C17.B6_deriv`
(`y·(B₆∘y)' = (B₃∘y)·y'`, with `B₃∘y = −½log(1−x)²`, `Work.C7.g_form`) is evaluated at
`z` with the analytic bridge `Work.CPull.evpMul` (evaluation is multiplicative on the unit
disc) and `Work.A14D.evp_deriv` (term-by-term differentiation); the closed form
`evp yps w = w²/(w−1)` (`Work.CPull.evp_sympPhi`) supplies the remaining pieces.
-/

open scoped BigOperators

/-- `evp` commutes with negation (no summability needed: `tsum_neg` is unconditional). -/
private lemma evp_neg_aux (f : PowerSeries ℚ) (z : ℂ) :
    Work.CPull.evp (-f) z = -Work.CPull.evp f z := by
  rw [Work.CPull.evp, Work.CPull.evp]
  have h : (fun n : ℕ => ((PowerSeries.coeff n (-f) : ℚ) : ℂ) * z ^ n)
      = fun n : ℕ => -(((PowerSeries.coeff n f : ℚ) : ℂ) * z ^ n) := by
    funext n
    rw [map_neg]
    push_cast
    ring
  rw [h, tsum_neg]

/-- `evp` commutes with multiplication by a constant series. -/
private lemma evp_C_mul_aux (c : ℚ) (f : PowerSeries ℚ) (z : ℂ) :
    Work.CPull.evp (PowerSeries.C c * f) z = (c : ℂ) * Work.CPull.evp f z := by
  rw [Work.CPull.evp, Work.CPull.evp]
  have h : (fun n : ℕ => ((PowerSeries.coeff n (PowerSeries.C c * f) : ℚ) : ℂ) * z ^ n)
      = fun n : ℕ => (c : ℂ) * (((PowerSeries.coeff n f : ℚ) : ℂ) * z ^ n) := by
    funext n
    rw [PowerSeries.coeff_C_mul]
    push_cast
    ring
  rw [h, tsum_mul_left]

/-- Polynomial growth of the coefficients of a constant series `C c`. -/
private lemma poly_growth_C_aux (c : ℚ) : ∃ C : ℝ, 0 ≤ C ∧ ∃ k : ℕ, ∀ n : ℕ,
    ‖((PowerSeries.coeff n (PowerSeries.C c) : ℚ) : ℂ)‖ ≤ C * ((n : ℝ) + 1) ^ k := by
  refine ⟨‖(c : ℂ)‖, norm_nonneg _, 0, fun n => ?_⟩
  rw [pow_zero, mul_one, PowerSeries.coeff_C]
  split_ifs with h
  · exact le_rfl
  · simp

theorem deriv_evp_pureB5 (z : ℂ) (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    HasDerivAt (fun w : ℂ =>
        Work.CPull.evp ((Submission.CDTPlan.pureB 5).subst Submission.CDT.sympY) w)
      (-(Complex.log (1 - z)) ^ 2 / 2 * ((z - 2) / (z * (z - 1)))) z := by
  have hz1 : z ≠ 1 := by
    intro h
    rw [h] at hz
    simp at hz
  have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 hz0
  have hz1sq : (z - 1) ^ 2 ≠ 0 := pow_ne_zero 2 hz1'
  have hzm1 : z * (z - 1) ≠ 0 := mul_ne_zero hz0 hz1'
  have hzmem : z ∈ Metric.ball (0 : ℂ) 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  -- ## growth bounds
  obtain ⟨Cg, hCg0, kg, hkg0⟩ := pureB_subst_poly_growth (5 : Fin 7)
  have hkg : ∀ n : ℕ, ‖((PowerSeries.coeff n (Work.C7.g (5 : Fin 7)) : ℚ) : ℂ)‖
      ≤ Cg * ((n : ℝ) + 1) ^ kg := hkg0
  obtain ⟨Cd, hCd0, kd, hkd⟩ := poly_growth_deriv hCg0 hkg
  obtain ⟨Cs, hCs0, ks, hks0⟩ := poly_growth_sympY
  have hks : ∀ n : ℕ, ‖((PowerSeries.coeff n Work.C7.yps : ℚ) : ℂ)‖
      ≤ Cs * ((n : ℝ) + 1) ^ ks := hks0
  obtain ⟨Cdy, hCdy0, kdy, hkdy⟩ := poly_growth_deriv hCs0 hks
  obtain ⟨CL, hCL0, kL, hkL⟩ := poly_growth_Lps
  obtain ⟨Cc, hCc0, kc, hkc⟩ := poly_growth_C_aux (-(1/2))
  -- ## summability of the weighted coefficient series on the disc
  have hsumL : Summable fun n : ℕ => ‖((PowerSeries.coeff n Work.C7.Lps : ℚ) : ℂ) * z ^ n‖ :=
    summable_abs_coeff_of_poly_growth hCL0 hkL hz
  have hsumL2 : Summable fun n : ℕ =>
      ‖((PowerSeries.coeff n (Work.C7.Lps * Work.C7.Lps) : ℚ) : ℂ) * z ^ n‖ :=
    (Work.CPull.evpMul Work.C7.Lps Work.C7.Lps z hsumL hsumL).1
  have hsumChalf : Summable fun n : ℕ =>
      ‖((PowerSeries.coeff n (PowerSeries.C (-(1/2) : ℚ)) : ℚ) : ℂ) * z ^ n‖ :=
    summable_abs_coeff_of_poly_growth hCc0 hkc hz
  have hsumyps : Summable fun n : ℕ =>
      ‖((PowerSeries.coeff n Work.C7.yps : ℚ) : ℂ) * z ^ n‖ :=
    summable_abs_coeff_of_poly_growth hCs0 hks hz
  have hsumdyps : Summable fun n : ℕ =>
      ‖((PowerSeries.coeff n (PowerSeries.derivative (R := ℚ) Work.C7.yps) : ℚ) : ℂ) * z ^ n‖ :=
    summable_abs_coeff_of_poly_growth hCdy0 hkdy hz
  have hsumg5 : Summable fun n : ℕ =>
      ‖((PowerSeries.coeff n (Work.C7.g (5 : Fin 7)) : ℚ) : ℂ) * z ^ n‖ :=
    summable_abs_coeff_of_poly_growth hCg0 hkg hz
  have hsumdg5 : Summable fun n : ℕ =>
      ‖((PowerSeries.coeff n (PowerSeries.derivative (R := ℚ) (Work.C7.g (5 : Fin 7))) : ℚ) : ℂ)
        * z ^ n‖ :=
    summable_abs_coeff_of_poly_growth hCd0 hkd hz
  -- ## the closed form of `B₃ ∘ y = g 2`
  have hCneg : (PowerSeries.C (-(1/2) : ℚ) : PowerSeries ℚ) = -(PowerSeries.C (1/2 : ℚ)) :=
    map_neg (PowerSeries.C : ℚ →+* PowerSeries ℚ) (1/2)
  have hg2eq : Work.C7.g (2 : Fin 7)
      = PowerSeries.C (-(1/2) : ℚ) * (Work.C7.Lps * Work.C7.Lps) := by
    rw [Work.C7.g_form.2.1, hCneg, pow_two]
  have hsumg2 : Summable fun n : ℕ =>
      ‖((PowerSeries.coeff n (Work.C7.g (2 : Fin 7)) : ℚ) : ℂ) * z ^ n‖ := by
    rw [hg2eq]
    exact (Work.CPull.evpMul (PowerSeries.C (-(1/2) : ℚ)) (Work.C7.Lps * Work.C7.Lps) z
      hsumChalf hsumL2).1
  have hratcast : (((-(1/2) : ℚ)) : ℂ) = -(1/2 : ℂ) := by norm_num
  have hLpsval : Work.CPull.evp Work.C7.Lps z = Complex.log (1 - z) :=
    (Work.C7.hasSum_Lps hz).tsum_eq
  have hLps2val : Work.CPull.evp (Work.C7.Lps * Work.C7.Lps) z
      = (Complex.log (1 - z)) ^ 2 := by
    rw [(Work.CPull.evpMul Work.C7.Lps Work.C7.Lps z hsumL hsumL).2.2.2, hLpsval]
    ring
  have hg2val : Work.CPull.evp (Work.C7.g (2 : Fin 7)) z
      = -(1/2) * (Complex.log (1 - z)) ^ 2 := by
    rw [hg2eq, evp_C_mul_aux, hLps2val, hratcast]
  -- ## the closed form of `yps = x²/(x−1)` and of its derivative
  have hsympY : Work.CPull.evp Work.C7.yps z = z ^ 2 / (z - 1) :=
    (Work.CPull.evp_sympPhi z hz).2
  have hev_eq : (fun w : ℂ => Work.CPull.evp Work.C7.yps w)
      =ᶠ[nhds z] (fun w : ℂ => w ^ 2 / (w - 1)) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hzmem] with w hw
    exact (Work.CPull.evp_sympPhi w (by simpa [Metric.mem_ball, dist_zero_right] using hw)).2
  have hd2 : HasDerivAt (fun w : ℂ => w ^ 2 / (w - 1)) (z * (z - 2) / (z - 1) ^ 2) z := by
    have hnum : HasDerivAt (fun w : ℂ => w ^ 2) (2 * z) z := by
      have h := hasDerivAt_pow 2 (z : ℂ)
      have hder : (((2 : ℕ) : ℂ) * z ^ ((2 : ℕ) - 1)) = 2 * z := by
        rw [show (2 : ℕ) - 1 = 1 from by norm_num, pow_one]
        push_cast
        ring
      rwa [hder] at h
    have hden : HasDerivAt (fun w : ℂ => w - 1) (1 : ℂ) z := by
      have h := (hasDerivAt_id (x := z)).sub (hasDerivAt_const (x := z) (c := (1 : ℂ)))
      have hd : (1 : ℂ) - 0 = 1 := by ring
      rw [hd] at h
      exact h
    have h := hnum.div hden hz1'
    rwa [show (2 * z * (z - 1) - z ^ 2 * 1) / (z - 1) ^ 2
        = z * (z - 2) / (z - 1) ^ 2 by ring] at h
  have hdypsval : Work.CPull.evp (PowerSeries.derivative (R := ℚ) Work.C7.yps) z
      = z * (z - 2) / (z - 1) ^ 2 := by
    rw [evp_deriv hCs0 hks hz, Filter.EventuallyEq.deriv_eq hev_eq, hd2.deriv]
  have hdg5val : Work.CPull.evp (PowerSeries.derivative (R := ℚ) (Work.C7.g (5 : Fin 7))) z
      = deriv (fun w : ℂ => Work.CPull.evp (Work.C7.g (5 : Fin 7)) w) z :=
    evp_deriv hCg0 hkg hz
  -- ## evaluate the pullback identity `y·(B₆∘y)' = (B₃∘y)·y'` at `z`
  have hB6 : Work.C7.yps * PowerSeries.derivative (R := ℚ) (Work.C7.g (5 : Fin 7))
      = (Work.C7.g (2 : Fin 7)) * PowerSeries.derivative (R := ℚ) Work.C7.yps := Work.C17.B6_deriv
  have hLHS : Work.CPull.evp (Work.C7.yps * PowerSeries.derivative (R := ℚ) (Work.C7.g (5 : Fin 7))) z
      = (z ^ 2 / (z - 1))
          * deriv (fun w : ℂ => Work.CPull.evp (Work.C7.g (5 : Fin 7)) w) z := by
    rw [(Work.CPull.evpMul Work.C7.yps
          (PowerSeries.derivative (R := ℚ) (Work.C7.g (5 : Fin 7))) z hsumyps hsumdg5).2.2.2,
      hdg5val, hsympY]
  have hRHS : Work.CPull.evp ((Work.C7.g (2 : Fin 7)) * PowerSeries.derivative (R := ℚ) Work.C7.yps) z
      = (-(1/2) * (Complex.log (1 - z)) ^ 2) * (z * (z - 2) / (z - 1) ^ 2) := by
    rw [(Work.CPull.evpMul (Work.C7.g (2 : Fin 7)) (PowerSeries.derivative (R := ℚ) Work.C7.yps)
        z hsumg2 hsumdyps).2.2.2, hg2val, hdypsval]
  have key : (z ^ 2 / (z - 1))
        * deriv (fun w : ℂ => Work.CPull.evp (Work.C7.g (5 : Fin 7)) w) z
      = (-(1/2) * (Complex.log (1 - z)) ^ 2) * (z * (z - 2) / (z - 1) ^ 2) := by
    rw [← hLHS, ← hRHS, hB6]
  -- ## solve for the derivative
  have hderiv : deriv (fun w : ℂ => Work.CPull.evp (Work.C7.g (5 : Fin 7)) w) z
      = -(Complex.log (1 - z)) ^ 2 / 2 * ((z - 2) / (z * (z - 1))) := by
    have hdenom : z ^ 2 / (z - 1) ≠ 0 := div_ne_zero hz2 hz1'
    have h1 : deriv (fun w : ℂ => Work.CPull.evp (Work.C7.g (5 : Fin 7)) w) z
        = (-(1/2) * (Complex.log (1 - z)) ^ 2) * (z * (z - 2) / (z - 1) ^ 2)
            / (z ^ 2 / (z - 1)) := by
      rw [eq_div_iff hdenom, mul_comm]
      exact key
    rw [h1]
    field_simp
  have hFdiff : DifferentiableAt ℂ (fun w : ℂ => Work.CPull.evp (Work.C7.g (5 : Fin 7)) w) z :=
    (differentiableOn_evp_of_poly_growth hCg0 hkg).differentiableAt
      (Metric.isOpen_ball.mem_nhds hzmem)
  have hmain : HasDerivAt (fun w : ℂ => Work.CPull.evp (Work.C7.g (5 : Fin 7)) w)
      (-(Complex.log (1 - z)) ^ 2 / 2 * ((z - 2) / (z * (z - 1)))) z :=
    hFdiff.hasDerivAt.congr_deriv hderiv
  exact hmain

end Work.A14D
