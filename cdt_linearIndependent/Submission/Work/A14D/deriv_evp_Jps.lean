import Mathlib
import Submission.Work.A14D.ppc_aux
import Submission.Work.C17I.evp_poly_mul

/-!
# `Work.A14D.deriv_evp_Jps`

Derivative of the analytic evaluation of the series `Jps = x·₃F₂(1/2,1,1;3/2,3/2;y/4)`.

`Jps` is characterised by the first-order ODE (`Work.C7.J_ode`)

`2·x(x−1)·J' − x·J = 2(1−x)·log(1−x)`

in `ℚ⟦x⟧`.  Evaluating this identity at `z ∈ ℂ` with `‖z‖ < 1` (where `Work.CPull.evp` is
multiplicative, `Work.CPull.evpMul`, and equals `Polynomial.eval₂` on polynomials,
`Work.C17I.evp_poly`/`evp_poly_mul`) gives

`2z(z−1)·evp J' z = z·evp J z + 2(1−z)·log(1−z)`,

i.e. `evp J' z = evp J z / (2(z−1)) − log(1−z)/z`.  Since `evp J` is holomorphic on the unit
disc with `deriv (evp J) z = evp J' z` (`Work.A14D.evp_deriv`), the claim follows.
-/

namespace Work.A14D

open PowerSeries

noncomputable section

/-- The analytic evaluation of `Lps = log(1−x)` on the open unit disc. -/
lemma evp_Lps {z : ℂ} (hz : ‖z‖ < 1) : Work.CPull.evp Work.C7.Lps z = Complex.log (1 - z) :=
  Work.C7.evA_Lps hz

theorem deriv_evp_Jps (z : ℂ) (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    HasDerivAt (fun w : ℂ => Work.CPull.evp Work.C7.Jps w)
      (Work.CPull.evp Work.C7.Jps z / (2 * (z - 1)) - Complex.log (1 - z) / z) z := by
  -- growth of the coefficients of `Jps`, of its derivative, and of `Lps`
  obtain ⟨C, hC0, k, hCk⟩ := poly_growth_Jps
  obtain ⟨C', hC'0, k', hC'k'⟩ := poly_growth_deriv hC0 hCk
  obtain ⟨CL, hCL0, kL, hCLk⟩ := poly_growth_Lps
  have hsJ : Summable (fun n : ℕ => ((PowerSeries.coeff n Work.C7.Jps : ℚ) : ℂ) * z ^ n) :=
    Summable.of_norm (summable_abs_coeff_of_poly_growth hC0 hCk hz)
  have hsD : Summable (fun n : ℕ =>
      ((PowerSeries.coeff n (PowerSeries.derivative (R := ℚ) Work.C7.Jps) : ℚ) : ℂ) * z ^ n) :=
    Summable.of_norm (summable_abs_coeff_of_poly_growth hC'0 hC'k' hz)
  have hsL : Summable (fun n : ℕ => ((PowerSeries.coeff n Work.C7.Lps : ℚ) : ℂ) * z ^ n) :=
    Summable.of_norm (summable_abs_coeff_of_poly_growth hCL0 hCLk hz)
  -- the ODE satisfied by `Jps`
  have hode := Work.C7.J_ode Work.C7.g_form.1 Work.C17.g4_form Work.C17.B5_pullback
  -- the same identity, with the polynomial factors coerced from `ℚ[X]`
  have hkey :
      (((2 * Polynomial.X * (Polynomial.X - 1) : Polynomial ℚ)) : PowerSeries ℚ)
          * PowerSeries.derivative (R := ℚ) Work.C7.Jps
        = ((Polynomial.X : Polynomial ℚ) : PowerSeries ℚ) * Work.C7.Jps
          + ((2 * (1 - Polynomial.X) : Polynomial ℚ) : PowerSeries ℚ) * Work.C7.Lps := by
    have h2 : ((2 : Polynomial ℚ) : PowerSeries ℚ) = (2 : PowerSeries ℚ) := by
      rw [← Polynomial.coeToPowerSeries.ringHom_apply]
      exact map_ofNat (Polynomial.coeToPowerSeries.ringHom (R := ℚ)) 2
    simp only [Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_X, Polynomial.coe_one, h2]
    linear_combination hode
  -- evaluate the identity at `z`
  obtain ⟨-, hPDval⟩ :=
    Work.C17I.evp_poly_mul (2 * Polynomial.X * (Polynomial.X - 1))
      (PowerSeries.derivative (R := ℚ) Work.C7.Jps) z hsD
  obtain ⟨hXJsum, hXJval⟩ := Work.C17I.evp_poly_mul Polynomial.X Work.C7.Jps z hsJ
  obtain ⟨hQLsum, hQLval⟩ := Work.C17I.evp_poly_mul (2 * (1 - Polynomial.X)) Work.C7.Lps z hsL
  have hadd := (Work.CPull.evp_add_mul
      (((Polynomial.X : Polynomial ℚ) : PowerSeries ℚ) * Work.C7.Jps)
      (((2 * (1 - Polynomial.X) : Polynomial ℚ) : PowerSeries ℚ) * Work.C7.Lps)
      z hXJsum hQLsum).1
  have h1 : ((2 * Polynomial.X * (Polynomial.X - 1) : Polynomial ℚ)).eval₂ (algebraMap ℚ ℂ) z
      * Work.CPull.evp (PowerSeries.derivative (R := ℚ) Work.C7.Jps) z
      = (Polynomial.X : Polynomial ℚ).eval₂ (algebraMap ℚ ℂ) z
          * Work.CPull.evp Work.C7.Jps z
        + ((2 * (1 - Polynomial.X) : Polynomial ℚ)).eval₂ (algebraMap ℚ ℂ) z
          * Work.CPull.evp Work.C7.Lps z := by
    simp only [Work.CPull.evp] at hPDval hXJval hQLval hadd ⊢
    rw [hPDval, hkey, hadd, ← hXJval, ← hQLval]
  have hmain : 2 * z * (z - 1) * Work.CPull.evp (PowerSeries.derivative (R := ℚ) Work.C7.Jps) z
      = z * Work.CPull.evp Work.C7.Jps z + 2 * (1 - z) * Complex.log (1 - z) := by
    simpa [evp_Lps hz] using h1
  -- solve for `evp J' z`
  have hz1 : z - 1 ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    rw [h] at hz
    norm_num at hz
  have hDval : Work.CPull.evp (PowerSeries.derivative (R := ℚ) Work.C7.Jps) z
      = Work.CPull.evp Work.C7.Jps z / (2 * (z - 1)) - Complex.log (1 - z) / z := by
    have hden : 2 * z * (z - 1) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hz0) hz1
    have h2 : Work.CPull.evp (PowerSeries.derivative (R := ℚ) Work.C7.Jps) z * (2 * z * (z - 1))
        = z * Work.CPull.evp Work.C7.Jps z + 2 * (1 - z) * Complex.log (1 - z) := by
      linear_combination hmain
    have key2 := (eq_div_iff hden).mpr h2
    have key : (z * Work.CPull.evp Work.C7.Jps z + 2 * (1 - z) * Complex.log (1 - z))
          / (2 * z * (z - 1))
        = Work.CPull.evp Work.C7.Jps z / (2 * (z - 1)) - Complex.log (1 - z) / z := by
      field_simp
      ring
    rw [key2, key]
  -- `evp J` is holomorphic on the unit disc, with derivative `evp J'`
  have hG : DifferentiableAt ℂ (fun w : ℂ => Work.CPull.evp Work.C7.Jps w) z :=
    (differentiableOn_evp_of_poly_growth hC0 hCk).differentiableAt
      (Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball, dist_zero_right] using hz))
  have h := hG.hasDerivAt
  rw [← evp_deriv hC0 hCk hz, hDval] at h
  exact h

end

end Work.A14D
