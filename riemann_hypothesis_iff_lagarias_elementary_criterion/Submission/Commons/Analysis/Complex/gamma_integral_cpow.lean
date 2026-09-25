import Mathlib.Analysis.MellinTransform
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gamma_vertical_exp_decay

/-! # Euler's integral for `Γ(a) · z^{-a}`

For `0 < re a` and `0 < re z`, the classical Laplace-type integral

`∫₀^∞ t^{a-1} e^{-z t} dt = Γ(a) z^{-a}`

is proved by combining the (already formalised) rotation of the Γ-contour
along a ray with the real rescaling identity for the Mellin transform.
-/

open Complex MeasureTheory Set Filter
open scoped Real

namespace Commons.Analysis.Complex

open Commons.Analysis.SpecialFunctions.Gamma

noncomputable section

/-- Multiplicativity of the complex power in the base for a positive real factor:
`(r * x)^s = r^s * x^s` for `0 < r`. -/
lemma ofReal_mul_cpow (r : ℝ) (hr : 0 < r) (x : ℂ) (hx : x ≠ 0) (s : ℂ) :
    ((r : ℂ) * x) ^ s = (r : ℂ) ^ s * x ^ s := by
  rw [cpow_def_of_ne_zero (mul_ne_zero (ofReal_ne_zero.mpr hr.ne') hx),
      cpow_def_of_ne_zero (ofReal_ne_zero.mpr hr.ne'), cpow_def_of_ne_zero hx,
      log_ofReal_mul hr hx, Complex.ofReal_log hr.le, add_mul, exp_add]

/-- For real `θ ∈ (-π, π]`: `(e^{iθ})^s = e^{s·iθ}`. -/
lemma cpow_cexp_I_mul (θ : ℝ) (hθ1 : -Real.pi < θ) (hθ2 : θ ≤ Real.pi) (s : ℂ) :
    (Complex.exp (Complex.I * (θ : ℂ))) ^ s =
      Complex.exp (s * (Complex.I * (θ : ℂ))) := by
  have him : (Complex.I * (θ : ℂ)).im = θ := by
    rw [mul_comm Complex.I (θ : ℂ), Complex.mul_I_im]
    simp
  rw [Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _)]
  congr 1
  rw [Complex.log_exp]
  · ring
  · rwa [him]
  · rwa [him]

theorem gamma_integral_cpow {a z : ℂ} (ha : 0 < a.re) (hz : 0 < z.re) :
    ∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ (a - 1) * Complex.exp (-(z * (t : ℂ)))
      = Complex.Gamma a * z ^ (-a) := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  set ρ : ℝ := ‖z‖ with hρdef
  have hρ : 0 < ρ := by rw [hρdef]; exact norm_pos_iff.mpr hz0
  set θ : ℝ := z.arg with hθdef
  have hθmem : θ ∈ Set.Ioc (-Real.pi) Real.pi := by
    rw [hθdef]; exact Complex.arg_mem_Ioc z
  have hθabs : |θ| < Real.pi / 2 := by
    rw [hθdef, Complex.abs_arg_lt_pi_div_two_iff]; exact Or.inl hz
  set c : ℂ := Complex.exp (Complex.I * (θ : ℂ)) with hcdef
  have hc_ne : c ≠ 0 := by rw [hcdef]; exact Complex.exp_ne_zero _
  have hzdecomp : z = (ρ : ℂ) * c := by
    rw [hcdef, hρdef, hθdef, mul_comm Complex.I (z.arg : ℂ)]
    exact (Complex.norm_mul_exp_arg_mul_I z).symm
  set G : ℝ → ℂ := fun u => Complex.exp (-((u : ℂ) * c)) with hGdef
  -- pointwise agreement of the rotated Γ-integrand with the Mellin integrand
  have hpt : ∀ r : ℝ, GRBase.Jr a (-θ) r = (r : ℂ) ^ (a - 1) * G r := by
    intro r
    have h1 : Complex.exp (-(Complex.I * (((-θ) : ℝ) : ℂ))) = c := by
      rw [hcdef]; congr 1; push_cast; ring
    simp only [GRBase.Jr, hGdef, h1]
    exact mul_comm _ _
  -- exponent identification `c^{-a} = e^{-iθa}`
  have hc_pow : c ^ (-a) = Complex.exp (-(Complex.I * (θ : ℂ) * a)) := by
    rw [hcdef, cpow_cexp_I_mul θ hθmem.1 hθmem.2 (-a)]
    congr 1
    ring
  -- Step 1: rewrite the integrand as `mellin (G ∘ (ρ ·)) a`.
  have hA : (∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ (a - 1) * Complex.exp (-(z * (t : ℂ))))
      = mellin (fun t : ℝ => G (ρ * t)) a := by
    rw [mellin]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    simp only [smul_eq_mul]
    rw [hGdef]
    have harg : z * (t : ℂ) = ((ρ * t : ℝ) : ℂ) * c := by
      rw [hzdecomp]; push_cast; ring
    rw [harg]
  -- Step 2: real rescaling via the Mellin transform.
  have hB : mellin (fun t : ℝ => G (ρ * t)) a = (ρ : ℂ) ^ (-a) • mellin G a :=
    mellin_comp_mul_left G a hρ
  -- Step 3: the rotation identity identifies `mellin G a`.
  have hC_int : (∫ r in Set.Ioi 0, GRBase.Jr a (-θ) r) = mellin G a := by
    rw [mellin]
    refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
    simp only [smul_eq_mul]
    exact hpt r
  have hC : mellin G a = c ^ (-a) * Complex.Gamma a := by
    have hrot := GRRect.gamma_eq_Jr_integral a ha (θ := -θ) (by rwa [abs_neg])
    rw [hC_int] at hrot
    rw [hrot, hc_pow, ← mul_assoc, ← Complex.exp_add]
    rw [show (-(Complex.I * (θ : ℂ) * a)) + (-(Complex.I * (((-θ) : ℝ) : ℂ) * a)) = 0
          by push_cast; ring]
    rw [Complex.exp_zero, one_mul]
  rw [hA, hB, hC, smul_eq_mul]
  have hzpow : z ^ (-a) = (ρ : ℂ) ^ (-a) * c ^ (-a) := by
    rw [hzdecomp, ofReal_mul_cpow ρ hρ c hc_ne (-a)]
  rw [hzpow]
  ring

end

end Commons.Analysis.Complex