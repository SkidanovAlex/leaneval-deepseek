import Mathlib
import Submission.Work.TMC13.Defs
import Submission.Work.TMC13.fourier_amp
import Submission.Work.TMC13.ref_fourier_factor
import Submission.Work.TMC13.ref_perturb_slitPlane
import Submission.Work.TMC13.ref_scale_div_norm
import Submission.Work.TMC13.ref_arg_perturb_continuous

/-!
# `Work.TMC13.ref_lift`

For a real `2 × 2` matrix `A` with `det A = 1` we build a continuous *reference lift*
`G : ℝ → ℝ` of the projective action of `A`: `vc (G t) = unit (A · vc t)`, normalised so that
`G (t + 1) = G t + 1`.

The construction is explicit.  Writing `vc t = e^{iπt}` and
`A · vc t = c1 A · vc t + c2 A · conj (vc t)` (see `fourier_amp`), the determinant identity
`‖c1 A‖² - ‖c2 A‖² = det A = 1` gives `‖c2 A‖ < ‖c1 A‖`, so

  `A · vc t = c1 A · vc t · (1 + r · vc (-2t))`,  `r = c2 A / c1 A`, `‖r‖ < 1`

(`Work.TMC13.ref_fourier_factor`), and the perturbation factor `1 + r · vc (-2t)` stays in the
open right half-plane (`Work.TMC13.ref_perturb_slitPlane`).  Hence

  `G t = t + (arg (1 + r · vc (-2t)) + arg (c1 A)) / π`

is well defined and continuous; `vc (G t) = unit (A · vc t)` follows from
`vc (arg ζ / π) = ζ / ‖ζ‖`, and `G (t + 1) = G t + 1` from the `2`-periodicity of `vc (-2 ·)`.
-/

namespace Work.TMC13

open Work.TMComp.RotBasics

noncomputable section

/-! ## Elementary facts about `vc` -/

/-- `vc s` is the exponential `exp (i π s)`. -/
theorem ref_lift_vc_eq_exp (s : ℝ) : vc s = Complex.exp ((↑(Real.pi * s) : ℂ) * Complex.I) := by
  apply Complex.ext <;>
    simp only [vc, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]

/-- The argument-to-`vc` bridge: `vc (arg ζ / π)` is the unit vector in the direction of `ζ`. -/
theorem ref_lift_vc_arg_div_pi (ζ : ℂ) (hζ : ζ ≠ 0) :
    vc (Complex.arg ζ / Real.pi) = ζ / (↑‖ζ‖ : ℂ) := by
  have hπ : Real.pi * (Complex.arg ζ / Real.pi) = Complex.arg ζ := by
    field_simp
  have hne : (↑‖ζ‖ : ℂ) ≠ 0 := by
    simpa only [ne_eq, Complex.ofReal_eq_zero] using norm_ne_zero_iff.mpr hζ
  rw [ref_lift_vc_eq_exp, hπ, eq_div_iff hne, mul_comm]
  exact Complex.norm_mul_exp_arg_mul_I ζ

/-! ## The leading Fourier coefficient -/

/-- For `det A = 1` the leading Fourier coefficient dominates: `‖c2 A‖ < ‖c1 A‖`. -/
theorem ref_lift_norm_c2_lt_c1 {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det = 1) :
    ‖c2 A‖ < ‖c1 A‖ := by
  have hdet : (c1 A).re ^ 2 + (c1 A).im ^ 2 - ((c2 A).re ^ 2 + (c2 A).im ^ 2) = 1 := by
    have h := (fourier_amp A).2
    rwa [hA] at h
  have hns : ‖c1 A‖ ^ 2 - ‖c2 A‖ ^ 2 = 1 := by
    have h1 : ‖c1 A‖ ^ 2 = (c1 A).re ^ 2 + (c1 A).im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    have h2 : ‖c2 A‖ ^ 2 = (c2 A).re ^ 2 + (c2 A).im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    rw [h1, h2]
    exact hdet
  nlinarith [norm_nonneg (c1 A), norm_nonneg (c2 A), hns]

/-! ## The reference lift -/

theorem ref_lift {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det = 1) :
    ∃ G : ℝ → ℝ, Continuous G ∧ (∀ t : ℝ, G (t + 1) = G t + 1) ∧
      (∀ t : ℝ, Work.TMComp.RotBasics.vc (G t) =
        Work.TMComp.RotBasics.smul A (Work.TMComp.RotBasics.vc t) /
          (↑‖Work.TMComp.RotBasics.smul A (Work.TMComp.RotBasics.vc t)‖ : ℂ)) := by
  have hlt := ref_lift_norm_c2_lt_c1 hA
  have hc1ne : c1 A ≠ 0 := c1_ne_zero_of_det_one hA
  have hc1pos : 0 < ‖c1 A‖ := norm_pos_iff.mpr hc1ne
  set r : ℂ := c2 A / c1 A with hrdef
  have hrlt : ‖r‖ < 1 := by
    rw [hrdef, norm_div]
    exact (div_lt_one hc1pos).mpr hlt
  refine ⟨fun t : ℝ => t + (Complex.arg (1 + r * vc (-2 * t)) + Complex.arg (c1 A)) / Real.pi,
    ?_, ?_, ?_⟩
  · exact Continuous.add continuous_id (Continuous.div_const
      (Continuous.add (ref_arg_perturb_continuous hrlt) continuous_const) Real.pi)
  · intro t
    dsimp only
    have hvc : vc (-2 * (t + 1)) = vc (-2 * t) := by
      rw [show -2 * (t + 1) = (-2 * t) - 2 by ring, vc_sub_two]
    rw [hvc]
    ring
  · intro t
    dsimp only
    set u : ℂ := 1 + r * vc (-2 * t) with hudef
    have hfac : smul A (vc t) = c1 A * vc t * u := by
      rw [hudef, hrdef]
      exact ref_fourier_factor hA t
    have hune : u ≠ 0 := by
      rw [hudef]
      exact Complex.slitPlane_ne_zero (ref_perturb_slitPlane r hrlt t)
    have hvcG : vc (t + (Complex.arg u + Complex.arg (c1 A)) / Real.pi)
        = vc t * (c1 A / (↑‖c1 A‖ : ℂ)) * (u / (↑‖u‖ : ℂ)) := by
      rw [show t + (Complex.arg u + Complex.arg (c1 A)) / Real.pi
            = t + (Complex.arg u / Real.pi + Complex.arg (c1 A) / Real.pi) by ring,
          vc_add, vc_add, ref_lift_vc_arg_div_pi u hune, ref_lift_vc_arg_div_pi (c1 A) hc1ne]
      ring
    rw [hvcG,
      ref_scale_div_norm (c1 A) u (vc t) hc1ne hune (vc_ne_zero t) (vc_norm t), ← hfac]

end

end Work.TMC13
