/-
# The first moment of the rescaled cutoffs

This file proves `Work.KMTAreas.A4.offLamMoment`: the rescaled Littlewood–Paley kernel
`K_k = 𝓕⁻ η_{≤k}` (`Work.KMTAreas.A7.etaMult_K k`), where `η_{≤k}(θ) = η(θ / 2^k)`, has first
moment bounded by a *single* constant times `2^{-k}`:

  `∃ C > 0, ∀ k : ℤ, ∫ x, |x| ‖K_k x‖ ≤ C · 2^{-k}`.

## The mathematics

`etaMult_K_coe` (in `A4/offLamTail.lean`) gives the explicit dilation form
`K_k x = 2^k · ψ(2^k x)` with `ψ = 𝓕⁻ η` (`etaMult_psiSch`).  Hence, pointwise,

  `|x| ‖K_k x‖ = |2^k x| · ‖ψ (2^k x)‖`,

because `2^k > 0`.  The change of variables `u = 2^k x` for the Bochner integral on `ℝ`
(`Measure.integral_comp_mul_left`, the dilation invariance of Lebesgue measure) then gives the
**identity**

  `∫ x, |x| ‖K_k x‖ = 2^{-k} · ∫ u, |u| ‖ψ u‖`,

with *no* integrability hypothesis: both sides are ordinary real numbers and the pulled-out
constant is `|(2^k)⁻¹| = 2^{-k}`.  Taking `C = max (∫ |u| ‖ψ u‖) 1` gives the estimate, the
maximum only being needed to make the constant strictly positive.

## Layout

* `integral_abs_mul_norm_etaMult_K` — the identity above (the whole content);
* `offLamMoment` — the estimate.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.offLamTail

set_option autoImplicit false

namespace Work.KMTAreas.A4

open MeasureTheory

/-- The first moment of the rescaled kernel `K_k = 𝓕⁻ η_{≤k}`: it is `2^{-k}` times the first
moment of `ψ = 𝓕⁻ η`, by the dilation form `K_k x = 2^k ψ(2^k x)` and the change of variables
`u = 2^k x`. -/
theorem integral_abs_mul_norm_etaMult_K (k : ℤ) :
    (∫ x : ℝ, |x| * ‖((Work.KMTAreas.A7.etaMult_K k : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖)
      = ((2 : ℝ) ^ k)⁻¹ *
        (∫ y : ℝ, |y| * ‖((Work.KMTAreas.A7.etaMult_psiSch : SchwartzMap ℝ ℂ) : ℝ → ℂ) y‖) := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  -- pointwise: `|x| ‖K_k x‖ = G (2^k x)` with `G u = |u| ‖ψ u‖`
  have hpt : ∀ x : ℝ,
      |x| * ‖((Work.KMTAreas.A7.etaMult_K k : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖
        = (fun y : ℝ =>
            |y| * ‖((Work.KMTAreas.A7.etaMult_psiSch : SchwartzMap ℝ ℂ) : ℝ → ℂ) y‖)
            ((2 : ℝ) ^ k * x) := by
    intro x
    rw [etaMult_K_coe k]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, abs_mul]
    ring
  calc (∫ x : ℝ, |x| * ‖((Work.KMTAreas.A7.etaMult_K k : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖)
      = ∫ x : ℝ, (fun y : ℝ =>
            |y| * ‖((Work.KMTAreas.A7.etaMult_psiSch : SchwartzMap ℝ ℂ) : ℝ → ℂ) y‖)
            ((2 : ℝ) ^ k * x) := by
        rw [show (fun x : ℝ =>
              |x| * ‖((Work.KMTAreas.A7.etaMult_K k : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖)
            = (fun x : ℝ => (fun y : ℝ =>
                |y| * ‖((Work.KMTAreas.A7.etaMult_psiSch : SchwartzMap ℝ ℂ) : ℝ → ℂ) y‖)
                ((2 : ℝ) ^ k * x)) from funext hpt]
    _ = |(((2 : ℝ) ^ k))⁻¹| • (∫ y : ℝ,
            |y| * ‖((Work.KMTAreas.A7.etaMult_psiSch : SchwartzMap ℝ ℂ) : ℝ → ℂ) y‖) :=
        Measure.integral_comp_mul_left (fun y : ℝ =>
            |y| * ‖((Work.KMTAreas.A7.etaMult_psiSch : SchwartzMap ℝ ℂ) : ℝ → ℂ) y‖) ((2 : ℝ) ^ k)
    _ = (((2 : ℝ) ^ k))⁻¹ * (∫ y : ℝ,
            |y| * ‖((Work.KMTAreas.A7.etaMult_psiSch : SchwartzMap ℝ ℂ) : ℝ → ℂ) y‖) := by
        rw [abs_of_pos (inv_pos.mpr hpos), smul_eq_mul]

/-- **Moment bound for the rescaled cutoffs.**  There is a constant `C > 0` (namely
`max (∫ |u| ‖ψ u‖) 1`) such that for every `k : ℤ` the first moment of the kernel
`K_k = 𝓕⁻ η_{≤k}` is at most `C · 2^{-k}`. -/
theorem offLamMoment :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℤ),
      ∫ x : ℝ, |x| * ‖((Work.KMTAreas.A7.etaMult_K k : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖
        ≤ C * (2 : ℝ) ^ (-k) := by
  refine ⟨max (∫ y : ℝ,
      |y| * ‖((Work.KMTAreas.A7.etaMult_psiSch : SchwartzMap ℝ ℂ) : ℝ → ℂ) y‖) 1,
    lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro k
  have hpos : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  rw [integral_abs_mul_norm_etaMult_K k, zpow_neg, mul_comm (((2 : ℝ) ^ k)⁻¹)]
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (le_of_lt (inv_pos.mpr hpos))

end Work.KMTAreas.A4
