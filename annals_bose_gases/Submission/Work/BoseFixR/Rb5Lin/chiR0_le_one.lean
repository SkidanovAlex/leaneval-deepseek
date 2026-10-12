import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.Rb5Lin.W1Facts
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.Rb5Lin.chiR0_le_one` — the localization radius `chiR0` is at most `1`

`Submission.BoseGases.chiR0` is the `Classical.choose`-selected radius on which the
autocorrelation `(χ⋆χ)` of the cubic bump `χ` is at least `1/2`
(`Submission/ChiWitness.lean`).  Because the bump satisfies `χ x = 0` for `‖x‖ > 1/2`
(`Submission.BoseGases.chi_eq_zero_of_norm_gt`), the convolution `(χ⋆χ) x` vanishes
pointwise as soon as `‖x‖ > 1`: for every `y`, one of `y`, `x - y` has norm `> 1/2`.

Consequently *any* admissible radius — in particular the chosen one — is `≤ 1`:
the `choose_spec` property forces `(χ⋆χ) ≠ 0` on the closed ball of radius `chiR0`,
hence `‖x‖ ≤ 1` there, and a vector of norm exactly `chiR0` exists.

The two ingredients are:
* `conv3_chi_eq_zero_of_one_lt_norm` — the (strict) support bound of `χ⋆χ`;
* the packaging theorem `chiR0_le_one` itself, which only uses
  `BoseGases.chiR0_half`, `BoseGases.chiR0_pos` and `exists_norm_eq`.
-/

namespace Work.BoseFixR.Rb5Lin

open MeasureTheory

/-- The autocorrelation `(χ⋆χ)` of the cubic bump vanishes outside the unit ball:
if `‖x‖ > 1` then for every `y` at least one of `χ y`, `χ (x - y)` is zero, since
`χ` is supported in the ball of radius `1/2`. -/
theorem conv3_chi_eq_zero_of_one_lt_norm {x : EuclideanSpace ℝ (Fin 3)} (hx : 1 < ‖x‖) :
    Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi x = 0 := by
  unfold Submission.BoseGases.conv3
  have hz : ∀ y : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.chi y * Submission.BoseGases.chi (x - y) = 0 := by
    intro y
    by_cases hy : ‖y‖ ≤ 1 / 2
    · -- then `‖x - y‖ ≥ ‖x‖ - ‖y‖ > 1 - 1/2 = 1/2`
      have hxy : 1 / 2 < ‖x - y‖ := by
        have h1 : ‖x‖ - ‖y‖ ≤ ‖x - y‖ := norm_sub_norm_le x y
        linarith
      rw [Submission.BoseGases.chi_eq_zero_of_norm_gt (x - y) hxy, mul_zero]
    · rw [Submission.BoseGases.chi_eq_zero_of_norm_gt y (lt_of_not_ge hy), zero_mul]
  rw [integral_congr_ae (ae_of_all _ hz), integral_zero]

/-- **The chosen localization radius is at most `1`.**

The `choose_spec` property of `chiR0` gives `(χ⋆χ) x₀ ≥ 1/2` for a point `x₀` of norm
exactly `chiR0`; in particular `(χ⋆χ) x₀ ≠ 0`, which by
`conv3_chi_eq_zero_of_one_lt_norm` forbids `‖x₀‖ = chiR0 > 1`. -/
theorem chiR0_le_one : Submission.BoseGases.chiR0 ≤ 1 := by
  -- some point of norm exactly `chiR0`
  obtain ⟨x₀, hx₀⟩ := exists_norm_eq (EuclideanSpace ℝ (Fin 3))
    (le_of_lt Submission.BoseGases.chiR0_pos)
  -- on the ball of radius `chiR0` the autocorrelation is `≥ 1/2`, hence nonzero
  have hhalf : 1 / 2 ≤ Submission.BoseGases.conv3 Submission.BoseGases.chi
      Submission.BoseGases.chi x₀ :=
    Submission.BoseGases.chiR0_half x₀ (le_of_eq hx₀)
  have hne : Submission.BoseGases.conv3 Submission.BoseGases.chi
      Submission.BoseGases.chi x₀ ≠ 0 := by linarith
  by_contra hlt
  rw [not_le] at hlt
  exact hne (conv3_chi_eq_zero_of_one_lt_norm (x := x₀) (by rw [hx₀]; exact hlt))

end Work.BoseFixR.Rb5Lin
