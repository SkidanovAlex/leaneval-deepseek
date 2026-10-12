import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.OneBodyKin.integrable_profHat_sq_mul_norm_pow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.integrable_fsKinCoeff_shift_mul_profHat_sq`

The `fsKinCoeff`-weighted profile square with a **shifted momentum**,

    `p ↦ [‖ρ + p‖ − C]₊² · profHat(p)²`,

is Lebesgue integrable on `ℝ³`, for every cut-off `C` and every shift `ρ`.

Only the behaviour at infinity matters (every factor is continuous).  Two elementary facts
reduce the weight to the polynomial weights already handled in
`integrable_profHat_sq_mul_norm_pow`:

* the shift changes the argument of the cut-off by at most `‖ρ‖`
  (`fsKinCoeff_shift_le`): `[‖ρ+p‖−C]₊ ≤ [‖p‖−(C−‖ρ‖)]₊`, so the weight may be taken radial
  at the price of replacing `C` by `C − ‖ρ‖`;
* `[r−A]₊² ≤ (1+|A|)² (1+r)²`, and `(1+r)² ≤ 2 + 2r²`, hence

    `[‖p‖−A]₊² profHat(p)² ≤ 2(1+|A|)² profHat(p)² + 2(1+|A|)² profHat(p)²‖p‖²`.

The two summands are integrable by `integrable_profHat_sq_mul_norm_pow` at `n = 0` and `n = 2`
(the decay `ProfHatDecay`, `|profHat p| ≤ K(1+‖p‖)⁻⁶`, makes `profHat(p)²(1+‖p‖)²` decay like
`(1+‖p‖)⁻¹⁰`, integrable in dimension `3`).

The declaration is provided under the documented name `Work.OneBodyKin.…` (module
`Submission.Work.OneBodyKin.integrable_fsKinCoeff_shift_mul_profHat_sq` ⇔ namespace
`Work.OneBodyKin`); the same statement is repeated at the end of the file under the doubled
namespace prefix used by the original stub, so that both spellings resolve.
-/

namespace Work.OneBodyKin

open MeasureTheory

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000

/-- **The shift only costs `‖ρ‖` in the cut-off.**  Since `‖ρ+p‖ ≤ ‖ρ‖ + ‖p‖`, the excess of
`‖ρ+p‖` over `C` is at most the excess of `‖p‖` over `C − ‖ρ‖`: `[‖ρ+p‖−C]₊ ≤ [‖p‖−(C−‖ρ‖)]₊`,
and squaring preserves the inequality (both sides are nonnegative). -/
private lemma fsKinCoeff_shift_le (C : ℝ) (ρ p : ℝ³) :
    Submission.BoseGases.fsKinCoeff C ‖ρ + p‖
      ≤ Submission.BoseGases.fsKinCoeff (C - ‖ρ‖) ‖p‖ := by
  unfold Submission.BoseGases.fsKinCoeff
  have h1 : ‖ρ + p‖ - C ≤ ‖p‖ - (C - ‖ρ‖) := by
    have := norm_add_le ρ p
    linarith
  have h2 : max (‖ρ + p‖ - C) 0 ≤ max (‖p‖ - (C - ‖ρ‖)) 0 :=
    max_le (h1.trans (le_max_left _ _)) (le_max_right _ _)
  exact pow_le_pow_left₀ (le_max_right _ _) h2 2

/-- **Domination of the weighted profile square by the two integrable weights**
`profHat²` and `profHat²‖p‖²`.  With `A := C − ‖ρ‖` the radial cut-off satisfies
`[r−A]₊² ≤ (1+|A|)²(1+r)²` (as in `integrable_fsKinCoeff_mul_abs_profHat`), and
`(1+r)² ≤ 2 + 2r²`; multiplying by the nonnegative factor `profHat(p)²` and expanding gives the
claim. -/
private lemma fsKinCoeff_mul_profHat_sq_le (A : ℝ) (p : ℝ³) :
    Submission.BoseGases.fsKinCoeff A ‖p‖ * (Work.OneBodyKin.profHat p) ^ 2
      ≤ 2 * (1 + |A|) ^ 2 * (Work.OneBodyKin.profHat p) ^ 2
        + 2 * (1 + |A|) ^ 2 * ((Work.OneBodyKin.profHat p) ^ 2 * ‖p‖ ^ 2) := by
  have hfs : Submission.BoseGases.fsKinCoeff A ‖p‖ ≤ (1 + |A|) ^ 2 * (1 + ‖p‖) ^ 2 := by
    unfold Submission.BoseGases.fsKinCoeff
    have h2 : max (‖p‖ - A) 0 ≤ (1 + |A|) * (1 + ‖p‖) := by
      have h1 : ‖p‖ - A ≤ (1 + |A|) * (1 + ‖p‖) := by
        have h3 := neg_le_abs A
        nlinarith [norm_nonneg p, abs_nonneg A,
          mul_nonneg (by positivity : (0 : ℝ) ≤ 1 + |A|) (norm_nonneg p)]
      exact max_le h1 (by positivity)
    have h0 : 0 ≤ max (‖p‖ - A) 0 := le_max_right _ _
    calc max (‖p‖ - A) 0 ^ 2 ≤ ((1 + |A|) * (1 + ‖p‖)) ^ 2 := pow_le_pow_left₀ h0 h2 2
      _ = (1 + |A|) ^ 2 * (1 + ‖p‖) ^ 2 := by rw [mul_pow]
  have hsq : (1 + ‖p‖) ^ 2 ≤ 2 + 2 * ‖p‖ ^ 2 := by
    nlinarith [norm_nonneg p, sq_nonneg (‖p‖ - 1)]
  have hK : (0 : ℝ) ≤ (1 + |A|) ^ 2 := by positivity
  calc Submission.BoseGases.fsKinCoeff A ‖p‖ * (Work.OneBodyKin.profHat p) ^ 2
      ≤ ((1 + |A|) ^ 2 * (1 + ‖p‖) ^ 2) * (Work.OneBodyKin.profHat p) ^ 2 :=
        mul_le_mul_of_nonneg_right hfs (sq_nonneg _)
    _ ≤ ((1 + |A|) ^ 2 * (2 + 2 * ‖p‖ ^ 2)) * (Work.OneBodyKin.profHat p) ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hK) (sq_nonneg _)
    _ = 2 * (1 + |A|) ^ 2 * (Work.OneBodyKin.profHat p) ^ 2
          + 2 * (1 + |A|) ^ 2 * ((Work.OneBodyKin.profHat p) ^ 2 * ‖p‖ ^ 2) := by ring

theorem integrable_fsKinCoeff_shift_mul_profHat_sq (C : ℝ) (ρ : EuclideanSpace ℝ (Fin 3)) :
    Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.fsKinCoeff C ‖ρ + p‖ * (Work.OneBodyKin.profHat p) ^ 2) := by
  -- the two integrable polynomial weights `profHat²` (`n = 0`) and `profHat²‖p‖²` (`n = 2`)
  have h0 : Integrable (fun p : ℝ³ => (profHat p) ^ 2) :=
    (integrable_profHat_sq_mul_norm_pow 0 (by norm_num)).congr
      (Filter.Eventually.of_forall fun p => by simp)
  have h2 : Integrable (fun p : ℝ³ => (profHat p) ^ 2 * ‖p‖ ^ 2) :=
    integrable_profHat_sq_mul_norm_pow 2 le_rfl
  -- their combination dominates the weighted shifted profile square
  have hg : Integrable (fun p : ℝ³ =>
      2 * (1 + |C - ‖ρ‖|) ^ 2 * (profHat p) ^ 2
        + 2 * (1 + |C - ‖ρ‖|) ^ 2 * ((profHat p) ^ 2 * ‖p‖ ^ 2)) :=
    (h0.const_mul (2 * (1 + |C - ‖ρ‖|) ^ 2)).add
      (h2.const_mul (2 * (1 + |C - ‖ρ‖|) ^ 2))
  refine hg.mono' ?_ ?_
  · have hcont : Continuous (fun p : ℝ³ => Submission.BoseGases.fsKinCoeff C ‖ρ + p‖) := by
      unfold Submission.BoseGases.fsKinCoeff
      fun_prop
    exact (hcont.mul (continuous_profHat.pow 2)).aestronglyMeasurable
  · filter_upwards with p
    rw [Real.norm_of_nonneg
      (mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg C ‖ρ + p‖) (sq_nonneg _))]
    refine (mul_le_mul_of_nonneg_right (fsKinCoeff_shift_le C ρ p) (sq_nonneg _)).trans ?_
    exact fsKinCoeff_mul_profHat_sq_le (C - ‖ρ‖) p

end Work.OneBodyKin

namespace Work.OneBodyKin

namespace Work.OneBodyKin

open MeasureTheory

/-- The same statement under the doubled namespace prefix of the original stub
(`Work.OneBodyKin.Work.OneBodyKin.…`); an alias of
`Work.OneBodyKin.integrable_fsKinCoeff_shift_mul_profHat_sq`. -/
theorem integrable_fsKinCoeff_shift_mul_profHat_sq (C : ℝ) (ρ : EuclideanSpace ℝ (Fin 3)) :
    Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.fsKinCoeff C ‖ρ + p‖ * (Work.OneBodyKin.profHat p) ^ 2) :=
  _root_.Work.OneBodyKin.integrable_fsKinCoeff_shift_mul_profHat_sq C ρ

end Work.OneBodyKin

end Work.OneBodyKin
