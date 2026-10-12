import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.UBBInputs8.A.abs_wSmallPair_chiB_le
import Submission.Work.UBBInputs8.A.sq_integral_le_integral_sq_mul_support
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs8.A

open Submission.BoseGases

/-- **Real volume of the `x`-support of the localised cutoff.**  The Lebesgue
volume, as a real number, of the support of `χ_{B(u)}` is at most `(ℓd)³`:
`chiSmallB_x_support_measure_le` gives the `ℝ≥0∞` bound
`volume {x | χ_{B(u)}(x) ≠ 0} ≤ ENNReal.ofReal ((ℓd)³)`, and `ENNReal.toReal_mono`
(with `(ℓd)³ ≥ 0`) transfers it to the real measure. -/
lemma measureReal_support_chiSmallB_le {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) (u : EuclideanSpace ℝ (Fin 3)) :
    (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).real
        (Function.support (fun x : EuclideanSpace ℝ (Fin 3) => chiSmallB M ℓ d u x))
      ≤ (ℓ * d) ^ 3 := by
  have hle := chiSmallB_x_support_measure_le hM hℓ hd u
  have hnn : 0 ≤ (ℓ * d) ^ 3 := pow_nonneg (mul_nonneg (le_of_lt hℓ) (le_of_lt hd)) 3
  have htr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rw [MeasureTheory.measureReal_def]
  rw [show Function.support (fun x : EuclideanSpace ℝ (Fin 3) => chiSmallB M ℓ d u x)
      = {x : EuclideanSpace ℝ (Fin 3) | chiSmallB M ℓ d u x ≠ 0} from by
        ext x; simp [Function.mem_support]]
  simpa [ENNReal.toReal_ofReal hnn] using htr

/-- **The Cauchy–Schwarz mass bound for the localised cutoff.**  `chiMass M L d u = ∫ χ_{B(u)}²`,
so the `L¹`-mass `∫ χ_{B(u)}` of the cutoff is controlled by its `L²`-mass:

    `(∫ χ_{B(u)})² ≤ (∫ χ_{B(u)}²) · |supp χ_{B(u)}| ≤ chiMass · (L d)³`,

the second factor from `Submission.BoseGases.chiSmallB_x_support_measure_le`
(the support of `χ_{B(u)}` lies in the `(L d)`-cube centred at `(L d)u`).  Cauchy–Schwarz is
applied on the support set, where `χ_{B(u)}` is `L²` and `1` is `L²` because the measure is
finite; the elementary route is the mean subtraction `0 ≤ ∫ (χ_B − λ)²` with
`λ = (∫ χ_B)/(vol supp)`. -/
theorem sq_integral_chiSmallB_le {M : ℕ} (hM : 1 ≤ M) {L d : ℝ} (hL : 0 < L) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) :
    (∫ x : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.chiSmallB M L d u x) ^ 2
      ≤ Work.SmallBoxSliding.chiMass M L d u * (L * d) ^ 3 := by
  have hf : Continuous (fun x : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.chiSmallB M L d u x) :=
    Submission.BoseGases.chiSmallB_continuous hM hL hd u
  have hcs : HasCompactSupport (fun x : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.chiSmallB M L d u x) :=
    Submission.BoseGases.chiSmallB_hasCompactSupport hM hL u
  have hmain := sq_integral_le_integral_sq_mul_support hf hcs
  have hvol := measureReal_support_chiSmallB_le hM hL hd u
  have hmass : 0 ≤ Work.SmallBoxSliding.chiMass M L d u :=
    Work.SmallBoxSliding.chiMass_nonneg M L d u
  calc
    (∫ x : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.chiSmallB M L d u x) ^ 2
        ≤ (∫ x : EuclideanSpace ℝ (Fin 3),
              (Submission.BoseGases.chiSmallB M L d u x) ^ 2)
            * (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).real
                (Function.support (fun x : EuclideanSpace ℝ (Fin 3) =>
                  Submission.BoseGases.chiSmallB M L d u x)) := hmain
    _ = Work.SmallBoxSliding.chiMass M L d u
            * (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).real
                (Function.support (fun x : EuclideanSpace ℝ (Fin 3) =>
                  Submission.BoseGases.chiSmallB M L d u x)) := by
        rw [Work.SmallBoxSliding.chiMass_def]
    _ ≤ Work.SmallBoxSliding.chiMass M L d u * (L * d) ^ 3 :=
        mul_le_mul_of_nonneg_left hvol hmass

end Work.UBBInputs8.A
