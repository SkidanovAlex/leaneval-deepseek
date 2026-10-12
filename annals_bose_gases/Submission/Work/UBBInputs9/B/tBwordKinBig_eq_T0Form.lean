import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.UBBInputs9.A.tBdiagFormInd_eq_tBdiagForm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs9.B.tBwordKinBig_eq_T0Form`

The big-box kinetic word at the centred box `Λ(0) = acube ℓ` with the box window `chiScale ℓ`
and no spectral cutoff (`c = 0`) is exactly the corpus's one-body windowed kinetic form
`T0Form ℓ (‖·‖²)`:

    `tBwordKinBig 1 ℓ 0 Φ = T0Form ℓ (fun r => r ^ 2) Φ`.

Both sides are the same object written through two different projections:

* `tBwordKinBig` uses the FS-faithful word `tBwordKinInd` built on the indicator-carrying
  projection `boxQInd` (`Work.UBBInputs8`), with symbol `fsKinCoeff 0 = [·]₊²`;
* `T0Form` uses the corpus projection `aQ ℓ` and the plain symbol `‖·‖²`.

The two steps are the corpus's existing bridges:

* `Work.UBBInputs9.A.tBdiagFormInd_eq_tBdiagForm` removes the box indicator — the sliding window
  `chiScale ℓ` is supported in `acube ℓ`;
* `Work.SmallBoxTBWord.tBdiagForm_chiScale_eq_T0Form` identifies the indicator-free word with
  `T0Form` (both `boxQ (ℓ³) (acube ℓ) = aQ ℓ` and `tBamp (chiScale ℓ) = rawSlotAmp ℓ`);

and the leftover is the pointwise identity `fsKinCoeff 0 ‖p‖ = ‖p‖²` on `[0, ∞)`.
-/

namespace Work.UBBInputs9.B

open MeasureTheory
open Submission.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The scaled bump vanishes off the centred cube: `z ∉ acube ℓ → chiScale ℓ z = 0`. -/
lemma chiScale_eq_zero_of_not_mem_acube {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℝ³}
    (hz : z ∉ acube ℓ) : chiScale ℓ z = 0 := by
  by_contra h
  exact hz (chiScale_mem_acube hℓ h)

/-- The spectral coefficient with no cutoff is the square on the nonnegative half-line:
`fsKinCoeff 0 r = r²` for `0 ≤ r`. -/
lemma fsKinCoeff_zero_eq_sq {r : ℝ} (hr : 0 ≤ r) : fsKinCoeff 0 r = r ^ 2 := by
  rw [fsKinCoeff, sub_zero]
  rw [max_eq_left hr]

/-- `tBdiagFormInd` with the box window `chiScale ℓ` on `acube ℓ` equals `T0Form`. -/
lemma tBdiagFormInd_chiScale_eq_T0Form {ℓ : ℝ} (hℓ : 0 < ℓ) (F : ℝ → ℝ)
    {N : ℕ} (Ψ : X N → ℝ) :
    Work.UBBInputs8.tBdiagFormInd ℓ (acube ℓ) (ℓ ^ 3) (chiScale ℓ) F Ψ
      = Work.SmallBoxTBWord.tBdiagForm ℓ (acube ℓ) (ℓ ^ 3) (chiScale ℓ) F Ψ :=
  Work.UBBInputs9.A.tBdiagFormInd_eq_tBdiagForm F Ψ
    (fun z hz => chiScale_eq_zero_of_not_mem_acube hℓ hz)

theorem tBwordKinBig_eq_T0Form {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X 1 → ℝ} :
    Work.UBBInputs9.tBwordKinBig 1 ℓ 0 Φ = Submission.BoseGases.T0Form ℓ (fun r => r ^ 2) Φ := by
  calc Work.UBBInputs9.tBwordKinBig 1 ℓ 0 Φ
      = Work.UBBInputs8.tBdiagFormInd ℓ (acube ℓ) (ℓ ^ 3) (chiScale ℓ)
          (fsKinCoeff 0) Φ := rfl
    _ = Work.SmallBoxTBWord.tBdiagForm ℓ (acube ℓ) (ℓ ^ 3) (chiScale ℓ)
          (fsKinCoeff 0) Φ := by
        rw [Work.UBBInputs9.A.tBdiagFormInd_eq_tBdiagForm (fsKinCoeff 0) Φ
          (fun z hz => chiScale_eq_zero_of_not_mem_acube hℓ hz)]
    _ = Submission.BoseGases.T0Form ℓ (fsKinCoeff 0) Φ :=
        Work.SmallBoxTBWord.tBdiagForm_chiScale_eq_T0Form (n := 0) hℓ (fsKinCoeff 0) Φ
    _ = Submission.BoseGases.T0Form ℓ (fun r => r ^ 2) Φ := by
        unfold Submission.BoseGases.T0Form
        refine Finset.sum_congr rfl (fun i _ => ?_)
        congr 1
        apply integral_congr_ae
        filter_upwards with p
        rw [fsKinCoeff_zero_eq_sq (norm_nonneg p)]

end Work.UBBInputs9.B
