import Mathlib
import Submission.Work.KMTPlan.A6Clean.packetFamG_aux
import Submission.Work.A6Clean.ennreal_tsum_conv_sq_le
-- the definitions (`mdlSliceF` / `mdlSliceG` / `MdlSliceCoreGainMemLp`) live in the cycle-free
-- definitions module (see the note in `KMTPlan/A6Clean/packetFamG_aux.lean`); importing the
-- §8-chain file `MdlSliceCoreGainBig` drags the copied chain in and clashes with the `KMTPlan`
-- originals.

namespace Work.A6Clean

open MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

/-! ## Elementary facts used in the assembly -/

/-- `‖z‖ₑ = ofReal ‖z‖` for complex `z`. -/
lemma enorm_complex_eq_ofReal (z : ℂ) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by
  rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal]
  norm_cast

/-- The real exponent `2` and the natural exponent `2` agree. -/
lemma rpow_two_eq_pow_two (x : ENNReal) : x ^ (2 : ℝ) = x ^ (2 : ℕ) := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]

/-- The real exponent `2` and the natural exponent `2` agree (other direction). -/
lemma pow_two_eq_rpow_two (x : ENNReal) : x ^ (2 : ℕ) = x ^ (2 : ℝ) :=
  (rpow_two_eq_pow_two x).symm

/-- The window modulation `winModR α` multiplies the sequence by a unimodular scalar, hence does
not change the `r`-variational norm. -/
lemma variationalNorm_winModR_apply (R : NNReal) (hR : 1 ≤ R)
    (α : Work.Analysis.IonescuWainger.Circle) (v : ℕ → ℤ → ℂ) (x : ℤ) :
    PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ => Work.KMTAreas.A7.winModR α (v n) x)
      = PointwiseErgodicTheorems.variationalNorm R (fun n : ℕ => v n x) := by
  have h : (fun n : ℕ => Work.KMTAreas.A7.winModR α (v n) x)
      = (fourier (T := 1) (-x) α) • (fun n : ℕ => v n x) := by
    funext n
    rfl
  rw [h, Submission.PointwiseErgodicTheorems.variationalNorm_smul hR, enorm_complex_eq_ofReal,
    Work.KMTAreas.A7.norm_fourier_applyR, ENNReal.ofReal_one, one_mul]

/-- **Young's inequality for the window convolution against the variational norm**: the `r`-variation
of the window convolution of a family is bounded by the `ℓ¹`-mass of the window kernel times the
`r`-variation of the modulated family (the phase `winModR` is unimodular and drops out). -/
lemma vr_winConvR_winMod_le (R : NNReal) (hR : 1 ≤ R) (m₂ : ℝ → ℂ)
    (β : Work.Analysis.IonescuWainger.Circle) (u : ℕ → ℤ → ℂ) (m : ℤ) :
    PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ => Work.KMTAreas.A7.winConvR m₂ (Work.KMTAreas.A7.winModR (-β) (u n)) m)
      ≤ ∑' j : ℤ, ‖Work.KMTAreas.A7.cw m₂ j‖ₑ *
          PointwiseErgodicTheorems.variationalNorm R (fun n : ℕ => u n (m - j)) := by
  have h := Work.KMTAreas.A7Hi.variationalNorm_tsum_le R hR (Work.KMTAreas.A7.cw m₂)
    (fun j n => Work.KMTAreas.A7.winModR (-β) (u n) (m - j))
  refine le_of_eq_of_le ?_ (h.trans (ENNReal.tsum_le_tsum (fun j => ?_)))
  · rfl
  · rw [variationalNorm_winModR_apply R hR (-β) u (m - j)]

end

end Work.A6Clean
