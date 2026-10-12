import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Submission.Work.BoseBoxFock.L1Tails.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.L1Tails.coulMomentumLe` — the Fourier link for the Coulomb energy

The momentum-space (H⁻¹-)energy of an `L¹` weight `W` is controlled by its position-space
Coulomb energy:

`∫⁻_p ‖Ŵ(p)‖²/‖p‖² dp ≤ (2π)³(4π)⁻¹ ∬ W(x)W(y)/‖x−y‖ dx dy`,

where `Ŵ = kinFT W` is the `p`-convention Fourier transform (`kinFT_eq_fourier`).

This is the statement that `1/‖x‖` has Fourier transform `4π/‖p‖²` (equivalently, the
subordination identity `∫_{s>0}(4πs)^{-3/2}e^{-‖x‖²/4s}ds = (4π‖x‖)⁻¹`), and it is one of the
two halves of the design's T3 (the other being the x-space duality `coulombDual`).

## Proof

The commons lemma `Commons.Analysis.Fourier.lintegral_fourier_inv_smul_sq_div_le` already
proves the sharp form at the *Mathlib* Fourier convention:

`(2π)^{-3} ∫⁻_q ‖𝓕f(q/2π)‖²/‖q‖² ≤ (4π)⁻¹ ∫⁻_x∫⁻_y f x f y/‖x−y‖`

for `f ∈ L¹`, `f ≥ 0` **pointwise**.  Our `W` is only a.e. nonnegative, so we apply it to the
positive part `|W| =ᵐ W` (which changes neither `kinFT` nor the Coulomb double integral), and
then convert the double lintegral `∫⁻_x∫⁻_y` into `ENNReal.ofReal` of the Bochner integral of
`coulInt W` (legitimate by `hW0` and `hJ`).
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock.L1Tails

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000

theorem coulMomentumLe {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hWi : MeasureTheory.Integrable W)
    (hW0 : ∀ᵐ x, 0 ≤ W x) (hJ : MeasureTheory.Integrable (Work.BoseBoxFock.coulInt W)) :
    (∫⁻ p, ENNReal.ofReal
        (‖Submission.BoseGases.kinFT (fun x : EuclideanSpace ℝ (Fin 3) => ((W x : ℝ) : ℂ)) p‖ ^ 2
          / ‖p‖ ^ 2))
      ≤ ENNReal.ofReal ((2 * Real.pi) ^ 3 * (4 * Real.pi)⁻¹
          * ∫ q, Work.BoseBoxFock.coulInt W q) := by
  -- `|W| =ᵐ W`, since `W ≥ 0` a.e.
  have hae : (fun x : E3 => |W x|) =ᵐ[volume] W := by
    filter_upwards [hW0] with x hx
    exact abs_of_nonneg hx
  -- `kinFT` is unchanged by replacing `W` by `|W|`
  have hkin : ∀ p : E3, Submission.BoseGases.kinFT (fun x : E3 => ((|W x| : ℝ) : ℂ)) p
      = Submission.BoseGases.kinFT (fun x : E3 => ((W x : ℝ) : ℂ)) p := by
    intro p
    simp only [Submission.BoseGases.kinFT]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hae] with x hx
    rw [hx]
  -- the momentum side: rewrite `kinFT` as Mathlib's `𝓕`
  have hA : (∫⁻ p, ENNReal.ofReal
        (‖Submission.BoseGases.kinFT (fun x : E3 => ((W x : ℝ) : ℂ)) p‖ ^ 2 / ‖p‖ ^ 2))
      = ∫⁻ q, ENNReal.ofReal
          (‖FourierTransform.fourier (fun x : E3 => ((|W x| : ℝ) : ℂ))
              ((2 * Real.pi)⁻¹ • q)‖ ^ 2 / ‖q‖ ^ 2) := by
    rw [show (∫⁻ p, ENNReal.ofReal
          (‖Submission.BoseGases.kinFT (fun x : E3 => ((W x : ℝ) : ℂ)) p‖ ^ 2 / ‖p‖ ^ 2))
        = ∫⁻ p, ENNReal.ofReal
          (‖Submission.BoseGases.kinFT (fun x : E3 => ((|W x| : ℝ) : ℂ)) p‖ ^ 2 / ‖p‖ ^ 2) from
        lintegral_congr (fun p => by rw [hkin p])]
    exact lintegral_congr (fun q => by rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier])
  -- the position side: the double lintegral of `|W|` is `ofReal` of the Coulomb integral of `W`
  have hY : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (|W x| * |W y| / ‖x - y‖))
      = ENNReal.ofReal (∫ q, Work.BoseBoxFock.coulInt W q) := by
    have h1 : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (|W x| * |W y| / ‖x - y‖))
        = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖) := by
      apply lintegral_congr_ae
      filter_upwards [hae] with x hx
      apply lintegral_congr_ae
      filter_upwards [hae] with y hy
      rw [hx, hy]
    have h2 : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y / ‖x - y‖))
        = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y * (‖x - y‖)⁻¹) := by
      apply lintegral_congr
      intro x
      apply lintegral_congr
      intro y
      congr 1
    have hJae : AEMeasurable
        (Function.uncurry (fun x y : E3 =>
          ENNReal.ofReal (W x * W y * (‖x - y‖)⁻¹))) (volume.prod volume) :=
      ENNReal.measurable_ofReal.comp_aemeasurable hJ.aestronglyMeasurable.aemeasurable
    have h3 : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (W x * W y * (‖x - y‖)⁻¹))
        = ∫⁻ q : E3 × E3, ENNReal.ofReal (Work.BoseBoxFock.coulInt W q) :=
      MeasureTheory.lintegral_lintegral
        (f := fun x y : E3 => ENNReal.ofReal (W x * W y * (‖x - y‖)⁻¹)) hJae
    have h4 : (∫⁻ q : E3 × E3, ENNReal.ofReal (Work.BoseBoxFock.coulInt W q))
        = ENNReal.ofReal (∫ q, Work.BoseBoxFock.coulInt W q) := by
      refine (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hJ ?_).symm
      have hq1 : ∀ᵐ q : E3 × E3 ∂(volume.prod volume), 0 ≤ W q.1 :=
        MeasureTheory.Measure.quasiMeasurePreserving_fst.ae hW0
      have hq2 : ∀ᵐ q : E3 × E3 ∂(volume.prod volume), 0 ≤ W q.2 :=
        MeasureTheory.Measure.quasiMeasurePreserving_snd.ae hW0
      filter_upwards [hq1, hq2] with q h1 h2
      exact mul_nonneg (mul_nonneg h1 h2) (inv_nonneg.mpr (norm_nonneg _))
    rw [h1, h2, h3, h4]
  have hL := Commons.Analysis.Fourier.lintegral_fourier_inv_smul_sq_div_le
    (f := fun x : E3 => |W x|) hWi.abs (fun x => abs_nonneg (W x))
  set Aq : ENNReal := ∫⁻ q, ENNReal.ofReal
      (‖FourierTransform.fourier (fun x : E3 => ((|W x| : ℝ) : ℂ)) ((2 * Real.pi)⁻¹ • q)‖ ^ 2
        / ‖q‖ ^ 2)
  set Yq : ENNReal := ∫⁻ x, ∫⁻ y, ENNReal.ofReal (|W x| * |W y| / ‖x - y‖)
  calc (∫⁻ p, ENNReal.ofReal
        (‖Submission.BoseGases.kinFT (fun x : E3 => ((W x : ℝ) : ℂ)) p‖ ^ 2 / ‖p‖ ^ 2))
      = ENNReal.ofReal ((2 * Real.pi) ^ 3) *
          (ENNReal.ofReal (((2 * Real.pi) ^ 3)⁻¹) * Aq) := by
        rw [hA, ← mul_assoc,
          ← ENNReal.ofReal_mul (show (0:ℝ) ≤ (2 * Real.pi) ^ 3 by positivity),
          mul_inv_cancel₀ (ne_of_gt (show (0:ℝ) < (2 * Real.pi) ^ 3 by positivity)),
          ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal ((2 * Real.pi) ^ 3) *
          (ENNReal.ofReal (1 / (4 * Real.pi)) * Yq) :=
        mul_le_mul_of_nonneg_left hL zero_le
    _ = ENNReal.ofReal ((2 * Real.pi) ^ 3 * (4 * Real.pi)⁻¹
          * ∫ q, Work.BoseBoxFock.coulInt W q) := by
        rw [hY,
          ← ENNReal.ofReal_mul (show (0:ℝ) ≤ 1 / (4 * Real.pi) by positivity),
          ← ENNReal.ofReal_mul (show (0:ℝ) ≤ (2 * Real.pi) ^ 3 by positivity)]
        congr 1
        rw [one_div]
        ring

end Work.BoseBoxFock.L1Tails
