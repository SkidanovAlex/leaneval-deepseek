import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.farLatFourier
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory

namespace Work.BoseFixR.LatGreen

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The position-space Coulomb/autocorrelation identity for an a.e.-nonnegative kernel.**

`Work.BoseFixR.LatGreen.coulomb_pair_eq_autocorr_integral` proves

  `∫ p : ℝ³ × ℝ³, V p.1 · V p.2/‖p.1 − p.2‖ = ∫ u, (∫ x, V x · V(x+u))/‖u‖`

for an integrable, **pointwise** nonnegative, even `V` with finite momentum-space Coulomb energy
(`hint`).  The kernels of this project are only known to be nonnegative a.e., so we need the same
identity from the a.e. hypothesis alone.  The proof is the `U⁺ = max U 0` trick already used by
`Work.BoseFixR.coulomb_autocorr_eq` (`Submission/Work/BoseFixR/farLatFourier.lean`): `V⁺ = max V 0`
is pointwise nonnegative, even, a.e. equal to `V`, and has the same `chat`
(`Work.BoseB7AK.C3Q.chat_congr_ae`) and the same autocorrelation
(`Work.BoseFixR.autocorr_congr_ae`, same file); apply the pointwise identity to `V⁺` and transfer
both sides back along `V⁺ =ᵐ V` (left side: `Measure.quasiMeasurePreserving_fst`/`_snd` with
`QuasiMeasurePreserving.ae`, or `integral_congr_ae` under `volume.prod volume`). -/
theorem coulomb_pair_eq_autocorr_integral_ae {V : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hV1 : MeasureTheory.Integrable V)
    (hVnn : 0 ≤ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))] V)
    (hVev : ∀ x : EuclideanSpace ℝ (Fin 3), V (-x) = V x)
    (hint : MeasureTheory.Integrable
      (fun q : EuclideanSpace ℝ (Fin 3) =>
        (Work.BoseFixR.chat V q) ^ 2 / (2 * ‖q‖ ^ 2))) :
    (∫ p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
        V p.1 * V p.2 / ‖p.1 - p.2‖)
      = ∫ u : EuclideanSpace ℝ (Fin 3),
          (∫ x : EuclideanSpace ℝ (Fin 3), V x * V (x + u)) / ‖u‖ := by
  -- the pointwise nonnegative representative `V⁺ = max V 0`
  set Vp : E3 → ℝ := fun x => max (V x) 0 with hVp
  have hVp0 : ∀ x, 0 ≤ Vp x := fun x => by rw [hVp]; exact le_max_right _ _
  have hVpe : ∀ x, Vp (-x) = Vp x := fun x => by rw [hVp]; simp only [hVev x]
  have hae : Vp =ᵐ[volume] V :=
    hVnn.mono (fun x hx => by rw [hVp]; exact max_eq_left hx)
  have hVp1 : MeasureTheory.Integrable Vp := hV1.congr hae.symm
  have hintp : MeasureTheory.Integrable
      (fun q : E3 => (Work.BoseFixR.chat Vp q) ^ 2 / (2 * ‖q‖ ^ 2)) := by
    refine hint.congr ?_
    filter_upwards with q
    rw [Work.BoseB7AK.C3Q.chat_congr_ae hae q]
  -- the pointwise identity, at `V⁺`
  have hpair := Work.BoseFixR.LatGreen.coulomb_pair_eq_autocorr_integral
    hVp1 hVp0 hVpe hintp
  -- transfer the left-hand (pair-energy) side back to `V`
  have hL : (∫ p : E3 × E3, Vp p.1 * Vp p.2 / ‖p.1 - p.2‖)
      = ∫ p : E3 × E3, V p.1 * V p.2 / ‖p.1 - p.2‖ := by
    refine MeasureTheory.integral_congr_ae ?_
    have h1 : (fun p : E3 × E3 => Vp p.1) =ᵐ[volume.prod volume]
        (fun p : E3 × E3 => V p.1) :=
      (MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := volume)
        (ν := volume)).ae_eq_comp hae
    have h2 : (fun p : E3 × E3 => Vp p.2) =ᵐ[volume.prod volume]
        (fun p : E3 × E3 => V p.2) :=
      (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := volume)
        (ν := volume)).ae_eq_comp hae
    filter_upwards [h1, h2] with p hp1 hp2
    rw [hp1, hp2]
  -- transfer the right-hand (autocorrelation) side back to `V`
  have hR : (∫ u : E3, (∫ x : E3, Vp x * Vp (x + u)) / ‖u‖)
      = ∫ u : E3, (∫ x : E3, V x * V (x + u)) / ‖u‖ := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with u
    rw [Work.BoseFixR.autocorr_congr_ae hae u]
  rw [← hL, ← hR]
  exact hpair

end Work.BoseFixR.LatGreen
