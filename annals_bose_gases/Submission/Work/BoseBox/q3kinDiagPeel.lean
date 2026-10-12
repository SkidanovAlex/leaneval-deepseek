import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBox.q3kinDiagCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBox.q3kinDiagPeel` — peeling one slot out of the diagonal mode content

This module proves the slot-peel identity used to compare the diagonal `p`-space mode content
of an `(m+1)`-body state with the fibre energy of the `m`-body state obtained by removing that
slot:

    (ℓ³)⁻¹ ∫_{abox (m+1) ℓ} ‖pSlotAmp ℓ p Φ i x‖² dx
      = ∫_{abox m ℓ} bOKT ℓ (fibre_i Φ r) p dr .

The mathematics is the composition of three already-available identifications:

* `pSlotAmp ℓ p Φ i = tBamp (chiScale ℓ) p (aQ ℓ i Φ) i`: the corpus's `Q_B`-projected mode
  amplitude is the windowed-exponential amplitude of the `Q_i`-projected state
  (`SmallBoxBridge.ModeIdent.pSlotAmp_eq_rawSlotAmp` together with
  `SmallBoxTBWord.tBamp_chiScale_eq_rawSlotAmp`);
* `SmallBoxTBWord.tBamp_peel`: the ambient box integral over the `(m+1)`-particle box
  factorises, the `i`-th slot contributing exactly its volume `ℓ³`, and the remaining
  amplitude is the `p`-Fourier transform of the windowed inserted fibre;
* the pointwise identification `bsQ ℓ 0 (fibre_i Φ r) = aQ ℓ i Φ ∘ kcInsN m i (·, r)` of the
  mean-free parts (this file), which converts the last amplitude into `fibKT`.
-/

namespace Work.BoseBox

open MeasureTheory
open scoped Topology Real BigOperators

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## 1. The `Q_i`-projection of the fibre is the box mean-free fibre -/

/-- **The mean-free fibre identity.**  Subtracting from `Φ` its `i`-th slot mean over the small
box `acube ℓ` and then restricting to the `i`-th slot fibre is the same as subtracting from the
fibre its box mean; this is the pointwise bridge between the corpus projection `aQ ℓ i` on
`X (m+1)` and the moving-box projection `bsQ ℓ 0` on functions on `ℝ³`. -/
lemma aQ_fibre_eq_bsQ {m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : X (m + 1) → ℝ} (hΦ : Continuous Φ) (i : Fin (m + 1)) (r : X m)
    (z : EuclideanSpace ℝ (Fin 3)) :
    aQ ℓ i Φ (kcInsN m i (z, r))
      = Work.BSKinetic.bsQ ℓ 0
          (fun z' : EuclideanSpace ℝ (Fin 3) => Φ (kcInsN m i (z', r))) z := by
  unfold aQ aP Work.BSKinetic.bsQ Work.BSKinetic.bsMean
  simp only [update_kcInsN, one_div, smul_zero, zero_add]

/-! ## 2. `fibKT` is the squared windowed Fourier transform of the `Q_i`-projected fibre -/

/-- **`fibKT` unwrapped.**  `fibKT ℓ Φ i r p` is the square of the windowed `p`-Fourier
transform, not of the raw fibre, but of the `Q_i`-projected fibre — the two agree because the
box mean of the fibre is exactly the value of the slot mean of `Φ`. -/
lemma fibKT_eq_kinFT_aQ {m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : X (m + 1) → ℝ} (hΦ : Continuous Φ) (i : Fin (m + 1)) (r : X m)
    (p : EuclideanSpace ℝ (Fin 3)) :
    fibKT ℓ Φ i r p
      = ‖kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (chiScale ℓ z : ℂ) *
          ((aQ ℓ i Φ) (kcInsN m i (z, r)) : ℂ)) p‖ ^ 2 := by
  unfold fibKT bOKT
  have hfun : (fun z : EuclideanSpace ℝ (Fin 3) => (Work.BSKinetic.bsWin ℓ 0 z : ℂ) *
        (Work.BSKinetic.bsQ ℓ 0
          (fun z' : EuclideanSpace ℝ (Fin 3) => Φ (kcInsN m i (z', r))) z : ℂ))
      = fun z : EuclideanSpace ℝ (Fin 3) => (chiScale ℓ z : ℂ) *
          ((aQ ℓ i Φ) (kcInsN m i (z, r)) : ℂ) := by
    funext z
    rw [aQ_fibre_eq_bsQ hℓ hΦ i r z]
    simp [Work.BSKinetic.bsWin]
  rw [hfun]

/-! ## 3. The corpus slot amplitude is the windowed-exponential amplitude of `aQ ℓ i Φ` -/

/-- **The slot amplitude in `tBamp` form.** -/
lemma pSlotAmp_eq_tBamp_chiScale {m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : X (m + 1) → ℝ} (hΦ : Continuous Φ) (i : Fin (m + 1))
    (p : EuclideanSpace ℝ (Fin 3)) (x : X (m + 1)) :
    pSlotAmp ℓ p Φ i x
      = Work.SmallBoxTBWord.tBamp (chiScale ℓ) p (aQ ℓ i Φ) i x := by
  rw [Work.SmallBoxBridge.ModeIdent.pSlotAmp_eq_rawSlotAmp hℓ p hΦ i x]
  exact (Work.SmallBoxTBWord.tBamp_chiScale_eq_rawSlotAmp hℓ p (aQ ℓ i Φ) i x).symm

/-! ## 4. The peel -/

theorem q3kinDiagPeel {m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X (m + 1) → ℝ} (hΦ : Continuous Φ) (i : Fin (m + 1))
    (p : EuclideanSpace ℝ (Fin 3)) :
    (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (m + 1) ℓ,
        ‖Submission.BoseGases.pSlotAmp ℓ p Φ i x‖ ^ 2
      = ∫ r in Submission.BoseGases.abox m ℓ, Work.BoseBox.fibKT ℓ Φ i r p := by
  have hstep : (ℓ ^ 3)⁻¹ * ∫ x in abox (m + 1) ℓ, ‖pSlotAmp ℓ p Φ i x‖ ^ 2
      = (ℓ ^ 3)⁻¹ * ∫ x in abox (m + 1) ℓ,
          ‖Work.SmallBoxTBWord.tBamp (chiScale ℓ) p (aQ ℓ i Φ) i x‖ ^ 2 := by
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    simp only []
    rw [pSlotAmp_eq_tBamp_chiScale hℓ hΦ i p x]
  rw [hstep,
    Work.SmallBoxTBWord.tBamp_peel hℓ (chiScale_continuous ℓ)
      (fun z hz => by_contra fun h => hz (chiScale_mem_acube hℓ h))
      (aQ_continuous hℓ i hΦ) i p]
  exact integral_congr_ae (Filter.Eventually.of_forall
    (fun r => (fibKT_eq_kinFT_aQ hℓ hΦ i r p).symm))

end Work.BoseBox
