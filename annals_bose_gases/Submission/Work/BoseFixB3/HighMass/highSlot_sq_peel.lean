import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB3.HighMass.Base
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.HighMass.highSlot_sq_peel`

Peeling one slot out of the box integral of the `Q̄_{L,i}` mass:

`∫_{abox (m+1) ℓ} (Q̄_{L,i}(Q_iΦ))² = ∫_{abox m ℓ} ∫_{acube ℓ} (highMult (bsQ ℓ 0 (Φ∘kcInsN)) y)²`.

The proof is the measure-preserving change of variables `kcInsN m i` together with the
pointwise fibre identification `highSlot_aQ_eq`: after inserting the `i`-th coordinate the
slot-`i` fibre is `z ↦ Φ (kcInsN m i (z,r))`, independently of the inserted value `y`.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixB3.HighMass

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseKinLoc
open Work.BoseBoxFix Work.BSKinetic

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The slot-`i` fibre of a state at an inserted configuration `kcInsN m i (y,r)` is the
inserted slot fibre `z ↦ Φ (kcInsN m i (z,r))`, independent of the inserted value `y`. -/
lemma fibre_kcInsN {m : ℕ} (i : Fin (m + 1)) (Φ : X (m + 1) → ℝ) (y : ℝ³) (r : X m) :
    fibre (m + 1) i Φ (kcInsN m i (y, r)) = fun z : ℝ³ => Φ (kcInsN m i (z, r)) := by
  funext z
  rw [fibre, update_kcInsN]

theorem highSlot_sq_peel {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ} (hℓ : 0 < ℓ) {m : ℕ}
    (i : Fin (m + 1)) {Φ : Submission.BoseGases.X (m + 1) → ℝ} (hΦc : Continuous Φ)
    (hInt : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X (m + 1) =>
        (Work.BoseFixB3.highSlot fc κ ℓ i (Submission.BoseGases.aQ ℓ i Φ) x) ^ 2)
      (Submission.BoseGases.abox (m + 1) ℓ)) :
    ∫ x in Submission.BoseGases.abox (m + 1) ℓ,
        (Work.BoseFixB3.highSlot fc κ ℓ i (Submission.BoseGases.aQ ℓ i Φ) x) ^ 2
      = ∫ r in Submission.BoseGases.abox m ℓ, ∫ y in Submission.BoseGases.acube ℓ,
          (Work.BoseFixB3.highMult fc κ ℓ
            (Work.BSKinetic.bsQ ℓ 0
              (fun z : EuclideanSpace ℝ (Fin 3) => Φ (Submission.BoseGases.kcInsN m i (z, r)))) y) ^ 2 := by
  -- Pointwise: `highSlot` of `Q_iΦ` is the complementary multiplier of the mean-free fibre.
  have hpt : ∀ x : X (m + 1),
      (highSlot fc κ ℓ i (aQ ℓ i Φ) x) ^ 2
        = (highMult fc κ ℓ (bsQ ℓ 0 (fibre (m + 1) i Φ x)) (x i)) ^ 2 :=
    fun x => by rw [highSlot_aQ_eq hℓ i hΦc x]
  have hInt' : IntegrableOn
      (fun x : X (m + 1) =>
        (highMult fc κ ℓ (bsQ ℓ 0 (fibre (m + 1) i Φ x)) (x i)) ^ 2)
      (abox (m + 1) ℓ) volume :=
    hInt.congr (Filter.Eventually.of_forall hpt)
  -- Peel the `i`-th coordinate out of the box integral.
  have hpeel := abox_integral_peel (n := m) (ℓ := ℓ) i
    (fun x : X (m + 1) => (highMult fc κ ℓ (bsQ ℓ 0 (fibre (m + 1) i Φ x)) (x i)) ^ 2) hInt'
  calc
    ∫ x in abox (m + 1) ℓ, (highSlot fc κ ℓ i (aQ ℓ i Φ) x) ^ 2
        = ∫ x in abox (m + 1) ℓ,
            (highMult fc κ ℓ (bsQ ℓ 0 (fibre (m + 1) i Φ x)) (x i)) ^ 2 :=
          integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ∫ r in abox m ℓ, ∫ y in acube ℓ,
            (highMult fc κ ℓ (bsQ ℓ 0 (fibre (m + 1) i Φ (kcInsN m i (y, r))))
              ((kcInsN m i (y, r)) i)) ^ 2 := hpeel
    _ = ∫ r in abox m ℓ, ∫ y in acube ℓ,
          (highMult fc κ ℓ
            (bsQ ℓ 0 (fun z : ℝ³ => Φ (kcInsN m i (z, r)))) y) ^ 2 := by
          apply integral_congr_ae
          filter_upwards with r
          apply integral_congr_ae
          filter_upwards with y
          rw [fibre_kcInsN i Φ y r, kc_insN_apply_same]

end Work.BoseFixB3.HighMass
