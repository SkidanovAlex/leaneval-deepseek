import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1B.B1Bfix.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.B1Bfix.Basic`

The elementary `p`-space step of the convergence proof for
`Work.BoseFixB1B.tendsto_tBdiagFormInd_cut`: a **uniform `(1+‖p‖)⁻³` decay bound on the
windowed slot amplitude makes the slot form integrable**.

If `‖slotAmpF a A volA χ i v p x‖ ≤ C/(1+‖p‖)³` for every frequency `p` and every configuration
`x` of the ambient box, then

    slotY a A volA χ i v p = (a³)⁻¹ ∫_{abox} ‖slotAmpF‖² ≤ (a³)⁻¹ |abox| (C/(1+‖p‖)³)² ,

and `p ↦ fsKinCoeff c ‖p‖ (C/(1+‖p‖)³)²` is integrable on `ℝ³`
(`Work.SlotWord.integrable_fsKinCoeff_decay`), so the `p`-integrand of the slot form is
integrable.  This is the integrability half of the dominated-convergence bookkeeping of the
assembly: it is what makes the arithmetic (linearity in the state) of the Bochner integrals
legitimate at every fixed `δ`.
-/

noncomputable section

open MeasureTheory
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-- **The `x`-energy of a slot amplitude is bounded by its pointwise bound** on the box. -/
theorem slotY_le_of_bound {n : ℕ} {a : ℝ} (ha : 0 < a) {A : Set E3} {volA : ℝ} {χ : E3 → ℝ}
    {v : Submission.BoseGases.X (n + 1) → ℝ} (i : Fin (n + 1)) {p : E3} {C : ℝ}
    (hdec : ∀ x ∈ Submission.BoseGases.abox (n + 1) a,
      ‖slotAmpF a A volA χ i v p x‖ ≤ C) :
    slotY a A volA χ i v p
      ≤ (a ^ 3)⁻¹ * (volume.real (Submission.BoseGases.abox (n + 1) a)) * C ^ 2 := by
  haveI : IsFiniteMeasure
      ((volume : Measure (Submission.BoseGases.X (n + 1))).restrict
        (Submission.BoseGases.abox (n + 1) a)) :=
    isFiniteMeasure_restrict.mpr
      (ne_of_lt (Submission.BoseGases.abox_compact (n + 1) ha).measure_lt_top)
  have hle : ∀ᵐ x ∂((volume : Measure (Submission.BoseGases.X (n + 1))).restrict
      (Submission.BoseGases.abox (n + 1) a)),
      ‖slotAmpF a A volA χ i v p x‖ ^ 2 ≤ C ^ 2 := by
    rw [MeasureTheory.ae_restrict_iff'
      (Submission.BoseGases.abox_isClosed (n + 1) a).measurableSet]
    exact Filter.Eventually.of_forall fun x hx =>
      pow_le_pow_left₀ (norm_nonneg _) (hdec x hx) 2
  have h1 : (∫ x in Submission.BoseGases.abox (n + 1) a,
        ‖slotAmpF a A volA χ i v p x‖ ^ 2)
      ≤ (C ^ 2) * (volume.real (Submission.BoseGases.abox (n + 1) a)) := by
    calc (∫ x in Submission.BoseGases.abox (n + 1) a,
          ‖slotAmpF a A volA χ i v p x‖ ^ 2)
        ≤ ∫ x in Submission.BoseGases.abox (n + 1) a, C ^ 2 :=
          MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _)
            (integrable_const _) hle
      _ = (C ^ 2) * (volume.real (Submission.BoseGases.abox (n + 1) a)) := by
          rw [MeasureTheory.integral_const, smul_eq_mul, mul_comm, MeasureTheory.Measure.real,
            MeasureTheory.Measure.restrict_apply_univ]
          rfl
  rw [slotY]
  calc (a ^ 3)⁻¹ * (∫ x in Submission.BoseGases.abox (n + 1) a,
        ‖slotAmpF a A volA χ i v p x‖ ^ 2)
      ≤ (a ^ 3)⁻¹ * ((C ^ 2) * (volume.real (Submission.BoseGases.abox (n + 1) a))) :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr (pow_nonneg ha.le 3))
    _ = (a ^ 3)⁻¹ * (volume.real (Submission.BoseGases.abox (n + 1) a)) * C ^ 2 := by ring

/-- `slotY` is nonnegative. -/
theorem slotY_nonneg {n : ℕ} {a : ℝ} (ha : 0 ≤ a) {A : Set E3} {volA : ℝ} {χ : E3 → ℝ}
    {v : Submission.BoseGases.X (n + 1) → ℝ} (i : Fin (n + 1)) (p : E3) :
    0 ≤ slotY a A volA χ i v p := by
  rw [slotY]
  exact mul_nonneg (inv_nonneg.mpr (pow_nonneg ha 3))
    (integral_nonneg fun x => sq_nonneg _)

/-- **Integrability of the slot form from a pointwise amplitude bound.** -/
theorem slotFormL_integrable_of_decay {n : ℕ} {a c : ℝ} (ha : 0 < a) {A : Set E3} {volA : ℝ}
    {χ : E3 → ℝ} {v : Submission.BoseGases.X (n + 1) → ℝ} (i : Fin (n + 1))
    (hYm : AEMeasurable (fun p : E3 => slotY a A volA χ i v p) volume) {Cdec : ℝ}
    (hdec : ∀ (p : E3) (x : Submission.BoseGases.X (n + 1)),
      x ∈ Submission.BoseGases.abox (n + 1) a →
        ‖slotAmpF a A volA χ i v p x‖ ≤ Cdec / (1 + ‖p‖) ^ 3) :
    Integrable (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖ * slotY a A volA χ i v p) := by
  set K : ℝ := (a ^ 3)⁻¹ * (volume.real (Submission.BoseGases.abox (n + 1) a)) with hK
  have hKnn : 0 ≤ K := by
    rw [hK]
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg ha.le 3))
      (measureReal_nonneg (μ := volume) (s := Submission.BoseGases.abox (n + 1) a))
  have hg : Integrable (fun p : E3 => K * (Submission.BoseGases.fsKinCoeff c ‖p‖ *
      (Cdec / (1 + ‖p‖) ^ 3) ^ 2)) :=
    (Work.SlotWord.integrable_fsKinCoeff_decay c Cdec).const_mul K
  refine hg.mono' ?_ ?_
  · have hcont : Continuous (fun p : E3 => Submission.BoseGases.fsKinCoeff c ‖p‖) := by
      unfold Submission.BoseGases.fsKinCoeff
      exact (((continuous_id.sub continuous_const).max continuous_const).pow 2).comp
        continuous_norm
    exact (hcont.aemeasurable.mul hYm).aestronglyMeasurable
  · filter_upwards with p
    have h1 : slotY a A volA χ i v p ≤ K * (Cdec / (1 + ‖p‖) ^ 3) ^ 2 := by
      rw [hK]
      exact slotY_le_of_bound ha i (fun x hx => hdec p x hx)
    rw [Real.norm_of_nonneg (mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖)
      (slotY_nonneg ha.le i p))]
    calc Submission.BoseGases.fsKinCoeff c ‖p‖ * slotY a A volA χ i v p
        ≤ Submission.BoseGases.fsKinCoeff c ‖p‖ * (K * (Cdec / (1 + ‖p‖) ^ 3) ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (Submission.BoseGases.fsKinCoeff_nonneg c ‖p‖)
      _ = K * (Submission.BoseGases.fsKinCoeff c ‖p‖ * (Cdec / (1 + ‖p‖) ^ 3) ^ 2) := by ring

end Work.BoseFixB1B
