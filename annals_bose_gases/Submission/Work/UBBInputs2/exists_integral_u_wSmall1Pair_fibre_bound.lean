import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.UBBInputs2.LocPotential
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs2

open MeasureTheory
open scoped Real BigOperators ENNReal Topology

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

/-- **Uniform-in-`a` bound for the sliding integral of the localised one-body kernel.**

At the REPOINTED kernels the dominating weight is
`chiSupAbs · chiSmall M ((ℓ*d)⁻¹ • a - u)` (the `ℓ`-scale corpus factor has sup `chiSupAbs`) times
`2·(chiSupAbs·chiSmallDecay M)/smallConvLower M · |g₀ v h (a - y)|` (the `(ℓd)`-scale factor and
its denominator, plus the `ℓ`-scale denominator `(χ⋆χ)(·/ℓ) ≥ 1/2`); the new hypothesis
`hRχ : R0 ≤ ℓ·chiR0` is exactly the regime making the last bound available.  The bound is
UNIFORMLY in the fixed configuration point `a` and the constant is
`chiSupAbs · (2·(chiSupAbs·chiSmallDecay M)/smallConvLower M) · (∫χ_M)·(∫|g₀|)`. -/
theorem exists_integral_u_wSmall1Pair_fibre_bound {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (h : Work.UBB.ScatSol v) {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ (ℓ * d) / 16) (hRχ : R0 ≤ ℓ * chiR0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : EuclideanSpace ℝ (Fin 3),
      ∫ u : EuclideanSpace ℝ (Fin 3), ‖∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmall1Pair h M ℓ d u a y‖ ≤ C := by
  refine ⟨chiSupAbs * (2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M) *
      ((∫ z : ℝ³, chiSmall M z) * (∫ z : ℝ³, |g0 v h z|)), ?_, ?_⟩
  · have hK0 : 0 ≤ 2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M :=
      div_nonneg (mul_nonneg (by norm_num) (mul_nonneg chiSupAbs_nonneg (chiSmallDecay_nonneg M)))
        (le_of_lt (Work.SmallBoxSliding.smallConvLower_pos M))
    have hX0 : 0 ≤ (∫ z : ℝ³, chiSmall M z) := integral_nonneg (fun z => chiSmall_nonneg M z)
    have hY0 : 0 ≤ (∫ z : ℝ³, |g0 v h z|) := integral_nonneg (fun z => abs_nonneg _)
    exact mul_nonneg (mul_nonneg chiSupAbs_nonneg hK0) (mul_nonneg hX0 hY0)
  · intro a
    have hg0int : Integrable (fun y : ℝ³ => |g0 v h (a - y)|) :=
      (g0_integrable hR0 hv_supp h).abs.comp_sub_left a
    have hGint : Integrable (fun y : ℝ³ =>
        (2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M) * |g0 v h (a - y)|) :=
      hg0int.const_mul _
    have hGint' : Integrable (fun y : ℝ³ =>
        (2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M) * |g0 v h (a - y)|)
        ((volume : Measure ℝ³).restrict (acube ℓ)) :=
      hGint.mono_measure Measure.restrict_le_self
    have hpt : ∀ u : ℝ³, ‖∫ y in acube ℓ, wSmall1Pair h M ℓ d u a y‖ ≤
        (chiSupAbs * chiSmall M ((ℓ * d)⁻¹ • a - u)) *
          (∫ y in acube ℓ, (2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M) *
            |g0 v h (a - y)|) := by
      intro u
      calc ‖∫ y in acube ℓ, wSmall1Pair h M ℓ d u a y‖
          ≤ ∫ y, ‖wSmall1Pair h M ℓ d u a y‖
              ∂((volume : Measure ℝ³).restrict (acube ℓ)) :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ y, (chiSupAbs * chiSmall M ((ℓ * d)⁻¹ • a - u)) *
              ((2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M) *
                |g0 v h (a - y)|)
              ∂((volume : Measure ℝ³).restrict (acube ℓ)) := by
            refine integral_mono_of_nonneg (ae_of_all _ (fun y => norm_nonneg _))
              (hGint'.const_mul _) (ae_of_all _ (fun y => ?_))
            calc ‖wSmall1Pair h M ℓ d u a y‖
                ≤ (chiSupAbs * chiSmall M ((ℓ * d)⁻¹ • a - u)) *
                    (2 * (chiSupAbs * chiSmallDecay M) * |g0 v h (a - y)|)
                    / Work.SmallBoxSliding.smallConvLower M :=
                  Work.SmallBoxSliding.abs_wSmall1Pair_le hv_supp hR0 h hM hℓ hd hR hRχ u a y
              _ = (chiSupAbs * chiSmall M ((ℓ * d)⁻¹ • a - u)) *
                    ((2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M) *
                      |g0 v h (a - y)|) := by ring
        _ = (chiSupAbs * chiSmall M ((ℓ * d)⁻¹ • a - u)) *
              (∫ y, (2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M) *
                |g0 v h (a - y)| ∂((volume : Measure ℝ³).restrict (acube ℓ))) := by
            rw [integral_const_mul]
    have houter : (∫ u : ℝ³, ‖∫ y in acube ℓ, wSmall1Pair h M ℓ d u a y‖)
        ≤ ∫ u : ℝ³, (chiSupAbs * chiSmall M ((ℓ * d)⁻¹ • a - u)) *
            (∫ y in acube ℓ, (2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M) *
              |g0 v h (a - y)|) := by
      refine integral_mono_of_nonneg (ae_of_all _ (fun u => norm_nonneg _)) ?_
        (ae_of_all _ hpt)
      exact ((Work.SmallBoxSliding.integrable_chiSmall_shift hM
        ((ℓ * d)⁻¹ • a)).const_mul chiSupAbs).mul_const _
    have hmid : (∫ u : ℝ³, (chiSupAbs * chiSmall M ((ℓ * d)⁻¹ • a - u)) *
            (∫ y in acube ℓ, (2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M) *
              |g0 v h (a - y)|))
        = (chiSupAbs * (∫ z : ℝ³, chiSmall M z)) *
          ((2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M) *
            (∫ y in acube ℓ, |g0 v h (a - y)|)) := by
      rw [integral_mul_const, integral_const_mul]
      rw [integral_const_mul]
      rw [integral_sub_left_eq_self (fun z : ℝ³ => chiSmall M z) volume ((ℓ * d)⁻¹ • a)]
    have hY' : (∫ y in acube ℓ, |g0 v h (a - y)|) ≤ (∫ z : ℝ³, |g0 v h z|) := by
      calc ∫ y in acube ℓ, |g0 v h (a - y)| ≤ ∫ y : ℝ³, |g0 v h (a - y)| :=
            setIntegral_le_integral hg0int (ae_of_all _ (fun y => abs_nonneg _))
        _ = ∫ z : ℝ³, |g0 v h z| :=
            integral_sub_left_eq_self (fun z : ℝ³ => |g0 v h z|) volume a
    have hK0 : 0 ≤ 2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M :=
      div_nonneg (mul_nonneg (by norm_num) (mul_nonneg chiSupAbs_nonneg (chiSmallDecay_nonneg M)))
        (le_of_lt (Work.SmallBoxSliding.smallConvLower_pos M))
    have hX0 : 0 ≤ (∫ z : ℝ³, chiSmall M z) := integral_nonneg (fun z => chiSmall_nonneg M z)
    calc ∫ u : ℝ³, ‖∫ y in acube ℓ, wSmall1Pair h M ℓ d u a y‖
        ≤ ∫ u : ℝ³, (chiSupAbs * chiSmall M ((ℓ * d)⁻¹ • a - u)) *
            (∫ y in acube ℓ, (2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M) *
              |g0 v h (a - y)|) := houter
      _ = (chiSupAbs * (∫ z : ℝ³, chiSmall M z)) *
          ((2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M) *
            (∫ y in acube ℓ, |g0 v h (a - y)|)) := hmid
      _ ≤ (chiSupAbs * (∫ z : ℝ³, chiSmall M z)) *
          ((2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M) *
            (∫ z : ℝ³, |g0 v h z|)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hY' hK0)
            (mul_nonneg chiSupAbs_nonneg hX0)
      _ = chiSupAbs * (2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M) *
            ((∫ z : ℝ³, chiSmall M z) * (∫ z : ℝ³, |g0 v h z|)) := by ring

end Work.UBBInputs2
