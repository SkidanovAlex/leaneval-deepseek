import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.ClassCHon.RgCSTarget
import Submission.Work.Coercivity.holder_two_mul
import Submission.Work.FTS.ClassCHon.WeightIntegrals.far_weight_integral_le
import Submission.Work.FTS.ClassCHon.RgL2Pointwise

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FTS/ClassCHon/Hcoef/far_cs` — the far-field Cauchy–Schwarz bound

For a source `c` with `∫_{t>0} (c t · w t)² < ∞` and `p > 3/2`, `a > 0`,

  `∫_{t>a} c t · t^{-p-1}` is absolutely convergent and
  `|∫_{t>a} c t · t^{-p-1}| ≤ B · a^{-p}/√(2p-3)`,  where `B ≥ √(∫_{t>0} (c t · w t)²)`.

The kernel is split against the weight `w(t) = (1+t)²/t²`:

  `c t · t^{-p-1} = (c t · w t) · (t^{-p-1}/w t)`,

so Cauchy–Schwarz (`Work.Coercivity.holder_two_mul`) reduces the claim to the source norm and the
explicit weight integral `∫_{t>a} t^{-2p-2}/w(t)² ≤ a^{-2p}/(2p-3)`
(`WeightIntegrals.far_weight_integral_le`).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.ClassCHon.Hcoef

local notation "w" => Work.Spaces.w

/-- The square of the far-field kernel factor, in the form consumed by
`WeightIntegrals.far_weight_integral_le`. -/
theorem far_cs_kernel_sq_eq {P t : ℝ} (ht : 0 < t) :
    (t ^ (-P - 1) / w t) ^ 2 = t ^ (-2 * P - 2) / (w t) ^ 2 := by
  rw [div_pow]
  congr 1
  rw [← Real.rpow_ofNat (t ^ (-P - 1)) 2, ← Real.rpow_mul ht.le]
  ring_nf

/-- Pointwise domination of the far-field kernel square by the pure power `t^{-2P+2}`. -/
theorem far_cs_kernel_sq_le {P t : ℝ} (ht : 0 < t) (hP : 3 / 2 < P) :
    (t ^ (-P - 1) / w t) ^ 2 ≤ t ^ (-2 * P + 2) := by
  rw [far_cs_kernel_sq_eq ht]
  exact Work.FTS.ClassCHon.far_div_w_sq_le_rpow ht hP

/-- Integrability of the squared far-field kernel factor on `(a,∞)`. -/
theorem far_cs_kernel_sq_integrable {P a : ℝ} (ha : 0 < a) (hP : 3 / 2 < P) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (t ^ (-P - 1) / w t) ^ 2) (Set.Ioi a) := by
  have hbase : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (-2 * P + 2)) (Set.Ioi a) :=
    integrableOn_Ioi_rpow_of_lt (by linarith : -2 * P + 2 < -1) ha
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => (t ^ (-P - 1) / w t) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi a)) := by
    have h0 : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => t ^ (-P - 1) / w t)
        (MeasureTheory.volume.restrict (Set.Ioi a)) :=
      (Work.FTS.ClassCHon.aestronglyMeasurable_div_w' (e := -P - 1)).mono_measure
        (Measure.restrict_mono (fun t ht => lt_trans ha ht) le_rfl)
    convert h0.mul h0 using 1
    funext t
    rw [Pi.mul_apply, pow_two]
  refine hbase.mono' hmeas ?_
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact far_cs_kernel_sq_le (lt_trans ha ht) hP

theorem far_cs {p B a : ℝ} (hp : 3 / 2 < p) (ha : 0 < a) {c : ℝ → ℝ}
    (hc : MeasureTheory.IntegrableOn (fun t : ℝ => (c t * Work.Spaces.w t) ^ 2) (Set.Ioi 0))
    (hcm : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => c t * Work.Spaces.w t)
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hB : Real.sqrt (∫ t in Set.Ioi (0 : ℝ), (c t * Work.Spaces.w t) ^ 2) ≤ B) :
    MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ (-p - 1)) (Set.Ioi a) ∧
      |∫ t in Set.Ioi a, c t * t ^ (-p - 1)|
        ≤ B * (a ^ (-p) / Real.sqrt (2 * p - 3)) := by
  have hsub : Set.Ioi a ⊆ Set.Ioi (0 : ℝ) := fun t ht => lt_trans ha ht
  -- the two `L²` factors, restricted to `(a,∞)`
  have hu : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => c t * w t)
      (MeasureTheory.volume.restrict (Set.Ioi a)) :=
    hcm.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hv : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => t ^ (-p - 1) / w t)
      (MeasureTheory.volume.restrict (Set.Ioi a)) :=
    (Work.FTS.ClassCHon.aestronglyMeasurable_div_w' (e := -p - 1)).mono_measure
      (Measure.restrict_mono hsub le_rfl)
  have hu2 : MeasureTheory.Integrable (fun t : ℝ => (c t * w t) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi a)) := hc.mono_set hsub
  have hv2 : MeasureTheory.Integrable (fun t : ℝ => (t ^ (-p - 1) / w t) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi a)) :=
    far_cs_kernel_sq_integrable ha hp
  obtain ⟨hint, hcs⟩ := Work.Coercivity.holder_two_mul
    (MeasureTheory.volume.restrict (Set.Ioi a))
    (fun t : ℝ => c t * w t) (fun t : ℝ => t ^ (-p - 1) / w t) hu hv hu2 hv2
  -- the pointwise identification of the product with the requested integrand
  have hae : (fun x : ℝ => (fun t : ℝ => c t * w t) x * (fun t : ℝ => t ^ (-p - 1) / w t) x)
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioi a)] (fun t : ℝ => c t * t ^ (-p - 1)) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
    have hw : w t ≠ 0 := ne_of_gt (Work.FTS.ClassCHon.w_pos_of_pos (lt_trans ha ht))
    field_simp
  have hprod : ∫ t in Set.Ioi a,
        (fun t : ℝ => c t * w t) t * (fun t : ℝ => t ^ (-p - 1) / w t) t
      = ∫ t in Set.Ioi a, c t * t ^ (-p - 1) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have hw : w t ≠ 0 := ne_of_gt (Work.FTS.ClassCHon.w_pos_of_pos (lt_trans ha ht))
    field_simp
  have hcs' : |∫ t in Set.Ioi a, c t * t ^ (-p - 1)|
      ≤ Real.sqrt (∫ t in Set.Ioi a, (c t * w t) ^ 2)
        * Real.sqrt (∫ t in Set.Ioi a, (t ^ (-p - 1) / w t) ^ 2) := by
    rw [← hprod]; exact hcs
  -- the weight integral and its square root
  have hker : ∫ t in Set.Ioi a, (t ^ (-p - 1) / w t) ^ 2 ≤ a ^ (-2 * p) / (2 * p - 3) := by
    rw [show (∫ t in Set.Ioi a, (t ^ (-p - 1) / w t) ^ 2)
        = ∫ t in Set.Ioi a, t ^ (-2 * p - 2) / (w t) ^ 2 from
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        (fun t ht => far_cs_kernel_sq_eq (lt_trans ha ht))]
    exact Work.FTS.ClassCHon.WeightIntegrals.far_weight_integral_le ha hp
  have hsq : Real.sqrt (∫ t in Set.Ioi a, (t ^ (-p - 1) / w t) ^ 2)
      ≤ a ^ (-p) / Real.sqrt (2 * p - 3) := by
    refine (Real.sqrt_le_sqrt hker).trans ?_
    rw [Real.sqrt_div (Real.rpow_nonneg ha.le _) (2 * p - 3),
      show a ^ (-2 * p) = (a ^ (-p)) ^ 2 by rw [sq, ← Real.rpow_add ha]; ring_nf,
      Real.sqrt_sq (Real.rpow_nonneg ha.le _)]
  -- the source norm is dominated by `B`
  have hmono : ∫ t in Set.Ioi a, (c t * w t) ^ 2 ≤ ∫ t in Set.Ioi (0 : ℝ), (c t * w t) ^ 2 :=
    MeasureTheory.setIntegral_mono_set hc (Eventually.of_forall fun t => sq_nonneg _)
      (Eventually.of_forall fun t ht => lt_trans ha ht)
  have hsq2 : Real.sqrt (∫ t in Set.Ioi a, (c t * w t) ^ 2) ≤ B :=
    (Real.sqrt_le_sqrt hmono).trans hB
  have hB0 : 0 ≤ B := (Real.sqrt_nonneg _).trans hsq2
  refine ⟨hint.congr hae, ?_⟩
  calc |∫ t in Set.Ioi a, c t * t ^ (-p - 1)|
      = |∫ t in Set.Ioi a,
          (fun t : ℝ => c t * w t) t * (fun t : ℝ => t ^ (-p - 1) / w t) t| := by rw [hprod]
    _ ≤ Real.sqrt (∫ t in Set.Ioi a, (c t * w t) ^ 2)
        * Real.sqrt (∫ t in Set.Ioi a, (t ^ (-p - 1) / w t) ^ 2) := hcs
    _ ≤ B * (a ^ (-p) / Real.sqrt (2 * p - 3)) :=
        mul_le_mul hsq2 hsq (Real.sqrt_nonneg _) hB0

end Work.FTS.ClassCHon.Hcoef
