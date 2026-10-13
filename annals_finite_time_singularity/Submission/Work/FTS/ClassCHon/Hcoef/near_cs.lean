import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.ClassCHon.RgCSTarget
import Submission.Work.Coercivity.holder_two_mul
import Submission.Work.FTS.ClassCHon.WeightIntegrals.near_weight_integral_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FTS/ClassCHon/Hcoef/near_cs` — the near (small `t`) Cauchy–Schwarz coefficient bound

For a source `c` whose `w`-weighted square `(c·w)²` is integrable on `(0,∞)` with
`√(∫_{(0,∞)} (c·w)²) ≤ B`, the "near" kernel `t ↦ c t · t^{q-1}` is integrable on `(0,a]` and

  `|∫_{(0,a]} c t · t^{q-1}| ≤ B · a^q / √(2q-1)`   (`q > 1`, `a > 0`).

This is the pointwise coefficient bound used by the `ℋ^k`-membership argument for the
class-`C^α` datum: the mode coefficients are exactly of this shape (`HkMemOuter`/`Hcoef`),
with `B = ‖c‖_{w²}`.

The proof is Cauchy–Schwarz on `(0,a]` against the weight `w(t) = (1+t)²/t²`:
`c t · t^{q-1} = (c t · w t) · (t^{q-1}/w t)`, so

  `|∫_{(0,a]} c t t^{q-1}| ≤ √(∫_{(0,a]}(c·w)²) · √(∫_{(0,a]} t^{2q-2}/w²)`

and the second factor is `≤ a^q/√(2q-1)` by `WeightIntegrals.near_weight_integral_le`
(the elementary weight identity `t^{2Q-2}/w² = t^{2Q+2}/(1+t)⁴ ≤ (2Q/(2Q-1))·t^{2Q-1}`).
The reduction of the statement to the `L²`-pair is `Work.Coercivity.holder_two_mul`.
-/

namespace Work.FTS.ClassCHon.Hcoef

open MeasureTheory Set

/-- **Integrability of the near kernel.**  For `Q > 1` and `z > 0` the function
`t ↦ (t^{Q-1}/w(t))²` is integrable on `(0,z]`.

By `near_div_w_sq_le_self` it is dominated pointwise (on `t > 0`) by `t^{2Q-2}`, which is
integrable on `(0,z]` because `2Q - 2 > -1`. -/
theorem integrableOn_div_w_sq {Q z : ℝ} (hz : 0 < z) (hQ : 1 < Q) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (t ^ (Q - 1) / Work.Spaces.w t) ^ 2)
      (Set.Ioc 0 z) := by
  have hsub : Set.Ioc (0 : ℝ) z ⊆ Set.Ioi 0 := fun t ht => ht.1
  have hbase : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (2 * Q - 2)) (Set.Ioc 0 z) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hz.le).mp
      (intervalIntegral.intervalIntegrable_rpow' (r := 2 * Q - 2) (by linarith))
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => (t ^ (Q - 1) / Work.Spaces.w t) ^ 2) (volume.restrict (Set.Ioc 0 z)) :=
    ((Work.FTS.ClassCHon.aestronglyMeasurable_div_w hQ).mono_measure
      (Measure.restrict_mono hsub le_rfl)).pow 2
  refine hbase.mono' hmeas ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
  have ht0 : 0 < t := ht.1
  have h1 : (t ^ (Q - 1)) ^ 2 = t ^ (2 * Q - 2) := by
    rw [← Real.rpow_ofNat (t ^ (Q - 1)) 2, ← Real.rpow_mul ht0.le (Q - 1) 2]
    ring_nf
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), div_pow, h1]
  exact Work.FTS.ClassCHon.near_div_w_sq_le_self ht0 hQ

theorem near_cs {q B a : ℝ} (hq : 1 < q) (ha : 0 < a) {c : ℝ → ℝ}
    (hc : MeasureTheory.IntegrableOn (fun t : ℝ => (c t * Work.Spaces.w t) ^ 2) (Set.Ioi 0))
    (hcm : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => c t * Work.Spaces.w t)
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hB : Real.sqrt (∫ t in Set.Ioi (0 : ℝ), (c t * Work.Spaces.w t) ^ 2) ≤ B) :
    MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ (q - 1)) (Set.Ioc 0 a) ∧
      |∫ t in Set.Ioc (0 : ℝ) a, c t * t ^ (q - 1)|
        ≤ B * (a ^ q / Real.sqrt (2 * q - 1)) := by
  have hsub : Set.Ioc (0 : ℝ) a ⊆ Set.Ioi 0 := fun t ht => ht.1
  -- the two Cauchy–Schwarz factors, restricted to `(0,a]`
  have huz : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => c t * Work.Spaces.w t)
      (volume.restrict (Set.Ioc 0 a)) :=
    hcm.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hvz : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => t ^ (q - 1) / Work.Spaces.w t)
      (volume.restrict (Set.Ioc 0 a)) :=
    (Work.FTS.ClassCHon.aestronglyMeasurable_div_w hq).mono_measure
      (Measure.restrict_mono hsub le_rfl)
  have hu2 : MeasureTheory.Integrable (fun t : ℝ => (c t * Work.Spaces.w t) ^ 2)
      (volume.restrict (Set.Ioc 0 a)) := hc.mono_set hsub
  have hv2 : MeasureTheory.Integrable (fun t : ℝ => (t ^ (q - 1) / Work.Spaces.w t) ^ 2)
      (volume.restrict (Set.Ioc 0 a)) := integrableOn_div_w_sq ha hq
  obtain ⟨hUVint, hcs⟩ := Work.Coercivity.holder_two_mul (volume.restrict (Set.Ioc 0 a))
    (fun t : ℝ => c t * Work.Spaces.w t) (fun t : ℝ => t ^ (q - 1) / Work.Spaces.w t)
    huz hvz hu2 hv2
  -- the product is the near kernel, on `(0,a]` where `w ≠ 0`
  have hpt : ∀ t ∈ Set.Ioc (0 : ℝ) a,
      (fun t : ℝ => c t * Work.Spaces.w t) t * (fun t : ℝ => t ^ (q - 1) / Work.Spaces.w t) t
        = c t * t ^ (q - 1) := by
    intro t ht
    have hwt : Work.Spaces.w t ≠ 0 := ne_of_gt (Work.FTS.ClassCHon.w_pos_of_pos ht.1)
    field_simp
  have hprod : ∫ t in Set.Ioc (0 : ℝ) a,
        (fun t : ℝ => c t * Work.Spaces.w t) t * (fun t : ℝ => t ^ (q - 1) / Work.Spaces.w t) t
      = ∫ t in Set.Ioc (0 : ℝ) a, c t * t ^ (q - 1) :=
    setIntegral_congr_fun measurableSet_Ioc hpt
  -- the weight integral
  have hker : ∫ t in Set.Ioc (0 : ℝ) a, (t ^ (q - 1) / Work.Spaces.w t) ^ 2
      ≤ a ^ (2 * q) / (2 * q - 1) := by
    rw [show (∫ t in Set.Ioc (0 : ℝ) a, (t ^ (q - 1) / Work.Spaces.w t) ^ 2)
        = ∫ t in Set.Ioc (0 : ℝ) a, t ^ (2 * q - 2) / (Work.Spaces.w t) ^ 2 from
      setIntegral_congr_fun measurableSet_Ioc fun t ht => by
        have ht0 : 0 < t := ht.1
        have h1 : (t ^ (q - 1)) ^ 2 = t ^ (2 * q - 2) := by
          rw [← Real.rpow_ofNat (t ^ (q - 1)) 2, ← Real.rpow_mul ht0.le (q - 1) 2]
          ring_nf
        rw [div_pow, h1]]
    exact Work.FTS.ClassCHon.WeightIntegrals.near_weight_integral_le ha hq
  have hsqV : Real.sqrt (∫ t in Set.Ioc (0 : ℝ) a, (t ^ (q - 1) / Work.Spaces.w t) ^ 2)
      ≤ a ^ q / Real.sqrt (2 * q - 1) := by
    refine (Real.sqrt_le_sqrt hker).trans ?_
    rw [Real.sqrt_div (x := a ^ (2 * q)) (Real.rpow_nonneg ha.le _) (2 * q - 1),
      show a ^ (2 * q) = (a ^ q) ^ 2 by rw [sq, ← Real.rpow_add ha]; ring_nf,
      Real.sqrt_sq (Real.rpow_nonneg ha.le q)]
  -- the source `L²`-norm, on `(0,a]` and on `(0,∞)`
  have hmono : ∫ t in Set.Ioc (0 : ℝ) a, (c t * Work.Spaces.w t) ^ 2
      ≤ ∫ t in Set.Ioi 0, (c t * Work.Spaces.w t) ^ 2 :=
    setIntegral_mono_set hc (Filter.Eventually.of_forall fun t => sq_nonneg _)
      (Filter.Eventually.of_forall fun t ht => ht.1)
  have hsqU : Real.sqrt (∫ t in Set.Ioc (0 : ℝ) a, (c t * Work.Spaces.w t) ^ 2) ≤ B :=
    (Real.sqrt_le_sqrt hmono).trans hB
  refine ⟨?_, ?_⟩
  · exact hUVint.congr (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
      exact hpt t ht)
  · have hcs' : |∫ t in Set.Ioc (0 : ℝ) a, c t * t ^ (q - 1)|
        ≤ Real.sqrt (∫ t in Set.Ioc (0 : ℝ) a, (c t * Work.Spaces.w t) ^ 2)
          * Real.sqrt (∫ t in Set.Ioc (0 : ℝ) a, (t ^ (q - 1) / Work.Spaces.w t) ^ 2) := by
      rw [← hprod]; exact hcs
    have hBnn : (0 : ℝ) ≤ B := le_trans (Real.sqrt_nonneg _) hB
    exact hcs'.trans (mul_le_mul hsqU hsqV (Real.sqrt_nonneg _) hBnn)

end Work.FTS.ClassCHon.Hcoef
