import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.ClassCHon.RgL2Pointwise
import Submission.Work.FTS.ClassCHon.WeightIntegrals.near_weight_integral_le
import Submission.Work.FTS.ClassCHon.WeightIntegrals.far_weight_integral_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FTS/ClassCHon/RgCSTarget` — the Cauchy–Schwarz step of the `w²`-weighted Green bound

This is the `L²(w²)` step promised in `RgL2Pointwise.lean` (§3 of
`NOTES_EllNode7_session3.md`).  The kernel of `radGreen` is split against the weight `w`,

  `c t · t^{Q-1} = (c t · w t) · (t^{Q-1} / w t)`,

so that `Work.Coercivity.holder_two_mul` on `volume.restrict (Set.Ioc 0 z)` turns the near
integral into `√(∫ (c w)²) · √(∫ t^{2Q-2}/w²)`, and the second factor is controlled by the
(now proved) weight integral `WeightIntegrals.near_weight_integral_le`.  Retaining the
`1/(α(4m+5))` of `radGreen` and using `rgQ α m ≥ 8m` then gives the headline
`|radGreen α m c z| ≤ ‖c‖_{w²}/(4α m^{3/2})`.

The two *integrals* entering the statement (`∫_{Ioi 0}(c·w)²` and `∫_{Ioc 0 z}(t^{Q-1}/w)²`)
are hypotheses here; both are discharged in the intended application by the slicewise conjunct
of `HkMem` and by `near_pow_form` + boundedness on `Ioc 0 z` (see the note).  The measurability
of the kernel factor `t^{Q-1}/w t` is proved in this file (`aestronglyMeasurable_div_w`).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.ClassCHon

local notation "w" => Work.Spaces.w

/-- **Measurability of the kernel factor** `t^{Q-1}/w(t)` on `(0,∞)`.

`w t = (1+t)²/t²` is `ContinuousOn (Ioi 0)`, `t^{Q-1}` is continuous there for `Q > 1`, and the
denominator never vanishes on `(0,∞)` — so the quotient is `ContinuousOn (Ioi 0)`, hence a.e.
strongly measurable on the restricted measure.  (Note: this cannot be done with `Continuous.div`
on `ℝ`, where the denominator of the `(1+t)²/t²` form vanishes at `t = 0` and `t = -1`.) -/
theorem aestronglyMeasurable_div_w {Q : ℝ} (hQ : 1 < Q) :
    AEStronglyMeasurable (fun t : ℝ => t ^ (Q - 1) / w t) (volume.restrict (Set.Ioi 0)) := by
  have hfe : (fun t : ℝ => t ^ (Q - 1) / w t)
      = fun t : ℝ => t ^ (Q - 1) * t ^ 2 / (1 + t) ^ 2 := by
    funext t
    rw [Work.Spaces.w, div_eq_mul_inv, inv_div]
    ring
  rw [hfe]
  have hnum : ContinuousOn (fun t : ℝ => t ^ (Q - 1) * t ^ 2) (Set.Ioi 0) :=
    (continuousOn_id.rpow_const (fun t _ => Or.inr (by linarith))).mul (continuousOn_id.pow 2)
  have hden : ContinuousOn (fun t : ℝ => (1 + t) ^ 2) (Set.Ioi 0) :=
    (continuousOn_const.add continuousOn_id).pow 2
  exact (hnum.div hden (fun t ht => pow_ne_zero 2 (ne_of_gt (by have h1 : (0:ℝ) < t := ht; linarith)))).aestronglyMeasurable
    measurableSet_Ioi
local notation "rq" => Work.FTS.EllExist.rgQ
local notation "rp" => Work.FTS.EllExist.rgP

/-- The decaying branch of `radGreen` is `z^{-q}` times the interval integral of the kernel:
the unfolding needed before Cauchy–Schwarz.  (`rgF1 α m c t` is *definitionally*
`c t * t^{q-1}`, so `rfl` closes the last step; `rgF1` must **not** be `rw`-ed.) -/
theorem rgG1_eq {α : ℝ} {m : ℕ} {c : ℝ → ℝ} {z : ℝ} (hz : 0 < z) :
    Work.FTS.EllExist.rgG1 α m c z
      = z ^ (-(rq α m)) * ∫ t in Set.Ioc (0 : ℝ) z, c t * t ^ (rq α m - 1) := by
  rw [Work.FTS.EllExist.rgG1, Work.FTS.EllExist.rgA,
    intervalIntegral.integral_of_le hz.le]
  rfl

/-- The growing branch of `radGreen` (already a set integral). -/
theorem rgG2_eq {α : ℝ} {m : ℕ} {c : ℝ → ℝ} {z : ℝ} :
    Work.FTS.EllExist.rgG2 α m c z
      = z ^ (rp α m) * ∫ t in Set.Ioi z, c t * t ^ (-(rp α m) - 1) := by
  rw [Work.FTS.EllExist.rgG2, Work.FTS.EllExist.rgB]
  rfl

/-- **The Cauchy–Schwarz bound for the decaying branch of `radGreen`.**

For `Q = rgQ α m > 1`, `z > 0`, a source `c` with `(c·w)²` integrable and a.e. strongly
measurable on `(0,∞)`, and with `(t^{Q-1}/w t)²` integrable on `(0,z]`:

  `|z^{-Q} ∫_{(0,z]} c t^{Q-1}| ≤ ‖c·w‖_{L²(0,∞)} / √(2Q-1)`.

The integrability of the two `L²`-pieces is a hypothesis here; both are discharged in the
intended application (the slicewise conjunct of `HkMem` for the first, and
`near_pow_form` + boundedness on the bounded set `Ioc 0 z` for the second). -/
theorem rgG1_L2_le {α : ℝ} {m : ℕ} {c : ℝ → ℝ} {z : ℝ}
    (hc : IntegrableOn (fun t => (c t * w t) ^ 2) (Set.Ioi 0))
    (hcm : AEStronglyMeasurable (fun t => c t * w t) (volume.restrict (Set.Ioi 0)))
    (hv2 : IntegrableOn (fun t => (t ^ (rq α m - 1) / w t) ^ 2) (Set.Ioc 0 z))
    (hQ : 1 < rq α m) (hz : 0 < z) :
    |Work.FTS.EllExist.rgG1 α m c z| ≤
      Real.sqrt (∫ t in Set.Ioi 0, (c t * w t) ^ 2) / Real.sqrt (2 * rq α m - 1) := by
  have hsub : Set.Ioc (0 : ℝ) z ⊆ Set.Ioi 0 := fun t ht => ht.1
  have hQ1 : (0 : ℝ) < 2 * rq α m - 1 := by linarith
  -- the two Cauchy–Schwarz factors, restricted to `(0,z]`
  have huz : AEStronglyMeasurable (fun t => c t * w t) (volume.restrict (Set.Ioc 0 z)) :=
    hcm.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hvz : AEStronglyMeasurable (fun t => t ^ (rq α m - 1) / w t)
      (volume.restrict (Set.Ioc 0 z)) :=
    (aestronglyMeasurable_div_w hQ).mono_measure (Measure.restrict_mono hsub le_rfl)
  have hu2 : Integrable (fun t => (c t * w t) ^ 2) (volume.restrict (Set.Ioc 0 z)) :=
    hc.mono_set hsub
  obtain ⟨-, hcs⟩ := Work.Coercivity.holder_two_mul (volume.restrict (Set.Ioc 0 z))
    (fun t => c t * w t) (fun t => t ^ (rq α m - 1) / w t) huz hvz hu2 hv2
  -- `hprod` in the *redex* form produced by `holder_two_mul`, so that `← hprod` fires
  have hprod : ∫ t in Set.Ioc (0 : ℝ) z,
        (fun t => c t * w t) t * (fun t => t ^ (rq α m - 1) / w t) t
      = ∫ t in Set.Ioc (0 : ℝ) z, c t * t ^ (rq α m - 1) := by
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have hwt : w t ≠ 0 := ne_of_gt (w_pos_of_pos ht.1)
    field_simp
  have hcs' : |∫ t in Set.Ioc (0 : ℝ) z, c t * t ^ (rq α m - 1)|
      ≤ Real.sqrt (∫ t in Set.Ioc (0 : ℝ) z, (c t * w t) ^ 2)
        * Real.sqrt (∫ t in Set.Ioc (0 : ℝ) z, (t ^ (rq α m - 1) / w t) ^ 2) := by
    rw [← hprod]; exact hcs
  -- the kernel mass, and its square-root form
  have hker : ∫ t in Set.Ioc (0 : ℝ) z, (t ^ (rq α m - 1) / w t) ^ 2
      ≤ z ^ (2 * rq α m) / (2 * rq α m - 1) := by
    rw [show (∫ t in Set.Ioc (0 : ℝ) z, (t ^ (rq α m - 1) / w t) ^ 2)
        = ∫ t in Set.Ioc (0 : ℝ) z, t ^ (2 * rq α m - 2) / (w t) ^ 2 from
      setIntegral_congr_fun measurableSet_Ioc fun t ht => by
        have ht0 : 0 < t := ht.1
        have h1 : (t ^ (rq α m - 1)) ^ 2 = t ^ (2 * rq α m - 2) := by
          rw [← Real.rpow_ofNat (t ^ (rq α m - 1)) 2,
            ← Real.rpow_mul ht0.le (rq α m - 1) 2]
          ring_nf
        rw [div_pow, h1]]
    exact WeightIntegrals.near_weight_integral_le hz hQ
  have hsq : Real.sqrt (∫ t in Set.Ioc (0 : ℝ) z, (t ^ (rq α m - 1) / w t) ^ 2)
      ≤ z ^ (rq α m) / Real.sqrt (2 * rq α m - 1) := by
    refine (Real.sqrt_le_sqrt hker).trans ?_
    rw [Real.sqrt_div (Real.rpow_nonneg hz.le _) (2 * rq α m - 1),
      show z ^ (2 * rq α m) = (z ^ (rq α m)) ^ 2 by rw [sq, ← Real.rpow_add hz]; ring_nf,
      Real.sqrt_sq (Real.rpow_nonneg hz.le _)]
  have hXnn : (0 : ℝ) ≤ z ^ (rq α m) / Real.sqrt (2 * rq α m - 1) :=
    div_nonneg (Real.rpow_nonneg hz.le _) (Real.sqrt_nonneg _)
  have hmono : ∫ t in Set.Ioc (0 : ℝ) z, (c t * w t) ^ 2
      ≤ ∫ t in Set.Ioi 0, (c t * w t) ^ 2 :=
    setIntegral_mono_set hc (Filter.Eventually.of_forall fun t => sq_nonneg _)
      (Filter.Eventually.of_forall fun t ht => ht.1)
  have hsq2 : Real.sqrt (∫ t in Set.Ioc (0 : ℝ) z, (c t * w t) ^ 2)
      ≤ Real.sqrt (∫ t in Set.Ioi 0, (c t * w t) ^ 2) := Real.sqrt_le_sqrt hmono
  -- assemble
  have hzQ : (0 : ℝ) < z ^ (-(rq α m)) := Real.rpow_pos_of_pos hz _
  have hzQmul : z ^ (-(rq α m)) * z ^ (rq α m) = 1 := by
    rw [← Real.rpow_add hz, neg_add_cancel, Real.rpow_zero]
  rw [rgG1_eq (α := α) (m := m) (c := c) hz, abs_mul, abs_of_pos hzQ]
  calc z ^ (-(rq α m)) * |∫ t in Set.Ioc (0 : ℝ) z, c t * t ^ (rq α m - 1)|
      ≤ z ^ (-(rq α m)) * (Real.sqrt (∫ t in Set.Ioc (0 : ℝ) z, (c t * w t) ^ 2)
          * (z ^ (rq α m) / Real.sqrt (2 * rq α m - 1))) := by
        refine mul_le_mul_of_nonneg_left ?_ hzQ.le
        exact hcs'.trans (mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _))
    _ ≤ z ^ (-(rq α m)) * (Real.sqrt (∫ t in Set.Ioi 0, (c t * w t) ^ 2)
          * (z ^ (rq α m) / Real.sqrt (2 * rq α m - 1))) := by
        refine mul_le_mul_of_nonneg_left ?_ hzQ.le
        exact mul_le_mul_of_nonneg_right hsq2 hXnn
    _ = Real.sqrt (∫ t in Set.Ioi 0, (c t * w t) ^ 2) / Real.sqrt (2 * rq α m - 1) := by
        rw [show z ^ (-(rq α m)) * (Real.sqrt (∫ t in Set.Ioi 0, (c t * w t) ^ 2)
              * (z ^ (rq α m) / Real.sqrt (2 * rq α m - 1)))
            = (z ^ (-(rq α m)) * z ^ (rq α m))
              * (Real.sqrt (∫ t in Set.Ioi 0, (c t * w t) ^ 2) / Real.sqrt (2 * rq α m - 1))
            from by ring, hzQmul, one_mul]

/-- **Measurability of the kernel factor** `t^{e}/w(t)` on `(0,∞)`, for an *arbitrary* real
exponent `e` (the far branch of `radGreen` uses the negative exponent `-p-1`). -/
theorem aestronglyMeasurable_div_w' {e : ℝ} :
    AEStronglyMeasurable (fun t : ℝ => t ^ e / w t) (volume.restrict (Set.Ioi 0)) := by
  have hfe : (fun t : ℝ => t ^ e / w t)
      = fun t : ℝ => t ^ e * t ^ 2 / (1 + t) ^ 2 := by
    funext t
    rw [Work.Spaces.w, div_eq_mul_inv, inv_div]
    ring
  rw [hfe]
  have hnum : ContinuousOn (fun t : ℝ => t ^ e * t ^ 2) (Set.Ioi 0) :=
    (continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht))).mul (continuousOn_id.pow 2)
  have hden : ContinuousOn (fun t : ℝ => (1 + t) ^ 2) (Set.Ioi 0) :=
    (continuousOn_const.add continuousOn_id).pow 2
  exact (hnum.div hden (fun t ht => pow_ne_zero 2 (ne_of_gt (by have h1 : (0:ℝ) < t := ht; linarith)))).aestronglyMeasurable
    measurableSet_Ioi

/-- **The Cauchy–Schwarz bound for the growing branch of `radGreen`** (the mirror of
`rgG1_L2_le`, with the far weight integral `far_weight_integral_le`).

For `P = rgP α m > 3/2`, `z > 0`, `(c·w)²` integrable and a.e. strongly measurable on `(0,∞)`,
and `(t^{-P-1}/w t)²` integrable on `(z,∞)`:

  `|z^{P} ∫_{(z,∞)} c t^{-P-1}| ≤ ‖c·w‖_{L²(0,∞)} / √(2P-3)`. -/
theorem rgG2_L2_le {α : ℝ} {m : ℕ} {c : ℝ → ℝ} {z : ℝ}
    (hc : IntegrableOn (fun t => (c t * w t) ^ 2) (Set.Ioi 0))
    (hcm : AEStronglyMeasurable (fun t => c t * w t) (volume.restrict (Set.Ioi 0)))
    (hv2 : IntegrableOn (fun t => (t ^ (-(rp α m) - 1) / w t) ^ 2) (Set.Ioi z))
    (hP : 3 / 2 < rp α m) (hz : 0 < z) :
    |Work.FTS.EllExist.rgG2 α m c z| ≤
      Real.sqrt (∫ t in Set.Ioi 0, (c t * w t) ^ 2) / Real.sqrt (2 * rp α m - 3) := by
  have hsub : Set.Ioi z ⊆ Set.Ioi 0 := fun t ht => lt_trans hz ht
  have hP1 : (0 : ℝ) < 2 * rp α m - 3 := by linarith
  have huz : AEStronglyMeasurable (fun t => c t * w t) (volume.restrict (Set.Ioi z)) :=
    hcm.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hvz : AEStronglyMeasurable (fun t => t ^ (-(rp α m) - 1) / w t)
      (volume.restrict (Set.Ioi z)) :=
    (aestronglyMeasurable_div_w' (e := -(rp α m) - 1)).mono_measure
      (Measure.restrict_mono hsub le_rfl)
  have hu2 : Integrable (fun t => (c t * w t) ^ 2) (volume.restrict (Set.Ioi z)) :=
    hc.mono_set hsub
  obtain ⟨-, hcs⟩ := Work.Coercivity.holder_two_mul (volume.restrict (Set.Ioi z))
    (fun t => c t * w t) (fun t => t ^ (-(rp α m) - 1) / w t) huz hvz hu2 hv2
  -- `hprod` in the redex form emitted by `holder_two_mul`
  have hprod : ∫ t in Set.Ioi z,
        (fun t => c t * w t) t * (fun t => t ^ (-(rp α m) - 1) / w t) t
      = ∫ t in Set.Ioi z, c t * t ^ (-(rp α m) - 1) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have hwt : w t ≠ 0 := ne_of_gt (w_pos_of_pos (lt_trans hz ht))
    field_simp
  have hcs' : |∫ t in Set.Ioi z, c t * t ^ (-(rp α m) - 1)|
      ≤ Real.sqrt (∫ t in Set.Ioi z, (c t * w t) ^ 2)
        * Real.sqrt (∫ t in Set.Ioi z, (t ^ (-(rp α m) - 1) / w t) ^ 2) := by
    rw [← hprod]; exact hcs
  have hker : ∫ t in Set.Ioi z, (t ^ (-(rp α m) - 1) / w t) ^ 2
      ≤ z ^ (-2 * rp α m) / (2 * rp α m - 3) := by
    rw [show (∫ t in Set.Ioi z, (t ^ (-(rp α m) - 1) / w t) ^ 2)
        = ∫ t in Set.Ioi z, t ^ (-2 * rp α m - 2) / (w t) ^ 2 from
      setIntegral_congr_fun measurableSet_Ioi fun t ht => by
        have ht0 : 0 < t := lt_trans hz ht
        have h1 : (t ^ (-(rp α m) - 1)) ^ 2 = t ^ (-2 * rp α m - 2) := by
          rw [← Real.rpow_ofNat (t ^ (-(rp α m) - 1)) 2,
            ← Real.rpow_mul ht0.le (-(rp α m) - 1) 2]
          ring_nf
        rw [div_pow, h1]]
    exact WeightIntegrals.far_weight_integral_le hz hP
  have hsq : Real.sqrt (∫ t in Set.Ioi z, (t ^ (-(rp α m) - 1) / w t) ^ 2)
      ≤ z ^ (-(rp α m)) / Real.sqrt (2 * rp α m - 3) := by
    refine (Real.sqrt_le_sqrt hker).trans ?_
    rw [Real.sqrt_div (Real.rpow_nonneg hz.le _) (2 * rp α m - 3),
      show z ^ (-2 * rp α m) = (z ^ (-(rp α m))) ^ 2 by rw [sq, ← Real.rpow_add hz]; ring_nf,
      Real.sqrt_sq (Real.rpow_nonneg hz.le _)]
  have hXnn : (0 : ℝ) ≤ z ^ (-(rp α m)) / Real.sqrt (2 * rp α m - 3) :=
    div_nonneg (Real.rpow_nonneg hz.le _) (Real.sqrt_nonneg _)
  have hmono : ∫ t in Set.Ioi z, (c t * w t) ^ 2 ≤ ∫ t in Set.Ioi 0, (c t * w t) ^ 2 :=
    setIntegral_mono_set hc (Filter.Eventually.of_forall fun t => sq_nonneg _)
      (Filter.Eventually.of_forall fun t ht => lt_trans hz ht)
  have hsq2 : Real.sqrt (∫ t in Set.Ioi z, (c t * w t) ^ 2)
      ≤ Real.sqrt (∫ t in Set.Ioi 0, (c t * w t) ^ 2) := Real.sqrt_le_sqrt hmono
  have hzP : (0 : ℝ) < z ^ (rp α m) := Real.rpow_pos_of_pos hz _
  have hzPmul : z ^ (rp α m) * z ^ (-(rp α m)) = 1 := by
    rw [← Real.rpow_add hz, add_neg_cancel, Real.rpow_zero]
  rw [rgG2_eq (α := α) (m := m) (c := c), abs_mul, abs_of_pos hzP]
  calc z ^ (rp α m) * |∫ t in Set.Ioi z, c t * t ^ (-(rp α m) - 1)|
      ≤ z ^ (rp α m) * (Real.sqrt (∫ t in Set.Ioi z, (c t * w t) ^ 2)
          * (z ^ (-(rp α m)) / Real.sqrt (2 * rp α m - 3))) := by
        refine mul_le_mul_of_nonneg_left ?_ hzP.le
        exact hcs'.trans (mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _))
    _ ≤ z ^ (rp α m) * (Real.sqrt (∫ t in Set.Ioi 0, (c t * w t) ^ 2)
          * (z ^ (-(rp α m)) / Real.sqrt (2 * rp α m - 3))) := by
        refine mul_le_mul_of_nonneg_left ?_ hzP.le
        exact mul_le_mul_of_nonneg_right hsq2 hXnn
    _ = Real.sqrt (∫ t in Set.Ioi 0, (c t * w t) ^ 2) / Real.sqrt (2 * rp α m - 3) := by
        rw [show z ^ (rp α m) * (Real.sqrt (∫ t in Set.Ioi 0, (c t * w t) ^ 2)
              * (z ^ (-(rp α m)) / Real.sqrt (2 * rp α m - 3)))
            = (z ^ (rp α m) * z ^ (-(rp α m)))
              * (Real.sqrt (∫ t in Set.Ioi 0, (c t * w t) ^ 2) / Real.sqrt (2 * rp α m - 3))
            from by ring, hzPmul, one_mul]

/-- **The `w²`-weighted pointwise bound for `radGreen`** (the pointwise input of the modal
route for the node's solution): assembling the two branch bounds with
`radGreen = rgK·(rgG1 + rgG2)`.

  `|radGreen α m c z| ≤ rgK α m · ( √(∫(c·w)²)/√(2·rgQ α m − 1)
                                   + √(∫(c·w)²)/√(2·rgP α m − 3) )`. -/
theorem radGreen_L2_le {α : ℝ} (hα : 0 < α) {m : ℕ} {c : ℝ → ℝ} {z : ℝ}
    (hc : IntegrableOn (fun t => (c t * w t) ^ 2) (Set.Ioi 0))
    (hcm : AEStronglyMeasurable (fun t => c t * w t) (volume.restrict (Set.Ioi 0)))
    (hv1 : IntegrableOn (fun t => (t ^ (rq α m - 1) / w t) ^ 2) (Set.Ioc 0 z))
    (hv2 : IntegrableOn (fun t => (t ^ (-(rp α m) - 1) / w t) ^ 2) (Set.Ioi z))
    (hQ : 1 < rq α m) (hP : 3 / 2 < rp α m) (hz : 0 < z) :
    |Work.FTS.PhiStar.Radial.radGreen α m c z| ≤
      Work.FTS.EllExist.rgK α m *
        (Real.sqrt (∫ t in Set.Ioi 0, (c t * w t) ^ 2) / Real.sqrt (2 * rq α m - 1)
          + Real.sqrt (∫ t in Set.Ioi 0, (c t * w t) ^ 2) / Real.sqrt (2 * rp α m - 3)) := by
  have h1 := rgG1_L2_le (α := α) (m := m) (c := c) (z := z) hc hcm hv1 hQ hz
  have h2 := rgG2_L2_le (α := α) (m := m) (c := c) (z := z) hc hcm hv2 hP hz
  have hK : (0 : ℝ) < Work.FTS.EllExist.rgK α m := Work.FTS.EllExist.rgK_pos hα m
  rw [Work.FTS.EllExist.radGreen_eq α m c z]
  calc |Work.FTS.EllExist.rgK α m *
        (Work.FTS.EllExist.rgG1 α m c z + Work.FTS.EllExist.rgG2 α m c z)|
      = Work.FTS.EllExist.rgK α m *
        |Work.FTS.EllExist.rgG1 α m c z + Work.FTS.EllExist.rgG2 α m c z| := by
        rw [abs_mul, abs_of_pos hK]
    _ ≤ Work.FTS.EllExist.rgK α m *
        (|Work.FTS.EllExist.rgG1 α m c z| + |Work.FTS.EllExist.rgG2 α m c z|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) hK.le
    _ ≤ Work.FTS.EllExist.rgK α m *
        (Real.sqrt (∫ t in Set.Ioi 0, (c t * w t) ^ 2) / Real.sqrt (2 * rq α m - 1)
          + Real.sqrt (∫ t in Set.Ioi 0, (c t * w t) ^ 2) / Real.sqrt (2 * rp α m - 3)) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) hK.le

end Work.FTS.ClassCHon
