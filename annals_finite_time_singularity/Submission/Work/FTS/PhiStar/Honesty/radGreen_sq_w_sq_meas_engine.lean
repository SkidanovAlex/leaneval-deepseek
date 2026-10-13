/-
# `Work.FTS.PhiStar.Honesty.radGreen_sq_w_sq_meas_engine`

Weighted `L²`-honesty of the mode-`m` radial Green function on `(0,∞)` under the *weak*
(a.e.-measurability only) hypotheses on the source `c`:

  `∫_0^∞ (radGreen α m c z)² · w(z)² dz < ∞`,   `w(z) = (1+z)²/z²`,

from a *near* `L²`-condition (`∫_0^1 c²/z⁴ < ∞`) and a *far* `L²`-condition (`∫_1^∞ c² < ∞`).
No pointwise decay and no continuity of `c` is assumed: `AEMeasurable c` suffices, because the
only role of regularity is to make the two primitives defining `radGreen` a.e. strongly
measurable (the Bochner integral of a non-integrable function is `0`, so the junk convention is
harmless), and that is supplied by the continuity of the branch `rgG1` and by the general
a.e.-strong-measurability of the tail primitive.

## Route

`radGreen α m c = rgK α m · (rgG1 α m c + rgG2 α m c)` (`rgG1 = z^{-q}∫_0^z c t^{q-1}`,
`rgG2 = z^{p}∫_z^∞ c t^{-p-1}`, `q = (2m+5)/α ≥ 28`, `p = 2m/α ≥ 8`), so

  `(rgG1 + rgG2)² ≤ 2 rgG1² + 2 rgG2²`   and   `w² ≤ 16/z⁴` on `(0,1)`, `w² ≤ 16` on `(1,∞)`.

The four weighted square-integrability statements for the two branches — the *already proved*
`rgG1_sq_div_z4_Ioo`, `rgG2_sq_div_z4_Ioo` (near field) and `rgG1_sq_Ioi`, `rgG2_sq_Ioi`
(far field) — then close both pieces by `Integrable.mono'`, and the two pieces are glued with
`(0,1) ∪ (1,∞) = (0,∞)` up to the null set `{1}` (`IntegrableOn.union`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllExist.RadGreenDefs
import Submission.Work.FTS.EllExist.Closers.aesm_tailPrim_Ioi
import Submission.Work.FTS.PhiStar.Honesty.rgG1_cont_Ioi
import Submission.Work.FTS.PhiStar.Honesty.rgG1_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.Honesty.rgG1_sq_Ioi
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_Ioi

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Work.FTS.PhiStar.Honesty

open Work.FTS.EllExist

/-- `radGreen` written in terms of the two named indicial branches (`radGreen_eq` followed by the
unfolding of `rgG1`, `rgG2`). -/
private lemma radGreen_eq_rgK_mul (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (z : ℝ) :
    Work.FTS.PhiStar.Radial.radGreen α m c z
      = rgK α m * (rgG1 α m c z + rgG2 α m c z) := by
  rw [radGreen_eq]
  simp only [rgG1, rgG2]

/-- The weight identity `(w z)² = (1+z)⁴/z⁴`. -/
private lemma w_sq_eq (z : ℝ) : (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 4 := by
  rw [Work.Spaces.w, div_pow]
  rw [show ((1 + z) ^ 2) ^ 2 = (1 + z) ^ 4 by ring, show (z ^ 2) ^ 2 = z ^ 4 by ring]

/-- `(1+z)⁴ ≤ 16` for `0 < z ≤ 1`. -/
private lemma one_add_pow_four_le {z : ℝ} (hz0 : 0 < z) (hz1 : z ≤ 1) : (1 + z) ^ 4 ≤ 16 := by
  have h0 : (0 : ℝ) ≤ 1 + z := by linarith
  have h1 : 1 + z ≤ 2 := by linarith
  calc (1 + z) ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ h0 h1 4
    _ = 16 := by norm_num

/-- `(1+z)⁴ ≤ 16 z⁴` for `1 ≤ z`. -/
private lemma one_add_pow_four_le_mul {z : ℝ} (hz1 : 1 ≤ z) : (1 + z) ^ 4 ≤ 16 * z ^ 4 := by
  have h0 : (0 : ℝ) ≤ 1 + z := by linarith
  have h1 : 1 + z ≤ 2 * z := by linarith
  calc (1 + z) ^ 4 ≤ (2 * z) ^ 4 := pow_le_pow_left₀ h0 h1 4
    _ = 16 * z ^ 4 := by ring

/-- `(a + b)² ≤ 2a² + 2b²`. -/
private lemma sq_add_le_two (a b : ℝ) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

theorem radGreen_sq_w_sq_meas_engine {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : AEMeasurable c)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioi 0) := by
  -- the four weighted square bounds for the two indicial branches
  have hG1n := rgG1_sq_div_z4_Ioo (α := α) (m := m) (c := c) hα hα4 hm hc hnear hfar
  have hG2n := rgG2_sq_div_z4_Ioo (α := α) (m := m) (c := c) hα hα4 hm hc hnear hfar
  have hG1f := rgG1_sq_Ioi (α := α) (m := m) (c := c) hα hα4 hm hc hnear hfar
  have hG2f := rgG2_sq_Ioi (α := α) (m := m) (c := c) hα hα4 hm hc hnear hfar
  -- continuity of the weight square on `(0,∞)`
  have hwcont : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
    have h : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
        = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := by
      funext z
      rw [Work.Spaces.w]
    rw [h]
    exact (((continuous_const.add continuous_id).pow 2).continuousOn.div
      ((continuous_id.pow 2).continuousOn)
      (fun z hz => pow_ne_zero 2 (ne_of_gt hz))).pow 2
  -- a.e. strong measurability of the two branches on `(0,∞)`
  have hG1meas : AEStronglyMeasurable (fun z : ℝ => rgG1 α m c z)
      (volume.restrict (Set.Ioi 0)) :=
    (rgG1_cont_Ioi (α := α) (m := m) (c := c) hα hα4 hm hc hnear hfar).aestronglyMeasurable
      measurableSet_Ioi
  have hG2meas : AEStronglyMeasurable (fun z : ℝ => rgG2 α m c z)
      (volume.restrict (Set.Ioi 0)) := by
    have htail : AEStronglyMeasurable (fun z : ℝ => ∫ t in Set.Ioi z, rgF2 α m c t)
        (volume.restrict (Set.Ioi 0)) :=
      Work.FTS.EllExist.Closers.aesm_tailPrim_Ioi (rgF2 α m c)
    have hpow : AEStronglyMeasurable (fun z : ℝ => z ^ (rgP α m))
        (volume.restrict (Set.Ioi 0)) :=
      (continuousOn_id.rpow_const (fun z hz => Or.inl (ne_of_gt hz))).aestronglyMeasurable
        measurableSet_Ioi
    simpa only [rgG2, rgB] using hpow.fun_mul htail
  have hradMeas : AEStronglyMeasurable (fun z : ℝ => Work.FTS.PhiStar.Radial.radGreen α m c z)
      (volume.restrict (Set.Ioi 0)) := by
    have h : AEStronglyMeasurable
        (fun z : ℝ => rgK α m * (rgG1 α m c z + rgG2 α m c z))
        (volume.restrict (Set.Ioi 0)) := (hG1meas.fun_add hG2meas).const_mul (rgK α m)
    refine h.congr ?_
    filter_upwards with z
    exact (radGreen_eq_rgK_mul α m c z).symm
  have htarget : AEStronglyMeasurable
      (fun z : ℝ => (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (volume.restrict (Set.Ioi 0)) :=
    (hradMeas.pow 2).fun_mul (hwcont.aestronglyMeasurable measurableSet_Ioi)
  -- ## the near piece `(0,1)`
  have hnear_int : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioo 0 1) := by
    have hdom : MeasureTheory.IntegrableOn
        (fun z : ℝ => 16 * (rgK α m) ^ 2 *
          (2 * ((rgG2 α m c z) ^ 2 / z ^ 4) + 2 * ((rgG1 α m c z) ^ 2 / z ^ 4)))
        (Set.Ioo 0 1) :=
      ((hG2n.const_mul 2).add (hG1n.const_mul 2)).const_mul (16 * (rgK α m) ^ 2)
    refine Integrable.mono' hdom ?_ ?_
    · have hw : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
          (volume.restrict (Set.Ioo 0 1)) :=
        (hwcont.mono (fun z hz => hz.1)).aestronglyMeasurable measurableSet_Ioo
      have hrad : AEStronglyMeasurable
          (fun z : ℝ => Work.FTS.PhiStar.Radial.radGreen α m c z)
          (volume.restrict (Set.Ioo 0 1)) :=
        hradMeas.mono_measure (Measure.restrict_mono Set.Ioo_subset_Ioi_self le_rfl)
      exact (hrad.pow 2).fun_mul hw
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
      have hz0 : (0 : ℝ) < z := hz.1
      have hz1 : z ≤ 1 := hz.2.le
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      have hwle : (Work.Spaces.w z) ^ 2 ≤ 16 / z ^ 4 := by
        rw [w_sq_eq z, div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < z ^ 4)]
        exact one_add_pow_four_le hz0 hz1
      have hsq := sq_add_le_two (rgG1 α m c z) (rgG2 α m c z)
      rw [radGreen_eq_rgK_mul α m c z]
      calc (rgK α m * (rgG1 α m c z + rgG2 α m c z)) ^ 2 * (Work.Spaces.w z) ^ 2
          = (rgK α m) ^ 2 * (rgG1 α m c z + rgG2 α m c z) ^ 2
              * (Work.Spaces.w z) ^ 2 := by ring
        _ ≤ (rgK α m) ^ 2 * (2 * (rgG1 α m c z) ^ 2 + 2 * (rgG2 α m c z) ^ 2)
              * (16 / z ^ 4) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hsq (sq_nonneg _)) hwle ?_ ?_
            · positivity
            · positivity
        _ = 16 * (rgK α m) ^ 2 * (2 * ((rgG2 α m c z) ^ 2 / z ^ 4)
              + 2 * ((rgG1 α m c z) ^ 2 / z ^ 4)) := by ring
  -- ## the far piece `(1,∞)`
  have hfar_int : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioi 1) := by
    have hdom : MeasureTheory.IntegrableOn
        (fun z : ℝ => 16 * (rgK α m) ^ 2 *
          (2 * (rgG2 α m c z) ^ 2 + 2 * (rgG1 α m c z) ^ 2)) (Set.Ioi 1) :=
      ((hG2f.const_mul 2).add (hG1f.const_mul 2)).const_mul (16 * (rgK α m) ^ 2)
    refine Integrable.mono' hdom ?_ ?_
    · have hsub : Set.Ioi (1 : ℝ) ⊆ Set.Ioi (0 : ℝ) := Set.Ioi_subset_Ioi (by norm_num)
      have hw : AEStronglyMeasurable (fun z : ℝ => (Work.Spaces.w z) ^ 2)
          (volume.restrict (Set.Ioi 1)) :=
        (hwcont.mono hsub).aestronglyMeasurable measurableSet_Ioi
      have hrad : AEStronglyMeasurable
          (fun z : ℝ => Work.FTS.PhiStar.Radial.radGreen α m c z)
          (volume.restrict (Set.Ioi 1)) :=
        hradMeas.mono_measure (Measure.restrict_mono hsub le_rfl)
      exact (hrad.pow 2).fun_mul hw
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      have hz1 : (1 : ℝ) ≤ z := hz.le
      have hz0 : (0 : ℝ) < z := lt_of_lt_of_le one_pos hz1
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      have hwle : (Work.Spaces.w z) ^ 2 ≤ 16 := by
        rw [w_sq_eq z, div_le_iff₀ (by positivity : (0 : ℝ) < z ^ 4)]
        exact one_add_pow_four_le_mul hz1
      have hsq := sq_add_le_two (rgG1 α m c z) (rgG2 α m c z)
      rw [radGreen_eq_rgK_mul α m c z]
      calc (rgK α m * (rgG1 α m c z + rgG2 α m c z)) ^ 2 * (Work.Spaces.w z) ^ 2
          = (rgK α m) ^ 2 * (rgG1 α m c z + rgG2 α m c z) ^ 2
              * (Work.Spaces.w z) ^ 2 := by ring
        _ ≤ (rgK α m) ^ 2 * (2 * (rgG1 α m c z) ^ 2 + 2 * (rgG2 α m c z) ^ 2) * 16 := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hsq (sq_nonneg _)) hwle ?_ ?_
            · positivity
            · positivity
        _ = 16 * (rgK α m) ^ 2 * (2 * (rgG2 α m c z) ^ 2
              + 2 * (rgG1 α m c z) ^ 2) := by ring
  -- ## glue `(0,1)` and `(1,∞)`
  have hA : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Icc (0 : ℝ) 1) :=
    hnear_int.congr_set_ae (MeasureTheory.Ioo_ae_eq_Icc).symm
  have hB : MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ici (1 : ℝ)) :=
    hfar_int.congr_set_ae (MeasureTheory.Ioi_ae_eq_Ici).symm
  have hU := hA.union hB
  have hset : Set.Icc (0 : ℝ) 1 ∪ Set.Ici (1 : ℝ) = Set.Ici (0 : ℝ) := by
    ext x
    simp only [Set.mem_union, Set.mem_Icc, Set.mem_Ici]
    constructor
    · rintro (⟨h1, _⟩ | h3) <;> linarith
    · intro h
      rcases le_or_gt x 1 with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr h'.le
  rw [hset] at hU
  exact hU.mono_set Set.Ioi_subset_Ici_self

end Work.FTS.PhiStar.Honesty
