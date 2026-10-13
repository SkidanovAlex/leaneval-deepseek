import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.ClassCHon.RgCSTarget
import Submission.Work.FTS.ClassCHon.WeightIntegrals.near_weight_integral_le
import Submission.Work.FTS.ClassCHon.WeightIntegrals.far_weight_integral_le
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.EllExist.RadGreenDefs
import Submission.Work.FTS.ClassCHon.Hcoef.near_cs
import Submission.Work.FTS.ClassCHon.Hcoef.far_cs
import Submission.Work.FTS.ClassCHon.Hcoef.near_inner
import Submission.Work.FTS.ClassCHon.Hcoef.far_inner

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.Hcoef

open MeasureTheory Set Filter
open scoped Real Topology

local notation "rq" => Work.FTS.EllExist.rgQ
local notation "rp" => Work.FTS.EllExist.rgP
local notation "rK" => Work.FTS.EllExist.rgK
local notation "w" => Work.Spaces.w

/-- The weight `w` is continuous on `(0,∞)` (`w t = (1+t)²/t²` has a pole at `0`). -/
private lemma w_contOn : ContinuousOn w (Set.Ioi (0:ℝ)) := by
  have hfun : (w : ℝ → ℝ) = fun t => (1 + t)^2 / t^2 := rfl
  rw [hfun]
  refine ContinuousOn.div ?_ ?_ ?_
  · fun_prop
  · fun_prop
  · intro t ht; exact pow_ne_zero 2 (ne_of_gt ht)

/-- A function whose product with `w` is a.e. strongly measurable on `(0,∞)` is itself a.e.
strongly measurable on `(a,b] ⊂ (0,∞)` (`w` does not vanish there, so one may divide). -/
private lemma aesm_c_of_aesm_mul_w {c : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hcm : AEStronglyMeasurable (fun t => c t * w t) (volume.restrict (Set.Ioi 0))) :
    AEStronglyMeasurable c (volume.restrict (Set.Ioc a b)) := by
  have hsub : Set.Ioc a b ⊆ Set.Ioi (0:ℝ) := fun t ht => lt_trans ha ht.1
  have h1 : AEStronglyMeasurable (fun t => c t * w t) (volume.restrict (Set.Ioc a b)) :=
    hcm.mono_measure (MeasureTheory.Measure.restrict_mono hsub le_rfl)
  have h2 : AEStronglyMeasurable (fun t : ℝ => w t) (volume.restrict (Set.Ioc a b)) :=
    (w_contOn.mono hsub).aestronglyMeasurable measurableSet_Ioc
  refine (h1.div₀ h2).congr ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
  have ht0 : 0 < t := lt_trans ha ht.1
  have hwt : w t ≠ 0 := by
    have hw : (w t) = (1 + t)^2 / t^2 := rfl
    rw [hw]
    exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 (ne_of_gt ht0))
  simp only [Pi.div_apply]
  rw [mul_div_assoc, div_self hwt, mul_one]

/-- `z^{-q}·(z/2)^q = 2^{-q}` for `z > 0`: the scaling identity converting the near-field
Cauchy–Schwarz bound at the half point `z/2` into a bound at `z`. -/
private lemma rpow_neg_mul_half {q z : ℝ} (hz : 0 < z) :
    z ^ (-q) * (z / 2) ^ q = (2:ℝ) ^ (-q) := by
  have h2 : (0:ℝ) ≤ 2 := by norm_num
  have hinv : (1/2 : ℝ) ^ q = (2:ℝ) ^ (-q) := by
    rw [show (1/2 : ℝ) = (2:ℝ)⁻¹ by norm_num, Real.inv_rpow h2, ← Real.rpow_neg h2 q]
  calc z ^ (-q) * (z / 2) ^ q
      = z ^ (-q) * (z ^ q * (1/2:ℝ) ^ q) := by
        rw [show z / 2 = z * (1/2 : ℝ) by ring,
          Real.mul_rpow hz.le (by norm_num : (0:ℝ) ≤ (1/2:ℝ))]
    _ = (z ^ (-q) * z ^ q) * (1/2:ℝ)^q := by ring
    _ = z ^ (-q + q) * (1/2:ℝ)^q := by rw [Real.rpow_add hz]
    _ = (2:ℝ)^(-q) := by rw [hinv, neg_add_cancel, Real.rpow_zero, one_mul]

/-- `z^p·(2z)^{-p} = 2^{-p}` for `z > 0`: the mirror of `rpow_neg_mul_half`, converting the
far-field Cauchy–Schwarz bound at `2z` into a bound at `z`. -/
private lemma rpow_mul_two_neg {p z : ℝ} (hz : 0 < z) :
    z ^ p * (2 * z) ^ (-p) = (2:ℝ) ^ (-p) := by
  have h2 : (0:ℝ) ≤ 2 := by norm_num
  calc z ^ p * (2 * z) ^ (-p)
      = z ^ p * ((2:ℝ)^(-p) * z ^ (-p)) := by rw [Real.mul_rpow h2 hz.le]
    _ = (z ^ p * z ^ (-p)) * (2:ℝ)^(-p) := by ring
    _ = z ^ (p + -p) * (2:ℝ)^(-p) := by rw [Real.rpow_add hz]
    _ = (2:ℝ)^(-p) := by rw [add_neg_cancel, Real.rpow_zero, one_mul]

theorem radGreen_split_le {α : ℝ} (hα : 0 < α) {m : ℕ} {c : ℝ → ℝ}
    {z L B : ℝ} (hz : 0 < z) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hq : 1 < Work.FTS.EllExist.rgQ α m) (hp : 3 / 2 < Work.FTS.EllExist.rgP α m)
    (hcL : ∀ t ∈ Set.Icc (z / 2) (2 * z), |c t| ≤ L)
    (hc : MeasureTheory.IntegrableOn (fun t : ℝ => (c t * Work.Spaces.w t) ^ 2) (Set.Ioi 0))
    (hcm : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => c t * Work.Spaces.w t)
      (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hBs : Real.sqrt (∫ t in Set.Ioi (0 : ℝ), (c t * Work.Spaces.w t) ^ 2) ≤ B) :
    |Work.FTS.PhiStar.Radial.radGreen α m c z| ≤ Work.FTS.EllExist.rgK α m *
      (L * (1 / Work.FTS.EllExist.rgQ α m + 1 / Work.FTS.EllExist.rgP α m)
        + B * ((2 : ℝ) ^ (-(Work.FTS.EllExist.rgQ α m))
              / Real.sqrt (2 * Work.FTS.EllExist.rgQ α m - 1)
            + (2 : ℝ) ^ (-(Work.FTS.EllExist.rgP α m))
              / Real.sqrt (2 * Work.FTS.EllExist.rgP α m - 3))) := by
  have hz2 : 0 < z / 2 := by linarith
  have h2z : 0 < 2 * z := by linarith
  have hz2le : z / 2 ≤ z := by linarith
  have hzle2 : z ≤ 2 * z := by linarith
  have hqpos : 0 < rq α m := by linarith
  have hppos : 0 < rp α m := by linarith
  have hKpos : 0 < rK α m := Work.FTS.EllExist.rgK_pos hα m
  -- a.e. strong measurability of `c` on the two middle intervals
  have hcme1 : AEStronglyMeasurable c (volume.restrict (Set.Ioc (z / 2) z)) :=
    aesm_c_of_aesm_mul_w hz2 hcm
  have hcme2 : AEStronglyMeasurable c (volume.restrict (Set.Ioc z (2 * z))) :=
    aesm_c_of_aesm_mul_w hz hcm
  -- the four pieces of the split
  obtain ⟨hintN, hbdN⟩ := near_cs (q := rq α m) (a := z / 2)
      (B := Real.sqrt (∫ t in Set.Ioi (0 : ℝ), (c t * w t) ^ 2)) hq hz2 hc hcm le_rfl
  obtain ⟨hintM, hbdM⟩ := near_inner (q := rq α m) (L := L) (a := z / 2) (b := z)
      hqpos hz2 hz2le hL hcme1 (fun t ht => hcL t ⟨ht.1, le_trans ht.2 hzle2⟩)
  obtain ⟨hintF1, hbdF1⟩ := far_inner (p := rp α m) (L := L) (a := z) (b := 2 * z)
      hppos hz hzle2 hL hcme2 (fun t ht => hcL t ⟨le_trans hz2le ht.1, ht.2⟩)
  obtain ⟨hintF2, hbdF2⟩ := far_cs (p := rp α m) (a := 2 * z)
      (B := Real.sqrt (∫ t in Set.Ioi (0 : ℝ), (c t * w t) ^ 2)) hp h2z hc hcm le_rfl
  -- the two splits of the Green integrals
  have hsplit1 : ∫ t in Set.Ioc (0 : ℝ) z, c t * t ^ (rq α m - 1)
      = (∫ t in Set.Ioc (0 : ℝ) (z / 2), c t * t ^ (rq α m - 1))
        + ∫ t in Set.Ioc (z / 2) z, c t * t ^ (rq α m - 1) := by
    rw [← Set.Ioc_union_Ioc_eq_Ioc hz2.le hz2le]
    exact setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hintN hintM
  have hsplit2 : ∫ t in Set.Ioi z, c t * t ^ (-(rp α m) - 1)
      = (∫ t in Set.Ioc z (2 * z), c t * t ^ (-(rp α m) - 1))
        + ∫ t in Set.Ioi (2 * z), c t * t ^ (-(rp α m) - 1) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hzle2]
    exact setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hintF1 hintF2
  -- bound on the decaying branch
  have hG1 : |Work.FTS.EllExist.rgG1 α m c z| ≤
      Real.sqrt (∫ t in Set.Ioi (0 : ℝ), (c t * w t) ^ 2)
          * ((2 : ℝ) ^ (-(rq α m)) / Real.sqrt (2 * rq α m - 1)) + L / rq α m := by
    rw [Work.FTS.ClassCHon.rgG1_eq (α := α) (m := m) (c := c) hz, hsplit1]
    have hzQ : 0 < z ^ (-(rq α m)) := Real.rpow_pos_of_pos hz _
    rw [abs_mul, abs_of_pos hzQ]
    refine (mul_le_mul_of_nonneg_left (abs_add_le _ _) hzQ.le).trans ?_
    rw [mul_add]
    refine add_le_add ?_ ?_
    · refine (mul_le_mul_of_nonneg_left hbdN hzQ.le).trans ?_
      rw [show z ^ (-(rq α m)) * (Real.sqrt (∫ t in Set.Ioi (0 : ℝ), (c t * w t) ^ 2)
            * ((z / 2) ^ (rq α m) / Real.sqrt (2 * rq α m - 1)))
          = Real.sqrt (∫ t in Set.Ioi (0 : ℝ), (c t * w t) ^ 2)
            * ((z ^ (-(rq α m)) * (z / 2) ^ (rq α m)) / Real.sqrt (2 * rq α m - 1))
          from by ring,
        rpow_neg_mul_half hz]
    · refine (mul_le_mul_of_nonneg_left hbdM hzQ.le).trans ?_
      rw [show z ^ (-(rq α m)) * (L * z ^ (rq α m) / rq α m)
          = L * (z ^ (-(rq α m)) * z ^ (rq α m)) / rq α m from by ring,
        ← Real.rpow_add hz, neg_add_cancel, Real.rpow_zero, mul_one]
  -- bound on the growing branch
  have hG2 : |Work.FTS.EllExist.rgG2 α m c z| ≤ L / rp α m
      + Real.sqrt (∫ t in Set.Ioi (0 : ℝ), (c t * w t) ^ 2)
          * ((2 : ℝ) ^ (-(rp α m)) / Real.sqrt (2 * rp α m - 3)) := by
    rw [Work.FTS.ClassCHon.rgG2_eq (α := α) (m := m) (c := c), hsplit2]
    have hzP : 0 < z ^ (rp α m) := Real.rpow_pos_of_pos hz _
    rw [abs_mul, abs_of_pos hzP]
    refine (mul_le_mul_of_nonneg_left (abs_add_le _ _) hzP.le).trans ?_
    rw [mul_add]
    refine add_le_add ?_ ?_
    · refine (mul_le_mul_of_nonneg_left hbdF1 hzP.le).trans ?_
      rw [show z ^ (rp α m) * (L * z ^ (-(rp α m)) / rp α m)
          = L * (z ^ (rp α m) * z ^ (-(rp α m))) / rp α m from by ring,
        ← Real.rpow_add hz, add_neg_cancel, Real.rpow_zero, mul_one]
    · refine (mul_le_mul_of_nonneg_left hbdF2 hzP.le).trans ?_
      rw [show z ^ (rp α m) * (Real.sqrt (∫ t in Set.Ioi (0 : ℝ), (c t * w t) ^ 2)
            * ((2 * z) ^ (-(rp α m)) / Real.sqrt (2 * rp α m - 3)))
          = Real.sqrt (∫ t in Set.Ioi (0 : ℝ), (c t * w t) ^ 2)
            * ((z ^ (rp α m) * (2 * z) ^ (-(rp α m))) / Real.sqrt (2 * rp α m - 3))
          from by ring,
        rpow_mul_two_neg hz]
  -- `radGreen` in terms of the two branches
  have hrad : |Work.FTS.PhiStar.Radial.radGreen α m c z| ≤
      rK α m * (|Work.FTS.EllExist.rgG1 α m c z| + |Work.FTS.EllExist.rgG2 α m c z|) := by
    rw [Work.FTS.EllExist.radGreen_eq α m c z, abs_mul, abs_of_pos hKpos]
    exact mul_le_mul_of_nonneg_left (abs_add_le _ _) hKpos.le
  -- assembly of the four pieces
  have hmain : |Work.FTS.EllExist.rgG1 α m c z| + |Work.FTS.EllExist.rgG2 α m c z| ≤
      L * (1 / rq α m + 1 / rp α m)
        + B * ((2 : ℝ) ^ (-(rq α m)) / Real.sqrt (2 * rq α m - 1)
            + (2 : ℝ) ^ (-(rp α m)) / Real.sqrt (2 * rp α m - 3)) := by
    have hsum : Real.sqrt (∫ t in Set.Ioi (0 : ℝ), (c t * w t) ^ 2)
          * ((2 : ℝ) ^ (-(rq α m)) / Real.sqrt (2 * rq α m - 1))
        + Real.sqrt (∫ t in Set.Ioi (0 : ℝ), (c t * w t) ^ 2)
          * ((2 : ℝ) ^ (-(rp α m)) / Real.sqrt (2 * rp α m - 3))
        ≤ B * ((2 : ℝ) ^ (-(rq α m)) / Real.sqrt (2 * rq α m - 1)
            + (2 : ℝ) ^ (-(rp α m)) / Real.sqrt (2 * rp α m - 3)) := by
      rw [← mul_add]
      refine mul_le_mul_of_nonneg_right hBs (add_nonneg ?_ ?_)
      · exact div_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.sqrt_nonneg _)
      · exact div_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.sqrt_nonneg _)
    calc |Work.FTS.EllExist.rgG1 α m c z| + |Work.FTS.EllExist.rgG2 α m c z|
        ≤ (Real.sqrt (∫ t in Set.Ioi (0 : ℝ), (c t * w t) ^ 2)
              * ((2 : ℝ) ^ (-(rq α m)) / Real.sqrt (2 * rq α m - 1)) + L / rq α m)
          + (L / rp α m + Real.sqrt (∫ t in Set.Ioi (0 : ℝ), (c t * w t) ^ 2)
              * ((2 : ℝ) ^ (-(rp α m)) / Real.sqrt (2 * rp α m - 3))) := add_le_add hG1 hG2
      _ = (L / rq α m + L / rp α m)
          + (Real.sqrt (∫ t in Set.Ioi (0 : ℝ), (c t * w t) ^ 2)
              * ((2 : ℝ) ^ (-(rq α m)) / Real.sqrt (2 * rq α m - 1))
            + Real.sqrt (∫ t in Set.Ioi (0 : ℝ), (c t * w t) ^ 2)
              * ((2 : ℝ) ^ (-(rp α m)) / Real.sqrt (2 * rp α m - 3))) := by ring
      _ ≤ (L / rq α m + L / rp α m)
          + B * ((2 : ℝ) ^ (-(rq α m)) / Real.sqrt (2 * rq α m - 1)
              + (2 : ℝ) ^ (-(rp α m)) / Real.sqrt (2 * rp α m - 3)) :=
          add_le_add_right hsum _
      _ = L * (1 / rq α m + 1 / rp α m)
          + B * ((2 : ℝ) ^ (-(rq α m)) / Real.sqrt (2 * rq α m - 1)
              + (2 : ℝ) ^ (-(rp α m)) / Real.sqrt (2 * rp α m - 3)) := by ring
  calc |Work.FTS.PhiStar.Radial.radGreen α m c z|
      ≤ rK α m * (|Work.FTS.EllExist.rgG1 α m c z| + |Work.FTS.EllExist.rgG2 α m c z|) := hrad
    _ ≤ rK α m * (L * (1 / rq α m + 1 / rp α m)
          + B * ((2 : ℝ) ^ (-(rq α m)) / Real.sqrt (2 * rq α m - 1)
              + (2 : ℝ) ^ (-(rp α m)) / Real.sqrt (2 * rp α m - 3))) :=
        mul_le_mul_of_nonneg_left hmain hKpos.le

end Work.FTS.ClassCHon.Hcoef
