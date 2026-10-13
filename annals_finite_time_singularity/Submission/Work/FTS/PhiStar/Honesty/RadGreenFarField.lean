/-
# Far-field weighted `L²`-integrability of the `G2` Green term

`radGreen α m c = K·(G1 + G2)` with `G1 z = z^{-A}∫_0^z c t^{A-1} dt` (`A = (2m+5)/α`) and
`G2 z = z^{p}∫_z^∞ c t^{-p-1} dt` (`p = 2m/α`); this file treats `G2` (the `G1` half is in
`RadGreenFarG1`).  Assuming only `∫_1^∞ c² < ∞` (plus `0 < α ≤ 1/4`, `m ≥ 1`) we prove
`∫_1^∞ G2(z)² w(z)² dz < ∞`.

No pointwise domination of `G2` by the `L²` data is possible: `G2` can decay only like `z^{-1/2}`,
so at the level of the crude Cauchy–Schwarz estimate its square is only `≈ z^{-1}`, exactly on the
boundary of non-integrability.  The sharp information comes from the first-order relation
`z G2' = p·G2 - c`, which with the fundamental theorem of calculus on `[1,y]` gives

  `(1+2p)∫_1^y G2² = y·G2(y)² - G2(1)² + 2∫_1^y c·G2`,

and the boundary term is controlled by Cauchy–Schwarz on the tail,
`y·G2(y)² ≤ (1/p)∫_y^∞ c² ≤ (1/p)∫_1^∞ c²`.  The remaining term is absorbed by the weighted
AM–GM `2|c·G2| ≤ λG2² + c²/λ` with `λ = (1+2p)/2`, which gives `∫_1^y G2² ≤ T` *uniformly in*
`y ∈ (1,∞)`, and `radFar_integrableOn_Ioi_one_of_sq_interval_bound` converts that into
integrability on `(1,∞)`; the bounded weight `w² ≤ 16` is absorbed by `Integrable.bdd_mul`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllExist.Honesty.FarAux.Basic
import Submission.Work.FTS.PhiStar.Honesty.IoiTool
import Submission.Work.FTS.PhiStar.Honesty.RadGreenFarTools
import Submission.Work.FTS.PhiStar.Honesty.psi_cs_of_aesm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace Work.FTS.PhiStar.Honesty

open Work.FTS.EllExist.Honesty (G1 G2 G1f radPsi_eq_G2 radPsi_hasDerivAt)
open Work.FTS.PhiStar.RadialWAux (radP radQ radPsi)

/-- `G2` is differentiable on all of `(0,∞)` with `z G2' = p·G2 - c` (`p = 2m/α`).  (Compare
`Work.FTS.EllExist.Honesty.G2_hasDerivAt`, stated on `(1,∞)` only; we need `z = 1` for the
fundamental theorem of calculus.) -/
private theorem G2_hasDerivAt_pos {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : ContinuousOn c (Set.Ioi 0))
    (hinf : MeasureTheory.IntegrableOn (fun t : ℝ => |c t| * t ^ (-(radP α m) - 1))
      (Set.Ioi 1)) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (G2 α m c) ((radP α m * G2 α m c z - c z) / z) z := by
  intro z hz
  have h := radPsi_hasDerivAt hα hα4 m hm hc hinf z hz
  have hev : radPsi α m c =ᶠ[𝓝 z] G2 α m c := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
    exact radPsi_eq_G2 α m c hy
  have hd : (radP α m * radPsi α m c z - c z) / z
      = (radP α m * G2 α m c z - c z) / z := by
    rw [radPsi_eq_G2 α m c hz]
  exact (h.congr_of_eventuallyEq hev.symm).congr_deriv hd

/-- **The tail bound for `G2`**: `y·G2(y)² ≤ (1/p)·∫_1^∞ c²` for `p = 2m/α`. -/
private theorem G2_tail_bound {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hm : 1 ≤ m) (hc : ContinuousOn c (Set.Ioi 0))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    ∀ y : ℝ, 1 < y → y * (G2 α m c y) ^ 2
      ≤ (1 / radP α m) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by
    have h : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hp : 0 < radP α m := by
    rw [radP]
    exact div_pos (by linarith) hα
  have hp1 : 0 < 1 / radP α m := div_pos (by norm_num) hp
  have hc1 : ContinuousOn c (Set.Ioi 1) :=
    hc.mono (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
  intro y hy
  have hy0 : 0 < y := lt_trans one_pos hy
  have hcs := psi_cs_of_aesm (p := radP α m) hp hy0
    ((hc1.mono (Set.Ioi_subset_Ioi hy.le)).aestronglyMeasurable measurableSet_Ioi)
    (hfar.mono_set (Set.Ioi_subset_Ioi hy.le))
  have hwt : (∫ t in Set.Ioi y, (c t) ^ 2 * t ^ (-radP α m - 1))
      ≤ y ^ (-radP α m - 1) * (∫ t in Set.Ioi y, (c t) ^ 2) := by
    have hfy : IntegrableOn (fun t : ℝ => (c t) ^ 2 * t ^ (-radP α m - 1)) (Set.Ioi y) := by
      refine Integrable.mono' (hfar.mono_set (Set.Ioi_subset_Ioi hy.le)) ?_ ?_
      · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
        exact ((hc1.mono (Set.Ioi_subset_Ioi hy.le)).pow 2).mul
          (continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt (lt_trans hy0 ht))))
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : 0 < t := lt_trans hy0 ht
        have ht1 : (1 : ℝ) ≤ t := le_of_lt (lt_trans hy ht)
        have hpow : t ^ (-radP α m - 1) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos ht1 (by linarith)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (c t)),
          abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
        calc (c t) ^ 2 * t ^ (-radP α m - 1) ≤ (c t) ^ 2 * 1 :=
              mul_le_mul_of_nonneg_left hpow (sq_nonneg _)
          _ = (c t) ^ 2 := by rw [mul_one]
    have hgy : IntegrableOn (fun t : ℝ => y ^ (-radP α m - 1) * (c t) ^ 2) (Set.Ioi y) :=
      (hfar.mono_set (Set.Ioi_subset_Ioi hy.le)).const_mul _
    have hmono := setIntegral_mono_on hfy hgy measurableSet_Ioi
      (fun t ht => by
        have hpow : t ^ (-radP α m - 1) ≤ y ^ (-radP α m - 1) :=
          Real.rpow_le_rpow_of_nonpos hy0 (le_of_lt ht) (by linarith : -radP α m - 1 ≤ 0)
        rw [mul_comm (y ^ (-radP α m - 1)) ((c t) ^ 2)]
        exact mul_le_mul_of_nonneg_left hpow (sq_nonneg _))
    rw [MeasureTheory.integral_const_mul] at hmono
    exact hmono
  have htailP : (∫ t in Set.Ioi y, (c t) ^ 2) ≤ ∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2 :=
    MeasureTheory.setIntegral_mono_set hfar (ae_of_all _ fun t => sq_nonneg (c t))
      (ae_of_all _ fun t ht => lt_trans hy ht)
  have hsq : (G2 α m c y) ^ 2
      = y ^ (2 * radP α m) * (∫ t in Set.Ioi y, c t * t ^ (-radP α m - 1)) ^ 2 := by
    have hG2y : G2 α m c y
        = y ^ (radP α m) * (∫ t in Set.Ioi y, c t * t ^ (-radP α m - 1)) := rfl
    rw [hG2y, mul_pow, ← Real.rpow_natCast (y ^ radP α m) 2, ← Real.rpow_mul hy0.le,
      show radP α m * ((2 : ℕ) : ℝ) = 2 * radP α m by push_cast; ring]
  have hA : (∫ t in Set.Ioi y, c t * t ^ (-radP α m - 1)) ^ 2
      ≤ (1 / radP α m) * y ^ (-2 * radP α m - 1)
        * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2) := by
    have hB : (∫ t in Set.Ioi y, (c t) ^ 2 * t ^ (-radP α m - 1))
        ≤ y ^ (-radP α m - 1) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2) :=
      hwt.trans (mul_le_mul_of_nonneg_left htailP (Real.rpow_nonneg hy0.le _))
    calc (∫ t in Set.Ioi y, c t * t ^ (-radP α m - 1)) ^ 2
        ≤ (1 / radP α m) * y ^ (-radP α m)
            * (∫ t in Set.Ioi y, (c t) ^ 2 * t ^ (-radP α m - 1)) := hcs
      _ ≤ (1 / radP α m) * y ^ (-radP α m)
            * (y ^ (-radP α m - 1) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2)) :=
          mul_le_mul_of_nonneg_left hB
            (mul_nonneg (le_of_lt hp1) (Real.rpow_nonneg hy0.le _))
      _ = (1 / radP α m) * (y ^ (-radP α m) * y ^ (-radP α m - 1))
            * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2) := by ring
      _ = (1 / radP α m) * y ^ (-2 * radP α m - 1)
            * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2) := by
          rw [← Real.rpow_add hy0,
            show -radP α m + (-radP α m - 1) = -2 * radP α m - 1 by ring]
  have hG2sq : (G2 α m c y) ^ 2
      ≤ (1 / radP α m) * y ^ (-1 : ℝ) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2) := by
    calc (G2 α m c y) ^ 2
        = y ^ (2 * radP α m)
            * (∫ t in Set.Ioi y, c t * t ^ (-radP α m - 1)) ^ 2 := hsq
      _ ≤ y ^ (2 * radP α m)
            * ((1 / radP α m) * y ^ (-2 * radP α m - 1)
              * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2)) :=
          mul_le_mul_of_nonneg_left hA (Real.rpow_nonneg hy0.le _)
      _ = (1 / radP α m) * (y ^ (2 * radP α m) * y ^ (-2 * radP α m - 1))
            * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2) := by ring
      _ = (1 / radP α m) * y ^ (-1 : ℝ) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2) := by
          rw [← Real.rpow_add hy0,
            show 2 * radP α m + (-2 * radP α m - 1) = -1 by ring]
  calc y * (G2 α m c y) ^ 2
      ≤ y * ((1 / radP α m) * y ^ (-1 : ℝ) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2)) :=
        mul_le_mul_of_nonneg_left hG2sq hy0.le
    _ = (1 / radP α m) * (y * y ^ (-1 : ℝ)) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2) := by ring
    _ = (1 / radP α m) * 1 * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2) := by
        rw [Real.rpow_neg_one, mul_inv_cancel₀ (ne_of_gt hy0)]
    _ = (1 / radP α m) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2) := by ring

/-- **The `G2` interval estimate**: for every `y > 1`,
`∫_1^y G2² ≤ 2/(1+2p)·((1/p)·P + (2/(1+2p))·P)`, `P = ∫_1^∞ c²`. -/
private theorem G2_far_interval_bound {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : ContinuousOn c (Set.Ioi 0))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    ∀ y : ℝ, 1 < y → (∫ z in (1 : ℝ)..y, (G2 α m c z) ^ 2)
      ≤ 2 / (1 + 2 * radP α m)
        * ((1 / radP α m) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2)
          + (2 / (1 + 2 * radP α m)) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2)) := by
  have hp : 0 < radP α m := by
    rw [radP]
    exact div_pos (by positivity) hα
  have hp1 : 0 < 1 + 2 * radP α m := by linarith
  have hc1 : ContinuousOn c (Set.Ioi 1) :=
    hc.mono (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
  have hinf : MeasureTheory.IntegrableOn (fun t : ℝ => |c t| * t ^ (-(radP α m) - 1))
      (Set.Ioi 1) :=
    integrableOn_abs_mul_rpow_of_sq (p := radP α m) (by linarith) hc1 hfar
  have hderiv0 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (G2 α m c) ((radP α m * G2 α m c z - c z) / z) z :=
    G2_hasDerivAt_pos hα hα4 hm hc hinf
  have henergy : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun y : ℝ => y * (G2 α m c y) ^ 2)
      ((1 + 2 * radP α m) * (G2 α m c z) ^ 2 - 2 * (c z * G2 α m c z)) z := by
    intro z hz
    have h := radFar_hasDerivAt_mul_sq (A := G2 α m c) (s := radP α m) (d := fun w => -(c w))
      hderiv0 z hz
    refine h.congr_deriv ?_
    ring_nf
  have hcont0 : ContinuousOn (G2 α m c) (Set.Ioi (0 : ℝ)) := fun z hz =>
    (hderiv0 z hz).continuousAt.continuousWithinAt
  intro y hy
  have hy0 : (0 : ℝ) < y := lt_trans one_pos hy
  have hIcc : Set.Icc (1 : ℝ) y ⊆ Set.Ioi (0 : ℝ) := by
    intro z hz
    show (0 : ℝ) < z
    linarith [hz.1]
  have hcontG : ContinuousOn (G2 α m c) (Set.Icc (1 : ℝ) y) := hcont0.mono hIcc
  have hcontc : ContinuousOn c (Set.Icc (1 : ℝ) y) := hc.mono hIcc
  have hint_sq : IntervalIntegrable (fun z : ℝ => (G2 α m c z) ^ 2) volume (1 : ℝ) y :=
    (hcontG.pow 2).intervalIntegrable_of_Icc hy.le
  have hint_cG : IntervalIntegrable (fun z : ℝ => c z * G2 α m c z) volume (1 : ℝ) y :=
    (hcontc.mul hcontG).intervalIntegrable_of_Icc hy.le
  have hint_csq : IntervalIntegrable (fun z : ℝ => (c z) ^ 2) volume (1 : ℝ) y :=
    (hcontc.pow 2).intervalIntegrable_of_Icc hy.le
  have hcontD : ContinuousOn (fun z : ℝ => (1 + 2 * radP α m) * (G2 α m c z) ^ 2
      - 2 * (c z * G2 α m c z)) (Set.Icc (1 : ℝ) y) :=
    ((hcontG.pow 2).const_mul _).sub ((hcontc.mul hcontG).const_mul 2)
  have hintD : IntervalIntegrable (fun z : ℝ => (1 + 2 * radP α m) * (G2 α m c z) ^ 2
      - 2 * (c z * G2 α m c z)) volume (1 : ℝ) y :=
    hcontD.intervalIntegrable_of_Icc hy.le
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (1 : ℝ)) (b := y)
    (f := fun t : ℝ => t * (G2 α m c t) ^ 2)
    (f' := fun z : ℝ => (1 + 2 * radP α m) * (G2 α m c z) ^ 2 - 2 * (c z * G2 α m c z))
    (fun z hz => by
      rw [Set.uIcc_of_le hy.le] at hz
      exact henergy z (lt_of_lt_of_le zero_lt_one hz.1))
    hintD
  rw [intervalIntegral.integral_sub (hint_sq.const_mul _) (hint_cG.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, one_mul] at hFTC
  have habs : (∫ z in (1 : ℝ)..y, c z * G2 α m c z)
      ≤ ∫ z in (1 : ℝ)..y, |c z * G2 α m c z| :=
    intervalIntegral.integral_mono_on hy.le hint_cG hint_cG.abs (fun z _ => le_abs_self _)
  have hint_abs : IntervalIntegrable (fun z : ℝ => |c z * G2 α m c z|) volume (1 : ℝ) y :=
    hint_cG.abs
  have hamgm : 2 * (∫ z in (1 : ℝ)..y, |c z * G2 α m c z|)
      ≤ ((1 + 2 * radP α m) / 2) * (∫ z in (1 : ℝ)..y, (G2 α m c z) ^ 2)
        + (2 / (1 + 2 * radP α m)) * (∫ z in (1 : ℝ)..y, (c z) ^ 2) := by
    have hlm : ((1 + 2 * radP α m) / 2) * (2 / (1 + 2 * radP α m)) = 1 := by
      rw [div_mul_div_comm, mul_comm (1 + 2 * radP α m) 2]
      exact div_self (by positivity)
    have hpt : ∀ z ∈ Set.Icc (1 : ℝ) y,
        2 * |c z * G2 α m c z|
          ≤ ((1 + 2 * radP α m) / 2) * (G2 α m c z) ^ 2
            + (2 / (1 + 2 * radP α m)) * (c z) ^ 2 := by
      intro z _
      have h := radFar_amgm (l := (1 + 2 * radP α m) / 2) (m := 2 / (1 + 2 * radP α m))
        (by linarith) (div_pos (by norm_num) hp1) hlm (X := G2 α m c z) (Y := c z)
      have h2 : 2 * |(G2 α m c z) * (c z)| = 2 * |c z * G2 α m c z| := by
        rw [mul_comm (G2 α m c z) (c z)]
      rwa [h2] at h
    have hint_lhs : IntervalIntegrable (fun z : ℝ => 2 * |c z * G2 α m c z|) volume (1 : ℝ) y :=
      hint_abs.const_mul 2
    have hint_rhs : IntervalIntegrable (fun z : ℝ =>
        ((1 + 2 * radP α m) / 2) * (G2 α m c z) ^ 2
          + (2 / (1 + 2 * radP α m)) * (c z) ^ 2) volume (1 : ℝ) y :=
      (hint_sq.const_mul _).add (hint_csq.const_mul _)
    have hmono := intervalIntegral.integral_mono_on hy.le hint_lhs hint_rhs hpt
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
      (hint_sq.const_mul _) (hint_csq.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
    exact hmono
  have hcsq_le : (∫ z in (1 : ℝ)..y, (c z) ^ 2) ≤ ∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2 := by
    rw [intervalIntegral.integral_of_le hy.le]
    exact MeasureTheory.setIntegral_mono_set hfar (ae_of_all _ fun t => sq_nonneg (c t))
      (ae_of_all _ fun t ht => ht.1)
  have hY : y * (G2 α m c y) ^ 2 ≤ (1 / radP α m) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2) :=
    G2_tail_bound hα hm hc hfar y hy
  set P : ℝ := ∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2 with hPdef
  set I : ℝ := ∫ z in (1 : ℝ)..y, (G2 α m c z) ^ 2 with hIdef
  set J : ℝ := ∫ z in (1 : ℝ)..y, c z * G2 α m c z with hJdef
  set K : ℝ := ∫ z in (1 : ℝ)..y, |c z * G2 α m c z| with hKdef
  set Q : ℝ := ∫ z in (1 : ℝ)..y, (c z) ^ 2 with hQdef
  set Y : ℝ := y * (G2 α m c y) ^ 2 with hYdef
  set C1 : ℝ := (G2 α m c 1) ^ 2 with hC1def
  have hC1nn : 0 ≤ C1 := by rw [hC1def]; exact sq_nonneg _
  have hkey : (1 + 2 * radP α m) * I
      ≤ (1 / radP α m) * P + ((1 + 2 * radP α m) / 2) * I
        + (2 / (1 + 2 * radP α m)) * P := by
    have h1 : (1 + 2 * radP α m) * I = Y - C1 + 2 * J := by
      rw [hIdef, hYdef, hC1def, hJdef]
      linarith [hFTC]
    have h2 : Y ≤ (1 / radP α m) * P := by rw [hYdef, hPdef]; exact hY
    have h4 : 2 * J ≤ 2 * K := by rw [hJdef, hKdef]; linarith [habs]
    have h5 : 2 * K ≤ ((1 + 2 * radP α m) / 2) * I + (2 / (1 + 2 * radP α m)) * Q := by
      rw [hKdef, hIdef, hQdef]; exact hamgm
    have h6 : (2 / (1 + 2 * radP α m)) * Q ≤ (2 / (1 + 2 * radP α m)) * P := by
      rw [hQdef, hPdef]
      exact mul_le_mul_of_nonneg_left hcsq_le (le_of_lt (div_pos (by norm_num) hp1))
    linarith [h1, h2, hC1nn, h4, h5, h6]
  have hfinal : I ≤ 2 / (1 + 2 * radP α m) * ((1 / radP α m) * P
      + (2 / (1 + 2 * radP α m)) * P) := by
    have hstep : ((1 + 2 * radP α m) / 2) * I
        ≤ (1 / radP α m) * P + (2 / (1 + 2 * radP α m)) * P := by
      linarith [hkey]
    have hmul : 2 * (((1 + 2 * radP α m) / 2) * I)
        ≤ 2 * ((1 / radP α m) * P + (2 / (1 + 2 * radP α m)) * P) :=
      mul_le_mul_of_nonneg_left hstep (by norm_num)
    have heq : 2 * (((1 + 2 * radP α m) / 2) * I) = (1 + 2 * radP α m) * I := by ring
    rw [heq] at hmul
    rw [show 2 / (1 + 2 * radP α m)
          * ((1 / radP α m) * P + (2 / (1 + 2 * radP α m)) * P)
        = 2 * ((1 / radP α m) * P + (2 / (1 + 2 * radP α m)) * P) / (1 + 2 * radP α m)
        from by ring,
      le_div_iff₀ hp1]
    linarith [hmul]
  rw [hIdef, hPdef] at hfinal
  exact hfinal

/-- **Far-field weighted `L²`-integrability of `G2`.** -/
theorem G2_sq_w_sq_integrableOn_far {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : ContinuousOn c (Set.Ioi 0))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => (G2 α m c z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 1) := by
  have hp : 0 < radP α m := by
    rw [radP]
    exact div_pos (by positivity) hα
  have hp1 : 0 < 1 + 2 * radP α m := by linarith
  have hc1 : ContinuousOn c (Set.Ioi 1) :=
    hc.mono (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
  have hinf : MeasureTheory.IntegrableOn (fun t : ℝ => |c t| * t ^ (-(radP α m) - 1))
      (Set.Ioi 1) :=
    integrableOn_abs_mul_rpow_of_sq (p := radP α m) (by linarith) hc1 hfar
  have hcont0 : ContinuousOn (G2 α m c) (Set.Ioi (0 : ℝ)) := fun z hz =>
    ((G2_hasDerivAt_pos hα hα4 hm hc hinf z hz)).continuousAt.continuousWithinAt
  have hb := G2_far_interval_bound hα hα4 hm hc hfar
  have hT : 0 ≤ 2 / (1 + 2 * radP α m)
      * ((1 / radP α m) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2)
        + (2 / (1 + 2 * radP α m)) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2)) := by
    have hPnn : 0 ≤ ∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2 :=
      setIntegral_nonneg measurableSet_Ioi (fun t _ => sq_nonneg _)
    have h1 : 0 ≤ 1 / radP α m := le_of_lt (div_pos (by norm_num) hp)
    have h2 : 0 ≤ 2 / (1 + 2 * radP α m) := le_of_lt (div_pos (by norm_num) hp1)
    exact mul_nonneg h2 (add_nonneg (mul_nonneg h1 hPnn) (mul_nonneg h2 hPnn))
  have hsq : MeasureTheory.IntegrableOn (fun z : ℝ => (G2 α m c z) ^ 2) (Set.Ioi 1) :=
    radFar_integrableOn_Ioi_one_of_sq_interval_bound hT
      (T := 2 / (1 + 2 * radP α m)
        * ((1 / radP α m) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2)
          + (2 / (1 + 2 * radP α m)) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2)))
      (fun z => sq_nonneg _) (hcont0.pow 2) hb
  exact radFar_integrableOn_mul_w_sq hsq

end Work.FTS.PhiStar.Honesty
