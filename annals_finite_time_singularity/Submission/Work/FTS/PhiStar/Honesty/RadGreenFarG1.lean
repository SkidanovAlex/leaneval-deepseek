/-
# Far-field weighted `L²`-integrability of the `G1` Green term

`G1 z = z^{-A}∫_0^z c t^{A-1} dt` (`A = (2m+5)/α = radQ α m`) is the `z → 0`-singular half of
`Work.FTS.PhiStar.Radial.radGreen`; here we prove `∫_1^∞ G1(z)² w(z)² dz < ∞` for the far field
from the single hypothesis `∫_1^∞ c² < ∞`, via the energy identity `z G1' = -A·G1 + c` and the
fundamental theorem of calculus on `[1,y]` (exactly as for `G2` in `RadGreenFarField`, where the
method is explained):

  `(2A-1)∫_1^y G1² = G1(1)² - y·G1(y)² + 2∫_1^y c·G1`,

so here the boundary term has the *good* sign and is simply dropped.  The one degenerate case is
when `c` is not integrable against `t^{A-1}` on `(0,1]`: then the interval integral defining `G1`
is Lean's junk value `0` on `(1,∞)` and the claim is trivial.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllExist.Honesty.FarAux.Basic
import Submission.Work.FTS.PhiStar.Honesty.IoiTool
import Submission.Work.FTS.PhiStar.Honesty.RadGreenFarTools

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace Work.FTS.PhiStar.Honesty

open Work.FTS.EllExist.Honesty (G1 G1f)
open Work.FTS.PhiStar.RadialWAux (radQ)

/-- **The `G1` interval estimate** (in the case where `G1f` is integrable on `(0,1)`, so that `G1`
is differentiable and `G1(1)` is an honest number): for every `y > 1`,
`∫_1^y G1² ≤ (2/(2q-1))·(G1(1)² + (2/(2q-1))·P)`, `q = (2m+5)/α`, `P = ∫_1^∞ c²`. -/
private theorem G1_far_interval_bound {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : ContinuousOn c (Set.Ioi 0))
    (hInt : MeasureTheory.IntegrableOn (G1f α m c) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    ∀ y : ℝ, 1 < y → (∫ z in (1 : ℝ)..y, (G1 α m c z) ^ 2)
      ≤ 2 / (2 * radQ α m - 1)
        * ((G1 α m c 1) ^ 2
          + (2 / (2 * radQ α m - 1)) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2)) := by
  have hq28 : 28 ≤ radQ α m := by
    rw [radQ, le_div_iff₀ hα]
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith
  have hq1 : 0 < 2 * radQ α m - 1 := by linarith
  have hq21 : 0 < (2 * radQ α m - 1) / 2 := by linarith
  have hqm : 0 < 2 / (2 * radQ α m - 1) := div_pos (by norm_num) hq1
  have hderiv0 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (G1 α m c) (((-radQ α m) * G1 α m c z + c z) / z) z :=
    Work.FTS.EllExist.Honesty.G1_hasDerivAt_of_intervalIntegrable hc hInt
  have henergy : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun y : ℝ => y * (G1 α m c y) ^ 2)
      ((1 - 2 * radQ α m) * (G1 α m c z) ^ 2 + 2 * (c z * G1 α m c z)) z := by
    intro z hz
    have h := radFar_hasDerivAt_mul_sq (A := G1 α m c) (s := -radQ α m) (d := c) hderiv0 z hz
    refine h.congr_deriv ?_
    ring_nf
  have hcont0 : ContinuousOn (G1 α m c) (Set.Ioi (0 : ℝ)) := fun z hz =>
    (hderiv0 z hz).continuousAt.continuousWithinAt
  intro y hy
  have hy0 : (0 : ℝ) < y := lt_trans one_pos hy
  have hIcc : Set.Icc (1 : ℝ) y ⊆ Set.Ioi (0 : ℝ) := by
    intro z hz
    show (0 : ℝ) < z
    linarith [hz.1]
  have hcontG : ContinuousOn (G1 α m c) (Set.Icc (1 : ℝ) y) := hcont0.mono hIcc
  have hcontc : ContinuousOn c (Set.Icc (1 : ℝ) y) := hc.mono hIcc
  have hint_sq : IntervalIntegrable (fun z : ℝ => (G1 α m c z) ^ 2) volume (1 : ℝ) y :=
    (hcontG.pow 2).intervalIntegrable_of_Icc hy.le
  have hint_cG : IntervalIntegrable (fun z : ℝ => c z * G1 α m c z) volume (1 : ℝ) y :=
    (hcontc.mul hcontG).intervalIntegrable_of_Icc hy.le
  have hint_csq : IntervalIntegrable (fun z : ℝ => (c z) ^ 2) volume (1 : ℝ) y :=
    (hcontc.pow 2).intervalIntegrable_of_Icc hy.le
  have hcontD : ContinuousOn (fun z : ℝ => (1 - 2 * radQ α m) * (G1 α m c z) ^ 2
      + 2 * (c z * G1 α m c z)) (Set.Icc (1 : ℝ) y) :=
    ((hcontG.pow 2).const_mul _).add ((hcontc.mul hcontG).const_mul 2)
  have hintD : IntervalIntegrable (fun z : ℝ => (1 - 2 * radQ α m) * (G1 α m c z) ^ 2
      + 2 * (c z * G1 α m c z)) volume (1 : ℝ) y :=
    hcontD.intervalIntegrable_of_Icc hy.le
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (1 : ℝ)) (b := y)
    (f := fun t : ℝ => t * (G1 α m c t) ^ 2)
    (f' := fun z : ℝ => (1 - 2 * radQ α m) * (G1 α m c z) ^ 2 + 2 * (c z * G1 α m c z))
    (fun z hz => by
      rw [Set.uIcc_of_le hy.le] at hz
      exact henergy z (lt_of_lt_of_le zero_lt_one hz.1))
    hintD
  rw [intervalIntegral.integral_add (hint_sq.const_mul _) (hint_cG.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, one_mul] at hFTC
  have habs : (∫ z in (1 : ℝ)..y, c z * G1 α m c z)
      ≤ ∫ z in (1 : ℝ)..y, |c z * G1 α m c z| :=
    intervalIntegral.integral_mono_on hy.le hint_cG hint_cG.abs (fun z _ => le_abs_self _)
  have hint_abs : IntervalIntegrable (fun z : ℝ => |c z * G1 α m c z|) volume (1 : ℝ) y :=
    hint_cG.abs
  have hamgm : 2 * (∫ z in (1 : ℝ)..y, |c z * G1 α m c z|)
      ≤ ((2 * radQ α m - 1) / 2) * (∫ z in (1 : ℝ)..y, (G1 α m c z) ^ 2)
        + (2 / (2 * radQ α m - 1)) * (∫ z in (1 : ℝ)..y, (c z) ^ 2) := by
    have hlm : ((2 * radQ α m - 1) / 2) * (2 / (2 * radQ α m - 1)) = 1 := by
      rw [div_mul_div_comm, mul_comm (2 * radQ α m - 1) 2]
      exact div_self (mul_ne_zero (by norm_num) (ne_of_gt hq1))
    have hpt : ∀ z ∈ Set.Icc (1 : ℝ) y,
        2 * |c z * G1 α m c z|
          ≤ ((2 * radQ α m - 1) / 2) * (G1 α m c z) ^ 2
            + (2 / (2 * radQ α m - 1)) * (c z) ^ 2 := by
      intro z _
      have h := radFar_amgm (l := (2 * radQ α m - 1) / 2) (m := 2 / (2 * radQ α m - 1))
        hq21 hqm hlm (X := G1 α m c z) (Y := c z)
      have h2 : 2 * |(G1 α m c z) * (c z)| = 2 * |c z * G1 α m c z| := by
        rw [mul_comm (G1 α m c z) (c z)]
      rwa [h2] at h
    have hint_lhs : IntervalIntegrable (fun z : ℝ => 2 * |c z * G1 α m c z|) volume (1 : ℝ) y :=
      hint_abs.const_mul 2
    have hint_rhs : IntervalIntegrable (fun z : ℝ =>
        ((2 * radQ α m - 1) / 2) * (G1 α m c z) ^ 2
          + (2 / (2 * radQ α m - 1)) * (c z) ^ 2) volume (1 : ℝ) y :=
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
  set P : ℝ := ∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2 with hPdef
  set I : ℝ := ∫ z in (1 : ℝ)..y, (G1 α m c z) ^ 2 with hIdef
  set J : ℝ := ∫ z in (1 : ℝ)..y, c z * G1 α m c z with hJdef
  set K : ℝ := ∫ z in (1 : ℝ)..y, |c z * G1 α m c z| with hKdef
  set Q : ℝ := ∫ z in (1 : ℝ)..y, (c z) ^ 2 with hQdef
  set Y : ℝ := y * (G1 α m c y) ^ 2 with hYdef
  set C1 : ℝ := (G1 α m c 1) ^ 2 with hC1def
  have hYnn : 0 ≤ Y := by
    rw [hYdef]
    exact mul_nonneg hy0.le (sq_nonneg _)
  have hkey : (2 * radQ α m - 1) * I
      ≤ C1 + ((2 * radQ α m - 1) / 2) * I + (2 / (2 * radQ α m - 1)) * P := by
    have h1 : (2 * radQ α m - 1) * I = C1 - Y + 2 * J := by
      rw [hIdef, hC1def, hYdef, hJdef]
      linarith [hFTC]
    have h4 : 2 * J ≤ 2 * K := by rw [hJdef, hKdef]; linarith [habs]
    have h5 : 2 * K ≤ ((2 * radQ α m - 1) / 2) * I + (2 / (2 * radQ α m - 1)) * Q := by
      rw [hKdef, hIdef, hQdef]; exact hamgm
    have h6 : (2 / (2 * radQ α m - 1)) * Q ≤ (2 / (2 * radQ α m - 1)) * P := by
      rw [hQdef, hPdef]
      exact mul_le_mul_of_nonneg_left hcsq_le (le_of_lt hqm)
    linarith [h1, hYnn, h4, h5, h6]
  have hfinal : I ≤ 2 / (2 * radQ α m - 1) * (C1 + (2 / (2 * radQ α m - 1)) * P) := by
    have hstep : ((2 * radQ α m - 1) / 2) * I ≤ C1 + (2 / (2 * radQ α m - 1)) * P := by
      linarith [hkey]
    have hmul := mul_le_mul_of_nonneg_left hstep (le_of_lt hqm)
    have hcoef : (2 / (2 * radQ α m - 1)) * ((2 * radQ α m - 1) / 2) = 1 := by
      rw [div_mul_div_comm, mul_comm 2 (2 * radQ α m - 1)]
      exact div_self (mul_ne_zero (ne_of_gt hq1) (by norm_num))
    have hfirst : (2 / (2 * radQ α m - 1) * ((2 * radQ α m - 1) / 2)) * I = I := by
      rw [hcoef, one_mul]
    calc I = (2 / (2 * radQ α m - 1) * ((2 * radQ α m - 1) / 2)) * I := hfirst.symm
      _ = (2 / (2 * radQ α m - 1)) * (((2 * radQ α m - 1) / 2) * I) := by ring
      _ ≤ (2 / (2 * radQ α m - 1)) * (C1 + (2 / (2 * radQ α m - 1)) * P) := hmul
  rw [hIdef, hC1def, hPdef] at hfinal
  exact hfinal

/-- **Far-field weighted `L²`-integrability of `G1`.** -/
theorem G1_sq_w_sq_integrableOn_far {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : ContinuousOn c (Set.Ioi 0))
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => (G1 α m c z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 1) := by
  by_cases hgood : MeasureTheory.IntegrableOn (G1f α m c) (Set.Ioc (0 : ℝ) 1)
  · have hInt : MeasureTheory.IntegrableOn (G1f α m c) (Set.Ioo 0 1) :=
      hgood.mono_set (fun z hz => ⟨hz.1, le_of_lt hz.2⟩)
    have hderiv0 : ∀ z ∈ Set.Ioi (0 : ℝ),
        HasDerivAt (G1 α m c) (((-radQ α m) * G1 α m c z + c z) / z) z :=
      Work.FTS.EllExist.Honesty.G1_hasDerivAt_of_intervalIntegrable hc hInt
    have hcont0 : ContinuousOn (G1 α m c) (Set.Ioi (0 : ℝ)) := fun z hz =>
      (hderiv0 z hz).continuousAt.continuousWithinAt
    have hb := G1_far_interval_bound hα hα4 hm hc hInt hfar
    have hq28 : 28 ≤ radQ α m := by
      rw [radQ, le_div_iff₀ hα]
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      nlinarith
    have hq1 : 0 < 2 * radQ α m - 1 := by linarith
    have hT : 0 ≤ 2 / (2 * radQ α m - 1)
        * ((G1 α m c 1) ^ 2
          + (2 / (2 * radQ α m - 1)) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2)) := by
      have hPnn : 0 ≤ ∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2 :=
        setIntegral_nonneg measurableSet_Ioi (fun t _ => sq_nonneg _)
      have h2 : 0 ≤ 2 / (2 * radQ α m - 1) :=
        le_of_lt (div_pos (by norm_num) hq1)
      exact mul_nonneg h2 (add_nonneg (sq_nonneg _) (mul_nonneg h2 hPnn))
    have hsq : MeasureTheory.IntegrableOn (fun z : ℝ => (G1 α m c z) ^ 2) (Set.Ioi 1) :=
      radFar_integrableOn_Ioi_one_of_sq_interval_bound hT
        (T := 2 / (2 * radQ α m - 1)
          * ((G1 α m c 1) ^ 2
            + (2 / (2 * radQ α m - 1)) * (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2)))
        (fun z => sq_nonneg _) (hcont0.pow 2) hb
    exact radFar_integrableOn_mul_w_sq hsq
  · have hzero : ∀ z ∈ Set.Ioi (1 : ℝ),
        (fun z : ℝ => (0 : ℝ)) z = (G1 α m c z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
      intro z hz
      show (0 : ℝ) = (G1 α m c z) ^ 2 * (Work.Spaces.w z) ^ 2
      rw [Work.FTS.EllExist.Honesty.G1_eq_zero_of_not_integrableOn m hgood hz]
      ring
    exact IntegrableOn.congr_fun
      (integrableOn_zero : MeasureTheory.IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Set.Ioi 1))
      hzero measurableSet_Ioi

end Work.FTS.PhiStar.Honesty
