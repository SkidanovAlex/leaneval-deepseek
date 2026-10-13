/-
# The value bound `rgiB_abs_le_small` for the tail (growing) Green primitive

`Work.FTS.PhiStar.Series.rgiB α m c y = ∫_{t > y} c t · t^{-p-1} dt`, with `p = 2m/α > 0`.
Here the source `c` is *supported in `[a,b]`* (`hsupp`, `0 < a`) and bounded by `M` (`hb`).
Then for `y < a` the whole tail integral lives on `[a,b]`, and the sharp estimate is

  `|rgiB α m c y| ≤ M · a^{-p} / p`.

The proof is the elementary "dominate by the indicator of the support" argument:

* `‖∫_{t>y} f‖ ≤ ∫_{t>y} ‖f‖` (`norm_integral_le_integral_norm`);
* pointwise on `Ioi y`, `‖f t‖ = |c t|·t^{-p-1} ≤ (Icc a b).indicator (M · t^{-p-1}) t`:
  on the support use `|c t| ≤ M`, off it `c t = 0`;
* the majorant is integrable on `Ioi y` because `Ioi y ∩ Icc a b ⊆ Ioi (a/2)`
  (`0 < a`);
* `∫_{t>y} (Icc a b).indicator (M t^{-p-1}) = ∫_{t ∈ (y,∞) ∩ [a,b]} M t^{-p-1} ≤
   ∫_{t ≥ a} M t^{-p-1} = M ∫_{t > a} t^{-p-1} = M a^{-p}/p`,
  the last equality being `integral_Ioi_rpow_of_lt` with exponent `-p-1 < -1`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.PhiStar.Series.radGreenI_differentiableAt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

theorem rgiB_abs_le_small {α : ℝ} (hα : 0 < α) {m : ℕ} (hm : 1 ≤ m) {c : ℝ → ℝ} {M a b : ℝ}
    (hM : 0 ≤ M) (ha : 0 < a) (hb : ∀ t : ℝ, |c t| ≤ M)
    (hsupp : ∀ t : ℝ, c t ≠ 0 → t ∈ Set.Icc a b) :
    ∀ y : ℝ, 0 < y → y < a →
      |Work.FTS.PhiStar.Series.rgiB α m c y|
        ≤ M * a ^ (-(2 * (m : ℝ) / α)) / (2 * (m : ℝ) / α) := by
  intro y hy hya
  -- the exponent `p = 2m/α` of the Green kernel is positive
  set p : ℝ := 2 * (m : ℝ) / α with hpdef
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hp : 0 < p := by
    rw [hpdef]
    exact div_pos (by linarith) hα
  -- unfold `rgiB` into a set integral
  have hB : Work.FTS.PhiStar.Series.rgiB α m c y
      = ∫ t in Set.Ioi y, c t * t ^ (-p - 1) := by
    unfold Work.FTS.PhiStar.Series.rgiB Work.FTS.PhiStar.Series.rgiF2
    rw [← hpdef]
  rw [hB]
  -- step 1: bound the integral by the integral of the norm
  have h1 : |∫ t in Set.Ioi y, c t * t ^ (-p - 1)|
      ≤ ∫ t in Set.Ioi y, ‖c t * t ^ (-p - 1)‖ := by
    simpa only [Real.norm_eq_abs] using
      (MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioi y))
        (f := fun t : ℝ => c t * t ^ (-p - 1)))
  -- the majorant: `M t^{-p-1}` on the support `[a,b]` and `0` elsewhere
  set G : ℝ → ℝ := (Set.Icc a b).indicator (fun t => M * t ^ (-p - 1)) with hGdef
  have hpt : ∀ t ∈ Set.Ioi y, ‖c t * t ^ (-p - 1)‖ ≤ G t := by
    intro t ht
    have ht0 : 0 < t := lt_trans hy ht
    by_cases hmem : t ∈ Set.Icc a b
    · have hGt : G t = M * t ^ (-p - 1) := by
        rw [hGdef]; exact Set.indicator_of_mem hmem _
      rw [hGt, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
      exact mul_le_mul_of_nonneg_right (hb t) (Real.rpow_nonneg ht0.le _)
    · have hct : c t = 0 := by
        by_contra hne
        exact hmem (hsupp t hne)
      have hGt : G t = 0 := by
        rw [hGdef]; exact Set.indicator_of_notMem hmem _
      rw [hGt, hct, zero_mul, Real.norm_eq_abs, abs_zero]
  have ha2 : 0 < a / 2 := by linarith
  have hbase : IntegrableOn (fun t : ℝ => t ^ (-p - 1)) (Set.Ioi (a / 2)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith : -p - 1 < -1) ha2
  have hbaseM : IntegrableOn (fun t : ℝ => M * t ^ (-p - 1)) (Set.Ioi (a / 2)) :=
    hbase.const_mul M
  have hIccsub : Set.Icc a b ∩ Set.Ioi y ⊆ Set.Ioi (a / 2) := by
    intro t ht
    have h1 : a ≤ t := ht.1.1
    exact lt_of_lt_of_le (by linarith) h1
  have hinter : IntegrableOn (fun t : ℝ => M * t ^ (-p - 1)) (Set.Icc a b ∩ Set.Ioi y) :=
    hbaseM.mono_set hIccsub
  have hintG : IntegrableOn G (Set.Ioi y) := by
    rw [hGdef]
    exact (MeasureTheory.integrableOn_indicator_iff measurableSet_Icc).mpr hinter
  -- step 2: monotonicity of the set integral
  have h2 : ∫ t in Set.Ioi y, ‖c t * t ^ (-p - 1)‖ ≤ ∫ t in Set.Ioi y, G t :=
    MeasureTheory.setIntegral_mono_of_nonneg (fun t _ => norm_nonneg _) hpt hintG
  -- step 3: evaluate the majorant
  have h3 : ∫ t in Set.Ioi y, G t ≤ M * a ^ (-p) / p := by
    rw [hGdef, MeasureTheory.setIntegral_indicator measurableSet_Icc]
    have hrow : IntegrableOn (fun t : ℝ => t ^ (-p - 1)) (Set.Ioi a) :=
      integrableOn_Ioi_rpow_of_lt (by linarith : -p - 1 < -1) ha
    have hci : IntegrableOn (fun t : ℝ => t ^ (-p - 1)) (Set.Ici a) :=
      (integrableOn_Ici_iff_integrableOn_Ioi).mpr hrow
    have hciM : IntegrableOn (fun t : ℝ => M * t ^ (-p - 1)) (Set.Ici a) := hci.const_mul M
    have hle : ∫ t in Set.Ioi y ∩ Set.Icc a b, M * t ^ (-p - 1)
        ≤ ∫ t in Set.Ici a, M * t ^ (-p - 1) :=
      MeasureTheory.setIntegral_mono_set hciM
        (by
          filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
          exact mul_nonneg hM (Real.rpow_nonneg (le_trans ha.le ht) _))
        (Filter.Eventually.of_forall (fun t ht => ht.2.1))
    have hval : ∫ t in Set.Ici a, M * t ^ (-p - 1) = M * a ^ (-p) / p := by
      rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
      rw [MeasureTheory.integral_const_mul]
      rw [integral_Ioi_rpow_of_lt (a := -p - 1) (by linarith : -p - 1 < -1) ha]
      rw [show (-p - 1) + 1 = -p from by ring]
      rw [neg_div_neg_eq]
      ring
    linarith [hle, hval]
  exact le_trans (le_trans h1 h2) h3

end Work.FTS.PhiStar.Honesty
