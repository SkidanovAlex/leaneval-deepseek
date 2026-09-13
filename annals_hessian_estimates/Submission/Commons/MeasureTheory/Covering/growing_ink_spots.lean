import Submission.Commons.Measure.HardyLittlewood.good_ball_cover
import Submission.Commons.Measure.HardyLittlewood.good_balls_cover_F

open MeasureTheory Metric

/-!
# Growing ink spots

A measure-theoretic covering lemma: if `E ⊆ F ⊆ B(0,R)` are open, every ball `D ⊆ B(0,R)`
which is more than `(1-δ)`-covered by the "ink" `E` is already contained in `F`, and the ink
has measure at most `(1-δ)` times the measure of the ambient ball, then the ink has measure at
most `(1-δ/5^d)` times the measure of `F`.

The proof covers `F` by the "good" balls `B(x, dist(x,Fᶜ))` (those that poke out of `F`), each
of which contains a `δ`-fraction of `F \ E`, and applies the Hardy–Littlewood weak-(1,1)
maximal inequality with its sharp constant `5^d` for Euclidean space.
-/

namespace Commons.MeasureTheory.Covering

theorem growing_ink_spots {d : ℕ} {R : ℝ} (hR : 0 < R)
    {E F : Set (EuclideanSpace ℝ (Fin d))}
    (hEopen : IsOpen E) (hFopen : IsOpen F) (hEF : E ⊆ F)
    (hFB : F ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hmain : ∀ (x : EuclideanSpace ℝ (Fin d)) (r : ℝ), 0 < r →
      Metric.ball x r ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R →
      ENNReal.ofReal (1 - δ) * MeasureTheory.volume (Metric.ball x r)
        < MeasureTheory.volume (Metric.ball x r ∩ E) → Metric.ball x r ⊆ F)
    (hsize : MeasureTheory.volume E ≤ ENNReal.ofReal (1 - δ) *
      MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R)) :
    MeasureTheory.volume E ≤ ENNReal.ofReal (1 - δ / 5 ^ d) * MeasureTheory.volume F := by
  rcases eq_or_ne F (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) R) with hF | hF
  · subst hF
    refine le_trans hsize ?_
    have hle : (1:ℝ) - δ ≤ 1 - δ / 5 ^ d := by
      have h5 : (1:ℝ) ≤ (5:ℝ)^d := one_le_pow₀ (by norm_num)
      rw [sub_le_sub_iff_left]; exact div_le_self hδ0.le h5
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hle) _
  · set V := ⋃ x ∈ {x ∈ F | Metric.infDist x (Fᶜ) < R - ‖x‖}, Metric.ball x (Metric.infDist x (Fᶜ)) with hV
    have hcov : F ⊆ ⋃ x ∈ {x ∈ F | Metric.infDist x (Fᶜ) < R - ‖x‖}, Metric.ball x (Metric.infDist x (Fᶜ)) :=
      Commons.Measure.HardyLittlewood.good_balls_cover_F (d:=d) (R:=R) hR hFopen hFB hF
    have hFU : MeasureTheory.volume F ≤ MeasureTheory.volume V := by
      rw [hV]; exact measure_mono hcov
    have hkey := Commons.Measure.HardyLittlewood.good_ball_cover (d:=d) (R:=R) (δ:=δ)
      hR hδ0 hδ1 hFopen hFB hEF hmain
    have hkeyV : ENNReal.ofReal δ * MeasureTheory.volume V ≤
        ENNReal.ofReal (5^d) * MeasureTheory.volume (F \ E) := by rw [hV]; exact hkey
    have h5pos : (0:ℝ) < (5:ℝ)^d := pow_pos (by norm_num) d
    have hcoef : ENNReal.ofReal (δ / 5 ^ d) = (ENNReal.ofReal ((5:ℝ)^d))⁻¹ * ENNReal.ofReal δ := by
      rw [← ENNReal.ofReal_inv_of_pos h5pos, ← ENNReal.ofReal_mul (inv_nonneg.mpr h5pos.le)]
      congr 1; rw [inv_mul_eq_div]
    have h5ne : ENNReal.ofReal ((5:ℝ)^d) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero]; linarith
    have hc : ENNReal.ofReal (δ / 5 ^ d) * MeasureTheory.volume V ≤ MeasureTheory.volume (F \ E) := by
      rw [hcoef, mul_assoc]
      calc (ENNReal.ofReal ((5:ℝ)^d))⁻¹ * (ENNReal.ofReal δ * MeasureTheory.volume V)
          ≤ (ENNReal.ofReal ((5:ℝ)^d))⁻¹ * (ENNReal.ofReal ((5:ℝ)^d) * MeasureTheory.volume (F\E)) :=
            mul_le_mul_right hkeyV _
        _ = MeasureTheory.volume (F \ E) := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel h5ne ENNReal.ofReal_ne_top, one_mul]
    have hTF : ENNReal.ofReal (δ/5^d) * MeasureTheory.volume F ≤ MeasureTheory.volume (F\E) :=
      le_trans (mul_le_mul_right hFU _) hc
    have hFE : MeasureTheory.volume F = MeasureTheory.volume E + MeasureTheory.volume (F \ E) := by
      conv_lhs => rw [← Set.union_sdiff_cancel hEF]
      rw [measure_union Set.disjoint_sdiff_right (hFopen.measurableSet.diff hEopen.measurableSet)]
    have hsum : MeasureTheory.volume E + ENNReal.ofReal (δ/5^d) * MeasureTheory.volume F ≤
        MeasureTheory.volume F := by
      calc MeasureTheory.volume E + ENNReal.ofReal (δ/5^d) * MeasureTheory.volume F
          ≤ MeasureTheory.volume E + MeasureTheory.volume (F \ E) := by gcongr
        _ = MeasureTheory.volume F := hFE.symm
    have hfinF : MeasureTheory.volume F < ⊤ :=
      lt_of_le_of_lt (measure_mono hFB) measure_ball_lt_top
    have hfin : ENNReal.ofReal (δ/5^d) * MeasureTheory.volume F ≠ ⊤ :=
      ne_top_of_lt (lt_of_le_of_lt hTF (lt_of_le_of_lt (measure_mono Set.sdiff_subset) hfinF))
    have h1a : (0:ℝ) ≤ 1 - δ/5^d := by
      have h5 : (1:ℝ) ≤ (5:ℝ)^d := one_le_pow₀ (by norm_num)
      have : δ/5^d ≤ 1 := by
        rw [div_le_one (pow_pos (by norm_num) d)]
        exact le_of_lt (lt_of_lt_of_le hδ1 h5)
      linarith
    have h1b : (0:ℝ) ≤ δ/5^d := by positivity
    have hid : ENNReal.ofReal (1 - δ/5^d) * MeasureTheory.volume F +
        ENNReal.ofReal (δ/5^d) * MeasureTheory.volume F = MeasureTheory.volume F := by
      rw [← add_mul]
      have h1 : ENNReal.ofReal (1 - δ/5^d) + ENNReal.ofReal (δ/5^d) = 1 := by
        rw [← ENNReal.ofReal_add h1a h1b]
        have : (1:ℝ) - δ/5^d + δ/5^d = 1 := by ring
        rw [this, ENNReal.ofReal_one]
      rw [h1, one_mul]
    have hle2 : MeasureTheory.volume E + ENNReal.ofReal (δ/5^d) * MeasureTheory.volume F ≤
        ENNReal.ofReal (1 - δ/5^d) * MeasureTheory.volume F + ENNReal.ofReal (δ/5^d) * MeasureTheory.volume F := by
      rw [hid]; exact hsum
    exact (ENNReal.add_le_add_iff_right hfin).mp hle2

end Commons.MeasureTheory.Covering
