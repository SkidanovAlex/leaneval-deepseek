import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Submission.Commons.Analysis.WeightedInterpolation.oscillation_sharp_bound

namespace Commons.Measure.WeightedInterpolation

open MeasureTheory Metric Set Filter
open scoped ENNReal

/-- Auxiliary average bound: if `f` is integrable on a finite-measure set `s` of positive volume and
`|f x - f y| ≤ a` on `s`, then `|f x|` is at most `a` plus the average of `|f|` over `s`. -/
private theorem abs_le_add_average {n : ℕ} {s : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)} {a : ℝ}
    (hsmeas : MeasurableSet s) (hfin : volume s < ∞) (hvolpos : 0 < (volume s).toReal)
    (hf : IntegrableOn f s volume) (hbound : ∀ y ∈ s, |f x - f y| ≤ a) :
    |f x| ≤ a + (∫ y in s, |f y|) / (volume s).toReal := by
  have hIntf : IntegrableOn (fun y => |f y|) s volume := hf.abs
  have hInta : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin n) => a) s volume :=
    IntegrableOn.of_bound hfin aestronglyMeasurable_const |a|
      (Eventually.of_forall (fun y => by simp [Real.norm_eq_abs]))
  have hIntSum : IntegrableOn (fun y => |f y| + a) s volume := hIntf.add hInta
  have hIntc : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin n) => |f x|) s volume :=
    IntegrableOn.of_bound hfin aestronglyMeasurable_const |f x|
      (Eventually.of_forall (fun y => by simp [Real.norm_eq_abs]))
  have hle : ∀ y ∈ s, |f x| ≤ |f y| + a := by
    intro y hy
    have h1 : |f x| ≤ |f x - f y| + |f y| := by
      calc |f x| = |(f x - f y) + f y| := by ring_nf
        _ ≤ |f x - f y| + |f y| := abs_add_le _ _
    linarith [hbound y hy]
  have hmono := setIntegral_mono_on hIntc hIntSum hsmeas hle
  have hcx : (∫ y in s, |f x|) = |f x| * (volume s).toReal := by
    rw [setIntegral_const, smul_eq_mul, measureReal_def]; ring
  have hsplit : (∫ y in s, (|f y| + a)) = (∫ y in s, |f y|) + (∫ y in s, a) := by
    rw [integral_add hIntf hInta]
  have hconst : (∫ y in s, a) = a * (volume s).toReal := by
    rw [setIntegral_const, smul_eq_mul, measureReal_def]; ring
  rw [hcx, hsplit, hconst] at hmono
  have hmain : (|f x| - a) * (volume s).toReal ≤ (∫ y in s, |f y|) := by
    have heq : (|f x| - a) * (volume s).toReal
        = |f x| * (volume s).toReal - a * (volume s).toReal := by ring
    rw [heq]; linarith
  have h4 : |f x| - a ≤ (∫ y in s, |f y|) / (volume s).toReal := by
    rw [le_div_iff₀ hvolpos]; exact hmain
  linarith

/-- Volume/scale ratio bound: with `c` the volume of the unit ball, the ratio `D^n / (r^n * c)`
(with `r = E*D/2^{n+1}`) is at most the target coefficient divided by `E^n`. -/
private theorem scale_ratio_bound_aux {n : ℕ} {D E c : ℝ} (hD : 0 < D) (hE : 0 < E) (hc : 0 < c) :
    D ^ n / ((E * D / 2 ^ (n + 1)) ^ n * c)
      ≤ ((2 ^ (n * (n + 2) + 2) + 2 ^ (n + 1)) / c + 1) / E ^ n := by
  have hL : D ^ n / ((E * D / 2 ^ (n + 1)) ^ n * c) = 2 ^ (n * (n + 1)) / (E ^ n * c) := by
    have h2pow : ((2:ℝ) ^ (n + 1)) ^ n = 2 ^ (n * (n + 1)) := by
      rw [← pow_mul, Nat.mul_comm (n+1) n]
    have h1 : (E * D / 2 ^ (n + 1)) ^ n = E ^ n * D ^ n / 2 ^ (n * (n + 1)) := by
      rw [div_pow, mul_pow, h2pow]
    rw [h1]
    field_simp
  rw [hL, div_le_iff₀ (mul_pos (pow_pos hE n) hc)]
  have hkey : (((2 ^ (n * (n + 2) + 2) + 2 ^ (n + 1)) / c + 1) / E ^ n) * (E ^ n * c)
      = (2 ^ (n * (n + 2) + 2) + 2 ^ (n + 1)) + c := by
    field_simp
  rw [hkey]
  have hmono : (2:ℝ) ^ (n * (n + 1)) ≤ (2:ℝ) ^ (n * (n + 2) + 2) := by
    apply pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num)
    have h : n * (n + 1) ≤ n * (n + 2) := Nat.mul_le_mul_left n (by omega)
    omega
  have hp : (0:ℝ) < 2 ^ (n+1) := by positivity
  linarith [hmono, hp, hc]

open MeasureTheory Metric Set Filter in
theorem weighted_le_interpolation {n : ℕ}
    {d : EuclideanSpace ℝ (Fin n) → ℝ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {K ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hK : 0 < K) (hΩ : IsOpen Ω)
    (hdpos : ∀ x ∈ Ω, 0 < d x) (hdball : ∀ x ∈ Ω, Metric.ball x (d x) ⊆ Ω)
    (hdlip : ∀ x y, |d x - d y| ≤ dist x y)
    (huint : IntegrableOn u Ω volume)
    (hlip : ∀ y ∈ Ω, ∀ z ∈ Ω, y ≠ z →
      (min (d y) (d z)) ^ (n + 1) * |u y - u z| / dist y z ≤ K)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Ω) :
    (d x) ^ n * |u x| ≤ ε * K +
      ((2 ^ (n * (n + 2) + 2) + 2 ^ (n + 1)) /
          (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal + 1)
        * ((∫ y in Ω, |u y|) / ε ^ n) := by
  classical
  have hDpos : 0 < d x := hdpos x hx
  have hcpos : 0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := by
    rw [ENNReal.toReal_pos_iff]
    refine ⟨Metric.measure_ball_pos volume 0 one_pos, ?_⟩
    exact lt_of_le_of_lt (measure_mono Metric.ball_subset_closedBall)
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).measure_lt_top
  set coeff : ℝ := ((2 ^ (n * (n + 2) + 2) + 2 ^ (n + 1)) /
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal + 1) with hcoeff
  -- the radius
  set r : ℝ := ε * d x / 2 ^ (n + 1) with hr
  have h2npos : (0:ℝ) < 2 ^ (n + 1) := by positivity
  have h2n1 : (2:ℝ) ≤ 2 ^ (n + 1) := by
    have h : (1:ℕ) ≤ n + 1 := by omega
    simpa using pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num) h
  have hrpos : 0 < r := by rw [hr]; positivity
  have hr_lt : r < d x := by
    have h1 : ε / 2 ^ (n + 1) < 1 := by
      rw [div_lt_one h2npos]; linarith
    calc r = (ε / 2 ^ (n + 1)) * d x := by rw [hr]; ring
      _ < 1 * d x := mul_lt_mul_of_pos_right h1 hDpos
      _ = d x := one_mul _
  have hdmr_pos : 0 < d x - r := sub_pos.mpr hr_lt
  have hBΩ : Metric.ball x r ⊆ Ω :=
    Subset.trans (Metric.ball_subset_ball hr_lt.le) (hdball x hx)
  have hBfin : volume (Metric.ball x r) < ∞ :=
    lt_of_le_of_lt (measure_mono Metric.ball_subset_closedBall)
      (isCompact_closedBall x r).measure_lt_top
  have hvbpos : 0 < (volume (Metric.ball x r)).toReal := by
    rw [ENNReal.toReal_pos_iff]
    exact ⟨Metric.measure_ball_pos volume x hrpos, hBfin⟩
  have hvb_eq : (volume (Metric.ball x r)).toReal
      = r ^ n * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := by
    have h := Measure.addHaar_ball_of_pos volume x hrpos
    rw [h, finrank_euclideanSpace, Fintype.card_fin, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (pow_nonneg hrpos.le n)]
  -- pointwise oscillation bound on the ball
  have hosc_nonneg : 0 ≤ K * r / (d x - r) ^ (n + 1) :=
    div_nonneg (mul_nonneg hK.le hrpos.le) (pow_nonneg hdmr_pos.le _)
  have hpoint : ∀ y ∈ Metric.ball x r, |u x - u y| ≤ K * r / (d x - r) ^ (n + 1) := by
    intro y hy
    have hdyx : dist y x < r := hy
    rcases eq_or_ne y x with rfl | hne
    · simp only [sub_self, abs_zero]; exact hosc_nonneg
    · have hyΩ : y ∈ Ω := hBΩ hy
      have hxy : x ≠ y := Ne.symm hne
      have hlipxy := hlip x hx y hyΩ hxy
      have hdy : d x - r < d y := by
        have h2 := (abs_le.mp (hdlip x y)).2
        have hdist : dist x y < r := by rw [dist_comm]; exact hdyx
        linarith
      have hmin : d x - r ≤ min (d x) (d y) := le_min (by linarith) hdy.le
      have hminpos : 0 < min (d x) (d y) := lt_of_lt_of_le hdmr_pos hmin
      have hdistpos : 0 < dist x y := dist_pos.mpr hxy
      have hKd : (min (d x) (d y)) ^ (n + 1) * |u x - u y| ≤ K * dist x y := by
        rw [div_le_iff₀ hdistpos] at hlipxy; exact hlipxy
      have hstep1 : |u x - u y| ≤ K * dist x y / (min (d x) (d y)) ^ (n + 1) := by
        rw [le_div_iff₀ (pow_pos hminpos _)]
        rw [mul_comm ((min (d x) (d y)) ^ (n + 1)) |u x - u y|] at hKd
        exact hKd
      have hstep2 : K * dist x y / (min (d x) (d y)) ^ (n + 1) ≤ K * r / (d x - r) ^ (n + 1) := by
        exact div_le_div₀ (mul_nonneg hK.le hrpos.le)
          (mul_le_mul_of_nonneg_left (by rw [dist_comm]; exact hdyx.le) hK.le)
          (pow_pos hdmr_pos _) (pow_le_pow_left₀ hdmr_pos.le hmin (n + 1))
      linarith
  -- average bound
  have hmain := abs_le_add_average (n := n) (s := Metric.ball x r) (f := u) (x := x)
    (a := K * r / (d x - r) ^ (n + 1)) isOpen_ball.measurableSet hBfin hvbpos
    (huint.mono_set hBΩ) hpoint
  -- oscillation term
  have hoscb : (d x) ^ n * (K * r / (d x - r) ^ (n + 1)) ≤ ε * K := by
    rw [hr]; exact Commons.Analysis.WeightedInterpolation.oscillation_sharp_bound hDpos hε hε1 hK
  -- integral term
  have hIBJ : (∫ y in Metric.ball x r, |u y|) ≤ ∫ y in Ω, |u y| :=
    setIntegral_mono_set huint.abs (Eventually.of_forall (fun y => abs_nonneg _))
      (Eventually.of_forall (fun y hy => hBΩ hy))
  have hratio : (d x) ^ n / (volume (Metric.ball x r)).toReal ≤ coeff / ε ^ n := by
    rw [hvb_eq, hr, hcoeff]
    exact scale_ratio_bound_aux hDpos hε hcpos
  have hint : (d x) ^ n * ((∫ y in Metric.ball x r, |u y|)
        / (volume (Metric.ball x r)).toReal) ≤ coeff * ((∫ y in Ω, |u y|) / ε ^ n) := by
    have hJnn : 0 ≤ ∫ y in Ω, |u y| := integral_nonneg (fun y => abs_nonneg _)
    have hfacnn : 0 ≤ (d x) ^ n / (volume (Metric.ball x r)).toReal :=
      div_nonneg (pow_nonneg hDpos.le n) hvbpos.le
    calc (d x) ^ n * ((∫ y in Metric.ball x r, |u y|) / (volume (Metric.ball x r)).toReal)
        = ((d x) ^ n / (volume (Metric.ball x r)).toReal) * (∫ y in Metric.ball x r, |u y|) := by
          ring
      _ ≤ ((d x) ^ n / (volume (Metric.ball x r)).toReal) * (∫ y in Ω, |u y|) :=
          mul_le_mul_of_nonneg_left hIBJ hfacnn
      _ ≤ (coeff / ε ^ n) * (∫ y in Ω, |u y|) := mul_le_mul_of_nonneg_right hratio hJnn
      _ = coeff * ((∫ y in Ω, |u y|) / ε ^ n) := by ring
  have hfinal : (d x) ^ n * |u x| ≤ ε * K + coeff * ((∫ y in Ω, |u y|) / ε ^ n) := by
    calc (d x) ^ n * |u x|
        ≤ (d x) ^ n * (K * r / (d x - r) ^ (n + 1)
            + (∫ y in Metric.ball x r, |u y|) / (volume (Metric.ball x r)).toReal) :=
          mul_le_mul_of_nonneg_left hmain (pow_nonneg hDpos.le n)
      _ = (d x) ^ n * (K * r / (d x - r) ^ (n + 1))
            + (d x) ^ n * ((∫ y in Metric.ball x r, |u y|)
              / (volume (Metric.ball x r)).toReal) := by ring
      _ ≤ ε * K + coeff * ((∫ y in Ω, |u y|) / ε ^ n) := add_le_add hoscb hint
  rwa [hcoeff] at hfinal

end Commons.Measure.WeightedInterpolation