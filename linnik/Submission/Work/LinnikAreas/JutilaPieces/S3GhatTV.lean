import Mathlib
import Submission.Work.LinnikAreas.JutilaPieces.S3FloorDefs
import Submission.Work.LinnikAreas.JutilaPieces.S3GhatSup
import Submission.Work.LinnikAreas.JutilaPieces.HarmonicLogBound

set_option maxHeartbeats 2000000

namespace Work.LinnikAreas.JutilaPieces

open Finset

noncomputable section

/-- `κ_r = ⌊N/(q·r·t)⌋`. -/
def tvkap (N q r t : ℕ) : ℕ := N / (q * r * t)

/-- `u_r = r·κ_r`. -/
def tvu (N q r t : ℕ) : ℝ := (r : ℝ) * (tvkap N q r t : ℝ)

/-- `Y = N/(q·t)`. -/
def tvY (N q t : ℕ) : ℝ := (N : ℝ) / ((q : ℝ) * (t : ℝ))

/-- `L = log z + 1`, the logarithm scale. -/
def tvL (z : ℕ) : ℝ := Real.log (z : ℝ) + 1

/-- `A_r = log(κ_r·t/z) − 1`. -/
def tvA (z N q r t : ℕ) : ℝ := Real.log ((tvkap N q r t : ℝ) * (t : ℝ) / (z : ℝ)) - 1

/-- `B_r = log(κ_r·r/z) − 1 = log(u_r/z) − 1`. -/
def tvB (z N q r t : ℕ) : ℝ := Real.log ((tvkap N q r t : ℝ) * (r : ℝ) / (z : ℝ)) - 1

/-- `P_r = A_r·B_r + 1`. -/
def tvP (z N q r t : ℕ) : ℝ := tvA z N q r t * tvB z N q r t + 1

/-- `M = log(Y/z) − 1`. -/
def tvM (z N q t : ℕ) : ℝ := Real.log (tvY N q t / (z : ℝ)) - 1

/-- `M₂ = log(N/(q·z)) − 1`. -/
def tvM2 (z N q t : ℕ) : ℝ := Real.log ((N : ℝ) / ((q : ℝ) * (z : ℝ))) - 1

/-- Telescoping over `Icc 1 n`. -/
lemma tv_telescope (f : ℕ → ℝ) (n : ℕ) :
    (∑ r ∈ Finset.Icc 1 n, (f r - f (r+1))) = f 1 - f (n+1) := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_Icc_succ_top (f := fun r => f r - f (r+1)) (a := 1) (b := m) (by omega), ih]
      ring

/-- `κ` is antitone in `r`. -/
lemma tvkap_mono {N q r s t : ℕ} (hr : 0 < r) (hs : 0 < s) (hq : 0 < q) (ht : 0 < t)
    (hrs : r ≤ s) : tvkap N q s t ≤ tvkap N q r t := by
  rw [tvkap, tvkap]
  refine Nat.div_le_div le_rfl ?_ ?_
  · have h1 : r*t ≤ s*t := Nat.mul_le_mul hrs le_rfl
    have h2 : q*(r*t) ≤ q*(s*t) := Nat.mul_le_mul_left q h1
    simpa [mul_assoc] using h2
  · have : 0 < q*(r*t) := by positivity
    simpa [mul_assoc] using this.ne'

/-- `1 ≤ κ_r` iff `q·r·t ≤ N`. -/
lemma tvkap_ge_one {N q r t : ℕ} (hpos : 0 < q*r*t) (h : q*r*t ≤ N) :
    1 ≤ tvkap N q r t := by
  rw [tvkap]
  rw [Nat.le_div_iff_mul_le hpos]
  simpa using h

/-- `r·κ_r ≤ Y`. -/
lemma tvu_le_Y {N q r t : ℕ} (hq : 1 ≤ q) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    tvu N q r t ≤ tvY N q t := by
  have hqrt : 0 < q*r*t := by positivity
  have h1 := (div_cast_bounds N (q*r*t) hqrt).1
  rw [show ((q*r*t : ℕ) : ℝ) = (q:ℝ)*(r:ℝ)*(t:ℝ) by push_cast; ring] at h1
  have hY : tvY N q t = (r:ℝ) * ((N:ℝ)/((q:ℝ)*(r:ℝ)*(t:ℝ))) := by
    rw [tvY]; field_simp
  rw [tvu, hY]
  exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg r)

/-- `Y < r·κ_r + r`. -/
lemma tvu_gt {N q r t : ℕ} (hq : 1 ≤ q) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    tvY N q t < tvu N q r t + (r:ℝ) := by
  have hqrt : 0 < q*r*t := by positivity
  have h2 := (div_cast_bounds N (q*r*t) hqrt).2
  rw [show ((q*r*t : ℕ) : ℝ) = (q:ℝ)*(r:ℝ)*(t:ℝ) by push_cast; ring] at h2
  have hY : tvY N q t = (r:ℝ) * ((N:ℝ)/((q:ℝ)*(r:ℝ)*(t:ℝ))) := by
    rw [tvY]; field_simp
  rw [tvu, hY]
  have hrpos : (0:ℝ) < (r:ℝ) := Nat.cast_pos.mpr (by omega)
  have h3 : (r:ℝ) * ((N:ℝ)/((q:ℝ)*(r:ℝ)*(t:ℝ)))
      < (r:ℝ) * (((N/(q*r*t) : ℕ) : ℝ) + 1) := mul_lt_mul_of_pos_left h2 hrpos
  rw [tvkap]
  linarith [h3]

/-- For `y ∈ [1/z, z]` (`z ≥ 2`): `|log y − 1| ≤ log z + 1`. -/
lemma tv_abs_log_sub_one_le {z : ℕ} {y : ℝ} (hz : 2 ≤ z)
    (hy1 : 1/(z:ℝ) ≤ y) (hy2 : y ≤ (z:ℝ)) : |Real.log y - 1| ≤ tvL z := by
  have hzpos : (0:ℝ) < (z:ℝ) := Nat.cast_pos.mpr (by omega)
  have hz1 : (1:ℝ) ≤ (z:ℝ) := by exact_mod_cast (by omega : 1 ≤ z)
  have hL0 : 0 ≤ Real.log (z:ℝ) := Real.log_nonneg hz1
  have h := s3_abs_log_le y (z:ℝ) hzpos hy1 hy2 hL0
  have h4 : |Real.log y - 1| ≤ |Real.log y| + 1 := by
    calc |Real.log y - 1| = |Real.log y + (-1)| := by ring_nf
      _ ≤ |Real.log y| + |(-1:ℝ)| := abs_add_le _ _
      _ = |Real.log y| + 1 := by rw [abs_neg, abs_one]
  rw [tvL]; linarith [h, h4]

/-- `κ_r·t ≤ N`. -/
lemma tvkap_mul_le (N q r t : ℕ) (hq : 1 ≤ q) (hr : 1 ≤ r) (ht : 1 ≤ t) :
    (tvkap N q r t : ℝ) * (t:ℝ) ≤ (N:ℝ) := by
  have hqrt : 0 < q*r*t := by positivity
  have h1 := (div_cast_bounds N (q*r*t) hqrt).1
  rw [show ((q*r*t : ℕ) : ℝ) = (q:ℝ)*(r:ℝ)*(t:ℝ) by push_cast; ring] at h1
  have ht0 : (0:ℝ) ≤ (t:ℝ) := Nat.cast_nonneg t
  have h2 : (tvkap N q r t : ℝ) * (t:ℝ)
      ≤ ((N:ℝ)/((q:ℝ)*(r:ℝ)*(t:ℝ))) * (t:ℝ) := mul_le_mul_of_nonneg_right h1 ht0
  have hqR : (0:ℝ) < (q:ℝ) := Nat.cast_pos.mpr (by omega)
  have hrR : (0:ℝ) < (r:ℝ) := Nat.cast_pos.mpr (by omega)
  have htR : (0:ℝ) < (t:ℝ) := Nat.cast_pos.mpr (by omega)
  have h3 : ((N:ℝ)/((q:ℝ)*(r:ℝ)*(t:ℝ))) * (t:ℝ) ≤ (N:ℝ) := by
    have e : ((N:ℝ)/((q:ℝ)*(r:ℝ)*(t:ℝ))) * (t:ℝ)
        = (N:ℝ) * ((t:ℝ)/((q:ℝ)*(r:ℝ)*(t:ℝ))) := by ring
    rw [e]
    have hdiv : (t:ℝ)/((q:ℝ)*(r:ℝ)*(t:ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity : (0:ℝ) < (q:ℝ)*(r:ℝ)*(t:ℝ))]
      have h1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
      have h2 : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
      have hqr1 : (1:ℝ) ≤ (q:ℝ)*(r:ℝ) := by
        have := mul_le_mul h1 h2 (by norm_num : (0:ℝ) ≤ 1) (by linarith : (0:ℝ) ≤ (q:ℝ))
        simpa using this
      have h4 := mul_le_mul_of_nonneg_right hqr1 (Nat.cast_nonneg t)
      linarith [h4]
    have h5 := mul_le_mul_of_nonneg_left hdiv ((by positivity : (0:ℝ) ≤ (N:ℝ)))
    linarith [h5]
  linarith [h2, h3]
lemma tvA_abs_le {z N q r t : ℕ} (hz : 2 ≤ z) (hq : 1 ≤ q) (hr : 1 ≤ r) (ht : 1 ≤ t)
    (h1 : q*r*t ≤ N) (hNz : N < z*z) : |tvA z N q r t| ≤ tvL z := by
  have hzpos : (0:ℝ) < (z:ℝ) := Nat.cast_pos.mpr (by omega)
  have hpos : 0 < q*r*t := by positivity
  have hκ1 : (1:ℝ) ≤ (tvkap N q r t : ℝ) := by
    have h := tvkap_ge_one hpos h1
    exact_mod_cast h
  have ht1R : (1:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht
  have hκt1 : (1:ℝ) ≤ (tvkap N q r t : ℝ) * (t:ℝ) := by
    have h := mul_le_mul hκ1 ht1R (by norm_num : (0:ℝ) ≤ 1)
      (by linarith : (0:ℝ) ≤ (tvkap N q r t : ℝ))
    simpa using h
  have hκt : (tvkap N q r t : ℝ) * (t:ℝ) ≤ (N:ℝ) := tvkap_mul_le N q r t hq hr ht
  have hNcast : (N:ℝ) < (z:ℝ)*(z:ℝ) := by exact_mod_cast hNz
  have hy1 : (1:ℝ)/(z:ℝ) ≤ (tvkap N q r t : ℝ) * (t:ℝ)/(z:ℝ) := by
    rw [div_le_div_iff₀ hzpos hzpos]
    nlinarith [hκt1, hzpos]
  have hy2 : (tvkap N q r t : ℝ) * (t:ℝ)/(z:ℝ) ≤ (z:ℝ) := by
    rw [div_le_iff₀ hzpos]
    linarith [hκt, hNcast]
  exact tv_abs_log_sub_one_le hz hy1 hy2

lemma tvB_abs_le {z N q r t : ℕ} (hz : 2 ≤ z) (hq : 1 ≤ q) (hr : 1 ≤ r) (ht : 1 ≤ t)
    (h1 : q*r*t ≤ N) (hNz : N < z*z) : |tvB z N q r t| ≤ tvL z := by
  have hzpos : (0:ℝ) < (z:ℝ) := Nat.cast_pos.mpr (by omega)
  have hpos : 0 < q*r*t := by positivity
  have hκ1 : (1:ℝ) ≤ (tvkap N q r t : ℝ) := by
    have h := tvkap_ge_one hpos h1
    exact_mod_cast h
  have hr1R : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hκr1 : (1:ℝ) ≤ (tvkap N q r t : ℝ) * (r:ℝ) := by
    have h := mul_le_mul hκ1 hr1R (by norm_num : (0:ℝ) ≤ 1)
      (by linarith : (0:ℝ) ≤ (tvkap N q r t : ℝ))
    simpa using h
  have hYle : tvu N q r t ≤ tvY N q t := tvu_le_Y (N:=N) (q:=q) (r:=r) (t:=t) hq hr ht
  have hNcast : (N:ℝ) < (z:ℝ)*(z:ℝ) := by exact_mod_cast hNz
  have hqt1 : (1:ℝ) ≤ (q:ℝ)*(t:ℝ) := by
    have h1' : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
    have h2' : (1:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht
    have h := mul_le_mul h1' h2' (by norm_num : (0:ℝ) ≤ 1) (by linarith : (0:ℝ) ≤ (q:ℝ))
    simpa using h
  have hYlt : tvY N q t < (z:ℝ)*(z:ℝ) := by
    rw [tvY, div_lt_iff₀ (by positivity : (0:ℝ) < (q:ℝ)*(t:ℝ))]
    nlinarith [hNcast, hqt1]
  have hy1 : (1:ℝ)/(z:ℝ) ≤ (tvkap N q r t : ℝ) * (r:ℝ)/(z:ℝ) := by
    rw [div_le_div_iff₀ hzpos hzpos]
    nlinarith [hκr1, hzpos]
  have hy2 : (tvkap N q r t : ℝ) * (r:ℝ)/(z:ℝ) ≤ (z:ℝ) := by
    rw [div_le_iff₀ hzpos]
    rw [tvu] at hYle
    linarith [hYle, hYlt]
  exact tv_abs_log_sub_one_le hz hy1 hy2

lemma tvM_abs_le {z N q t : ℕ} (hz : 2 ≤ z) (hq : 1 ≤ q) (ht : 1 ≤ t) (htz : t ≤ N/(q*z))
    (hNz : N < z*z) : |tvM z N q t| ≤ tvL z := by
  have hzpos : (0:ℝ) < (z:ℝ) := Nat.cast_pos.mpr (by omega)
  have hNcast : (N:ℝ) < (z:ℝ)*(z:ℝ) := by exact_mod_cast hNz
  have hqt1 : (1:ℝ) ≤ (q:ℝ)*(t:ℝ) := by
    have h1' : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
    have h2' : (1:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht
    have h := mul_le_mul h1' h2' (by norm_num : (0:ℝ) ≤ 1) (by linarith : (0:ℝ) ≤ (q:ℝ))
    simpa using h
  have hYge : (z:ℝ) ≤ tvY N q t := by
    rw [tvY, le_div_iff₀ (by positivity : (0:ℝ) < (q:ℝ)*(t:ℝ))]
    have ht' : ((t*(q*z) : ℕ) : ℝ) ≤ (N:ℝ) := by
      exact_mod_cast (Nat.le_div_iff_mul_le (by positivity : 0 < q*z)).mp htz
    have h2 : ((t*(q*z) : ℕ) : ℝ) = (t:ℝ)*(q:ℝ)*(z:ℝ) := by push_cast; ring
    rw [h2] at ht'
    nlinarith [ht']
  have hY1 : (1:ℝ)/(z:ℝ) ≤ tvY N q t/(z:ℝ) := by
    rw [div_le_div_iff₀ hzpos hzpos]
    have hz1R : (1:ℝ) ≤ (z:ℝ) := by exact_mod_cast (by omega : 1 ≤ z)
    have hYone : (1:ℝ) ≤ tvY N q t := le_trans hz1R hYge
    have h := mul_le_mul_of_nonneg_right hYone hzpos.le
    linarith [h]
  have hY2 : tvY N q t/(z:ℝ) ≤ (z:ℝ) := by
    rw [div_le_iff₀ hzpos, tvY, div_le_iff₀ (by positivity : (0:ℝ) < (q:ℝ)*(t:ℝ))]
    nlinarith [hNcast, hqt1]
  exact tv_abs_log_sub_one_le hz hY1 hY2
/-- Elementary algebra: `r·(κ·P − x·W) = (r·κ)·P − Y·W` when `r·x = Y`. -/
lemma tv_alg (r κ x Y P W : ℝ) (h : r * x = Y) :
    r * (κ*P - x*W) = (r*κ)*P - Y*W := by
  have h1 : r * (κ*P) = (r*κ)*P := by ring
  have h2 : r * (x*W) = Y*W := by rw [← mul_assoc, h]
  rw [mul_sub, h1, h2]

/-- `s3Ghat` in the `u·P − Y·W` form. -/
lemma tv_ghat_eq (z N q r t : ℕ) (hz : 2 ≤ z) (hq : 1 ≤ q) (hr : 1 ≤ r) (ht : 1 ≤ t)
    (h1 : q*r*t ≤ N) :
    s3Ghat z N q r t
      = tvu N q r t * tvP z N q r t
        - tvY N q t * ((tvM2 z N q t - Real.log (r:ℝ)) * tvM z N q t + 1) := by
  have hzpos : (0:ℝ) < (z:ℝ) := Nat.cast_pos.mpr (by omega)
  have hrpos : (0:ℝ) < (r:ℝ) := Nat.cast_pos.mpr (by omega)
  have hNpos : (0:ℝ) < (N:ℝ) := by
    have h : 0 < N := lt_of_lt_of_le (by positivity : 0 < q*r*t) h1
    exact_mod_cast h
  have hqz : ((N:ℝ) / ((q:ℝ)*(z:ℝ))) ≠ 0 := by positivity
  have hzr : (r:ℝ) ≠ 0 := hrpos.ne'
  have hrt : ((q:ℝ)*(r:ℝ)*(t:ℝ)) ≠ 0 := by positivity
  have hlt : Real.log ((N:ℝ)/((q:ℝ)*(r:ℝ)*(t:ℝ)) * (t:ℝ) / (z:ℝ))
      = tvM2 z N q t - Real.log (r:ℝ) + 1 := by
    rw [tvM2]
    have hA : (N:ℝ)/((q:ℝ)*(r:ℝ)*(t:ℝ)) * (t:ℝ) / (z:ℝ)
        = ((N:ℝ)/((q:ℝ)*(z:ℝ)))/(r:ℝ) := by field_simp <;> ring
    rw [hA, Real.log_div hqz hzr]
    ring
  have hlr : Real.log ((N:ℝ)/((q:ℝ)*(r:ℝ)*(t:ℝ)) * (r:ℝ) / (z:ℝ))
      = tvM z N q t + 1 := by
    rw [tvM]
    have hA : (N:ℝ)/((q:ℝ)*(r:ℝ)*(t:ℝ)) * (r:ℝ) / (z:ℝ) = tvY N q t / (z:ℝ) := by
      rw [tvY]; field_simp <;> ring
    rw [hA]
    ring
  have hBF : s3Bfloor z N q r t = tvP z N q r t := by
    rw [s3Bfloor, tvP, tvA, tvB, tvkap]
  have hBC : s3Bcont z N q r t
      = (tvM2 z N q t - Real.log (r:ℝ)) * tvM z N q t + 1 := by
    rw [s3Bcont, hlt, hlr]
    ring
  have hrx : (r:ℝ) * ((N:ℝ)/((q:ℝ)*(r:ℝ)*(t:ℝ))) = tvY N q t := by
    rw [tvY]; field_simp <;> ring
  rw [s3Ghat, hBF, hBC, tvu, tvkap]
  exact tv_alg (r:ℝ) (tvkap N q r t : ℝ) ((N:ℝ)/((q:ℝ)*(r:ℝ)*(t:ℝ))) (tvY N q t)
    (tvP z N q r t) ((tvM2 z N q t - Real.log (r:ℝ)) * tvM z N q t + 1) hrx
/-- One-step difference of `s3Ghat` in the `u·P` variables. -/
lemma tv_ghat_diff {z N q t r : ℕ} (hz : 2 ≤ z) (hq : 1 ≤ q) (ht : 1 ≤ t) (hr : 1 ≤ r)
    (h1 : q*r*t ≤ N) (h2 : q*(r+1)*t ≤ N) :
    s3Ghat z N q (r+1) t - s3Ghat z N q r t
      = (tvu N q (r+1) t * tvP z N q (r+1) t - tvu N q r t * tvP z N q r t)
        + tvY N q t * tvM z N q t * Real.log (((r:ℝ)+1)/(r:ℝ)) := by
  have hrpos : (0:ℝ) < (r:ℝ) := Nat.cast_pos.mpr (by omega)
  have hlog : Real.log (((r:ℝ)+1)/(r:ℝ)) = Real.log ((r:ℝ)+1) - Real.log (r:ℝ) :=
    Real.log_div (by positivity) hrpos.ne'
  rw [tv_ghat_eq z N q (r+1) t hz hq (by omega) ht h2,
      tv_ghat_eq z N q r t hz hq hr ht h1, hlog]
  push_cast <;> ring
lemma tv_ghat_incr {z N q t r : ℕ} (hz : 2 ≤ z) (hq : 1 ≤ q) (ht : 1 ≤ t) (hr : 1 ≤ r)
    (h1 : q*r*t ≤ N) (h2 : q*(r+1)*t ≤ N) (htz : t ≤ N/(q*z)) (hNz : N < z*z) :
    |s3Ghat z N q (r+1) t - s3Ghat z N q r t|
      ≤ |tvu N q (r+1) t - tvu N q r t| * (tvL z ^ 2 + 1)
        + tvu N q r t * tvL z *
            (2 * |Real.log ((tvkap N q (r+1) t : ℝ) / (tvkap N q r t : ℝ))|
              + Real.log (((r:ℝ)+1)/(r:ℝ)))
        + tvY N q t * tvL z * Real.log (((r:ℝ)+1)/(r:ℝ)) := by
  have hzR : (0:ℝ) < (z:ℝ) := Nat.cast_pos.mpr (by omega)
  have htR : (0:ℝ) < (t:ℝ) := Nat.cast_pos.mpr (by omega)
  have hrR : (0:ℝ) < (r:ℝ) := Nat.cast_pos.mpr (by omega)
  have hL0 : 0 ≤ tvL z := by
    rw [tvL]
    have h : (0:ℝ) ≤ Real.log (z:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ z))
    linarith
  have hlogr0 : 0 ≤ Real.log (((r:ℝ)+1)/(r:ℝ)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hrR]
    linarith
  have hκpos : (0:ℝ) < (tvkap N q r t : ℝ) := by
    have h := tvkap_ge_one (by positivity : 0 < q*r*t) h1
    exact_mod_cast h
  have hκ'pos : (0:ℝ) < (tvkap N q (r+1) t : ℝ) := by
    have h := tvkap_ge_one (by positivity : 0 < q*(r+1)*t) h2
    exact_mod_cast h
  have hA : |tvA z N q r t| ≤ tvL z := tvA_abs_le hz hq hr ht h1 hNz
  have hA' : |tvA z N q (r+1) t| ≤ tvL z := tvA_abs_le hz hq (by omega) ht h2 hNz
  have hB : |tvB z N q r t| ≤ tvL z := tvB_abs_le hz hq hr ht h1 hNz
  have hB' : |tvB z N q (r+1) t| ≤ tvL z := tvB_abs_le hz hq (by omega) ht h2 hNz
  have hM : |tvM z N q t| ≤ tvL z := tvM_abs_le hz hq ht htz hNz
  have hAsub : tvA z N q (r+1) t - tvA z N q r t
      = Real.log ((tvkap N q (r+1) t : ℝ) / (tvkap N q r t : ℝ)) := by
    rw [tvA, tvA,
        Real.log_div (show (tvkap N q (r+1) t : ℝ) * (t:ℝ) ≠ 0 by positivity)
          (show (z:ℝ) ≠ 0 by positivity),
        Real.log_div (show (tvkap N q r t : ℝ) * (t:ℝ) ≠ 0 by positivity)
          (show (z:ℝ) ≠ 0 by positivity),
        Real.log_mul hκ'pos.ne' htR.ne', Real.log_mul hκpos.ne' htR.ne',
        Real.log_div hκ'pos.ne' hκpos.ne']
    ring
  have hBsub : tvB z N q (r+1) t - tvB z N q r t
      = Real.log ((tvkap N q (r+1) t : ℝ) / (tvkap N q r t : ℝ))
        + Real.log (((r:ℝ)+1)/(r:ℝ)) := by
    rw [tvB, tvB,
        Real.log_div (show (tvkap N q (r+1) t : ℝ) * (((r+1:ℕ):ℝ)) ≠ 0 by positivity)
          (show (z:ℝ) ≠ 0 by positivity),
        Real.log_div (show (tvkap N q r t : ℝ) * (r:ℝ) ≠ 0 by positivity)
          (show (z:ℝ) ≠ 0 by positivity),
        Real.log_mul hκ'pos.ne' (show (((r+1:ℕ):ℕ):ℝ) ≠ 0 by positivity),
        Real.log_mul hκpos.ne' hrR.ne',
        Real.log_div hκ'pos.ne' hκpos.ne',
        Real.log_div (show ((r:ℝ)+1) ≠ 0 by positivity) hrR.ne']
    push_cast <;> ring
  have hP : |tvP z N q (r+1) t| ≤ tvL z ^ 2 + 1 := by
    rw [tvP]
    have h0 : |tvA z N q (r+1) t * tvB z N q (r+1) t| ≤ tvL z * tvL z := by
      rw [abs_mul]
      exact mul_le_mul hA' hB' (abs_nonneg _) hL0
    calc |tvA z N q (r+1) t * tvB z N q (r+1) t + 1|
        ≤ |tvA z N q (r+1) t * tvB z N q (r+1) t| + |(1:ℝ)| := abs_add_le _ _
      _ ≤ tvL z * tvL z + 1 := by rw [abs_one]; linarith
      _ = tvL z ^ 2 + 1 := by ring
  have hPdiff : |tvP z N q (r+1) t - tvP z N q r t|
      ≤ tvL z * (2 * |Real.log ((tvkap N q (r+1) t : ℝ) / (tvkap N q r t : ℝ))|
          + Real.log (((r:ℝ)+1)/(r:ℝ))) := by
    have hid : tvP z N q (r+1) t - tvP z N q r t
        = (tvA z N q (r+1) t - tvA z N q r t) * tvB z N q (r+1) t
          + tvA z N q r t * (tvB z N q (r+1) t - tvB z N q r t) := by
      rw [tvP, tvP]; ring
    rw [hid, hAsub, hBsub]
    have h1' : |Real.log ((tvkap N q (r+1) t : ℝ) / (tvkap N q r t : ℝ))
          * tvB z N q (r+1) t|
        ≤ |Real.log ((tvkap N q (r+1) t : ℝ) / (tvkap N q r t : ℝ))| * tvL z := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hB' (abs_nonneg _)
    have h2' : |tvA z N q r t * (Real.log ((tvkap N q (r+1) t : ℝ) / (tvkap N q r t : ℝ))
          + Real.log (((r:ℝ)+1)/(r:ℝ)))|
        ≤ tvL z * (|Real.log ((tvkap N q (r+1) t : ℝ) / (tvkap N q r t : ℝ))|
          + Real.log (((r:ℝ)+1)/(r:ℝ))) := by
      rw [abs_mul]
      have h3 : |Real.log ((tvkap N q (r+1) t : ℝ) / (tvkap N q r t : ℝ))
            + Real.log (((r:ℝ)+1)/(r:ℝ))|
          ≤ |Real.log ((tvkap N q (r+1) t : ℝ) / (tvkap N q r t : ℝ))|
            + Real.log (((r:ℝ)+1)/(r:ℝ)) := by
        calc |Real.log ((tvkap N q (r+1) t : ℝ) / (tvkap N q r t : ℝ))
              + Real.log (((r:ℝ)+1)/(r:ℝ))|
            ≤ |Real.log ((tvkap N q (r+1) t : ℝ) / (tvkap N q r t : ℝ))|
              + |Real.log (((r:ℝ)+1)/(r:ℝ))| := abs_add_le _ _
          _ = |Real.log ((tvkap N q (r+1) t : ℝ) / (tvkap N q r t : ℝ))|
              + Real.log (((r:ℝ)+1)/(r:ℝ)) := by rw [abs_of_nonneg hlogr0]
      exact mul_le_mul hA h3 (by positivity) hL0
    calc |Real.log ((tvkap N q (r+1) t : ℝ) / (tvkap N q r t : ℝ)) * tvB z N q (r+1) t
          + tvA z N q r t * (Real.log ((tvkap N q (r+1) t : ℝ) / (tvkap N q r t : ℝ))
              + Real.log (((r:ℝ)+1)/(r:ℝ)))|
        ≤ |Real.log ((tvkap N q (r+1) t : ℝ) / (tvkap N q r t : ℝ)) * tvB z N q (r+1) t|
          + |tvA z N q r t * (Real.log ((tvkap N q (r+1) t : ℝ) / (tvkap N q r t : ℝ))
              + Real.log (((r:ℝ)+1)/(r:ℝ)))| := abs_add_le _ _
      _ ≤ |Real.log ((tvkap N q (r+1) t : ℝ) / (tvkap N q r t : ℝ))| * tvL z
          + tvL z * (|Real.log ((tvkap N q (r+1) t : ℝ) / (tvkap N q r t : ℝ))|
              + Real.log (((r:ℝ)+1)/(r:ℝ))) := add_le_add h1' h2'
      _ = tvL z * (2 * |Real.log ((tvkap N q (r+1) t : ℝ) / (tvkap N q r t : ℝ))|
              + Real.log (((r:ℝ)+1)/(r:ℝ))) := by ring
  have hY0 : (0:ℝ) ≤ tvY N q t := by rw [tvY]; positivity
  have hu0 : (0:ℝ) ≤ tvu N q r t := by rw [tvu]; positivity
  have habs : |tvu N q (r+1) t * tvP z N q (r+1) t - tvu N q r t * tvP z N q r t|
      ≤ |tvu N q (r+1) t - tvu N q r t| * (tvL z ^ 2 + 1)
        + tvu N q r t * tvL z *
            (2 * |Real.log ((tvkap N q (r+1) t : ℝ) / (tvkap N q r t : ℝ))|
              + Real.log (((r:ℝ)+1)/(r:ℝ))) := by
    have e1 : tvu N q (r+1) t * tvP z N q (r+1) t - tvu N q r t * tvP z N q r t
        = (tvu N q (r+1) t - tvu N q r t) * tvP z N q (r+1) t
          + tvu N q r t * (tvP z N q (r+1) t - tvP z N q r t) := by ring
    rw [e1]
    have h1'' : |(tvu N q (r+1) t - tvu N q r t) * tvP z N q (r+1) t|
        ≤ |tvu N q (r+1) t - tvu N q r t| * (tvL z ^ 2 + 1) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hP (abs_nonneg _)
    have h2'' : |tvu N q r t * (tvP z N q (r+1) t - tvP z N q r t)|
        ≤ tvu N q r t * tvL z *
            (2 * |Real.log ((tvkap N q (r+1) t : ℝ) / (tvkap N q r t : ℝ))|
              + Real.log (((r:ℝ)+1)/(r:ℝ))) := by
      have h := mul_le_mul_of_nonneg_left hPdiff hu0
      have heq : tvu N q r t * (tvL z * (2 * |Real.log ((tvkap N q (r+1) t : ℝ) / (tvkap N q r t : ℝ))|
              + Real.log (((r:ℝ)+1)/(r:ℝ))))
          = tvu N q r t * tvL z * (2 * |Real.log ((tvkap N q (r+1) t : ℝ) / (tvkap N q r t : ℝ))|
              + Real.log (((r:ℝ)+1)/(r:ℝ))) := by ring
      rw [abs_mul, abs_of_nonneg hu0, ← heq]
      exact h
    calc |(tvu N q (r+1) t - tvu N q r t) * tvP z N q (r+1) t
          + tvu N q r t * (tvP z N q (r+1) t - tvP z N q r t)|
        ≤ |(tvu N q (r+1) t - tvu N q r t) * tvP z N q (r+1) t|
          + |tvu N q r t * (tvP z N q (r+1) t - tvP z N q r t)| := abs_add_le _ _
      _ ≤ _ := add_le_add h1'' h2''
  have habs2 : |tvY N q t * tvM z N q t * Real.log (((r:ℝ)+1)/(r:ℝ))|
      ≤ tvY N q t * tvL z * Real.log (((r:ℝ)+1)/(r:ℝ)) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hY0, abs_of_nonneg hlogr0]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM hY0) hlogr0
  rw [tv_ghat_diff hz hq ht hr h1 h2]
  calc |(tvu N q (r+1) t * tvP z N q (r+1) t - tvu N q r t * tvP z N q r t)
        + tvY N q t * tvM z N q t * Real.log (((r:ℝ)+1)/(r:ℝ))|
      ≤ |tvu N q (r+1) t * tvP z N q (r+1) t - tvu N q r t * tvP z N q r t|
        + |tvY N q t * tvM z N q t * Real.log (((r:ℝ)+1)/(r:ℝ))| := abs_add_le _ _
    _ ≤ |tvu N q (r+1) t - tvu N q r t| * (tvL z ^ 2 + 1)
        + tvu N q r t * tvL z *
            (2 * |Real.log ((tvkap N q (r+1) t : ℝ) / (tvkap N q r t : ℝ))|
              + Real.log (((r:ℝ)+1)/(r:ℝ)))
        + tvY N q t * tvL z * Real.log (((r:ℝ)+1)/(r:ℝ)) := by
        linarith [habs, habs2]
/-- Under the range hypotheses, `t ≤ z`. -/
lemma tv_t_le_z {z N q t : ℕ} (hz : 2 ≤ z) (hq : 1 ≤ q) (ht : 1 ≤ t) (htz : t ≤ N/(q*z))
    (hNz : N < z*z) : t ≤ z := by
  have hqz : 0 < q*z := by positivity
  have h1 : t*(q*z) ≤ N := (Nat.le_div_iff_mul_le hqz).mp htz
  have h2 : ((t*(q*z) : ℕ) : ℝ) ≤ (N:ℝ) := by exact_mod_cast h1
  have h3 : ((t*(q*z) : ℕ) : ℝ) = (t:ℝ)*(q:ℝ)*(z:ℝ) := by push_cast; ring
  rw [h3] at h2
  have h4 : (N:ℝ) < (z:ℝ)*(z:ℝ) := by exact_mod_cast hNz
  have hzR : (0:ℝ) < (z:ℝ) := Nat.cast_pos.mpr (by omega)
  have h5 : (t:ℝ)*(q:ℝ) < (z:ℝ) := by
    have h6 : ((t:ℝ)*(q:ℝ)*(z:ℝ))/(z:ℝ) < (z:ℝ) := by
      rw [div_lt_iff₀ hzR]; linarith [h2, h4]
    rwa [mul_div_cancel_right₀ _ hzR.ne'] at h6
  have hqR : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have htR : (0:ℝ) ≤ (t:ℝ) := Nat.cast_nonneg t
  have h7 : (t:ℝ) ≤ (t:ℝ)*(q:ℝ) := by nlinarith [htR, hqR]
  have h8 : (t:ℝ) < (z:ℝ) := lt_of_le_of_lt h7 h5
  exact_mod_cast (le_of_lt h8)

/-- `q·r·t ≤ N` when `r ≤ N/(q·z)` and `t ≤ z`. -/
lemma tv_mul_le_of_range {z N q t r : ℕ} (hq : 1 ≤ q) (hz : 2 ≤ z)
    (htz : t ≤ z) (hr : r ≤ N/(q*z)) : q*r*t ≤ N := by
  have hqz : 0 < q*z := by positivity
  have h1 : r*(q*z) ≤ N := (Nat.le_div_iff_mul_le hqz).mp hr
  have h2 : ((r*(q*z) : ℕ) : ℝ) ≤ (N:ℝ) := by exact_mod_cast h1
  have h3 : ((r*(q*z) : ℕ) : ℝ) = (r:ℝ)*(q:ℝ)*(z:ℝ) := by push_cast; ring
  rw [h3] at h2
  have htzR : (t:ℝ) ≤ (z:ℝ) := by exact_mod_cast htz
  have hqr0 : (0:ℝ) ≤ (q:ℝ)*(r:ℝ) := by positivity
  have h4 : (q:ℝ)*(r:ℝ)*(t:ℝ) ≤ (q:ℝ)*(r:ℝ)*(z:ℝ) :=
    mul_le_mul_of_nonneg_left htzR hqr0
  have h6 : (r:ℝ)*(q:ℝ)*(z:ℝ) = (q:ℝ)*(r:ℝ)*(z:ℝ) := by ring
  rw [h6] at h2
  have h5 : ((q*r*t : ℕ) : ℝ) = (q:ℝ)*(r:ℝ)*(t:ℝ) := by push_cast; ring
  have h7 : ((q*r*t : ℕ) : ℝ) ≤ (N:ℝ) := by rw [h5]; linarith [h2, h4]
  exact_mod_cast h7

/-- `Σ_{r=1}^{R-1} κ_{r+1} ≤ Y·(1 + log R)` for `R = N/(q·z)`. -/
lemma tv_sum_kap {z N q t : ℕ} (hq : 1 ≤ q) (ht : 1 ≤ t) (hR1 : 1 ≤ N/(q*z)) :
    (∑ r ∈ Finset.Icc 1 (N/(q*z) - 1), (tvkap N q (r+1) t : ℝ))
      ≤ tvY N q t * (1 + Real.log ((N/(q*z) : ℕ) : ℝ)) := by
  have hptw : ∀ r ∈ Finset.Icc 1 (N/(q*z) - 1),
      (tvkap N q (r+1) t : ℝ) ≤ tvY N q t * (1/(r:ℝ)) := by
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hrR : r ≤ N/(q*z) - 1 := (Finset.mem_Icc.mp hr).2
    have hrp : r+1 ≤ N/(q*z) := by omega
    have hpos : 0 < q*(r+1)*t := by positivity
    have h1 : ((N/(q*(r+1)*t) : ℕ) : ℝ) ≤ (N:ℝ)/((q:ℝ)*((r+1:ℕ):ℝ)*(t:ℝ)) := by
      have h := (div_cast_bounds N (q*(r+1)*t) hpos).1
      rwa [show ((q*(r+1)*t : ℕ) : ℝ) = (q:ℝ)*((r+1:ℕ):ℝ)*(t:ℝ) by push_cast; ring] at h
    have h2 : (N:ℝ)/((q:ℝ)*((r+1:ℕ):ℝ)*(t:ℝ)) ≤ tvY N q t * (1/(r:ℝ)) := by
      rw [tvY, mul_one_div]
      rw [le_div_iff₀ (by positivity : (0:ℝ) < (r:ℝ))]
      have hrw : (N:ℝ)/((q:ℝ)*((r+1:ℕ):ℝ)*(t:ℝ)) * (r:ℝ)
          = ((N:ℝ)*(r:ℝ))/((q:ℝ)*((r+1:ℕ):ℝ)*(t:ℝ)) := by ring
      rw [hrw, div_le_iff₀ (by positivity : (0:ℝ) < (q:ℝ)*((r+1:ℕ):ℝ)*(t:ℝ))]
      have hqne : (q:ℝ) ≠ 0 := by
        have : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
        exact this.ne'
      have htne : (t:ℝ) ≠ 0 := by
        have : (0:ℝ) < (t:ℝ) := by exact_mod_cast (by omega : 0 < t)
        exact this.ne'
      have hqtne : (q:ℝ)*(t:ℝ) ≠ 0 := mul_ne_zero hqne htne
      have hid : (N:ℝ)/((q:ℝ)*(t:ℝ)) * ((q:ℝ)*((r+1:ℕ):ℝ)*(t:ℝ))
          = (N:ℝ)*((r+1:ℕ):ℝ) := by
        have hre : (q:ℝ)*((r+1:ℕ):ℝ)*(t:ℝ) = ((q:ℝ)*(t:ℝ))*((r+1:ℕ):ℝ) := by ring
        rw [hre, ← mul_assoc, div_mul_cancel₀ _ hqtne]
      have hgoall : (N:ℝ) * (r:ℝ) ≤ (N:ℝ) * ((r+1:ℕ):ℝ) :=
        mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Nat.le_succ r)) (by positivity : (0:ℝ) ≤ (N:ℝ))
      linarith [hgoall, hid]
    rw [tvkap]
    linarith [h1, h2]
  calc (∑ r ∈ Finset.Icc 1 (N/(q*z) - 1), (tvkap N q (r+1) t : ℝ))
      ≤ ∑ r ∈ Finset.Icc 1 (N/(q*z) - 1), tvY N q t * (1/(r:ℝ)) := Finset.sum_le_sum hptw
    _ = tvY N q t * (∑ r ∈ Finset.Icc 1 (N/(q*z) - 1), (1/(r:ℝ))) := by rw [Finset.mul_sum]
    _ ≤ tvY N q t * (1 + Real.log (((N/(q*z) - 1 : ℕ) : ℝ))) := by
        have hY0 : 0 ≤ tvY N q t := by rw [tvY]; positivity
        have h := HarmonicLogBound (N/(q*z) - 1)
        exact mul_le_mul_of_nonneg_left h hY0
    _ ≤ tvY N q t * (1 + Real.log ((N/(q*z) : ℕ) : ℝ)) := by
        have hY0 : 0 ≤ tvY N q t := by rw [tvY]; positivity
        have hlog : Real.log (((N/(q*z) - 1 : ℕ) : ℝ)) ≤ Real.log ((N/(q*z) : ℕ) : ℝ) := by
          rcases Nat.eq_zero_or_pos (N/(q*z) - 1) with h0 | h0
          · rw [h0]; push_cast
            have h1 : (0:ℝ) ≤ Real.log ((N/(q*z) : ℕ) : ℝ) :=
              Real.log_nonneg (by exact_mod_cast hR1)
            rw [Real.log_zero]; linarith
          · apply Real.log_le_log
            · exact_mod_cast h0
            · exact_mod_cast Nat.sub_le _ _
        exact mul_le_mul_of_nonneg_left (by linarith) hY0
/-- Telescoping in the other direction. -/
lemma tv_telescope' (f : ℕ → ℝ) (n : ℕ) :
    (∑ r ∈ Finset.Icc 1 n, (f (r+1) - f r)) = f (n+1) - f 1 := by
  have h : (∑ r ∈ Finset.Icc 1 n, (f r - f (r+1))) = f 1 - f (n+1) := tv_telescope f n
  have h2 : (∑ r ∈ Finset.Icc 1 n, (f (r+1) - f r))
      = -(∑ r ∈ Finset.Icc 1 n, (f r - f (r+1))) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun r hr => by ring)
  rw [h2, h]; ring

/-- `Σ_{r=1}^{R-1} log((r+1)/r) = log R`. -/
lemma tv_sum_logr {R : ℕ} (hR : 1 ≤ R) :
    (∑ r ∈ Finset.Icc 1 (R-1), Real.log (((r+1:ℕ):ℝ)/(r:ℝ))) = Real.log (R:ℝ) := by
  have hptw : ∀ r ∈ Finset.Icc 1 (R-1),
      Real.log (((r+1:ℕ):ℝ)/(r:ℝ)) = Real.log (((r+1:ℕ):ℝ)) - Real.log ((r:ℝ)) := by
    intro r hr
    refine Real.log_div (by positivity) ?_
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have : (0:ℝ) < (r:ℝ) := by exact_mod_cast (by omega : 0 < r)
    exact this.ne'
  rw [Finset.sum_congr rfl hptw]
  have htel := tv_telescope' (fun r : ℕ => Real.log ((r:ℝ))) (R-1)
  have hcast : ((R-1)+1 : ℕ) = R := by omega
  rw [hcast] at htel
  have hlog1 : Real.log (((1:ℕ)):ℝ) = 0 := by simp
  rw [hlog1, sub_zero] at htel
  exact htel
/-- `Σ_{r=1}^{R-1} u_r·log((r+1)/r) ≤ Y·log R`. -/
lemma tv_sum_u_logr {z N q t : ℕ} (hq : 1 ≤ q) (ht : 1 ≤ t) (hR1 : 1 ≤ N/(q*z)) :
    (∑ r ∈ Finset.Icc 1 (N/(q*z) - 1),
        tvu N q r t * Real.log (((r+1:ℕ):ℝ)/(r:ℝ)))
      ≤ tvY N q t * Real.log ((N/(q*z) : ℕ) : ℝ) := by
  have hptw : ∀ r ∈ Finset.Icc 1 (N/(q*z) - 1),
      tvu N q r t * Real.log (((r+1:ℕ):ℝ)/(r:ℝ))
        ≤ tvY N q t * Real.log (((r+1:ℕ):ℝ)/(r:ℝ)) := by
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hrpos : (0:ℝ) < (r:ℝ) := by exact_mod_cast (by omega : 0 < r)
    have hlog0 : 0 ≤ Real.log (((r+1:ℕ):ℝ)/(r:ℝ)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hrpos]
      simpa using (Nat.cast_le.mpr (Nat.le_succ r) : ((r:ℕ):ℝ) ≤ ((r+1:ℕ):ℝ))
    exact mul_le_mul_of_nonneg_right (tvu_le_Y (N:=N) (q:=q) (r:=r) (t:=t) hq hr1 ht) hlog0
  calc (∑ r ∈ Finset.Icc 1 (N/(q*z) - 1),
        tvu N q r t * Real.log (((r+1:ℕ):ℝ)/(r:ℝ)))
      ≤ ∑ r ∈ Finset.Icc 1 (N/(q*z) - 1),
          tvY N q t * Real.log (((r+1:ℕ):ℝ)/(r:ℝ)) := Finset.sum_le_sum hptw
    _ = tvY N q t * (∑ r ∈ Finset.Icc 1 (N/(q*z) - 1),
          Real.log (((r+1:ℕ):ℝ)/(r:ℝ))) := by rw [Finset.mul_sum]
    _ = tvY N q t * Real.log ((N/(q*z) : ℕ) : ℝ) := by
        rw [tv_sum_logr (R := N/(q*z)) hR1]

/-- `Σ_{r=1}^{R-1} u_r·|log(κ_{r+1}/κ_r)| ≤ Y·(2 log z)`. -/
lemma tv_sum_u_abslog {z N q t : ℕ} (hq : 1 ≤ q) (ht : 1 ≤ t) (hz : 2 ≤ z)
    (hR1 : 1 ≤ N/(q*z)) (hNz : N < z*z) (htz : t ≤ N/(q*z)) :
    (∑ r ∈ Finset.Icc 1 (N/(q*z) - 1),
        tvu N q r t * |Real.log ((tvkap N q (r+1) t : ℝ)/(tvkap N q r t : ℝ))|)
      ≤ tvY N q t * (2 * Real.log (z:ℝ)) := by
  have hzt : t ≤ z := tv_t_le_z hz hq ht htz hNz
  have hz1R : (1:ℝ) ≤ (z:ℝ) := by exact_mod_cast (by omega : 1 ≤ z)
  have hzposR : (0:ℝ) < (z:ℝ) := Nat.cast_pos.mpr (by omega)
  have hL0 : 0 ≤ Real.log (z:ℝ) := Real.log_nonneg hz1R
  have hNcast : (N:ℝ) < (z:ℝ)*(z:ℝ) := by exact_mod_cast hNz
  have hqt1 : (1:ℝ) ≤ (q:ℝ)*(t:ℝ) := by
    have h1' : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
    have h2' : (1:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht
    have h := mul_le_mul h1' h2' (by norm_num : (0:ℝ) ≤ 1) (by linarith : (0:ℝ) ≤ (q:ℝ))
    simpa using h
  have hYlt : tvY N q t < (z:ℝ)*(z:ℝ) := by
    rw [tvY, div_lt_iff₀ (by positivity : (0:ℝ) < (q:ℝ)*(t:ℝ))]
    nlinarith [hNcast, hqt1]
  have hYge : (z:ℝ) ≤ tvY N q t := by
    rw [tvY, le_div_iff₀ (by positivity : (0:ℝ) < (q:ℝ)*(t:ℝ))]
    have ht' : ((t*(q*z) : ℕ) : ℝ) ≤ (N:ℝ) := by
      exact_mod_cast (Nat.le_div_iff_mul_le (by positivity : 0 < q*z)).mp htz
    have h2 : ((t*(q*z) : ℕ) : ℝ) = (t:ℝ)*(q:ℝ)*(z:ℝ) := by push_cast; ring
    rw [h2] at ht'
    nlinarith [ht']
  have hY0 : (0:ℝ) ≤ tvY N q t := by rw [tvY]; positivity
  have hY1 : (1:ℝ) ≤ tvY N q t := le_trans hz1R hYge
  have hlogY : Real.log (tvY N q t) ≤ 2 * Real.log (z:ℝ) := by
    have h1 : Real.log (tvY N q t) ≤ Real.log ((z:ℝ)*(z:ℝ)) :=
      Real.log_le_log (lt_of_lt_of_le zero_lt_one hY1) (le_of_lt hYlt)
    rw [Real.log_mul hzposR.ne' hzposR.ne'] at h1
    linarith
  have hk1 : Real.log ((tvkap N q 1 t : ℝ)) ≤ tvY N q t * 0 + Real.log (tvY N q t) := by
    have h1 : (tvkap N q 1 t : ℝ) ≤ tvY N q t := by
      rw [tvkap, tvY]
      have hA : ((N/(q*1*t) : ℕ) : ℝ) ≤ (N:ℝ)/(((q*1*t : ℕ)) : ℝ) :=
        (div_cast_bounds N (q*1*t) (by positivity)).1
      rw [show (((q*1*t : ℕ)) : ℝ) = (q:ℝ)*(t:ℝ) by push_cast; ring] at hA
      exact hA
    have h2 : (0:ℝ) < (tvkap N q 1 t : ℝ) := by
      have h := tvkap_ge_one (by positivity : 0 < q*1*t) (by
        simpa using tv_mul_le_of_range (t := t) (z := z) (N := N) (q := q) (r := 1) hq hz hzt hR1)
      exact_mod_cast h
    have h3 := Real.log_le_log h2 h1
    linarith [h3]
  have hptw : ∀ r ∈ Finset.Icc 1 (N/(q*z) - 1),
      tvu N q r t * |Real.log ((tvkap N q (r+1) t : ℝ)/(tvkap N q r t : ℝ))|
        ≤ tvY N q t * (Real.log ((tvkap N q r t : ℝ)) - Real.log ((tvkap N q (r+1) t : ℝ))) := by
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hrR : r ≤ N/(q*z) - 1 := (Finset.mem_Icc.mp hr).2
    have hrp : r+1 ≤ N/(q*z) := by omega
    have hmono : tvkap N q (r+1) t ≤ tvkap N q r t :=
      tvkap_mono (by omega) (by omega) (by omega) (by omega) (by omega)
    have hm : (tvkap N q (r+1) t : ℝ) ≤ (tvkap N q r t : ℝ) := by exact_mod_cast hmono
    have hpos : (0:ℝ) < (tvkap N q (r+1) t : ℝ) := by
      have h := tvkap_ge_one (by positivity : 0 < q*(r+1)*t) (tv_mul_le_of_range hq hz hzt hrp)
      exact_mod_cast h
    have hposr : (0:ℝ) < (tvkap N q r t : ℝ) := by
      have h := tvkap_ge_one (by positivity : 0 < q*r*t)
        (tv_mul_le_of_range hq hz hzt (by omega : r ≤ N/(q*z)))
      exact_mod_cast h
    have hlogeq : Real.log ((tvkap N q (r+1) t : ℝ)/(tvkap N q r t : ℝ))
        = Real.log ((tvkap N q (r+1) t : ℝ)) - Real.log ((tvkap N q r t : ℝ)) :=
      Real.log_div hpos.ne' hposr.ne'
    have hnonpos : Real.log ((tvkap N q (r+1) t : ℝ)/(tvkap N q r t : ℝ)) ≤ 0 := by
      rw [hlogeq]
      have hl := Real.log_le_log hpos hm
      linarith
    rw [abs_of_nonpos hnonpos, hlogeq, neg_sub]
    have hfac : 0 ≤ Real.log ((tvkap N q r t : ℝ)) - Real.log ((tvkap N q (r+1) t : ℝ)) := by linarith
    exact mul_le_mul_of_nonneg_right (tvu_le_Y (N:=N) (q:=q) (r:=r) (t:=t) hq hr1 ht) hfac
  have htel : (∑ r ∈ Finset.Icc 1 (N/(q*z) - 1),
        (Real.log ((tvkap N q r t : ℝ)) - Real.log ((tvkap N q (r+1) t : ℝ))))
      = Real.log ((tvkap N q 1 t : ℝ)) - Real.log ((tvkap N q (N/(q*z)) t : ℝ)) := by
    have h := tv_telescope (fun r : ℕ => Real.log ((tvkap N q r t : ℝ))) (N/(q*z) - 1)
    have hcast : ((N/(q*z) - 1) + 1 : ℕ) = N/(q*z) := by omega
    rw [hcast] at h
    exact h
  have hkR : 0 ≤ Real.log ((tvkap N q (N/(q*z)) t : ℝ)) := by
    apply Real.log_nonneg
    have h := tvkap_ge_one (by positivity : 0 < q*(N/(q*z))*t)
      (tv_mul_le_of_range hq hz hzt (Nat.le_refl _))
    exact_mod_cast h
  calc (∑ r ∈ Finset.Icc 1 (N/(q*z) - 1),
        tvu N q r t * |Real.log ((tvkap N q (r+1) t : ℝ)/(tvkap N q r t : ℝ))|)
      ≤ ∑ r ∈ Finset.Icc 1 (N/(q*z) - 1),
          tvY N q t * (Real.log ((tvkap N q r t : ℝ)) - Real.log ((tvkap N q (r+1) t : ℝ))) :=
        Finset.sum_le_sum hptw
    _ = tvY N q t * (∑ r ∈ Finset.Icc 1 (N/(q*z) - 1),
          (Real.log ((tvkap N q r t : ℝ)) - Real.log ((tvkap N q (r+1) t : ℝ)))) := by
        rw [Finset.mul_sum]
    _ = tvY N q t * (Real.log ((tvkap N q 1 t : ℝ)) - Real.log ((tvkap N q (N/(q*z)) t : ℝ))) := by
        rw [htel]
    _ ≤ tvY N q t * (2 * Real.log (z:ℝ)) := by
        have hk1' : Real.log ((tvkap N q 1 t : ℝ)) ≤ 2 * Real.log (z:ℝ) := by
          have h := hk1; simp only [mul_zero, zero_add] at h; exact le_trans h hlogY
        nlinarith [hk1', hkR, hY0]
/-- `Σ_{r=1}^{R-1} |u_{r+1} − u_r| ≤ 2Y(1 + log R) + Y`. -/
lemma tv_sum_absdu {z N q t : ℕ} (hq : 1 ≤ q) (ht : 1 ≤ t) (hz : 2 ≤ z) (hzt : t ≤ z)
    (hR1 : 1 ≤ N/(q*z)) :
    (∑ r ∈ Finset.Icc 1 (N/(q*z) - 1), |tvu N q (r+1) t - tvu N q r t|)
      ≤ 2 * (tvY N q t * (1 + Real.log ((N/(q*z) : ℕ) : ℝ))) + tvY N q t := by
  have hmax : ∀ r ∈ Finset.Icc 1 (N/(q*z) - 1),
      max 0 (tvu N q (r+1) t - tvu N q r t) ≤ (tvkap N q (r+1) t : ℝ) := by
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hmono : tvkap N q (r+1) t ≤ tvkap N q r t :=
      tvkap_mono (by omega) (by omega) (by omega) (by omega) (by omega)
    have hm : (tvkap N q (r+1) t : ℝ) ≤ (tvkap N q r t : ℝ) := by exact_mod_cast hmono
    have he : tvu N q (r+1) t - tvu N q r t
        = (tvkap N q (r+1) t : ℝ)
          + (r:ℝ) * ((tvkap N q (r+1) t : ℝ) - (tvkap N q r t : ℝ)) := by
      rw [tvu, tvu]; push_cast; ring
    have h2 : (r:ℝ) * ((tvkap N q (r+1) t : ℝ) - (tvkap N q r t : ℝ)) ≤ 0 := by
      have h0 : (0:ℝ) ≤ (r:ℝ) := by positivity
      have h1 : (tvkap N q (r+1) t : ℝ) - (tvkap N q r t : ℝ) ≤ 0 := by linarith
      nlinarith [h0, h1]
    have h3 : (0:ℝ) ≤ (tvkap N q (r+1) t : ℝ) := by positivity
    rw [he]
    exact max_le (by linarith) (by linarith)
  have hident : ∀ r ∈ Finset.Icc 1 (N/(q*z) - 1),
      |tvu N q (r+1) t - tvu N q r t|
        = 2 * max 0 (tvu N q (r+1) t - tvu N q r t) - (tvu N q (r+1) t - tvu N q r t) := by
    intro r hr
    rcases lt_or_ge (tvu N q (r+1) t - tvu N q r t) 0 with h | h
    · rw [abs_of_neg h, max_eq_left (le_of_lt h)]; ring
    · rw [abs_of_nonneg h, max_eq_right h]; ring
  have htel : (∑ r ∈ Finset.Icc 1 (N/(q*z) - 1), (tvu N q (r+1) t - tvu N q r t))
      = tvu N q (N/(q*z)) t - tvu N q 1 t := by
    have h := tv_telescope' (fun r : ℕ => tvu N q r t) (N/(q*z) - 1)
    have hcast : ((N/(q*z) - 1) + 1 : ℕ) = N/(q*z) := by omega
    rw [hcast] at h
    exact h
  have h1u : tvu N q 1 t ≤ tvY N q t := tvu_le_Y (N:=N) (q:=q) (r:=1) (t:=t) hq le_rfl ht
  have hRu : (0:ℝ) ≤ tvu N q (N/(q*z)) t := by rw [tvu]; positivity
  calc (∑ r ∈ Finset.Icc 1 (N/(q*z) - 1), |tvu N q (r+1) t - tvu N q r t|)
      = ∑ r ∈ Finset.Icc 1 (N/(q*z) - 1),
          (2 * max 0 (tvu N q (r+1) t - tvu N q r t)
            - (tvu N q (r+1) t - tvu N q r t)) := Finset.sum_congr rfl hident
    _ = 2 * (∑ r ∈ Finset.Icc 1 (N/(q*z) - 1), max 0 (tvu N q (r+1) t - tvu N q r t))
          - (∑ r ∈ Finset.Icc 1 (N/(q*z) - 1), (tvu N q (r+1) t - tvu N q r t)) := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ ≤ 2 * (tvY N q t * (1 + Real.log ((N/(q*z) : ℕ) : ℝ)))
          - (tvu N q (N/(q*z)) t - tvu N q 1 t) := by
        have hA : (∑ r ∈ Finset.Icc 1 (N/(q*z) - 1), max 0 (tvu N q (r+1) t - tvu N q r t))
            ≤ tvY N q t * (1 + Real.log ((N/(q*z) : ℕ) : ℝ)) :=
          le_trans (Finset.sum_le_sum hmax) (tv_sum_kap (N:=N) (q:=q) (t:=t) hq ht hR1)
        rw [htel]
        linarith [hA]
    _ ≤ 2 * (tvY N q t * (1 + Real.log ((N/(q*z) : ℕ) : ℝ))) + tvY N q t := by
        linarith [hRu, h1u]
/-- `1 ≤ N/(q·z)` under the range hypotheses. -/
lemma tv_R_ge_one {z N q t : ℕ} (hz : 1 ≤ z) (hq : 1 ≤ q) (ht : 1 ≤ t)
    (htz : t ≤ N/(q*z)) : 1 ≤ N/(q*z) := by
  have hq0 : 0 < q := by omega
  have hz0 : 0 < z := by omega
  have hqz : 0 < q*z := by positivity
  rw [Nat.le_div_iff_mul_le hqz]
  have h := (Nat.le_div_iff_mul_le hqz).mp htz
  calc 1*(q*z) = q*z := by ring
    _ ≤ t*(q*z) := le_mul_of_one_le_left (Nat.zero_le (q*z)) ht
    _ ≤ N := h

/-- `R = N/(q·z) ≤ Y = N/(q·t)`. -/
lemma tv_R_le_Y {z N q t : ℕ} (hq : 1 ≤ q) (ht : 1 ≤ t) (hzt : t ≤ z) :
    ((N/(q*z) : ℕ) : ℝ) ≤ tvY N q t := by
  have hqR : (0:ℝ) < (q:ℝ) := Nat.cast_pos.mpr (by omega)
  have hzR : (0:ℝ) < (z:ℝ) := Nat.cast_pos.mpr (by omega)
  have htR : (0:ℝ) < (t:ℝ) := Nat.cast_pos.mpr (by omega)
  have hqz : 0 < q*z := by
    have hq0 : 0 < q := by omega
    have hz0 : 0 < z := by omega
    positivity
  have hA : ((N/(q*z) : ℕ) : ℝ) ≤ (N:ℝ)/(((q*z:ℕ)):ℝ) :=
    (div_cast_bounds N (q*z) hqz).1
  rw [show (((q*z:ℕ)):ℝ) = (q:ℝ)*(z:ℝ) by push_cast; ring] at hA
  have hB : (N:ℝ)/((q:ℝ)*(z:ℝ)) ≤ tvY N q t := by
    have hqzR : (0:ℝ) < (q:ℝ)*(z:ℝ) := mul_pos hqR hzR
    rw [tvY, div_le_div_iff₀ hqzR (mul_pos hqR htR)]
    have htzR : (t:ℝ) ≤ (z:ℝ) := by exact_mod_cast hzt
    have hq0 : (0:ℝ) < (q:ℝ) := Nat.cast_pos.mpr (by omega)
    have hN0 : (0:ℝ) ≤ (N:ℝ) := by positivity
    have hNq0 : (0:ℝ) ≤ (N:ℝ)*(q:ℝ) := by positivity
    have h := mul_le_mul_of_nonneg_left htzR hNq0
    linarith [h]
  linarith [hA, hB]

/-- `log R ≤ 2 log z`. -/
lemma tv_logR_le {z N q t : ℕ} (hz : 2 ≤ z) (hq : 1 ≤ q) (ht : 1 ≤ t)
    (htz : t ≤ N/(q*z)) (hNz : N < z*z) :
    Real.log ((N/(q*z) : ℕ) : ℝ) ≤ 2 * Real.log (z:ℝ) := by
  have hzt : t ≤ z := tv_t_le_z hz hq ht htz hNz
  have hR1 : 1 ≤ N/(q*z) := tv_R_ge_one (by omega) hq ht htz
  have hRle : ((N/(q*z) : ℕ) : ℝ) ≤ tvY N q t :=
    tv_R_le_Y (N := N) (z := z) (q := q) (t := t) hq ht hzt
  have hz1 : (1:ℝ) ≤ (z:ℝ) := by exact_mod_cast (by omega : 1 ≤ z)
  have hz0 : (0:ℝ) < (z:ℝ) := Nat.cast_pos.mpr (by omega)
  have hNcast : (N:ℝ) < (z:ℝ)*(z:ℝ) := by exact_mod_cast hNz
  have hqt1 : (1:ℝ) ≤ (q:ℝ)*(t:ℝ) := by
    have h1' : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
    have h2' : (1:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht
    have h := mul_le_mul h1' h2' (by norm_num : (0:ℝ) ≤ 1) (by linarith : (0:ℝ) ≤ (q:ℝ))
    simpa using h
  have hYlt : tvY N q t < (z:ℝ)*(z:ℝ) := by
    rw [tvY, div_lt_iff₀ (by positivity : (0:ℝ) < (q:ℝ)*(t:ℝ))]
    nlinarith [hNcast, hqt1]
  have hY1 : (1:ℝ) ≤ tvY N q t := by
    have h := tv_R_le_Y (N := N) (z := z) (q := q) (t := t) hq ht hzt
    have h2 : (1:ℝ) ≤ ((N/(q*z) : ℕ) : ℝ) := by exact_mod_cast hR1
    linarith
  have hR0 : (0:ℝ) < ((N/(q*z) : ℕ) : ℝ) := by
    have h : (1:ℝ) ≤ ((N/(q*z) : ℕ) : ℝ) := by exact_mod_cast hR1
    linarith
  have h1 : Real.log ((N/(q*z) : ℕ) : ℝ) ≤ Real.log (tvY N q t) := Real.log_le_log hR0 hRle
  have h2 : Real.log (tvY N q t) ≤ 2 * Real.log (z:ℝ) := by
    have h := Real.log_le_log (lt_of_lt_of_le zero_lt_one hY1) (le_of_lt hYlt)
    rw [Real.log_mul hz0.ne' hz0.ne'] at h
    linarith
  linarith [h1, h2]
/-- The arithmetic at the end of the `S3GhatTV` bookkeeping. -/
lemma tv_arith (Y l r : ℝ) (hY : 0 ≤ Y) (hl : 0 ≤ l) (hr : r ≤ 2*l) :
    ((l+1)^2 + 1) * (2*(Y*(1+r)) + Y) + (l+1)*(2*(Y*(2*l)) + Y*r) + (l+1)*Y*r
      ≤ 16*Y*(l+1)^3 := by
  have h1 : (1:ℝ) ≤ l + 1 := by linarith
  have h0 : (0:ℝ) < l + 1 := by linarith
  have e1 : ((l+1)^2 + 1) * (2*(Y*(1+r)) + Y) ≤ 4*Y*(l+1)^3 + 4*(Y*(l+1)) := by
    have hh : 2*(Y*(1+r)) + Y ≤ 4 * (Y * (l+1)) := by nlinarith [hY, hl, hr]
    have h2 := mul_le_mul_of_nonneg_left hh (show (0:ℝ) ≤ (l+1)^2 + 1 by positivity)
    have h3 : ((l+1)^2 + 1) * (4 * (Y * (l+1))) = 4*Y*(l+1)^3 + 4*(Y*(l+1)) := by ring
    linarith [h2, h3]
  have e2 : (l+1)*(2*(Y*(2*l)) + Y*r) ≤ 6*Y*(l+1)^2 := by
    have hh : 2*(Y*(2*l)) + Y*r ≤ 6 * (Y * (l+1)) := by nlinarith [hY, hl, hr]
    have h2 := mul_le_mul_of_nonneg_left hh h0.le
    have h3 : (l+1) * (6 * (Y * (l+1))) = 6*Y*(l+1)^2 := by ring
    linarith [h2, h3]
  have e3 : (l+1)*Y*r ≤ 2*Y*(l+1)^2 := by
    have hh : Y*r ≤ 2 * (Y * (l+1)) := by nlinarith [hY, hl, hr]
    have h2 := mul_le_mul_of_nonneg_left hh h0.le
    have h3 : (l+1) * (2 * (Y * (l+1))) = 2*Y*(l+1)^2 := by ring
    linarith [h2, h3]
  have e4 : 4*Y*(l+1)^3 + 4*(Y*(l+1)) + 6*Y*(l+1)^2 + 2*Y*(l+1)^2 ≤ 16*Y*(l+1)^3 := by
    have hk : (4:ℝ) + 8*(l+1) ≤ 12*(l+1)^2 := by nlinarith [h1]
    have hYL : (0:ℝ) ≤ Y * (l+1) := mul_nonneg hY h0.le
    have h := mul_le_mul_of_nonneg_left hk hYL
    nlinarith [h]
  linarith [e1, e2, e3, e4]

theorem S3GhatTV :
    ∃ C : ℝ, 0 < C ∧ ∀ (z N q t : ℕ), 2 ≤ z → N < z * z →
      1 ≤ q → 1 ≤ t → t ≤ N / (q * z) →
      (∑ r ∈ Finset.Icc 1 (N / (q * z) - 1),
          |Work.LinnikAreas.JutilaPieces.s3Ghat z N q (r + 1) t
            - Work.LinnikAreas.JutilaPieces.s3Ghat z N q r t|)
        ≤ C * ((N : ℝ) / ((q : ℝ) * (t : ℝ))) * (Real.log (z : ℝ) + 2) ^ 3 := by
  refine ⟨16, by norm_num, ?_⟩
  intro z N q t hz hN hq ht htz
  have hzt : t ≤ z := tv_t_le_z hz hq ht htz hN
  have hR1 : 1 ≤ N/(q*z) := tv_R_ge_one (by omega) hq ht htz
  have hlogR : Real.log ((N/(q*z) : ℕ) : ℝ) ≤ 2 * Real.log (z:ℝ) :=
    tv_logR_le hz hq ht htz hN
  have hY0 : 0 ≤ tvY N q t := by rw [tvY]; positivity
  have hL0 : 0 ≤ Real.log (z:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ z))
  have hL1 : (1:ℝ) ≤ tvL z := by rw [tvL]; linarith
  have hL0' : 0 ≤ tvL z := le_trans zero_le_one hL1
  have hconv : ∀ r : ℕ, Real.log (((r+1:ℕ):ℝ)/(r:ℝ)) = Real.log (((r:ℝ)+1)/(r:ℝ)) := by
    intro r; congr 1; push_cast; ring
  have hsum1 : (∑ r ∈ Finset.Icc 1 (N/(q*z) - 1), |tvu N q (r+1) t - tvu N q r t|)
      ≤ 2 * (tvY N q t * (1 + Real.log ((N/(q*z) : ℕ) : ℝ))) + tvY N q t :=
    tv_sum_absdu hq ht hz hzt hR1
  have hsum2 : (∑ r ∈ Finset.Icc 1 (N/(q*z) - 1),
        tvu N q r t * |Real.log ((tvkap N q (r+1) t : ℝ)/(tvkap N q r t : ℝ))|)
      ≤ tvY N q t * (2 * Real.log (z:ℝ)) := tv_sum_u_abslog hq ht hz hR1 hN htz
  have hsum3 : (∑ r ∈ Finset.Icc 1 (N/(q*z) - 1),
        tvu N q r t * Real.log ((((r+1:ℕ)):ℝ)/(r:ℝ)))
      ≤ tvY N q t * Real.log ((N/(q*z) : ℕ) : ℝ) := tv_sum_u_logr hq ht hR1
  have hsum4 : (∑ r ∈ Finset.Icc 1 (N/(q*z) - 1), Real.log ((((r+1:ℕ)):ℝ)/(r:ℝ)))
      = Real.log ((N/(q*z) : ℕ) : ℝ) := tv_sum_logr hR1
  have hsum3' : (∑ r ∈ Finset.Icc 1 (N/(q*z) - 1),
        tvu N q r t * Real.log (((r:ℝ)+1)/(r:ℝ)))
      ≤ tvY N q t * Real.log ((N/(q*z) : ℕ) : ℝ) := by
    have heq : (∑ r ∈ Finset.Icc 1 (N/(q*z) - 1),
          tvu N q r t * Real.log (((r:ℝ)+1)/(r:ℝ)))
        = (∑ r ∈ Finset.Icc 1 (N/(q*z) - 1),
          tvu N q r t * Real.log ((((r+1:ℕ)):ℝ)/(r:ℝ))) :=
      Finset.sum_congr rfl (fun r hr => by rw [← hconv r])
    rw [heq]; exact hsum3
  have hsum4' : (∑ r ∈ Finset.Icc 1 (N/(q*z) - 1), Real.log (((r:ℝ)+1)/(r:ℝ)))
      = Real.log ((N/(q*z) : ℕ) : ℝ) := by
    rw [← hsum4]
    exact Finset.sum_congr rfl (fun r hr => by rw [hconv r])
  have hptw : ∀ r ∈ Finset.Icc 1 (N/(q*z) - 1),
      |s3Ghat z N q (r+1) t - s3Ghat z N q r t|
        ≤ (tvL z ^ 2 + 1) * |tvu N q (r+1) t - tvu N q r t|
          + tvL z * (tvu N q r t * (2 * |Real.log ((tvkap N q (r+1) t : ℝ)/(tvkap N q r t : ℝ))|
              + Real.log (((r:ℝ)+1)/(r:ℝ))))
          + (tvL z * tvY N q t) * Real.log (((r:ℝ)+1)/(r:ℝ)) := by
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hrp : r+1 ≤ N/(q*z) := by have h := (Finset.mem_Icc.mp hr).2; omega
    have h1 : q*r*t ≤ N := tv_mul_le_of_range hq hz hzt (by omega : r ≤ N/(q*z))
    have h2 : q*(r+1)*t ≤ N := tv_mul_le_of_range hq hz hzt hrp
    have h := tv_ghat_incr hz hq ht hr1 h1 h2 htz hN
    have he : |tvu N q (r+1) t - tvu N q r t| * (tvL z ^ 2 + 1)
          + tvu N q r t * tvL z * (2 * |Real.log ((tvkap N q (r+1) t : ℝ) / (tvkap N q r t : ℝ))|
              + Real.log (((r:ℝ)+1)/(r:ℝ)))
          + tvY N q t * tvL z * Real.log (((r:ℝ)+1)/(r:ℝ))
        = (tvL z ^ 2 + 1) * |tvu N q (r+1) t - tvu N q r t|
          + tvL z * (tvu N q r t * (2 * |Real.log ((tvkap N q (r+1) t : ℝ) / (tvkap N q r t : ℝ))|
              + Real.log (((r:ℝ)+1)/(r:ℝ))))
          + (tvL z * tvY N q t) * Real.log (((r:ℝ)+1)/(r:ℝ)) := by ring
    linarith [h, he]
  have hmain : (∑ r ∈ Finset.Icc 1 (N/(q*z) - 1),
        |s3Ghat z N q (r+1) t - s3Ghat z N q r t|)
      ≤ 16 * tvY N q t * (Real.log (z:ℝ) + 1)^3 := by
    calc (∑ r ∈ Finset.Icc 1 (N/(q*z) - 1), |s3Ghat z N q (r+1) t - s3Ghat z N q r t|)
        ≤ ∑ r ∈ Finset.Icc 1 (N/(q*z) - 1),
            ((tvL z ^ 2 + 1) * |tvu N q (r+1) t - tvu N q r t|
              + tvL z * (tvu N q r t * (2 * |Real.log ((tvkap N q (r+1) t : ℝ)/(tvkap N q r t : ℝ))|
                  + Real.log (((r:ℝ)+1)/(r:ℝ))))
              + (tvL z * tvY N q t) * Real.log (((r:ℝ)+1)/(r:ℝ))) := Finset.sum_le_sum hptw
      _ = (tvL z ^ 2 + 1) * (∑ r ∈ Finset.Icc 1 (N/(q*z) - 1), |tvu N q (r+1) t - tvu N q r t|)
            + tvL z * (∑ r ∈ Finset.Icc 1 (N/(q*z) - 1),
                tvu N q r t * (2 * |Real.log ((tvkap N q (r+1) t : ℝ)/(tvkap N q r t : ℝ))|
                  + Real.log (((r:ℝ)+1)/(r:ℝ))))
            + (tvL z * tvY N q t) * (∑ r ∈ Finset.Icc 1 (N/(q*z) - 1),
                Real.log (((r:ℝ)+1)/(r:ℝ))) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
              ← Finset.mul_sum]
      _ ≤ (tvL z ^ 2 + 1) * (2 * (tvY N q t * (1 + Real.log ((N/(q*z) : ℕ) : ℝ))) + tvY N q t)
            + tvL z * (2 * (tvY N q t * (2 * Real.log (z:ℝ)))
                + tvY N q t * Real.log ((N/(q*z) : ℕ) : ℝ))
            + (tvL z * tvY N q t) * Real.log ((N/(q*z) : ℕ) : ℝ) := by
          have hBsplit : (∑ r ∈ Finset.Icc 1 (N/(q*z) - 1),
                tvu N q r t * (2 * |Real.log ((tvkap N q (r+1) t : ℝ)/(tvkap N q r t : ℝ))|
                  + Real.log (((r:ℝ)+1)/(r:ℝ))))
              = 2 * (∑ r ∈ Finset.Icc 1 (N/(q*z) - 1),
                    tvu N q r t * |Real.log ((tvkap N q (r+1) t : ℝ)/(tvkap N q r t : ℝ))|)
                + (∑ r ∈ Finset.Icc 1 (N/(q*z) - 1),
                    tvu N q r t * Real.log (((r:ℝ)+1)/(r:ℝ))) := by
            rw [Finset.mul_sum, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl (fun r hr => by ring)
          rw [hBsplit, hsum4']
          have hS1 : 2 * (∑ r ∈ Finset.Icc 1 (N/(q*z) - 1),
                tvu N q r t * |Real.log ((tvkap N q (r+1) t : ℝ)/(tvkap N q r t : ℝ))|)
              ≤ 2 * (tvY N q t * (2 * Real.log (z:ℝ))) :=
            mul_le_mul_of_nonneg_left hsum2 (by norm_num)
          nlinarith [hsum1, hS1, hsum3', hL0', hY0, hL1]
      _ ≤ 16 * tvY N q t * (Real.log (z:ℝ) + 1)^3 := by
          rw [tvL]
          exact tv_arith (tvY N q t) (Real.log (z:ℝ)) (Real.log ((N/(q*z) : ℕ) : ℝ))
            hY0 hL0 hlogR
  have hfin : (∑ r ∈ Finset.Icc 1 (N/(q*z) - 1),
        |s3Ghat z N q (r+1) t - s3Ghat z N q r t|)
      ≤ 16 * tvY N q t * (Real.log (z:ℝ) + 2)^3 := by
    have h1 : (Real.log (z:ℝ) + 1)^3 ≤ (Real.log (z:ℝ) + 2)^3 := by
      have h2 : Real.log (z:ℝ) + 1 ≤ Real.log (z:ℝ) + 2 := by linarith
      have h3 : (0:ℝ) ≤ Real.log (z:ℝ) + 1 := by linarith
      exact pow_le_pow_left₀ h3 h2 3
    have h4 : (0:ℝ) ≤ 16 * tvY N q t := by positivity
    nlinarith [hmain, h1, h4]
  exact hfin
