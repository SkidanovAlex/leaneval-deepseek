import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 4000000

namespace Work.BoseBogFS

/-- Elementary real-arithmetic core of the Bogoliubov `MajC` estimate: bounds the
three-term expression by the four explicit monomials on the right, using only
`S ≥ 2W`, `W ≥ ulo/√2`, `ulo ≥ rlo²/8`, `V ≤ 4Vs/s`, `2D+2V ≤ 5r²`,
`uhi - ulo ≤ inc`, `vhi - vlo ≥ 0`, `Δ ≥ 0`, `2Δ ≤ r` and `d v = 0`. -/
theorem bogMajC_core {r Δ rlo rhi ulo uhi vlo vhi V D s W S Vs inc : ℝ}
    (hr0 : 0 < r) (hΔ0 : 0 ≤ Δ) (h2Δ : 2 * Δ ≤ r)
    (hrlo : rlo = r - Δ) (hrhi : rhi = r + Δ)
    (hrlo8 : rlo ^ 2 / 8 ≤ ulo)
    (huv : ulo / 2 ≤ ulo + 2 * vlo)
    (hW : W = Real.sqrt (ulo ^ 2 + 2 * ulo * vlo))
    (hS : S = ulo + vlo + W)
    (hV0 : 0 ≤ V) (hVs : V ≤ 4 * Vs / s) (hs0 : 0 < s)
    (huhi : uhi ≤ rlo ^ 2)
    (hvl : -(2 * Vs) ≤ vlo) (hdv : 0 ≤ vhi - vlo)
    (hD : 2 * D + 2 * V ≤ 5 * r ^ 2)
    (hinc : uhi - ulo ≤ inc) (hinc0 : 0 ≤ inc) :
    2 * (V ^ 2 / (S * W)) * (uhi - ulo)
      + 2 * (V * (2 * D + 2 * V) / (rlo ^ 2 * S) + V ^ 2 * (1 + uhi / W) / S ^ 2) * (vhi - vlo)
      + 2 * (V ^ 2 / 2) * (1 / rlo ^ 2 - 1 / rhi ^ 2)
    ≤ (2 * 10 ^ 5 * Vs ^ 2 * inc) / (s ^ 2 * r ^ 4)
      + (10 ^ 7 * Vs ^ 2 * (vhi - vlo)) / (s ^ 2 * r ^ 4)
      + (10 ^ 5 * Vs * (vhi - vlo)) / (s * r ^ 2)
      + (2 * 10 ^ 3 * Vs ^ 2 * Δ) / (s ^ 2 * r ^ 3) := by
  have hrlo_pos : 0 < rlo := by rw [hrlo]; linarith
  have hrhi_pos : 0 < rhi := by rw [hrhi]; linarith
  have hrlo_ge : r / 2 ≤ rlo := by rw [hrlo]; linarith
  have hrhi_ge : r ≤ rhi := by rw [hrhi]; linarith
  have hulo_pos : 0 < ulo := by
    have : 0 < rlo ^ 2 := by positivity
    linarith
  have hrad : 0 ≤ ulo ^ 2 + 2 * ulo * vlo := by nlinarith [hulo_pos, huv]
  have hWsq : W ^ 2 = ulo ^ 2 + 2 * ulo * vlo := by rw [hW, Real.sq_sqrt hrad]
  have hWpos : 0 < W := by
    rw [hW]; apply Real.sqrt_pos.mpr; nlinarith [hulo_pos, huv]
  have h2W2 : ulo ^ 2 ≤ 2 * W ^ 2 := by nlinarith [hWsq, hulo_pos, huv]
  have hW_ge : 2 * ulo / 3 ≤ W := by
    have h2 : (2 * ulo / 3) ^ 2 ≤ W ^ 2 := by nlinarith [h2W2, hulo_pos]
    have h3 : |2 * ulo / 3| ≤ |W| := sq_le_sq.mp h2
    rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * ulo / 3), abs_of_pos hWpos] at h3
  have hW_ge2 : rlo ^ 2 / 12 ≤ W := by
    have h2 : (rlo ^ 2 / 12) ^ 2 ≤ W ^ 2 := by nlinarith [h2W2, hrlo8, hulo_pos]
    have h3 : |rlo ^ 2 / 12| ≤ |W| := sq_le_sq.mp h2
    rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ rlo ^ 2 / 12), abs_of_pos hWpos] at h3
  have huv' : 0 ≤ ulo + vlo := by nlinarith [huv, hulo_pos]
  have hW_le : W ≤ ulo + vlo := by
    have h2 : W ^ 2 ≤ (ulo + vlo) ^ 2 := by nlinarith [hWsq, sq_nonneg vlo]
    have h3 : |W| ≤ |ulo + vlo| := sq_le_sq.mp h2
    rwa [abs_of_pos hWpos, abs_of_nonneg huv'] at h3
  have hS_ge2W : 2 * W ≤ S := by rw [hS]; linarith
  have hS_pos : 0 < S := by linarith
  have hS_ge : rlo ^ 2 / 6 ≤ S := by linarith
  have hSW_ge : ulo ^ 2 ≤ S * W := by
    have h1 : (2 * W) * W ≤ S * W := mul_le_mul_of_nonneg_right hS_ge2W (le_of_lt hWpos)
    nlinarith [h1, h2W2]
  have huhiW : 1 + uhi / W ≤ 13 := by
    have h1 : uhi ≤ 12 * W := by nlinarith [huhi, hrlo8, hW_ge, hulo_pos]
    have h2 : uhi / W ≤ 12 := by rw [div_le_iff₀ hWpos]; linarith
    linarith
  have hVs' : V * s ≤ 4 * Vs := (le_div_iff₀ hs0).mp hVs
  have hVs0 : 0 ≤ Vs := by
    have h0 : 0 ≤ V * s := mul_nonneg hV0 (le_of_lt hs0)
    nlinarith [h0, hVs']
  have hVs2 : 0 ≤ Vs ^ 2 := sq_nonneg Vs
  have hV2s2 : V ^ 2 * s ^ 2 ≤ 16 * Vs ^ 2 := by
    have h0 : 0 ≤ V * s := mul_nonneg hV0 (le_of_lt hs0)
    have h := pow_le_pow_left₀ h0 hVs' 2
    nlinarith [h]
  have hdS : 40 * r ^ 4 ≤ 10 ^ 5 * (rlo ^ 2 * S) := by
    have h1 : rlo ^ 2 * (rlo ^ 2 / 6) ≤ rlo ^ 2 * S :=
      mul_le_mul_of_nonneg_left hS_ge (sq_nonneg rlo)
    have h2 : r ^ 4 / 96 ≤ rlo ^ 4 / 6 := by
      have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ r / 2) hrlo_ge 4
      nlinarith [h]
    nlinarith [h1, h2]
  have hdS2 : 416 * r ^ 4 ≤ 10 ^ 7 * S ^ 2 := by
    have h1 : r ^ 2 / 24 ≤ S := by nlinarith [hS_ge, hrlo_ge, hrlo_pos]
    have h2 : (r ^ 2 / 24) ^ 2 ≤ S ^ 2 := by
      have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ r ^ 2 / 24) h1 2
      nlinarith [h]
    nlinarith [h2]
  have hSWb : 32 * r ^ 4 ≤ 2 * 10 ^ 5 * (S * W) := by
    have h8 : rlo ^ 2 ≤ 8 * ulo := by linarith
    have h1 : rlo ^ 4 ≤ 64 * ulo ^ 2 := by
      have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ rlo ^ 2) h8 2
      nlinarith [h]
    have h3 : r ^ 4 / 16 ≤ rlo ^ 4 := by
      have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ r / 2) hrlo_ge 4
      nlinarith [h]
    have h4 : r ^ 4 / 1024 ≤ S * W := by nlinarith [h1, h3, hSW_ge]
    nlinarith [h4]
  have hrh : r ^ 4 / 4 ≤ rlo ^ 2 * rhi ^ 2 := by
    have h1 : (r / 2) ^ 2 ≤ rlo ^ 2 := by
      have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ r / 2) hrlo_ge 2
      nlinarith [h]
    have h2 : r ^ 2 ≤ rhi ^ 2 := by
      have h := pow_le_pow_left₀ (le_of_lt hr0) hrhi_ge 2
      nlinarith [h]
    have h3 : (r / 2) ^ 2 * r ^ 2 ≤ rlo ^ 2 * rhi ^ 2 :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    nlinarith [h3]
  have hs2r4pos : 0 < s ^ 2 * r ^ 4 := by positivity
  have hr3pos : 0 < r ^ 3 := by positivity
  have hSWpos : 0 < S * W := mul_pos hS_pos hWpos
  have hrlo2pos : 0 < rlo ^ 2 := by positivity
  have hrhi2pos : 0 < rhi ^ 2 := by positivity
  have hrhi2prod : 0 < rlo ^ 2 * rhi ^ 2 := by positivity
  have hs2r3pos : 0 < s ^ 2 * r ^ 3 := by positivity
  have hSrloS : 0 < rlo ^ 2 * S := by positivity
  have hS2pos : 0 < S ^ 2 := by positivity
  have hsr2pos : 0 < s * r ^ 2 := by positivity
  have hT1 : 2 * (V ^ 2 / (S * W)) * (uhi - ulo) ≤
      (2 * 10 ^ 5 * Vs ^ 2 * inc) / (s ^ 2 * r ^ 4) := by
    have hcoef : 2 * (V ^ 2 / (S * W)) ≤ (2 * 10 ^ 5 * Vs ^ 2) / (s ^ 2 * r ^ 4) := by
      have e : 2 * (V ^ 2 / (S * W)) = (2 * V ^ 2) / (S * W) := by ring
      rw [e, div_le_div_iff₀ hSWpos hs2r4pos]
      have hA : 2 * V ^ 2 * (s ^ 2 * r ^ 4) ≤ 32 * Vs ^ 2 * r ^ 4 := by
        have h2 : 2 * (V ^ 2 * s ^ 2) ≤ 2 * (16 * Vs ^ 2) := by linarith [hV2s2]
        have h3 := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ r ^ 4)
        nlinarith [h3]
      have hB : 32 * Vs ^ 2 * r ^ 4 ≤ 2 * 10 ^ 5 * Vs ^ 2 * (S * W) := by
        have h3 := mul_le_mul_of_nonneg_left hSWb hVs2
        nlinarith [h3]
      linarith [hA, hB]
    calc 2 * (V ^ 2 / (S * W)) * (uhi - ulo)
        = (2 * (V ^ 2 / (S * W))) * (uhi - ulo) := by ring
      _ ≤ (2 * (V ^ 2 / (S * W))) * inc :=
            mul_le_mul_of_nonneg_left hinc (by positivity)
      _ ≤ ((2 * 10 ^ 5 * Vs ^ 2) / (s ^ 2 * r ^ 4)) * inc :=
            mul_le_mul_of_nonneg_right hcoef hinc0
      _ = (2 * 10 ^ 5 * Vs ^ 2 * inc) / (s ^ 2 * r ^ 4) := by ring
  have hT2a : 2 * (V * (2 * D + 2 * V) / (rlo ^ 2 * S)) * (vhi - vlo) ≤
      (10 ^ 5 * Vs * (vhi - vlo)) / (s * r ^ 2) := by
    have hcoef : 2 * (V * (2 * D + 2 * V) / (rlo ^ 2 * S)) ≤ (10 ^ 5 * Vs) / (s * r ^ 2) := by
      have e : 2 * (V * (2 * D + 2 * V) / (rlo ^ 2 * S)) =
          (2 * V * (2 * D + 2 * V)) / (rlo ^ 2 * S) := by ring
      rw [e, div_le_div_iff₀ hSrloS hsr2pos]
      have hA : 2 * V * (2 * D + 2 * V) * (s * r ^ 2) ≤ 40 * Vs * r ^ 4 := by
        have hV2nn : 0 ≤ 2 * V := by linarith
        have h1 : 2 * V * (2 * D + 2 * V) ≤ 2 * V * (5 * r ^ 2) :=
          mul_le_mul_of_nonneg_left hD hV2nn
        have h2 : 2 * V * (2 * D + 2 * V) * (s * r ^ 2) ≤ 2 * V * (5 * r ^ 2) * (s * r ^ 2) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
        have h4 : 10 * V * s * r ^ 4 ≤ 40 * Vs * r ^ 4 := by
          have h : 10 * (V * s) ≤ 10 * (4 * Vs) := mul_le_mul_of_nonneg_left hVs' (by norm_num)
          have h5 := mul_le_mul_of_nonneg_right h (by positivity : (0 : ℝ) ≤ r ^ 4)
          nlinarith [h5]
        nlinarith [h2, h4]
      have hB : 40 * Vs * r ^ 4 ≤ 10 ^ 5 * Vs * (rlo ^ 2 * S) := by
        have h := mul_le_mul_of_nonneg_left hdS hVs0
        nlinarith [h]
      linarith [hA, hB]
    calc 2 * (V * (2 * D + 2 * V) / (rlo ^ 2 * S)) * (vhi - vlo)
        = (2 * (V * (2 * D + 2 * V) / (rlo ^ 2 * S))) * (vhi - vlo) := by ring
      _ ≤ ((10 ^ 5 * Vs) / (s * r ^ 2)) * (vhi - vlo) :=
            mul_le_mul_of_nonneg_right hcoef hdv
      _ = (10 ^ 5 * Vs * (vhi - vlo)) / (s * r ^ 2) := by ring
  have hT2b : 2 * (V ^ 2 * (1 + uhi / W) / S ^ 2) * (vhi - vlo) ≤
      (10 ^ 7 * Vs ^ 2 * (vhi - vlo)) / (s ^ 2 * r ^ 4) := by
    have hcoef : 2 * (V ^ 2 * (1 + uhi / W) / S ^ 2) ≤ (10 ^ 7 * Vs ^ 2) / (s ^ 2 * r ^ 4) := by
      have e : 2 * (V ^ 2 * (1 + uhi / W) / S ^ 2) = (2 * V ^ 2 * (1 + uhi / W)) / S ^ 2 := by ring
      rw [e, div_le_div_iff₀ hS2pos hs2r4pos]
      have h1 : 2 * V ^ 2 * (1 + uhi / W) ≤ 2 * V ^ 2 * 13 :=
        mul_le_mul_of_nonneg_left huhiW (by positivity)
      have h6 : 2 * V ^ 2 * (1 + uhi / W) * (s ^ 2 * r ^ 4) ≤ 2 * V ^ 2 * 13 * (s ^ 2 * r ^ 4) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      have h2 : 2 * V ^ 2 * 13 * (s ^ 2 * r ^ 4) ≤ 416 * Vs ^ 2 * r ^ 4 := by
        have h3 : 26 * (V ^ 2 * s ^ 2) ≤ 26 * (16 * Vs ^ 2) := by linarith [hV2s2]
        have h4 := mul_le_mul_of_nonneg_right h3 (by positivity : (0 : ℝ) ≤ r ^ 4)
        nlinarith [h4]
      have h5 : 416 * Vs ^ 2 * r ^ 4 ≤ 10 ^ 7 * Vs ^ 2 * S ^ 2 := by
        have h := mul_le_mul_of_nonneg_left hdS2 hVs2
        nlinarith [h]
      linarith [h6, h2, h5]
    calc 2 * (V ^ 2 * (1 + uhi / W) / S ^ 2) * (vhi - vlo)
        = (2 * (V ^ 2 * (1 + uhi / W) / S ^ 2)) * (vhi - vlo) := by ring
      _ ≤ ((10 ^ 7 * Vs ^ 2) / (s ^ 2 * r ^ 4)) * (vhi - vlo) :=
            mul_le_mul_of_nonneg_right hcoef hdv
      _ = (10 ^ 7 * Vs ^ 2 * (vhi - vlo)) / (s ^ 2 * r ^ 4) := by ring
  have hT3 : 2 * (V ^ 2 / 2) * (1 / rlo ^ 2 - 1 / rhi ^ 2) ≤
      (2 * 10 ^ 3 * Vs ^ 2 * Δ) / (s ^ 2 * r ^ 3) := by
    have e2 : 2 * (V ^ 2 / 2) = V ^ 2 := by ring
    rw [e2]
    have e3 : V ^ 2 * (1 / rlo ^ 2 - 1 / rhi ^ 2) = (4 * V ^ 2 * r * Δ) / (rlo ^ 2 * rhi ^ 2) := by
      have h1 : 1 / rlo ^ 2 - 1 / rhi ^ 2 = (rhi ^ 2 - rlo ^ 2) / (rlo ^ 2 * rhi ^ 2) := by
        rw [div_sub_div _ _ (ne_of_gt hrlo2pos) (ne_of_gt hrhi2pos)]; ring
      have h2 : rhi ^ 2 - rlo ^ 2 = 4 * r * Δ := by rw [hrhi, hrlo]; ring
      rw [h1, h2]; ring
    rw [e3, div_le_div_iff₀ hrhi2prod hs2r3pos]
    have hA : 4 * V ^ 2 * r * Δ * (s ^ 2 * r ^ 3) ≤ 64 * Vs ^ 2 * Δ * r ^ 4 := by
      have h : 4 * (V ^ 2 * s ^ 2) ≤ 4 * (16 * Vs ^ 2) := by linarith [hV2s2]
      have h' := mul_le_mul_of_nonneg_right h (by positivity : (0 : ℝ) ≤ Δ * r ^ 4)
      nlinarith [h']
    have hB : 64 * Vs ^ 2 * Δ * r ^ 4 ≤ 2 * 10 ^ 3 * Vs ^ 2 * Δ * (rlo ^ 2 * rhi ^ 2) := by
      have hr4 : r ^ 4 ≤ 4 * (rlo ^ 2 * rhi ^ 2) := by linarith [hrh]
      have h : 64 * r ^ 4 ≤ 64 * (4 * (rlo ^ 2 * rhi ^ 2)) :=
        mul_le_mul_of_nonneg_left hr4 (by norm_num)
      have key : (64 : ℝ) * r ^ 4 ≤ 2 * 10 ^ 3 * (rlo ^ 2 * rhi ^ 2) := by linarith [h]
      have hnn : 0 ≤ Vs ^ 2 * Δ := by positivity
      calc 64 * Vs ^ 2 * Δ * r ^ 4 = Vs ^ 2 * Δ * (64 * r ^ 4) := by ring
        _ ≤ Vs ^ 2 * Δ * (2 * 10 ^ 3 * (rlo ^ 2 * rhi ^ 2)) := mul_le_mul_of_nonneg_left key hnn
        _ = 2 * 10 ^ 3 * Vs ^ 2 * Δ * (rlo ^ 2 * rhi ^ 2) := by ring
    linarith [hA, hB]
  have hT2 : 2 * (V * (2 * D + 2 * V) / (rlo ^ 2 * S) + V ^ 2 * (1 + uhi / W) / S ^ 2) *
        (vhi - vlo)
      ≤ (10 ^ 5 * Vs * (vhi - vlo)) / (s * r ^ 2) +
        (10 ^ 7 * Vs ^ 2 * (vhi - vlo)) / (s ^ 2 * r ^ 4) := by
    nlinarith [hT2a, hT2b]
  have hsum :
      2 * (V ^ 2 / (S * W)) * (uhi - ulo)
        + 2 * (V * (2 * D + 2 * V) / (rlo ^ 2 * S) + V ^ 2 * (1 + uhi / W) / S ^ 2) * (vhi - vlo)
        + 2 * (V ^ 2 / 2) * (1 / rlo ^ 2 - 1 / rhi ^ 2)
      ≤ (2 * 10 ^ 5 * Vs ^ 2 * inc) / (s ^ 2 * r ^ 4)
        + ((10 ^ 5 * Vs * (vhi - vlo)) / (s * r ^ 2) +
            (10 ^ 7 * Vs ^ 2 * (vhi - vlo)) / (s ^ 2 * r ^ 4))
        + (2 * 10 ^ 3 * Vs ^ 2 * Δ) / (s ^ 2 * r ^ 3) := by
    linarith [hT1, hT2, hT3]
  linarith [hsum]

end Work.BoseBogFS
