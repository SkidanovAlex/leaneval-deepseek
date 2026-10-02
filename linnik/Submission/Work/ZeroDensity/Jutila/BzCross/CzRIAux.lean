import Mathlib
import Submission.Work.ZeroDensity.Jutila.BzCross.ModelBDefs
import Submission.Work.ZeroDensity.Jutila.BzCross.BzCrossDefs
import Submission.Work.ZeroDensity.Jutila.Bz3Defs
import Submission.Work.ZeroDensity.Jutila.KappaMertensDefs
import Submission.Work.ZeroDensity.Jutila.MertensMuDecay

/-!
# Auxiliary estimates for Region I of the two-sided `S₃` boundary term

`czRI w y N` is the part of the boundary sum on which the maximum `czLo w y r t` is attained by
`⌊y/r⌋`.  This file collects the pointwise and range facts used to bound it, together with the
"row" estimate: for squarefree `t`, the `r`-sum over `r ≤ min (⌊N/(q w)⌋) (czD w y t)` is
`−y ζ(2) κ(t)/t + O(y σ_{-1/2}(t) e^{−c√log Y_t} + Y_t)`.

The key pointwise input is that with `C = ⌊y/r⌋` and `γ = log(C r/y) ∈ [−log 2, 0]` one has
`log(C t/w) = log(Y_t/r) + γ`, hence
`czFI w y r t = (log(Y_t/r)−1)(γ−1) + γ(γ−1) + 1`,
which turns the sum into a multiple of `Σ (μ(r)/κ(r))(log(Y_t/r)−1)` (controlled by the
Mertens-type input `KappaMertensInput`) plus error terms of size `O(Y_t)`.
-/

namespace Work.ZeroDensity.Jutila.BzCross

open Finset
open Work.ZeroDensity.Jutila

noncomputable section

/-- `Y_t = y·t/w`: the scale of the `t`-th row. -/
def czY (w y : ℝ) (t : ℕ) : ℝ := y * (t : ℝ) / w

/-- `ε(R) = exp(−c√(log R))`: the de la Vallée Poussin envelope. -/
def czEps (c : ℝ) (x : ℝ) : ℝ := Real.exp (-(c * Real.sqrt (Real.log x)))

/-- `σ_{-1/2}(t) = Σ_{d | t} d^{-1/2}`. -/
def czSig (t : ℕ) : ℝ := ∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ)

/-- The row sum of `czRI` at `(q,t)`. -/
def czRowSum (w y : ℝ) (N q t : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (min (czR w N q) (czD w y t)),
    czMM r t * ((r : ℝ) / kap r) * ((t : ℝ) / kap t)
      * ((⌊y / (r : ℝ)⌋₊ : ℝ) * czFI w y r t)

lemma czRI_eq_sum_row (w y : ℝ) (N : ℕ) :
    czRI w y N = ∑ q ∈ Finset.Icc 1 (czQ y N), ∑ t ∈ Finset.Icc 1 (czT y N q),
      czRowSum w y N q t := rfl

/-! ## Elementary range facts -/

lemma czQ_pos {y : ℝ} {N : ℕ} (hy1 : 1 ≤ y) (hyN : y ≤ (N : ℝ)) : 1 ≤ czQ y N := by
  rw [czQ]
  apply Nat.le_floor
  rw [Nat.cast_one, le_div_iff₀ (by linarith only [hy1] : (0:ℝ) < y)]
  linarith only [hyN]

lemma czQ_cast_le {y : ℝ} {N : ℕ} (hy : 0 < y) :
    ((czQ y N : ℕ) : ℝ) ≤ (N : ℝ) / y := by
  rw [czQ]; exact Nat.floor_le (by positivity)

lemma czQ_mul_le {y : ℝ} {N : ℕ} (hy : 0 < y) :
    ((czQ y N : ℕ) : ℝ) * y ≤ (N : ℝ) := by
  have h := czQ_cast_le (N := N) hy
  have := (le_div_iff₀ hy).mp h
  linarith only [this]

lemma czQ_lt_w {w y : ℝ} {N : ℕ} (hw1 : 1 ≤ w) (hwy : w ≤ y) (hNwy : (N : ℝ) < w * y) :
    ((czQ y N : ℕ) : ℝ) < w := by
  have hw : 0 < w := by linarith only [hw1]
  have hy : 0 < y := by linarith only [hw1, hwy]
  have hQy := czQ_mul_le (N := N) hy
  nlinarith only [hNwy, hQy, hw1, hwy]


variable {w y : ℝ} {N q t r : ℕ}

lemma floor_ge_half {x : ℝ} (hx : 1 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  by_cases h : x < 2
  · have h1 : 1 ≤ ⌊x⌋₊ := by rw [Nat.one_le_floor_iff]; linarith only [hx]
    have h2 : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h1
    linarith only [h, h2]
  · push Not at h
    have h1 : x - 1 ≤ (⌊x⌋₊ : ℝ) := by
      have h2 := Nat.lt_floor_add_one x
      linarith only [h2]
    linarith only [h, h1]

lemma czR_pos (hw : 0 < w) (hwy : w ≤ y) (hy : 0 < y) (hq : 1 ≤ q) (hqQ : q ≤ czQ y N) :
    1 ≤ czR w N q := by
  have hqR : ((q : ℕ) : ℝ) ≤ (N : ℝ) / y :=
    le_trans (by exact_mod_cast hqQ) (czQ_cast_le (N := N) hy)
  have hqy : ((q : ℕ) : ℝ) * y ≤ (N : ℝ) := (le_div_iff₀ hy).mp hqR
  have h2 : ((q : ℕ) : ℝ) * w ≤ ((q : ℕ) : ℝ) * y :=
    mul_le_mul_of_nonneg_left hwy (Nat.cast_nonneg q)
  rw [czR]
  apply Nat.le_floor
  rw [Nat.cast_one, le_div_iff₀ (by positivity)]
  linarith only [hqy, h2]

lemma cz_r_lt_y (hw : 0 < w) (hy : 0 < y) (hNwy : (N : ℝ) < w * y) (hq : 1 ≤ q)
    (hr : r ≤ czR w N q) : (r : ℝ) < y := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hrR' : ((r : ℕ) : ℝ) ≤ ((czR w N q : ℕ) : ℝ) := by exact_mod_cast hr
  have hrR2 : ((czR w N q : ℕ) : ℝ) ≤ (N : ℝ) / ((q : ℝ) * w) := by
    rw [czR]; exact Nat.floor_le (by positivity)
  have hrR : (r : ℝ) ≤ (N : ℝ) / ((q : ℝ) * w) := hrR'.trans hrR2
  have h1 : (N : ℝ) / ((q : ℝ) * w) < y / (q : ℝ) := by
    have hyw : (N : ℝ) < y * w := by linarith only [hNwy]
    have hmul : (N : ℝ) * (q : ℝ) < y * w * (q : ℝ) :=
      mul_lt_mul_of_pos_right hyw hq0
    rw [div_lt_div_iff₀ (by positivity) hq0]
    calc (N : ℝ) * (q : ℝ) < y * w * (q : ℝ) := hmul
      _ = y * ((q : ℝ) * w) := by ring
  have h2 : y / (q : ℝ) ≤ y := by
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    rw [div_le_iff₀ hq0]
    linarith only [mul_le_mul_of_nonneg_left hq1 (le_of_lt hy), hq1, hy]
  linarith only [hrR', hrR2, h1, h2]

lemma czCr_ge_one (hry : (r : ℝ) ≤ y) (hr1 : 1 ≤ r) : 1 ≤ ⌊y / (r : ℝ)⌋₊ := by
  rw [Nat.one_le_floor_iff, le_div_iff₀ (by positivity)]
  linarith only [hry]

lemma czCr_mul_le {y : ℝ} {r : ℕ} (hy : 0 < y) (hr1 : 1 ≤ r) :
    (⌊y / (r : ℝ)⌋₊ : ℝ) * (r : ℝ) ≤ y := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have h : ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) ≤ y / (r : ℝ) := Nat.floor_le (by positivity)
  have := (le_div_iff₀ hr0).mp h
  linarith only [this]

lemma czCr_mul_gt_half {y : ℝ} {r : ℕ} (hy : 0 < y) (hr1 : 1 ≤ r) (hry : (r : ℝ) ≤ y) :
    y / 2 < (⌊y / (r : ℝ)⌋₊ : ℝ) * (r : ℝ) := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hC1 : (1 : ℝ) ≤ ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) := by
    have h1 : 1 ≤ ⌊y / (r : ℝ)⌋₊ := czCr_ge_one hry hr1
    exact_mod_cast h1
  have hsand : y < (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) + 1) * (r : ℝ) :=
    (div_lt_iff₀ hr0).mp (Nat.lt_floor_add_one _)
  have hCnn : (0 : ℝ) ≤ ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) := by linarith only [hC1]
  nlinarith only [hsand, hC1, hr0, mul_nonneg hCnn (le_of_lt hr0)]

lemma kap_ge_self {n : ℕ} (hn : Squarefree n) : (n : ℝ) ≤ kap n := by
  have hn0 : n ≠ 0 := hn.ne_zero
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn0)
  have h1 : kappa n = kap n := kappa_eq_kap_of_squarefree hn
  have h2 : pfac n * kappa n = (n : ℝ) := pfac_mul_kappa (n := n) hn0
  have h3 : 0 < pfac n := pfac_pos n
  have h4 : pfac n ≤ 1 := pfac_le_one n
  have h5 : 0 < kappa n := kappa_pos hn0
  have h6 : (n : ℝ) ≤ kappa n := by nlinarith only [h2, h4, h3]
  rw [← h1]
  exact h6


lemma cz_t_le_w (hy : 0 < y) (hNwy : (N : ℝ) < w * y) (hq : 1 ≤ q)
    (ht : (t : ℝ) ≤ (czT y N q : ℕ)) : (t : ℝ) ≤ w := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have ht' : (t : ℝ) ≤ (N : ℝ) / ((q : ℝ) * y) :=
    le_trans ht (by rw [czT]; exact Nat.floor_le (by positivity))
  have h1 : (N : ℝ) / ((q : ℝ) * y) ≤ w := by
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have hyq : y ≤ (q : ℝ) * y := by nlinarith only [hq1, hy]
    have hwpos : 0 < w := by
      by_contra h
      push Not at h
      have : w * y ≤ 0 := by nlinarith only [hNwy, hy, h]
      linarith only [hNwy, this]
    have h2 : w * y ≤ w * ((q : ℝ) * y) := mul_le_mul_of_nonneg_left hyq hwpos.le
    rw [div_le_iff₀ (by positivity)]
    linarith only [hNwy, h2]
  linarith only [ht', h1]

lemma czY_le_N_div_qw (hw : 0 < w) (hy : 0 < y) (hq : 1 ≤ q)
    (ht : (t : ℝ) ≤ (czT y N q : ℕ)) : czY w y t ≤ (N : ℝ) / ((q : ℝ) * w) := by
  have ht' : (t : ℝ) ≤ (N : ℝ) / ((q : ℝ) * y) :=
    le_trans ht (by rw [czT]; exact Nat.floor_le (by positivity))
  have h2 : (t : ℝ) * ((q : ℝ) * y) ≤ (N : ℝ) := (le_div_iff₀ (by positivity)).mp ht'
  unfold czY
  rw [div_le_div_iff₀ (by positivity) (by positivity : (0 : ℝ) < (q : ℝ) * w)]
  nlinarith only [h2, hy, hw]

lemma czD_pos (hw : 0 < w) (hwy : w ≤ y) (hy : 0 < y) (ht1 : 1 ≤ t)
    (htw : (t : ℝ) ≤ w) : 1 ≤ czD w y t := by
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  have hAle : ((⌊w / (t : ℝ)⌋₊ : ℕ) : ℝ) ≤ w / (t : ℝ) := Nat.floor_le (by positivity)
  have hApos : (0 : ℝ) < ((⌊w / (t : ℝ)⌋₊ : ℕ) : ℝ) := by
    have h1 : 1 ≤ ⌊w / (t : ℝ)⌋₊ := by
      rw [Nat.one_le_floor_iff, le_div_iff₀ ht0]
      norm_num
      linarith only [htw]
    exact_mod_cast h1
  have h1 : ((⌊w / (t : ℝ)⌋₊ : ℕ) : ℝ) ≤ y := by
    have h2 : w / (t : ℝ) ≤ w := by
      rw [div_le_iff₀ ht0]
      have ht1' : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht1
      linarith only [mul_le_mul_of_nonneg_left ht1' (le_of_lt hw), ht1', hw]
    linarith only [hwy, hAle, h2]
  rw [czD]
  apply Nat.le_floor
  rw [Nat.cast_one, le_div_iff₀ hApos]
  norm_num
  linarith only [h1]

lemma czD_ge (hw : 0 < w) (hy : 0 < y) (htw : (t : ℝ) ≤ w) (ht1 : 1 ≤ t) :
    czY w y t - 1 ≤ ((czD w y t : ℕ) : ℝ) := by
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  have hApos : (0 : ℝ) < ((⌊w / (t : ℝ)⌋₊ : ℕ) : ℝ) := by
    have h1 : 1 ≤ ⌊w / (t : ℝ)⌋₊ := by
      rw [Nat.one_le_floor_iff, le_div_iff₀ ht0]; linarith only [htw]
    exact_mod_cast h1
  have hAle : ((⌊w / (t : ℝ)⌋₊ : ℕ) : ℝ) ≤ w / (t : ℝ) := Nat.floor_le (by positivity)
  have h1 : czY w y t ≤ y / ((⌊w / (t : ℝ)⌋₊ : ℕ) : ℝ) := by
    have heq : czY w y t = y / (w / (t : ℝ)) := by unfold czY; field_simp
    rw [heq, div_le_div_iff₀ (by positivity) hApos]
    nlinarith only [hAle, hy]
  have h2 : y / ((⌊w / (t : ℝ)⌋₊ : ℕ) : ℝ) - 1 ≤ ((czD w y t : ℕ) : ℝ) := by
    have hfl := Nat.lt_floor_add_one (y / ((⌊w / (t : ℝ)⌋₊ : ℕ) : ℝ))
    rw [czD]
    linarith only [hfl]
  linarith only [h1, h2]

lemma czD_le (hw : 0 < w) (hy : 0 < y) (htw : (t : ℝ) ≤ w) (ht1 : 1 ≤ t) :
    ((czD w y t : ℕ) : ℝ) ≤ 2 * czY w y t := by
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  have hApos : (0 : ℝ) < ((⌊w / (t : ℝ)⌋₊ : ℕ) : ℝ) := by
    have h1 : 1 ≤ ⌊w / (t : ℝ)⌋₊ := by
      rw [Nat.one_le_floor_iff, le_div_iff₀ ht0]; linarith only [htw]
    exact_mod_cast h1
  have hx : (1 : ℝ) ≤ w / (t : ℝ) := by rw [le_div_iff₀ ht0]; linarith only [htw]
  have hAge : w / (2 * (t : ℝ)) ≤ ((⌊w / (t : ℝ)⌋₊ : ℕ) : ℝ) := by
    have h := floor_ge_half hx
    have heq : w / (t : ℝ) / 2 = w / (2 * (t : ℝ)) := by ring
    linarith only [h, heq]
  have hD : ((czD w y t : ℕ) : ℝ) ≤ y / ((⌊w / (t : ℝ)⌋₊ : ℕ) : ℝ) := by
    rw [czD]; exact Nat.floor_le (by positivity)
  have h2 : y / ((⌊w / (t : ℝ)⌋₊ : ℕ) : ℝ) ≤ y / (w / (2 * (t : ℝ))) := by
    rw [div_le_div_iff₀ hApos (by positivity)]
    nlinarith only [hAge, hy]
  have h3 : y / (w / (2 * (t : ℝ))) = 2 * czY w y t := by unfold czY; field_simp
  linarith only [hD, h2, h3]

lemma czR_ge (hw : 0 < w) (hy : 0 < y) (hq : 1 ≤ q) (ht : (t : ℝ) ≤ (czT y N q : ℕ)) :
    czY w y t - 1 ≤ ((czR w N q : ℕ) : ℝ) := by
  have hY := czY_le_N_div_qw hw hy hq ht
  have hR : (N : ℝ) / ((q : ℝ) * w) - 1 ≤ ((czR w N q : ℕ) : ℝ) := by
    rw [czR]
    have hfl := Nat.lt_floor_add_one ((N : ℝ) / ((q : ℝ) * w))
    linarith only [hfl]
  linarith only [hY, hR]

lemma cz_r1_ge (hw : 0 < w) (hwy : w ≤ y) (hy : 0 < y) (hNwy : (N : ℝ) < w * y)
    (hq : 1 ≤ q) (hqQ : q ≤ czQ y N) (ht : (t : ℝ) ≤ (czT y N q : ℕ)) (ht1 : 1 ≤ t) :
    czY w y t / 2 ≤ ((min (czR w N q) (czD w y t) : ℕ) : ℝ) := by
  have htw : (t : ℝ) ≤ w := cz_t_le_w hy hNwy hq ht
  have hge : czY w y t - 1 ≤ ((min (czR w N q) (czD w y t) : ℕ) : ℝ) := by
    rw [Nat.cast_min]
    exact le_min (czR_ge hw hy hq ht) (czD_ge hw hy htw ht1)
  have hmin1 : (1 : ℝ) ≤ ((min (czR w N q) (czD w y t) : ℕ) : ℝ) := by
    rw [Nat.cast_min]
    exact le_min (by exact_mod_cast czR_pos hw hwy hy hq hqQ)
      (by exact_mod_cast czD_pos hw hwy hy ht1 htw)
  by_cases h2 : czY w y t ≤ 2
  · linarith only [hge, hmin1]
  · push Not at h2
    linarith only [hge, h2]

lemma cz_r1_le (hw : 0 < w) (hy : 0 < y) (htw : (t : ℝ) ≤ w) (ht1 : 1 ≤ t) :
    ((min (czR w N q) (czD w y t) : ℕ) : ℝ) ≤ 2 * czY w y t := by
  have h1 : ((min (czR w N q) (czD w y t) : ℕ) : ℝ) ≤ ((czD w y t : ℕ) : ℝ) := by
    rw [Nat.cast_min]; exact min_le_right _ _
  linarith only [h1, czD_le hw hy htw ht1, hw, hy, htw, ht1]

lemma czT_pos (hy : 0 < y) (hq : 1 ≤ q) (hqQ : q ≤ czQ y N) : 1 ≤ czT y N q := by
  have hqR : ((q : ℕ) : ℝ) ≤ (N : ℝ) / y :=
    le_trans (by exact_mod_cast hqQ) (czQ_cast_le (N := N) hy)
  have hqy : ((q : ℕ) : ℝ) * y ≤ (N : ℝ) := (le_div_iff₀ hy).mp hqR
  rw [czT]
  apply Nat.le_floor
  rw [Nat.cast_one, le_div_iff₀ (by positivity)]
  linarith only [hqy]

lemma cz_t_lt_w (hw : 0 < w) (hy : 0 < y) (hNwy : (N : ℝ) < w * y)
    (hq : 1 ≤ q) (ht : (t : ℝ) ≤ (czT y N q : ℕ)) : (t : ℝ) < w := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have htR : (t : ℝ) ≤ (N : ℝ) / ((q : ℝ) * y) :=
    le_trans ht (by rw [czT]; exact Nat.floor_le (by positivity))
  have h2 : y ≤ (q : ℝ) * y := by
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    nlinarith only [hy, hq1]
  have h3 : (N : ℝ) / ((q : ℝ) * y) ≤ (N : ℝ) / y := by
    rw [div_le_div_iff₀ (by positivity) hy]
    nlinarith only [h2]
  have h4 : (N : ℝ) / y < w := by rw [div_lt_iff₀ hy]; linarith only [hNwy]
  linarith only [htR, h3, h4]

lemma czAt_pos (hw : 0 < w) (hy : 0 < y) (hNwy : (N : ℝ) < w * y)
    (hq : 1 ≤ q) (ht : (t : ℝ) ≤ (czT y N q : ℕ)) (ht1 : 1 ≤ t) :
    1 ≤ ⌊w / (t : ℝ)⌋₊ := by
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  have hlt : (t : ℝ) < w := cz_t_lt_w hw hy hNwy hq ht
  rw [Nat.one_le_floor_iff, le_div_iff₀ ht0]
  norm_num
  linarith only [hlt]

lemma czY_pos (hw : 0 < w) (hy : 0 < y) (ht : 1 ≤ t) : 0 < czY w y t := by
  have ht0 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  unfold czY; positivity

lemma czY_one_le (hw : 0 < w) (hwy : w ≤ y) (ht : 1 ≤ t) : 1 ≤ czY w y t := by
  have hyt : (1 : ℝ) ≤ y / w := by rw [le_div_iff₀ hw]; linarith only [hwy]
  have ht0 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  unfold czY
  have heq : y * (t : ℝ) / w = (y / w) * (t : ℝ) := by field_simp
  rw [heq]
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ (y / w) * (t : ℝ) := mul_le_mul hyt ht0 (by norm_num) (by positivity)

lemma czY_le_y (hw : 0 < w) (hy : 0 ≤ y) (htw : (t : ℝ) ≤ w) : czY w y t ≤ y := by
  unfold czY
  have h1 : (t : ℝ) / w ≤ 1 := by rw [div_le_one hw]; exact htw
  have heq : y * (t : ℝ) / w = y * ((t : ℝ) / w) := by ring
  rw [heq]
  calc y * ((t : ℝ) / w) ≤ y * 1 := mul_le_mul_of_nonneg_left h1 hy
    _ = y := by ring

lemma czEps_pos (c : ℝ) (x : ℝ) : 0 < czEps c x := Real.exp_pos _

lemma czX_nonneg {y : ℝ} {r : ℕ} (hy : 0 ≤ y) (hry : (r : ℝ) ≤ y) :
    0 ≤ y - ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * (r : ℝ) := by
  rcases Nat.eq_zero_or_pos r with h | h
  · subst h
    simp only [Nat.cast_zero, mul_zero, sub_zero]
    exact hy
  · have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast h
    have h1 := Nat.floor_le (show (0 : ℝ) ≤ y / (r : ℝ) by positivity)
    have h2 := (le_div_iff₀ hr0).mp h1
    linarith only [h2]

lemma czX_lt {y : ℝ} {r : ℕ} (hy : 0 < y) (hr1 : 1 ≤ r) :
    y - ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * (r : ℝ) < (r : ℝ) := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hfl : y / (r : ℝ) < ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have h2 : y < (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) + 1) * (r : ℝ) := (div_lt_iff₀ hr0).mp hfl
  have heq : (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) + 1) * (r : ℝ)
      = ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * (r : ℝ) + (r : ℝ) := by ring
  rw [heq] at h2
  linarith only [h2]

lemma floor_eq_one_of {x : ℝ} (h1 : 1 ≤ x) (h2 : x < 2) : ⌊x⌋₊ = 1 := by
  have h0 : (0 : ℝ) ≤ x := by linarith only [h1]
  have ha : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).mpr h1
  have hb : ⌊x⌋₊ < 2 := (Nat.floor_lt h0).mpr h2
  omega

lemma czX_le_half {y : ℝ} {r : ℕ} (hy : 0 < y) (hr1 : 1 ≤ r) (hry : (r : ℝ) ≤ y) :
    y - ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * (r : ℝ) ≤ y / 2 := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  by_cases h : (r : ℝ) ≤ y / 2
  · have hlt := czX_lt hy hr1
    linarith only [h, hlt]
  · push Not at h
    have hC : ⌊y / (r : ℝ)⌋₊ = 1 := by
      apply floor_eq_one_of
      · rw [le_div_iff₀ hr0]; linarith only [hry]
      · rw [div_lt_iff₀ hr0]; linarith only [h]
    rw [hC]
    norm_num
    linarith only [h]

lemma czGam_le_zero {y : ℝ} {r : ℕ} (hy : 0 < y) (hr1 : 1 ≤ r) (hry : (r : ℝ) ≤ y) :
    Real.log (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * (r : ℝ) / y) ≤ 0 := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hC1 : 1 ≤ ⌊y / (r : ℝ)⌋₊ := czCr_ge_one hry hr1
  have h2 : (0 : ℝ) < ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) := by
    have : 0 < ⌊y / (r : ℝ)⌋₊ := by omega
    exact_mod_cast this
  have hpos : 0 < ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * (r : ℝ) / y :=
    div_pos (mul_pos h2 hr0) hy
  have hle : ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * (r : ℝ) / y ≤ 1 := by
    rw [div_le_one hy]
    exact czCr_mul_le hy hr1
  exact Real.log_nonpos (le_of_lt hpos) hle

lemma czGam_neg_log_two_le {y : ℝ} {r : ℕ} (hy : 0 < y) (hr1 : 1 ≤ r)
    (hry : (r : ℝ) ≤ y) :
    -Real.log 2 ≤ Real.log (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * (r : ℝ) / y) := by
  have hhalf : (1 : ℝ) / 2 ≤ ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * (r : ℝ) / y := by
    rw [le_div_iff₀ hy]
    have hX := czX_le_half hy hr1 hry
    linarith only [hX]
  have h1 : Real.log (1 / 2) ≤ Real.log (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * (r : ℝ) / y) :=
    Real.log_le_log (by norm_num) hhalf
  have h2 : Real.log (1 / 2) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  linarith only [h1, h2 ▸ h1, h2]

lemma czGam_abs_le {y : ℝ} {r : ℕ} (hy : 0 < y) (hr1 : 1 ≤ r) (hry : (r : ℝ) ≤ y) :
    |Real.log (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * (r : ℝ) / y)| ≤ 2 * (r : ℝ) / y := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hle := czGam_le_zero hy hr1 hry
  rw [abs_of_nonpos hle]
  have hCpos : (0 : ℝ) < ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) := by
    have h1 : 1 ≤ ⌊y / (r : ℝ)⌋₊ := czCr_ge_one hry hr1
    have h2 : (1 : ℝ) ≤ ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
    linarith only [h2]
  have hCr : 0 < ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * (r : ℝ) := mul_pos hCpos hr0
  have hX0 : 0 ≤ y - ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * (r : ℝ) := czX_nonneg (le_of_lt hy) hry
  have hXh : y - ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * (r : ℝ) ≤ y / 2 := czX_le_half hy hr1 hry
  have hXr : y - ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * (r : ℝ) ≤ (r : ℝ) := le_of_lt (czX_lt hy hr1)
  have h1 : -Real.log (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * (r : ℝ) / y)
      = Real.log (y / (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * (r : ℝ))) := by
    rw [Real.log_div (ne_of_gt hCr) (ne_of_gt hy),
      Real.log_div (ne_of_gt hy) (ne_of_gt hCr)]
    ring
  rw [h1]
  have hEpos : 0 < ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * (r : ℝ) := hCr
  have hsplit : y / (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * (r : ℝ))
      = 1 + (y - ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * (r : ℝ))
          / (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * (r : ℝ)) := by
    field_simp
    ring
  rw [hsplit]
  have hlog : Real.log (1 + (y - ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * (r : ℝ))
        / (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * (r : ℝ)))
      ≤ (y - ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * (r : ℝ))
        / (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * (r : ℝ)) := by
    have hpos : 0 < 1 + (y - ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * (r : ℝ))
        / (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * (r : ℝ)) := by
      have hq : 0 ≤ (y - ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * (r : ℝ))
          / (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * (r : ℝ)) := div_nonneg hX0 hEpos.le
      linarith only [hq]
    have := Real.log_le_sub_one_of_pos hpos
    linarith only [this]
  have hkey : (y - ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * (r : ℝ))
        / (((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * (r : ℝ))
      ≤ 2 * (y - ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * (r : ℝ)) / y := by
    rw [div_le_div_iff₀ hEpos hy]
    nlinarith only [hX0, hXh, hy]
  have hfin : 2 * (y - ((⌊y / (r : ℝ)⌋₊ : ℕ) : ℝ) * (r : ℝ)) / y ≤ 2 * (r : ℝ) / y := by
    rw [div_le_div_iff₀ hy hy]
    nlinarith only [hXr, hy]
  linarith only [hlog, hkey, hfin]

lemma czSig_nonneg (t : ℕ) : 0 ≤ czSig t := by
  unfold czSig
  exact Finset.sum_nonneg (fun d _ => by positivity)


variable {w y : ℝ} {N q t : ℕ}

/-! ### Elementary facts about the envelope -/

lemma czEps_antitone {c x z : ℝ} (hc : 0 ≤ c) (hx : 0 < x) (hxz : x ≤ z) :
    czEps c z ≤ czEps c x := by
  unfold czEps
  rw [Real.exp_le_exp]
  have h1 : Real.log x ≤ Real.log z := Real.log_le_log hx hxz
  have h2 : Real.sqrt (Real.log x) ≤ Real.sqrt (Real.log z) := Real.sqrt_le_sqrt h1
  have h3 : 0 ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
  nlinarith only [hc, h2]

lemma czEps_le_one {c x : ℝ} (hc : 0 ≤ c) : czEps c x ≤ 1 := by
  unfold czEps
  rw [Real.exp_le_one_iff]
  have h3 : 0 ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
  nlinarith only [hc, h3]

lemma cz_sum_Icc_cast_le (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, (t : ℝ) ≤ (T : ℝ) ^ 2 := by
  have hcard : (Finset.Icc 1 T).card = T := by
    rw [Nat.card_Icc]; omega
  calc ∑ t ∈ Finset.Icc 1 T, (t : ℝ) ≤ ∑ t ∈ Finset.Icc 1 T, (T : ℝ) := by
        refine Finset.sum_le_sum (fun t ht => ?_)
        exact_mod_cast (Finset.mem_Icc.mp ht).2
    _ = (Finset.Icc 1 T).card * (T : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (T : ℝ) ^ 2 := by rw [hcard]; ring

lemma cz_sum_inv_sq_le_aux : ∀ Q : ℕ, 1 ≤ Q →
    ∑ q ∈ Finset.Icc 1 Q, 1 / (q : ℝ) ^ 2 ≤ 2 - 1 / (Q : ℝ) := by
  intro Q
  induction Q with
  | zero => intro h; omega
  | succ n ih =>
    intro _
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      norm_num
    · have hn1 : 1 ≤ n := h
      have hstep : (Finset.Icc 1 (n + 1)) = insert (n + 1) (Finset.Icc 1 n) := by
        ext t; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot : (n + 1) ∉ Finset.Icc 1 n := by simp [Finset.mem_Icc]
      rw [hstep, Finset.sum_insert hnot]
      have hIH := ih hn1
      have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      have hn1' : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n + 1)
      have hkey : 1 / (((n + 1 : ℕ)) : ℝ) ^ 2 ≤ 1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ) := by
        have hn0' : (n : ℝ) ≠ 0 := hn0.ne'
        have hn1'' : (((n + 1 : ℕ)) : ℝ) ≠ 0 := hn1'.ne'
        have heq : 1 / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ)
            = 1 / ((n : ℝ) * ((n + 1 : ℕ) : ℝ)) := by
          have heq2 : (1 : ℝ) / (n : ℝ) - 1 / ((n + 1 : ℕ) : ℝ)
              = ((((n + 1 : ℕ)) : ℝ) - (n : ℝ)) / ((n : ℝ) * (((n + 1 : ℕ)) : ℝ)) := by
            field_simp
          rw [heq2]
          have hsub : (((n + 1 : ℕ)) : ℝ) - (n : ℝ) = 1 := by push_cast; ring
          rw [hsub, one_div]
        rw [heq]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        push_cast
        linarith only [hn0]
      push_cast
      push_cast at hIH hkey
      linarith only [hIH, hkey]

lemma cz_sum_inv_sq_le (Q : ℕ) :
    ∑ q ∈ Finset.Icc 1 Q, 1 / (q : ℝ) ^ 2 ≤ 2 := by
  rcases Nat.eq_zero_or_pos Q with h | h
  · subst h; simp
  · exact le_trans (cz_sum_inv_sq_le_aux Q h) (by
      have : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast h
      linarith only [one_div_pos.mpr this, this])

/-! ### The Mertens function -/

def czMert (T : ℕ) : ℝ := ∑ t ∈ Finset.Icc 1 T, ((ArithmeticFunction.moebius t : ℤ) : ℝ)

/-! ### `T_q` vs `N/(q y)` -/

lemma czT_lower {N q : ℕ} (hy : 0 < y) (hq : 1 ≤ q) (hqQ : q ≤ czQ y N) :
    (N : ℝ) / (2 * ((q : ℝ) * y)) ≤ ((czT y N q : ℕ) : ℝ) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hden : 0 < (q : ℝ) * y := by positivity
  have hqR : ((q : ℕ) : ℝ) ≤ (N : ℝ) / y :=
    le_trans (by exact_mod_cast hqQ) (czQ_cast_le (N := N) hy)
  have hqy : ((q : ℕ) : ℝ) * y ≤ (N : ℝ) := (le_div_iff₀ hy).mp hqR
  have hone : (1 : ℝ) ≤ (N : ℝ) / ((q : ℝ) * y) := by
    rw [le_div_iff₀ hden]; linarith only [hqy]
  have heq : (N : ℝ) / (2 * ((q : ℝ) * y)) = ((N : ℝ) / ((q : ℝ) * y)) / 2 := by
    field_simp
  by_cases h : (2 : ℝ) ≤ (N : ℝ) / ((q : ℝ) * y)
  · have hfl : (N : ℝ) / ((q : ℝ) * y) - 1 ≤ ((czT y N q : ℕ) : ℝ) := by
      have := Nat.lt_floor_add_one ((N : ℝ) / ((q : ℝ) * y))
      rw [czT]
      linarith only [this]
    rw [heq]
    linarith only [h, hfl]
  · push Not at h
    have h1 : 1 ≤ czT y N q := by
      rw [czT]
      apply Nat.le_floor
      rw [Nat.cast_one]
      exact hone
    have h2 : (1 : ℝ) ≤ ((czT y N q : ℕ) : ℝ) := by exact_mod_cast h1
    rw [heq]
    linarith only [h, h2]

/-! ### The `Y_t`-sum of the error -/

lemma cz_tsum_Y (hw : 0 < w) (hy : 0 < y) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T,
        |((ArithmeticFunction.moebius t : ℤ) : ℝ)| * ((t : ℝ) / kap t) * czY w y t
      ≤ (y / w) * (T : ℝ) ^ 2 := by
  have hterm : ∀ t ∈ Finset.Icc 1 T,
      |((ArithmeticFunction.moebius t : ℤ) : ℝ)| * ((t : ℝ) / kap t) * czY w y t
        ≤ czY w y t := by
    intro t ht
    have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
    by_cases hsq : Squarefree t
    · have hk : (t : ℝ) ≤ kap t := kap_ge_self hsq
      have hkpos : 0 < kap t := kap_pos t
      have hle : (t : ℝ) / kap t ≤ 1 := by
        rw [div_le_one hkpos]; exact hk
      have hYnn : 0 ≤ czY w y t := (czY_pos hw hy ht1).le
      have hmu : |((ArithmeticFunction.moebius t : ℤ) : ℝ)| = 1 := by
        have hne : ArithmeticFunction.moebius t ≠ 0 :=
          (ArithmeticFunction.moebius_ne_zero_iff_squarefree).mpr hsq
        rcases (ArithmeticFunction.moebius_ne_zero_iff_eq_or).mp hne with h | h
        · rw [h]; norm_num
        · rw [h]; norm_num
      rw [hmu, one_mul]
      exact mul_le_of_le_one_left hYnn hle
    · have hmu : ((ArithmeticFunction.moebius t : ℤ) : ℝ) = 0 := by
        rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
        norm_num
      rw [hmu]
      simp only [abs_zero, zero_mul]
      exact (czY_pos hw hy ht1).le
  calc ∑ t ∈ Finset.Icc 1 T,
        |((ArithmeticFunction.moebius t : ℤ) : ℝ)| * ((t : ℝ) / kap t) * czY w y t
      ≤ ∑ t ∈ Finset.Icc 1 T, czY w y t := Finset.sum_le_sum hterm
    _ = ∑ t ∈ Finset.Icc 1 T, (y / w) * (t : ℝ) := by
        refine Finset.sum_congr rfl (fun t _ => ?_)
        unfold czY; ring
    _ = (y / w) * ∑ t ∈ Finset.Icc 1 T, (t : ℝ) := by rw [Finset.mul_sum]
    _ ≤ (y / w) * (T : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left (cz_sum_Icc_cast_le T) (by positivity)

lemma cz_sum_lin {S : Finset ℕ} (f g : ℕ → ℝ) (c1 c2 : ℝ) :
    (∑ q ∈ S, (c1 * f q + c2 * g q)) = c1 * (∑ q ∈ S, f q) + c2 * (∑ q ∈ S, g q) := by
  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-! ### The assembly -/


/-! ### Small algebraic helpers -/

lemma czY_eq (w y : ℝ) (t : ℕ) : czY w y t = (y / w) * (t : ℝ) := by
  unfold czY; ring

lemma cz_div_two_mul (N y : ℝ) (q : ℕ) :
    (N) / (2 * ((q : ℝ) * y)) = (N / (2 * y)) / (q : ℝ) := by
  rw [div_div]; congr 1; ring

lemma cz_div_mul (N y : ℝ) {q : ℕ} (hq : (q : ℝ) ≠ 0) (hy : y ≠ 0) :
    (N) / ((q : ℝ) * y) = (N / y) * (1 / (q : ℝ)) := by
  field_simp

lemma cz_div_two_mul' (N y : ℝ) (q : ℕ) :
    (N) / (2 * ((q : ℝ) * y)) = (N / (2 * y)) * (1 / (q : ℝ)) := by
  rw [cz_div_two_mul, div_eq_mul_one_div]

/-! ### The assembly -/

theorem czRI_bound_aux
    (CM cM : ℝ) (hCM : 0 < CM) (hcM : 0 < cM)
    (hM : ∀ T : ℕ, 1 ≤ T → |czMert T| ≤ CM * (T : ℝ) * czEps cM (T : ℝ))
    (CR cR : ℝ) (hCR : 0 < CR) (hcR : 0 < cR)
    (hRow : ∀ {w y : ℝ} {N q t : ℕ}, 1 ≤ w → w ≤ y → y ≤ (N : ℝ) → (N : ℝ) < w * y →
        1 ≤ q → q ≤ czQ y N → t ∈ Finset.Icc 1 (czT y N q) → Squarefree t →
        |czRowSum w y N q t + y * (Real.pi ^ 2 / 6) * ((ArithmeticFunction.moebius t : ℤ) : ℝ)|
          ≤ CR * ((t : ℝ) / kap t)
              * (y * czSig t * czEps cR (czY w y t) + czY w y t))
    (CS : ℝ) (hCS : 0 < CS)
    (hSig : ∀ (a : ℝ) (T : ℕ), 1 ≤ a → 1 ≤ T →
        ∑ t ∈ Finset.Icc 1 T,
          |((ArithmeticFunction.moebius t : ℤ) : ℝ)| * ((t : ℝ) / kap t) * czSig t
            * czEps cR (a * (t : ℝ))
          ≤ CS * (T : ℝ) * czEps cR (a * (T : ℝ)))
    (CH1 : ℝ) (hCH1 : 0 < CH1)
    (hHarm1 : ∀ (A : ℝ) (Q : ℕ), 0 < A → (Q : ℝ) ≤ 2 * A →
        ∑ q ∈ Finset.Icc 1 Q, (1 / (q : ℝ)) * czEps cM (A / (q : ℝ)) ≤ CH1)
    (CH2 : ℝ) (hCH2 : 0 < CH2)
    (hHarm2 : ∀ (A : ℝ) (Q : ℕ), 0 < A → (Q : ℝ) ≤ 2 * A →
        ∑ q ∈ Finset.Icc 1 Q, (1 / (q : ℝ)) * czEps cR (A / (q : ℝ)) ≤ CH2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (w y : ℝ) (N : ℕ), 1 ≤ w → w ≤ y → y ≤ (N : ℝ) →
      (N : ℝ) < w * y → |czRI w y N| ≤ C * (N : ℝ) := by
  refine ⟨Real.pi ^ 2 / 6 * CM * CH1 + CR * (CS * CH2 + 2), by positivity, ?_⟩
  intro w y N hw1 hwy hyN hNwy
  have hw : 0 < w := by linarith only [hw1]
  have hy : 0 < y := by linarith only [hw1, hwy]
  have hy1 : 1 ≤ y := by linarith only [hw1, hwy]
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := le_trans zero_le_one (le_trans hw1 (le_trans hwy hyN))
  have hyle1 : (1 : ℝ) / y ≤ 1 := by
    rw [div_le_one hy]; linarith only [hw1, hwy]
  set c : ℝ := y * (Real.pi ^ 2 / 6) with hc_def
  -- split into rows plus the Mertens main term
  have hA : ∀ q : ℕ,
      (∑ t ∈ Finset.Icc 1 (czT y N q),
          (czRowSum w y N q t + c * ((ArithmeticFunction.moebius t : ℤ) : ℝ)))
        = (∑ t ∈ Finset.Icc 1 (czT y N q), czRowSum w y N q t)
          + c * czMert (czT y N q) := by
    intro q
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    rfl
  have hsplit : czRI w y N
      = (∑ q ∈ Finset.Icc 1 (czQ y N), ∑ t ∈ Finset.Icc 1 (czT y N q),
            (czRowSum w y N q t + c * ((ArithmeticFunction.moebius t : ℤ) : ℝ)))
        - c * ∑ q ∈ Finset.Icc 1 (czQ y N), czMert (czT y N q) := by
    rw [czRI_eq_sum_row]
    have h2 : (∑ q ∈ Finset.Icc 1 (czQ y N), ∑ t ∈ Finset.Icc 1 (czT y N q),
            (czRowSum w y N q t + c * ((ArithmeticFunction.moebius t : ℤ) : ℝ)))
        = (∑ q ∈ Finset.Icc 1 (czQ y N), ∑ t ∈ Finset.Icc 1 (czT y N q), czRowSum w y N q t)
          + c * ∑ q ∈ Finset.Icc 1 (czQ y N), czMert (czT y N q) := by
      rw [show (∑ q ∈ Finset.Icc 1 (czQ y N), ∑ t ∈ Finset.Icc 1 (czT y N q),
            (czRowSum w y N q t + c * ((ArithmeticFunction.moebius t : ℤ) : ℝ)))
          = ∑ q ∈ Finset.Icc 1 (czQ y N),
              ((∑ t ∈ Finset.Icc 1 (czT y N q), czRowSum w y N q t)
                + c * czMert (czT y N q)) from
            Finset.sum_congr rfl (fun q _ => hA q)]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [h2]; ring
  -- per-`q` bound for the Mertens term
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (1 : ℝ) ≤ (N : ℝ) := le_trans hy1 hyN
    linarith only [hw1, hwy, hyN]
  have hmainper : ∀ q ∈ Finset.Icc 1 (czQ y N),
      |czMert (czT y N q)| ≤ CM * ((N : ℝ) / y) * ((1 / (q : ℝ)) * czEps cM (((N : ℝ) / (2 * y)) / (q : ℝ))) := by
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
    have hT1 : 1 ≤ czT y N q := czT_pos hy hq1 (Finset.mem_Icc.mp hq).2
    have hTl : (N : ℝ) / (2 * ((q : ℝ) * y)) ≤ ((czT y N q : ℕ) : ℝ) := czT_lower (q := q) hy hq1 (Finset.mem_Icc.mp hq).2
    have hcast : ((czT y N q : ℕ) : ℝ) ≤ (N : ℝ) / ((q : ℝ) * y) := by
      rw [czT]; exact Nat.floor_le (by positivity)
    have habs := hM (czT y N q) hT1
    have heps : czEps cM ((czT y N q : ℕ) : ℝ) ≤ czEps cM (((N : ℝ) / (2 * y)) / (q : ℝ)) := by
      have hh := czEps_antitone hcM.le (by positivity) hTl
      rwa [cz_div_two_mul] at hh
    have hstep2 : CM * ((czT y N q : ℕ) : ℝ) * czEps cM (((N : ℝ) / (2 * y)) / (q : ℝ))
        ≤ CM * ((N : ℝ) / ((q : ℝ) * y)) * czEps cM (((N : ℝ) / (2 * y)) / (q : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (czEps_pos cM _).le
      exact mul_le_mul_of_nonneg_left hcast hCM.le
    calc |czMert (czT y N q)|
        ≤ CM * ((czT y N q : ℕ) : ℝ) * czEps cM ((czT y N q : ℕ) : ℝ) := habs
      _ ≤ CM * ((czT y N q : ℕ) : ℝ) * czEps cM (((N : ℝ) / (2 * y)) / (q : ℝ)) :=
          mul_le_mul_of_nonneg_left heps (by positivity)
      _ ≤ CM * ((N : ℝ) / ((q : ℝ) * y)) * czEps cM (((N : ℝ) / (2 * y)) / (q : ℝ)) := hstep2
      _ = CM * ((N : ℝ) / y) * ((1 / (q : ℝ)) * czEps cM (((N : ℝ) / (2 * y)) / (q : ℝ))) := by
          rw [cz_div_mul (N := (N : ℝ)) (y := y) (q := q) hq0.ne' hy.ne']
          ring
  -- the Mertens main term
  have hmain : c * (∑ q ∈ Finset.Icc 1 (czQ y N), |czMert (czT y N q)|)
      ≤ (N : ℝ) * (Real.pi ^ 2 / 6 * CM * CH1) := by
    have hsum : (∑ q ∈ Finset.Icc 1 (czQ y N), |czMert (czT y N q)|)
        ≤ CM * ((N : ℝ) / y) * ∑ q ∈ Finset.Icc 1 (czQ y N),
            (1 / (q : ℝ)) * czEps cM (((N : ℝ) / (2 * y)) / (q : ℝ)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hmainper
    have hA2 : (0 : ℝ) < (N : ℝ) / (2 * y) := by positivity
    have hQ2 : ((czQ y N : ℕ) : ℝ) ≤ 2 * ((N : ℝ) / (2 * y)) := by
      have h := czQ_cast_le (N := N) hy
      have heq : 2 * ((N : ℝ) / (2 * y)) = (N : ℝ) / y := by field_simp
      linarith only [h, heq]
    have hH := hHarm1 ((N : ℝ) / (2 * y)) (czQ y N) hA2 hQ2
    have hnn : (0 : ℝ) ≤ CM * ((N : ℝ) / y) := (mul_pos hCM (div_pos hNpos hy)).le
    have hfin := mul_le_mul_of_nonneg_left hH hnn
    have hcombined : (∑ q ∈ Finset.Icc 1 (czQ y N), |czMert (czT y N q)|)
        ≤ CM * ((N : ℝ) / y) * CH1 := le_trans hsum hfin
    calc c * (∑ q ∈ Finset.Icc 1 (czQ y N), |czMert (czT y N q)|)
        ≤ y * (Real.pi ^ 2 / 6) * (CM * ((N : ℝ) / y) * CH1) := by
          rw [hc_def]
          exact mul_le_mul_of_nonneg_left hcombined (by positivity)
      _ = (N : ℝ) * (Real.pi ^ 2 / 6 * CM * CH1) := by
          field_simp
  -- the row errors
  have hyw1 : (1 : ℝ) ≤ y / w := by rw [le_div_iff₀ hw]; linarith only [hwy]
  set A : ℕ → ℝ := fun t => |((ArithmeticFunction.moebius t : ℤ) : ℝ)| * ((t : ℝ) / kap t) with hA
  set B : ℕ → ℝ := fun t => czSig t * czEps cR (czY w y t) with hB
  have hrow1 : ∀ q ∈ Finset.Icc 1 (czQ y N), ∀ t ∈ Finset.Icc 1 (czT y N q),
      |czRowSum w y N q t + c * ((ArithmeticFunction.moebius t : ℤ) : ℝ)|
        ≤ CR * (A t * (y * B t + czY w y t)) := by
    intro q hq t ht
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
    by_cases hsq : Squarefree t
    · have hmu : |((ArithmeticFunction.moebius t : ℤ) : ℝ)| = 1 := by
        have hne : ArithmeticFunction.moebius t ≠ 0 :=
          (ArithmeticFunction.moebius_ne_zero_iff_squarefree).mpr hsq
        rcases (ArithmeticFunction.moebius_ne_zero_iff_eq_or).mp hne with h | h
        · rw [h]; norm_num
        · rw [h]; norm_num
      have h := hRow hw1 hwy hyN hNwy hq1 (Finset.mem_Icc.mp hq).2 ht hsq
      have h2 : CR * ((t : ℝ) / kap t) * (y * czSig t * czEps cR (czY w y t) + czY w y t)
          = CR * (A t * (y * B t + czY w y t)) := by
        simp only [hA, hB, hmu, one_mul]
        ring
      rw [hc_def]
      exact le_trans h (le_of_eq h2)
    · have hmut : ((ArithmeticFunction.moebius t : ℤ) : ℝ) = 0 := by
        rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
        norm_num
      have hrowz : czRowSum w y N q t = 0 := by
        unfold czRowSum
        refine Finset.sum_eq_zero (fun r hr => ?_)
        by_cases hc : Nat.Coprime r t
        · simp only [czMM, if_pos hc]
          rw [hmut]; ring
        · simp [czMM, if_neg hc]
      rw [hrowz, hmut, mul_zero, add_zero, abs_zero]
      simp only [hA, hmut, abs_zero, zero_mul, mul_zero]
      exact le_refl (0 : ℝ)
  have hrowsper : ∀ q ∈ Finset.Icc 1 (czQ y N),
      (∑ t ∈ Finset.Icc 1 (czT y N q),
          |czRowSum w y N q t + c * ((ArithmeticFunction.moebius t : ℤ) : ℝ)|)
        ≤ CR * (y * CS * (czT y N q : ℝ) * czEps cR ((y / w) * (czT y N q : ℝ))
            + (y / w) * (czT y N q : ℝ) ^ 2) := by
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hT1 : 1 ≤ czT y N q := czT_pos hy hq1 (Finset.mem_Icc.mp hq).2
    have hsplit2 : (∑ t ∈ Finset.Icc 1 (czT y N q),
          |czRowSum w y N q t + c * ((ArithmeticFunction.moebius t : ℤ) : ℝ)|)
        ≤ CR * y * (∑ t ∈ Finset.Icc 1 (czT y N q), A t * B t)
          + CR * (∑ t ∈ Finset.Icc 1 (czT y N q), A t * czY w y t) := by
      calc (∑ t ∈ Finset.Icc 1 (czT y N q),
            |czRowSum w y N q t + c * ((ArithmeticFunction.moebius t : ℤ) : ℝ)|)
          ≤ ∑ t ∈ Finset.Icc 1 (czT y N q), CR * (A t * (y * B t + czY w y t)) :=
            Finset.sum_le_sum (fun t ht => hrow1 q hq t ht)
        _ = ∑ t ∈ Finset.Icc 1 (czT y N q),
              (CR * y * (A t * B t) + CR * (A t * czY w y t)) :=
            Finset.sum_congr rfl (fun t ht => by ring)
        _ = CR * y * (∑ t ∈ Finset.Icc 1 (czT y N q), A t * B t)
              + CR * (∑ t ∈ Finset.Icc 1 (czT y N q), A t * czY w y t) :=
            cz_sum_lin (fun t => A t * B t) (fun t => A t * czY w y t) (CR * y) CR
    have hsig := hSig (y / w) (czT y N q) hyw1 hT1
    have hsig2 : (∑ t ∈ Finset.Icc 1 (czT y N q), A t * B t)
        ≤ CS * (czT y N q : ℝ) * czEps cR ((y / w) * (czT y N q : ℝ)) := by
      have hcongr : (∑ t ∈ Finset.Icc 1 (czT y N q), A t * B t)
          = (∑ t ∈ Finset.Icc 1 (czT y N q),
              |((ArithmeticFunction.moebius t : ℤ) : ℝ)| * ((t : ℝ) / kap t) * czSig t
                * czEps cR ((y / w) * (t : ℝ))) := by
        refine Finset.sum_congr rfl (fun t ht => ?_)
        simp only [hA, hB, czY_eq]
        ring
      rw [hcongr]
      exact hsig
    have hYsum : (∑ t ∈ Finset.Icc 1 (czT y N q), A t * czY w y t)
        ≤ (y / w) * (czT y N q : ℝ) ^ 2 := by
      have hcongr : (∑ t ∈ Finset.Icc 1 (czT y N q), A t * czY w y t)
          = (∑ t ∈ Finset.Icc 1 (czT y N q),
              |((ArithmeticFunction.moebius t : ℤ) : ℝ)| * ((t : ℝ) / kap t) * czY w y t) := by
        refine Finset.sum_congr rfl (fun t ht => ?_)
        rw [hA]
      rw [hcongr]
      exact cz_tsum_Y hw hy _
    calc (∑ t ∈ Finset.Icc 1 (czT y N q),
          |czRowSum w y N q t + c * ((ArithmeticFunction.moebius t : ℤ) : ℝ)|)
        ≤ CR * y * (∑ t ∈ Finset.Icc 1 (czT y N q), A t * B t)
          + CR * (∑ t ∈ Finset.Icc 1 (czT y N q), A t * czY w y t) := hsplit2
      _ ≤ CR * y * (CS * (czT y N q : ℝ) * czEps cR ((y / w) * (czT y N q : ℝ)))
          + CR * ((y / w) * (czT y N q : ℝ) ^ 2) := by
          have h1 : CR * y * (∑ t ∈ Finset.Icc 1 (czT y N q), A t * B t)
              ≤ CR * y * (CS * (czT y N q : ℝ) * czEps cR ((y / w) * (czT y N q : ℝ))) :=
            mul_le_mul_of_nonneg_left hsig2 (by positivity)
          have h2 : CR * (∑ t ∈ Finset.Icc 1 (czT y N q), A t * czY w y t)
              ≤ CR * ((y / w) * (czT y N q : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hYsum (by positivity)
          linarith only [h1, h2]
      _ = CR * (y * CS * (czT y N q : ℝ) * czEps cR ((y / w) * (czT y N q : ℝ))
            + (y / w) * (czT y N q : ℝ) ^ 2) := by ring
  have hrows : (∑ q ∈ Finset.Icc 1 (czQ y N), ∑ t ∈ Finset.Icc 1 (czT y N q),
        |czRowSum w y N q t + c * ((ArithmeticFunction.moebius t : ℤ) : ℝ)|)
      ≤ (N : ℝ) * (CR * (CS * CH2 + 2)) := by
    have hstep1 : (∑ q ∈ Finset.Icc 1 (czQ y N), ∑ t ∈ Finset.Icc 1 (czT y N q),
        |czRowSum w y N q t + c * ((ArithmeticFunction.moebius t : ℤ) : ℝ)|)
        ≤ CR * y * CS * (∑ q ∈ Finset.Icc 1 (czQ y N), (czT y N q : ℝ)
              * czEps cR ((y / w) * (czT y N q : ℝ)))
          + CR * (y / w) * (∑ q ∈ Finset.Icc 1 (czQ y N), (czT y N q : ℝ) ^ 2) := by
      calc (∑ q ∈ Finset.Icc 1 (czQ y N), ∑ t ∈ Finset.Icc 1 (czT y N q),
          |czRowSum w y N q t + c * ((ArithmeticFunction.moebius t : ℤ) : ℝ)|)
          ≤ ∑ q ∈ Finset.Icc 1 (czQ y N), CR * (y * CS * (czT y N q : ℝ)
              * czEps cR ((y / w) * (czT y N q : ℝ)) + (y / w) * (czT y N q : ℝ) ^ 2) :=
            Finset.sum_le_sum (fun q hq => hrowsper q hq)
        _ = ∑ q ∈ Finset.Icc 1 (czQ y N),
              ((CR * y * CS) * ((czT y N q : ℝ) * czEps cR ((y / w) * (czT y N q : ℝ)))
                + (CR * (y / w)) * (czT y N q : ℝ) ^ 2) :=
            Finset.sum_congr rfl (fun q hq => by ring)
        _ = CR * y * CS * (∑ q ∈ Finset.Icc 1 (czQ y N), (czT y N q : ℝ)
              * czEps cR ((y / w) * (czT y N q : ℝ)))
          + CR * (y / w) * (∑ q ∈ Finset.Icc 1 (czQ y N), (czT y N q : ℝ) ^ 2) :=
            cz_sum_lin (fun q => (czT y N q : ℝ) * czEps cR ((y / w) * (czT y N q : ℝ)))
              (fun q => (czT y N q : ℝ) ^ 2) (CR * y * CS) (CR * (y / w))
    have hpart1 : (∑ q ∈ Finset.Icc 1 (czQ y N), (czT y N q : ℝ)
          * czEps cR ((y / w) * (czT y N q : ℝ))) ≤ ((N : ℝ) / y) * CH2 := by
      have hb : (∑ q ∈ Finset.Icc 1 (czQ y N), (czT y N q : ℝ)
            * czEps cR ((y / w) * (czT y N q : ℝ)))
          ≤ ((N : ℝ) / y) * ∑ q ∈ Finset.Icc 1 (czQ y N),
              (1 / (q : ℝ)) * czEps cR ((N / (2 * w)) / (q : ℝ)) := by
        have hcong : (∑ q ∈ Finset.Icc 1 (czQ y N), (czT y N q : ℝ)
              * czEps cR ((y / w) * (czT y N q : ℝ)))
            ≤ ∑ q ∈ Finset.Icc 1 (czQ y N), ((N : ℝ) / ((q : ℝ) * y))
              * czEps cR ((N / (2 * w)) / (q : ℝ)) := by
          refine Finset.sum_le_sum (fun q hq => ?_)
          have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
          have hTl := czT_lower (q := q) hy hq1 (Finset.mem_Icc.mp hq).2
          have hTup : ((czT y N q : ℕ) : ℝ) ≤ (N : ℝ) / ((q : ℝ) * y) := by
            rw [czT]; exact Nat.floor_le (by positivity)
          have hYl : (N : ℝ) / (2 * ((q : ℝ) * w)) ≤ (y / w) * ((czT y N q : ℕ) : ℝ) := by
            have h1 := mul_le_mul_of_nonneg_left hTl (by positivity : (0:ℝ) ≤ y / w)
            have heq : (y / w) * ((N : ℝ) / (2 * ((q : ℝ) * y))) = (N : ℝ) / (2 * ((q : ℝ) * w)) := by
              field_simp
            linarith only [h1, heq ▸ h1, heq]
          have heps : czEps cR ((y / w) * ((czT y N q : ℕ) : ℝ))
              ≤ czEps cR ((N / (2 * w)) / (q : ℝ)) := by
            have hh := czEps_antitone hcR.le (by positivity) hYl
            rwa [cz_div_two_mul] at hh
          have hstep : ((czT y N q : ℕ) : ℝ) * czEps cR ((y / w) * ((czT y N q : ℕ) : ℝ))
              ≤ ((N : ℝ) / ((q : ℝ) * y)) * czEps cR ((N / (2 * w)) / (q : ℝ)) := by
            have h1 : ((czT y N q : ℕ) : ℝ) * czEps cR ((y / w) * ((czT y N q : ℕ) : ℝ))
                ≤ ((N : ℝ) / ((q : ℝ) * y)) * czEps cR ((y / w) * ((czT y N q : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_right hTup (czEps_pos cR _).le
            exact le_trans h1 (mul_le_mul_of_nonneg_left heps (by positivity))
          exact hstep
        have hsplit3 : (∑ q ∈ Finset.Icc 1 (czQ y N), ((N : ℝ) / ((q : ℝ) * y))
              * czEps cR ((N / (2 * w)) / (q : ℝ)))
            = ((N : ℝ) / y) * ∑ q ∈ Finset.Icc 1 (czQ y N),
                (1 / (q : ℝ)) * czEps cR ((N / (2 * w)) / (q : ℝ)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun q hq => ?_)
          have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
          have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
          rw [cz_div_mul (N := (N : ℝ)) (y := y) (q := q) hq0.ne' hy.ne']
          rw [mul_assoc]
        rw [← hsplit3]
        exact hcong
      have hA2pos : (0 : ℝ) < (N : ℝ) / (2 * w) := by positivity
      have hQ2 : ((czQ y N : ℕ) : ℝ) ≤ 2 * ((N : ℝ) / (2 * w)) := by
        have h := czQ_cast_le (N := N) hy
        have heq : 2 * ((N : ℝ) / (2 * w)) = (N : ℝ) / w := by field_simp
        rw [heq, le_div_iff₀ hw]
        have h1 : ((czQ y N : ℕ) : ℝ) * w ≤ ((N : ℝ) / y) * w :=
          mul_le_mul_of_nonneg_right h hw.le
        have h2 : ((N : ℝ) / y) * w ≤ (N : ℝ) := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hy]
          nlinarith only [hwy]
        linarith only [h1, h2]
      have hHa := hHarm2 ((N : ℝ) / (2 * w)) (czQ y N) hA2pos hQ2
      exact le_trans hb (mul_le_mul_of_nonneg_left hHa (by positivity))
    have hpart2 : (∑ q ∈ Finset.Icc 1 (czQ y N), (czT y N q : ℝ) ^ 2)
        ≤ 2 * ((N : ℝ) / y) ^ 2 := by
      have h1 : (∑ q ∈ Finset.Icc 1 (czQ y N), (czT y N q : ℝ) ^ 2)
          ≤ ∑ q ∈ Finset.Icc 1 (czQ y N), ((N : ℝ) / ((q : ℝ) * y)) ^ 2 := by
        refine Finset.sum_le_sum (fun q hq => ?_)
        have hTup : ((czT y N q : ℕ) : ℝ) ≤ (N : ℝ) / ((q : ℝ) * y) := by
          rw [czT]; exact Nat.floor_le (by positivity)
        have hTnn : (0 : ℝ) ≤ ((czT y N q : ℕ) : ℝ) := Nat.cast_nonneg _
        nlinarith only [hTup, hTnn]
      have h2 : (∑ q ∈ Finset.Icc 1 (czQ y N), ((N : ℝ) / ((q : ℝ) * y)) ^ 2)
          = ((N : ℝ) / y) ^ 2 * ∑ q ∈ Finset.Icc 1 (czQ y N), 1 / (q : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun q hq => ?_)
        have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
        have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
        field_simp
      have h3 := cz_sum_inv_sq_le (czQ y N)
      calc (∑ q ∈ Finset.Icc 1 (czQ y N), (czT y N q : ℝ) ^ 2)
          ≤ (∑ q ∈ Finset.Icc 1 (czQ y N), ((N : ℝ) / ((q : ℝ) * y)) ^ 2) := h1
        _ = ((N : ℝ) / y) ^ 2 * ∑ q ∈ Finset.Icc 1 (czQ y N), 1 / (q : ℝ) ^ 2 := h2
        _ ≤ ((N : ℝ) / y) ^ 2 * 2 := mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
        _ = 2 * ((N : ℝ) / y) ^ 2 := by ring
    have hfin2 : (y / w) * (2 * ((N : ℝ) / y) ^ 2) ≤ 2 * (N : ℝ) := by
      have hN2 : (N : ℝ) ^ 2 ≤ (N : ℝ) * (w * y) := by nlinarith only [hNwy]
      have heq : (y / w) * (2 * ((N : ℝ) / y) ^ 2) = 2 * (N : ℝ) ^ 2 / (w * y) := by
        field_simp
      rw [heq, div_le_iff₀ (by positivity)]
      linarith only [hN2]
    have hb1 : CR * y * CS * (∑ q ∈ Finset.Icc 1 (czQ y N), (czT y N q : ℝ)
          * czEps cR ((y / w) * (czT y N q : ℝ)))
        ≤ CR * y * CS * (((N : ℝ) / y) * CH2) :=
      mul_le_mul_of_nonneg_left hpart1 (by positivity)
    have hb2 : CR * (y / w) * (∑ q ∈ Finset.Icc 1 (czQ y N), (czT y N q : ℝ) ^ 2)
        ≤ CR * (y / w) * (2 * ((N : ℝ) / y) ^ 2) :=
      mul_le_mul_of_nonneg_left hpart2 (by positivity)
    have hb3 : CR * y * CS * (((N : ℝ) / y) * CH2) = (N : ℝ) * (CR * (CS * CH2)) := by
      field_simp
    calc (∑ q ∈ Finset.Icc 1 (czQ y N), ∑ t ∈ Finset.Icc 1 (czT y N q),
        |czRowSum w y N q t + c * ((ArithmeticFunction.moebius t : ℤ) : ℝ)|)
        ≤ CR * y * CS * (∑ q ∈ Finset.Icc 1 (czQ y N), (czT y N q : ℝ)
              * czEps cR ((y / w) * (czT y N q : ℝ)))
          + CR * (y / w) * (∑ q ∈ Finset.Icc 1 (czQ y N), (czT y N q : ℝ) ^ 2) := hstep1
      _ ≤ CR * y * CS * (((N : ℝ) / y) * CH2)
          + CR * (y / w) * (2 * ((N : ℝ) / y) ^ 2) := add_le_add hb1 hb2
      _ ≤ (N : ℝ) * (CR * (CS * CH2)) + CR * (2 * (N : ℝ)) := by
          rw [hb3]
          have := mul_le_mul_of_nonneg_left hfin2 hCR.le
          linarith only [this]
      _ = (N : ℝ) * (CR * (CS * CH2 + 2)) := by ring
  -- final assembly
  have h2 : |∑ q ∈ Finset.Icc 1 (czQ y N), ∑ t ∈ Finset.Icc 1 (czT y N q),
        (czRowSum w y N q t + c * ((ArithmeticFunction.moebius t : ℤ) : ℝ))|
      ≤ (N : ℝ) * (CR * (CS * CH2 + 2)) := by
      refine le_trans (abs_sum_le_sum_abs _ _) ?_
      refine le_trans (Finset.sum_le_sum (fun q hq => abs_sum_le_sum_abs _ _)) ?_
      exact hrows
  have h1 : |c * (∑ q ∈ Finset.Icc 1 (czQ y N), czMert (czT y N q))|
      ≤ (N : ℝ) * (Real.pi ^ 2 / 6 * CM * CH1) := by
    rw [abs_mul, abs_of_nonneg (by rw [hc_def]; positivity)]
    refine le_trans (mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (by rw [hc_def]; positivity)) ?_
    exact hmain
  calc |czRI w y N|
      = |(∑ q ∈ Finset.Icc 1 (czQ y N), ∑ t ∈ Finset.Icc 1 (czT y N q),
            (czRowSum w y N q t + c * ((ArithmeticFunction.moebius t : ℤ) : ℝ)))
          - c * ∑ q ∈ Finset.Icc 1 (czQ y N), czMert (czT y N q)| := by rw [hsplit]
    _ ≤ |(∑ q ∈ Finset.Icc 1 (czQ y N), ∑ t ∈ Finset.Icc 1 (czT y N q),
            (czRowSum w y N q t + c * ((ArithmeticFunction.moebius t : ℤ) : ℝ)))|
          + |c * (∑ q ∈ Finset.Icc 1 (czQ y N), czMert (czT y N q))| := abs_sub _ _
    _ ≤ (N : ℝ) * (CR * (CS * CH2 + 2)) + (N : ℝ) * (Real.pi ^ 2 / 6 * CM * CH1) :=
        add_le_add h2 h1
    _ = (Real.pi ^ 2 / 6 * CM * CH1 + CR * (CS * CH2 + 2)) * (N : ℝ) := by ring


lemma cz_inv_le_log_ratio (q : ℕ) (hq : 1 ≤ q) :
    (1 : ℝ) / (q : ℝ) ≤ 2 * Real.log (((q : ℝ) + 1) / (q : ℝ)) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have ht : (0 : ℝ) < 1 / (q : ℝ) := by positivity
  have ht1 : 1 / (q : ℝ) ≤ 1 := by
    rw [div_le_one hq0]; exact_mod_cast hq
  -- `log (1 + t) ≥ t / (1 + t) ≥ t / 2`
  have h6 : (1 / (q : ℝ)) / (1 + 1 / (q : ℝ)) ≤ Real.log (1 + 1 / (q : ℝ)) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / (1 + 1 / (q : ℝ)) by positivity)
    have h2 : Real.log (1 / (1 + 1 / (q : ℝ))) = -Real.log (1 + 1 / (q : ℝ)) := by
      rw [one_div, Real.log_inv]
    have h3 : (1 : ℝ) / (1 + 1 / (q : ℝ)) - 1 = -((1 / (q : ℝ)) / (1 + 1 / (q : ℝ))) := by
      field_simp
      ring
    rw [h2, h3] at h
    linarith only [h]
  have h5 : (1 / (q : ℝ)) / 2 ≤ (1 / (q : ℝ)) / (1 + 1 / (q : ℝ)) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith only [ht, ht1]
  have h2 : Real.log (((q : ℝ) + 1) / (q : ℝ)) = Real.log (1 + 1 / (q : ℝ)) := by
    congr 1
    field_simp
  rw [h2]
  calc (1 : ℝ) / (q : ℝ) = 2 * ((1 / (q : ℝ)) / 2) := by ring
    _ ≤ 2 * ((1 / (q : ℝ)) / (1 + 1 / (q : ℝ))) := by linarith only [h5]
    _ ≤ 2 * Real.log (1 + 1 / (q : ℝ)) := by linarith only [h6]

lemma cz_telescope (f : ℕ → ℝ) (M : ℕ) :
    (∑ q ∈ Finset.Icc 1 M, (f (q + 1) - f q)) = f (M + 1) - f 1 := by
  induction M with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih]
    ring

/-- The telescoping bound for the logarithmic weight. -/
lemma cz_weight_le (A : ℝ) (M : ℕ) (hA1 : 1 < A) (hMA : (M : ℝ) + 1 ≤ A / Real.exp 1) :
    (∑ q ∈ Finset.Icc 1 M, (1 / (q : ℝ)) * (1 / (Real.log (A / (q : ℝ))) ^ 2))
      ≤ 2 / Real.log (A / ((M : ℝ) + 1)) := by
  have hApos : 0 < A := by linarith only [hA1]
  have he1 : (1 : ℝ) < Real.exp 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by norm_num)
  have he2 : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
  rcases Nat.eq_zero_or_pos M with hM0 | hM
  · subst hM0
    rw [show (Finset.Icc 1 0 : Finset ℕ) = ∅ from by simp, Finset.sum_empty, Nat.cast_zero, zero_add]
    apply div_nonneg (by norm_num)
    rw [div_one]
    exact (Real.log_pos hA1).le
  have hAexp : A / Real.exp 1 + 1 ≤ A := by
    have h2 : (2 : ℝ) ≤ (M : ℝ) + 1 := by
      have : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      linarith only [this]
    have h3 : (2 : ℝ) * Real.exp 1 ≤ A := by
      have h4 := mul_le_mul_of_nonneg_right (le_trans h2 hMA) (Real.exp_pos 1).le
      rwa [div_mul_cancel₀ _ (ne_of_gt (Real.exp_pos 1))] at h4
    rw [div_add' _ _ _ (ne_of_gt (Real.exp_pos 1)), div_le_iff₀ (Real.exp_pos 1)]
    nlinarith only [h3, he2, Real.exp_pos 1, hA1, he1]
  have hstep : ∀ q ∈ Finset.Icc 1 M,
      (1 / (q : ℝ)) * (1 / (Real.log (A / (q : ℝ))) ^ 2)
        ≤ 2 * (1 / Real.log (A / ((q : ℝ) + 1)) - 1 / Real.log (A / (q : ℝ))) := by
    intro q hq
    obtain ⟨hq1, hqM⟩ := Finset.mem_Icc.mp hq
    have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
    have hqM' : (q : ℝ) ≤ (M : ℝ) := by exact_mod_cast hqM
    have hqA1 : (q : ℝ) + 1 < A := by
      have h1 : (q : ℝ) + 1 ≤ A / Real.exp 1 := le_trans (by linarith only [hqM']) hMA
      linarith only [h1, hAexp, hMA, hqM']
    have hqA : (q : ℝ) < A := by linarith only [hMA, hAexp, hqM']
    have hL : 0 < Real.log (A / (q : ℝ)) := Real.log_pos (by rw [one_lt_div hq0]; linarith only [hMA, hAexp, hqM'])
    have hL' : 0 < Real.log (A / ((q : ℝ) + 1)) := Real.log_pos (by
      rw [one_lt_div (by linarith only [hq0] : (0 : ℝ) < (q : ℝ) + 1)]; linarith only [hMA, hAexp, hqM'])
    have hle : Real.log (A / ((q : ℝ) + 1)) ≤ Real.log (A / (q : ℝ)) := by
      apply Real.log_le_log (by positivity)
      rw [div_le_div_iff₀ (by linarith only [hq0] : (0 : ℝ) < (q : ℝ) + 1) hq0]
      linarith only [hMA, hAexp, hq0, hqM']
    have hratio : Real.log (A / (q : ℝ)) - Real.log (A / ((q : ℝ) + 1))
        = Real.log (((q : ℝ) + 1) / (q : ℝ)) := by
      rw [← Real.log_div (by positivity) (by positivity)]
      congr 1
      field_simp
    have hinv : (1 / (q : ℝ))
        ≤ 2 * (Real.log (A / (q : ℝ)) - Real.log (A / ((q : ℝ) + 1))) := by
      rw [hratio]
      exact cz_inv_le_log_ratio q hq1
    have h1 : (1 / (q : ℝ)) * (1 / (Real.log (A / (q : ℝ))) ^ 2)
        ≤ 2 * (Real.log (A / (q : ℝ)) - Real.log (A / ((q : ℝ) + 1)))
            / (Real.log (A / (q : ℝ))) ^ 2 := by
      rw [show (1 / (q : ℝ)) * (1 / (Real.log (A / (q : ℝ))) ^ 2)
          = (1 / (q : ℝ)) / (Real.log (A / (q : ℝ))) ^ 2 by ring]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [hinv]
    have h2 : 2 * (Real.log (A / (q : ℝ)) - Real.log (A / ((q : ℝ) + 1)))
            / (Real.log (A / (q : ℝ))) ^ 2
        ≤ 2 * (1 / Real.log (A / ((q : ℝ) + 1)) - 1 / Real.log (A / (q : ℝ))) := by
      rw [show 2 * (1 / Real.log (A / ((q : ℝ) + 1)) - 1 / Real.log (A / (q : ℝ)))
          = 2 * (Real.log (A / (q : ℝ)) - Real.log (A / ((q : ℝ) + 1)))
              / (Real.log (A / (q : ℝ)) * Real.log (A / ((q : ℝ) + 1))) by
        field_simp]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [hL, hL', hle, mul_le_mul_of_nonneg_left hle hL.le]
    linarith only [h1, h2]
  have hM1 : (M : ℝ) + 1 ≤ A / Real.exp 1 := hMA
  have htelescope :
      (∑ q ∈ Finset.Icc 1 M,
          2 * (1 / Real.log (A / ((q : ℝ) + 1)) - 1 / Real.log (A / (q : ℝ))))
        = 2 * (1 / Real.log (A / ((M : ℝ) + 1)) - 1 / Real.log (A / 1)) := by
    have h1 : ∀ q : ℕ, 1 / Real.log (A / ((q : ℝ) + 1))
        = 1 / Real.log (A / (((q + 1 : ℕ)) : ℝ)) := by
      intro q; push_cast; ring_nf
    simp only [h1]
    rw [← Finset.mul_sum, cz_telescope (fun q => 1 / Real.log (A / (q : ℝ)))]
    push_cast
    ring
  calc (∑ q ∈ Finset.Icc 1 M, (1 / (q : ℝ)) * (1 / (Real.log (A / (q : ℝ))) ^ 2))
      ≤ ∑ q ∈ Finset.Icc 1 M,
          2 * (1 / Real.log (A / ((q : ℝ) + 1)) - 1 / Real.log (A / (q : ℝ))) :=
        Finset.sum_le_sum hstep
    _ = 2 * (1 / Real.log (A / ((M : ℝ) + 1)) - 1 / Real.log (A / 1)) := htelescope
    _ ≤ 2 / Real.log (A / ((M : ℝ) + 1)) := by
        rw [show 2 * (1 / Real.log (A / ((M : ℝ) + 1)) - 1 / Real.log (A / 1))
            = 2 / Real.log (A / ((M : ℝ) + 1)) - 2 / Real.log (A / 1) by ring]
        have h2 : (0 : ℝ) < 2 / Real.log (A / 1) := by
          apply div_pos (by norm_num)
          rw [div_one]; exact Real.log_pos hA1
        linarith only [h2]

/-- The envelope is bounded by a power of `log`. -/
lemma cz_exp_bound (c : ℝ) (hc : 0 < c) {u : ℝ} (hu : 1 ≤ u) :
    Real.exp (-(c * Real.sqrt u)) ≤ ((8 / c) ^ 8 + 1) / u ^ 2 := by
  by_cases h : u ≤ (8 / c) ^ 4
  · have hexp : Real.exp (-(c * Real.sqrt u)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := Real.sqrt_nonneg u
      nlinarith only [hc, this]
    have hK : 1 ≤ ((8 / c) ^ 8 + 1) / u ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have h2 : u ^ 2 ≤ ((8 / c) ^ 4) ^ 2 := by nlinarith only [hu, h]
      have h3 : ((8 / c) ^ 4) ^ 2 = (8 / c) ^ 8 := by ring
      linarith only [h2, h3]
    linarith only [hexp, hK]
  · push Not at h
    have hu0 : 0 < u := by linarith only [hu]
    have hlogu : Real.log u ≤ 4 * u ^ ((1 : ℝ) / 4) := by
      have h1 := Real.log_le_rpow_div (le_of_lt hu0) (show (0 : ℝ) < (1 : ℝ) / 4 by norm_num)
      rw [show u ^ ((1 : ℝ) / 4) / ((1 : ℝ) / 4) = 4 * u ^ ((1 : ℝ) / 4) by ring] at h1
      exact h1
    have hpow : (u ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt u := by
      have h4 : ((u ^ ((1 : ℝ) / 4)) ^ 2) ^ 2 = u := by
        rw [← pow_mul, show (2 : ℕ) * 2 = 4 by norm_num]
        rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hu0)]
        norm_num
      have h1 : ((u ^ ((1 : ℝ) / 4)) ^ 2) ^ 2 = (Real.sqrt u) ^ 2 := by
        rw [h4, Real.sq_sqrt hu0.le]
      exact le_antisymm
        ((pow_le_pow_iff_left₀ (by positivity) (Real.sqrt_nonneg u)
          (by norm_num : (2 : ℕ) ≠ 0)).mp (le_of_eq h1))
        ((pow_le_pow_iff_left₀ (Real.sqrt_nonneg u) (by positivity)
          (by norm_num : (2 : ℕ) ≠ 0)).mp (le_of_eq h1.symm))
    have hpow4 : (u ^ ((1 : ℝ) / 4)) ^ 4 = u := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hu0)]
      norm_num
    have hw : 8 ≤ c * u ^ ((1 : ℝ) / 4) := by
      have h4 : (8 / c) ^ 4 < (u ^ ((1 : ℝ) / 4)) ^ 4 := by rw [hpow4]; exact h
      have h8c : (0 : ℝ) ≤ 8 / c := by positivity
      have hup : (0 : ℝ) ≤ u ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hu0.le _
      have hp : (0 : ℝ) ≤ c * u ^ ((1 : ℝ) / 4) := by positivity
      have h5 : (8 / c) ^ 4 ≤ (u ^ ((1 : ℝ) / 4)) ^ 4 := le_of_lt h4
      have h6 : (8 / c) ≤ u ^ ((1 : ℝ) / 4) := by
        by_contra hc'
        have hc'' : u ^ ((1 : ℝ) / 4) < 8 / c := not_le.mp hc'
        have h7 : (u ^ ((1 : ℝ) / 4)) ^ 4 < (8 / c) ^ 4 :=
          (pow_lt_pow_iff_left₀ hup h8c (by norm_num : (4 : ℕ) ≠ 0)).mpr hc''
        linarith only [h, hpow4, h7]
      calc (8 : ℝ) = c * (8 / c) := by field_simp
        _ ≤ c * u ^ ((1 : ℝ) / 4) := mul_le_mul_of_nonneg_left h6 hc.le
    have hkey : 2 * Real.log u ≤ c * Real.sqrt u := by
      have h2 : 2 * Real.log u ≤ 8 * u ^ ((1 : ℝ) / 4) := by linarith only [hlogu]
      have hupos : 0 < u ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hu0 _
      have h3 : 8 * u ^ ((1 : ℝ) / 4) ≤ c * (u ^ ((1 : ℝ) / 4)) ^ 2 := by
        have := mul_le_mul_of_nonneg_right hw hupos.le
        linarith only [this]
      rw [hpow] at h3
      linarith only [h2, h3, hlogu]
    have hexp : Real.exp (-(c * Real.sqrt u)) ≤ Real.exp (-(2 * Real.log u)) := by
      rw [Real.exp_le_exp]
      linarith only [hkey]
    have hval : Real.exp (-(2 * Real.log u)) = 1 / u ^ 2 := by
      rw [show -(2 * Real.log u) = -(Real.log (u ^ 2)) by
        rw [Real.log_pow]; norm_num]
      rw [Real.exp_neg, Real.exp_log (by positivity), one_div]
    calc Real.exp (-(c * Real.sqrt u)) ≤ Real.exp (-(2 * Real.log u)) := hexp
      _ = 1 / u ^ 2 := hval
      _ ≤ ((8 / c) ^ 8 + 1) / u ^ 2 := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have h8 : (0 : ℝ) ≤ (8 / c) ^ 8 := by positivity
          nlinarith only [h8, sq_nonneg u]

lemma cz_sum_Icc_split' (T A : ℕ) (hA : A ≤ T) (F : ℕ → ℝ) :
    (∑ t ∈ Finset.Icc 1 T, F t) = (∑ t ∈ Finset.Icc 1 A, F t)
      + (∑ t ∈ Finset.Icc (A + 1) T, F t) := by
  rw [← Finset.sum_union]
  · congr 1
    ext t
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  · rw [Finset.disjoint_left]
    intro t h1 h2
    simp only [Finset.mem_Icc] at h1 h2
    omega

/-- Part 1 of the harmonic bound: the range where the logarithm is at least `1`. -/
lemma cz_harm_part1 (c : ℝ) (hc : 0 < c) {A : ℝ} {M : ℕ}
    (hM1 : (M : ℝ) + 1 ≤ A / Real.exp 1) (hM2 : (M : ℝ) ≤ A / Real.exp 2) :
    (∑ q ∈ Finset.Icc 1 M, (1 / (q : ℝ)) * czEps c (A / (q : ℝ)))
      ≤ 2 * ((8 / c) ^ 8 + 1) := by
  have hpoint : ∀ q ∈ Finset.Icc 1 M,
      (1 / (q : ℝ)) * czEps c (A / (q : ℝ))
        ≤ ((8 / c) ^ 8 + 1) * ((1 / (q : ℝ)) * (1 / (Real.log (A / (q : ℝ))) ^ 2)) := by
    intro q hq
    obtain ⟨hq1, hqM⟩ := Finset.mem_Icc.mp hq
    have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
    have hqM' : (q : ℝ) ≤ (M : ℝ) := by exact_mod_cast hqM
    have hqAe : (q : ℝ) ≤ A / Real.exp 2 := le_trans hqM' hM2
    have hAq2 : Real.exp 2 ≤ A / (q : ℝ) := by
      rw [le_div_iff₀ hq0]
      rw [le_div_iff₀ (Real.exp_pos 2)] at hqAe
      linarith only [hqAe]
    have hlog1 : 1 ≤ Real.log (A / (q : ℝ)) := by
      have h2 := Real.log_le_log (Real.exp_pos 2) hAq2
      rw [Real.log_exp] at h2
      linarith only [h2]
    have hb := cz_exp_bound c hc hlog1
    calc (1 / (q : ℝ)) * czEps c (A / (q : ℝ))
        = (1 / (q : ℝ))
            * Real.exp (-(c * Real.sqrt (Real.log (A / (q : ℝ))))) := rfl
      _ ≤ (1 / (q : ℝ))
            * (((8 / c) ^ 8 + 1) / Real.log (A / (q : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = ((8 / c) ^ 8 + 1) * ((1 / (q : ℝ)) * (1 / Real.log (A / (q : ℝ)) ^ 2)) := by ring
  calc (∑ q ∈ Finset.Icc 1 M, (1 / (q : ℝ)) * czEps c (A / (q : ℝ)))
      ≤ ∑ q ∈ Finset.Icc 1 M,
          ((8 / c) ^ 8 + 1) * ((1 / (q : ℝ)) * (1 / (Real.log (A / (q : ℝ))) ^ 2)) :=
        Finset.sum_le_sum hpoint
    _ = ((8 / c) ^ 8 + 1) * (∑ q ∈ Finset.Icc 1 M,
          (1 / (q : ℝ)) * (1 / (Real.log (A / (q : ℝ))) ^ 2)) := by
        rw [Finset.mul_sum]
    _ ≤ ((8 / c) ^ 8 + 1) * (2 / Real.log (A / ((M : ℝ) + 1))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply cz_weight_le
        · have h2 : (1 : ℝ) ≤ A / Real.exp 1 := le_trans (by
            have h3 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
            linarith only []) hM1
          have h4 : Real.exp 1 ≤ A := by
            rw [le_div_iff₀ (Real.exp_pos 1)] at h2
            linarith only [h2]
          have h5 : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
          linarith only [h4, h5]
        · exact hM1
    _ ≤ ((8 / c) ^ 8 + 1) * 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hMP : (0 : ℝ) < (M : ℝ) + 1 := by
          have : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
          linarith only []
        have h4 : ((M : ℝ) + 1) * Real.exp 1 ≤ A := by
          have h5 := mul_le_mul_of_nonneg_right hM1 (Real.exp_pos 1).le
          rwa [div_mul_cancel₀ _ (ne_of_gt (Real.exp_pos 1))] at h5
        have hlogpos : 0 < Real.log (A / ((M : ℝ) + 1)) := by
          apply Real.log_pos
          rw [one_lt_div hMP]
          have h2 : (1 : ℝ) ≤ (M : ℝ) + 1 := by linarith only []
          have h5 : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
          nlinarith only [h2, h4, h5, hMP]
        have h3 : (1 : ℝ) ≤ Real.log (A / ((M : ℝ) + 1)) := by
          have h5 : Real.exp 1 ≤ A / ((M : ℝ) + 1) := by
            rw [le_div_iff₀ hMP]
            linarith only [h4]
          have h6 := Real.log_le_log (Real.exp_pos 1) h5
          rwa [Real.log_exp] at h6
        rw [div_le_iff₀ hlogpos]
        linarith only [h3]
    _ = 2 * ((8 / c) ^ 8 + 1) := by ring

/-- Part 2 of the harmonic bound: the remaining range. -/
lemma cz_harm_part2 (c : ℝ) (hc : 0 < c) {A : ℝ} {Q M : ℕ} (hQ : (Q : ℝ) ≤ 2 * A)
    (hM : Q ≤ M ∨ A / Real.exp 2 ≤ (M : ℝ) + 1) :
    (∑ q ∈ Finset.Icc (M + 1) Q, (1 / (q : ℝ)) * czEps c (A / (q : ℝ)))
      ≤ 2 * Real.exp 2 := by
  rcases hM with hM | hM
  · rw [show (Finset.Icc (M + 1) Q : Finset ℕ) = ∅ from by simp [Finset.Icc_eq_empty_iff]; omega,
      Finset.sum_empty]
    positivity
  have hpoint : ∀ q ∈ Finset.Icc (M + 1) Q,
      (1 / (q : ℝ)) * czEps c (A / (q : ℝ)) ≤ 1 / ((M : ℝ) + 1) := by
    intro q hq
    obtain ⟨hq1, hqQ⟩ := Finset.mem_Icc.mp hq
    have hq0 : (0 : ℝ) < (q : ℝ) := by
      have : 0 < q := by omega
      exact_mod_cast this
    have hMq : ((M : ℝ) + 1) ≤ (q : ℝ) := by
      have : ((M + 1 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
      simpa using this
    have hMpos : 0 < (M : ℝ) + 1 := by positivity
    have h1 : 1 / (q : ℝ) ≤ 1 / ((M : ℝ) + 1) := by
      rw [div_le_div_iff₀ hq0 hMpos]
      linarith only [hMq]
    have h2 : czEps c (A / (q : ℝ)) ≤ 1 := czEps_le_one (c := c) (x := A / (q : ℝ)) (le_of_lt hc)
    have h3 : 0 < czEps c (A / (q : ℝ)) := czEps_pos c _
    have h4 : (1 / (q : ℝ)) * czEps c (A / (q : ℝ))
        ≤ (1 / ((M : ℝ) + 1)) * czEps c (A / (q : ℝ)) :=
      mul_le_mul_of_nonneg_right h1 h3.le
    have h5 : (1 / ((M : ℝ) + 1)) * czEps c (A / (q : ℝ)) ≤ (1 / ((M : ℝ) + 1)) * 1 :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith only [h4, h5]
  calc (∑ q ∈ Finset.Icc (M + 1) Q, (1 / (q : ℝ)) * czEps c (A / (q : ℝ)))
      ≤ ∑ q ∈ Finset.Icc (M + 1) Q, 1 / ((M : ℝ) + 1) := Finset.sum_le_sum hpoint
    _ = ((Finset.Icc (M + 1) Q).card : ℝ) * (1 / ((M : ℝ) + 1)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Q : ℝ) * (1 / ((M : ℝ) + 1)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [Nat.card_Icc]
        have h1 : Q + 1 - (M + 1) ≤ Q := by omega
        exact_mod_cast h1
    _ ≤ 2 * Real.exp 2 := by
        have h1 : (0 : ℝ) < Real.exp 2 := Real.exp_pos 2
        rw [show (Q : ℝ) * (1 / ((M : ℝ) + 1)) = (Q : ℝ) / ((M : ℝ) + 1) by ring]
        rw [div_le_iff₀ (by positivity)]
        have h2 : A ≤ Real.exp 2 * ((M : ℝ) + 1) := by
          have h3 : (A / Real.exp 2) * Real.exp 2 ≤ ((M : ℝ) + 1) * Real.exp 2 :=
            mul_le_mul_of_nonneg_right hM h1.le
          rw [div_mul_cancel₀ A (ne_of_gt h1)] at h3
          linarith only [h3]
        linarith only [hQ, h2, h1]

/-- **The harmonic sum against the decaying envelope is bounded.** -/
theorem czHarmDecay' (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : ℝ) (Q : ℕ), 0 < A → (Q : ℝ) ≤ 2 * A →
      ∑ q ∈ Finset.Icc 1 Q, (1 / (q : ℝ)) * czEps c (A / (q : ℝ)) ≤ C := by
  refine ⟨20 + (2 * ((8 / c) ^ 8 + 1) + 2 * Real.exp 2) + 1, by positivity, ?_⟩
  intro A Q hA hQ
  by_cases hAe : A ≤ Real.exp 2
  · have hQ20 : Q ≤ 20 := by
      have h1 : (Q : ℝ) ≤ 2 * Real.exp 2 := le_trans hQ (by linarith only [hAe])
      have h2 : (2 : ℝ) * Real.exp 2 < 20 := by
        have h3 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
          rw [← Real.exp_add]; norm_num
        have h4 : Real.exp 1 < 3 := Real.exp_one_lt_three
        rw [h3]
        nlinarith only [Real.exp_pos 1, h4]
      have h5 : (Q : ℝ) ≤ 20 := by linarith only [hQ, hAe, h2]
      exact_mod_cast h5
    calc (∑ q ∈ Finset.Icc 1 Q, (1 / (q : ℝ)) * czEps c (A / (q : ℝ)))
        ≤ ∑ q ∈ Finset.Icc 1 Q, (1 : ℝ) := by
          refine Finset.sum_le_sum (fun q hq => ?_)
          have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
          have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
          have h1 : 1 / (q : ℝ) ≤ 1 := by rw [div_le_one hq0]; exact_mod_cast hq1
          have h2 : czEps c (A / (q : ℝ)) ≤ 1 := czEps_le_one (c := c) (x := A / (q : ℝ)) (le_of_lt hc)
          have h3 : 0 < czEps c (A / (q : ℝ)) := czEps_pos c _
          nlinarith only [h1, h2, h3]
      _ = (Q : ℝ) := by simp
      _ ≤ 20 := by exact_mod_cast hQ20
      _ ≤ 20 + (2 * ((8 / c) ^ 8 + 1) + 2 * Real.exp 2) + 1 := by
          have h5 : (0 : ℝ) ≤ 2 * ((8 / c) ^ 8 + 1) + 2 * Real.exp 2 := by positivity
          linarith only [h5]
  · push Not at hAe
    set M : ℕ := min Q ⌊A / Real.exp 2⌋₊ with hMdef
    have hMQ : M ≤ Q := by rw [hMdef]; exact min_le_left _ _
    have hM2 : (M : ℝ) ≤ A / Real.exp 2 := by
      have h1 : ((min Q ⌊A / Real.exp 2⌋₊ : ℕ) : ℝ) ≤ ((⌊A / Real.exp 2⌋₊ : ℕ) : ℝ) := by
        exact_mod_cast min_le_right Q ⌊A / Real.exp 2⌋₊
      have h2 : ((⌊A / Real.exp 2⌋₊ : ℕ) : ℝ) ≤ A / Real.exp 2 := Nat.floor_le (by positivity)
      rw [hMdef]
      linarith only [h1, h2]
    have hM1 : (M : ℝ) + 1 ≤ A / Real.exp 1 := by
      have he : Real.exp 1 < Real.exp 2 := Real.exp_lt_exp.mpr (by norm_num)
      have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      have h1 : A / Real.exp 2 + 1 ≤ A / Real.exp 1 := by
        rw [div_add' _ _ _ (ne_of_gt (Real.exp_pos 2)),
          show A + 1 * Real.exp 2 = A + Real.exp 2 by ring,
          div_le_div_iff₀ (Real.exp_pos 2) (Real.exp_pos 1)]
        have he1 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
        have he3 : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
        have hA2 : Real.exp 1 * Real.exp 1 < A := by rw [← he2]; exact hAe
        nlinarith only [he1, he3, hA2, mul_pos he1 he1, mul_pos (mul_pos he1 he1) he1, he2, hA, hAe, he]
      linarith only [hM2, h1]
    have hcase : Q ≤ M ∨ A / Real.exp 2 ≤ (M : ℝ) + 1 := by
      by_cases h : Q ≤ M
      · exact Or.inl h
      · right
        have hlt : M < Q := not_le.mp h
        have hB : ⌊A / Real.exp 2⌋₊ ≤ Q := by
          by_contra hc
          push Not at hc
          have h1 : M = Q := by
            rw [hMdef]
            exact min_eq_left (le_of_lt hc)
          omega
        have h1 : M = ⌊A / Real.exp 2⌋₊ := by
          rw [hMdef]
          exact min_eq_right hB
        rw [h1]
        have h2 := Nat.lt_floor_add_one (A / Real.exp 2)
        linarith only [h2]
    calc (∑ q ∈ Finset.Icc 1 Q, (1 / (q : ℝ)) * czEps c (A / (q : ℝ)))
        = (∑ q ∈ Finset.Icc 1 M, (1 / (q : ℝ)) * czEps c (A / (q : ℝ)))
          + (∑ q ∈ Finset.Icc (M + 1) Q, (1 / (q : ℝ)) * czEps c (A / (q : ℝ))) :=
          cz_sum_Icc_split' Q M hMQ _
      _ ≤ 2 * ((8 / c) ^ 8 + 1) + 2 * Real.exp 2 :=
          add_le_add (cz_harm_part1 c hc hM1 hM2) (cz_harm_part2 c hc hQ hcase)
      _ ≤ 20 + (2 * ((8 / c) ^ 8 + 1) + 2 * Real.exp 2) + 1 := by
          have h5 : (0 : ℝ) ≤ 20 + 1 := by norm_num
          linarith only []

end

end Work.ZeroDensity.Jutila.BzCross
