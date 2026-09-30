import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.ztw_defs
import Submission.Work.BMF.N7.vk_interface
import Submission.Work.BMF.N7.mixing_v3
import Submission.Work.BMF.N7.logDeriv_LFunction_VK_of_growth_zf
import Submission.Work.BMF.N7.ztw_paramN7
import Submission.Work.BMF.liouville.zeta_tw_perron
import Submission.Work.BMF.liouville.zetaTwPerron_rect
import Submission.Work.BMF.liouville.zeta_logDeriv_near_four
import Submission.Work.BMF.liouville.zeta_tw_vk_sum
import Submission.Work.BMF.liouville.cpow_one_sub_I_mul_sub_le
import Submission.Work.BMF.liouville.zetaTwSum_small_x

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 10000000

/-! # V6: the twisted prime number theorem for the principal character

`Σ_{n ≤ x} Λ(n) n^{-iu} = x^{1-iu}/(1-iu) + O(x exp(-c (log x)^{1/12}))` uniformly for
`|u| ≤ exp((log x)^{21/20})`.

Route: the truncated twisted Perron formula at `Re w = 1 + 1/log x` (`zetaTwPerron_sub_sum`),
the rectangle shift with the single interior pole of `ζ` at `w = 1 - iu`
(`zetaTwPerron_rect`, residue `x^{1-iu}/(1-iu)`), and the bounds for the three other edges
(`norm_zetaTwLeft_le`, `norm_horiz_edge_le`) using the `6/7`-shaped zero-free region and
logarithmic-derivative bound for `ζ` supplied by `Work.BMF.logDeriv_LFunction_VK` (V4) at the
trivial character mod `1`, together with the near-axis data `zeta_logDeriv_near_four`.
-/

namespace Work.BMF.N7

open Finset Filter
open scoped Real Topology

noncomputable section

/-! ## The twisted Perron engine for the `6/7`-shaped zero-free region -/

open Work.BMF.liouville

/-- **The twisted prime number theorem for `ζ` from the `6/7`-shaped zero-free region.**

Inputs: the zero-free region and the logarithmic-derivative bound for `ζ` in the `6/7` shape
(heights `≥ 4`, `σ ≤ 2`), the near-axis data at heights `≤ 4`, the truncation error for the
twisted Perron integral, and the elementary parameter package `hparam`.  Output: for every
non-integer `y` beyond a threshold and every `|u| ≤ exp((log y)^{21/20})`,
`‖Σ_{n ≤ y} Λ(n) n^{-iu} - y^{1-iu}/(1-iu)‖ ≤ y exp(-(κ/16)(log y)^{1/12})`. -/
theorem zetaTwSum_main_le_of_region
    (κ δ₅ C₅ C Ctr : ℝ) (hκ : 0 < κ) (hδ₅ : 0 < δ₅) (hC₅ : 0 < C₅) (hC : 0 < C)
    (hCtr : 0 < Ctr)
    (hreg : ∀ t σ : ℝ, 4 ≤ |t| → 1 - κ / ztD |t| ≤ σ → σ ≤ 2 →
      riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hlog : ∀ t σ : ℝ, 4 ≤ |t| → 1 - κ / ztD |t| ≤ σ → σ ≤ 2 →
      ‖deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) /
        riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (Real.log (|t| + 3)) ^ 4)
    (hnearld : ∀ t σ : ℝ, |t| ≤ 4 → σ ≠ 1 → 1 - δ₅ ≤ σ → σ ≤ 2 →
      ‖deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) /
        riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C₅ + 1 / ‖((σ : ℂ) + (t : ℂ) * Complex.I) - 1‖)
    (hnearzz : ∀ t σ : ℝ, |t| ≤ 4 → 1 - δ₅ ≤ σ → σ ≤ 2 →
      riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (htrunc : ∀ u x T : ℝ, 3 ≤ x → (∀ n : ℕ, (n : ℝ) ≠ x) → 2 ≤ T →
      ‖zetaTwPerron u x T - zetaTwSum u x‖ ≤ Ctr * (x * (Real.log x) ^ 2 / T + Real.log x))
    (hparam : ∀ᶠ L : ℝ in Filter.atTop, ∀ u : ℝ, |u| ≤ Real.exp (L ^ (21 / 20 : ℝ)) →
      Real.log (2 * twT L u + 3) ≤ 2 * L ^ (21 / 20 : ℝ) ∧
      twD L u ≤ 2 * L ^ (11 / 12 : ℝ) ∧
      twδ κ L u ≤ min δ₅ (1 / 4) ∧
      Ctr * (Real.exp L * L ^ 2 / twT L u + L) ≤
        (1 / 8) * (Real.exp L * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ)))) ∧
      8 * (max (C * (Real.log (2 * twT L u + 3)) ^ 2) (C₅ + 1 / twδ κ L u)) *
          (Real.log (|u| + twT L u + 3)) ^ 2 * ((twδ κ L u + 1 / L) / twT L u) ≤
        (1 / 8) * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ))) ∧
      4 * (max (C * (Real.log (2 * twT L u + 3)) ^ 2) (C₅ + 1 / twδ κ L u)) *
          (Real.log (|u| + twT L u + 3)) ^ 2 *
          (2 * Real.sqrt 2 * Real.log (1 + twT L u / twσ κ L u)) ≤
        (1 / 8) * Real.exp ((κ / 16) * L ^ (1 / 12 : ℝ))) :
    ∃ N₀ : ℝ, ∀ y : ℝ, N₀ ≤ y → (∀ n : ℕ, (n : ℝ) ≠ y) → ∀ u : ℝ,
      |u| ≤ Real.exp ((Real.log y) ^ (21 / 20 : ℝ)) →
      ‖zetaTwSum u y - (y : ℂ) ^ (1 - Complex.I * (u : ℂ)) / (1 - Complex.I * (u : ℂ))‖
        ≤ y * Real.exp (-((κ / 16) * (Real.log y) ^ (1 / 12 : ℝ))) := by
  obtain ⟨Λ, hΛ⟩ := Filter.eventually_atTop.mp hparam
  refine ⟨max 3 (Real.exp Λ), ?_⟩
  intro y hy hyNat u hu
  have hy3 : 3 ≤ y := le_trans (le_max_left _ _) hy
  have hyexp : Real.exp Λ ≤ y := le_trans (le_max_right _ _) hy
  have hypos : 0 < y := by linarith
  have hy1 : 1 < y := by linarith
  set L : ℝ := Real.log y with hLdef
  have hL : Λ ≤ L := by
    rw [hLdef]
    have h := Real.log_le_log (Real.exp_pos Λ) hyexp
    rwa [Real.log_exp] at h
  have hLlog3 : Real.log 3 ≤ L := by
    rw [hLdef]; exact Real.log_le_log (by norm_num) hy3
  have hL1 : 1 ≤ L := le_trans one_le_log_three hLlog3
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hylog : Real.exp L = y := by rw [hLdef, Real.exp_log hypos]
  have huL : |u| ≤ Real.exp (L ^ (21 / 20 : ℝ)) := by
    rw [hLdef] at hu
    exact hu
  obtain ⟨hP1, hP2, hP3, hP4, hP5, hP6⟩ := hΛ L hL u huL
  set B : ℝ := max (C * (Real.log (2 * twT L u + 3)) ^ 2) (C₅ + 1 / twδ κ L u) with hBdef
  set T : ℝ := twT L u with hTdef
  set D : ℝ := twD L u with hDdef
  set δ : ℝ := twδ κ L u with hδdef
  set σ₁ : ℝ := twσ κ L u with hσdef
  have hT7 : 7 ≤ T := by rw [hTdef]; exact seven_le_twT L u
  have hTpos : 0 < T := by linarith
  have hT2 : 2 ≤ T := by linarith
  have huT : |u| < T := by rw [hTdef]; exact abs_lt_twT L u
  have hDpos : 0 < D := by rw [hDdef]; exact twD_pos L u
  have hδpos : 0 < δ := by rw [hδdef]; exact twδ_pos hκ
  have hδδ₅ : δ ≤ δ₅ := le_trans hP3 (min_le_left _ _)
  have hδ4 : δ ≤ 1 / 4 := le_trans hP3 (min_le_right _ _)
  have hσpos : 0 < σ₁ := by rw [hσdef, twσ]; linarith
  have hσlt1 : σ₁ < 1 := by rw [hσdef, twσ]; linarith
  have hσle2 : σ₁ ≤ 2 := by linarith
  have hσinv : 1 - σ₁ = δ := by rw [hσdef, twσ]; ring
  have hσlt : σ₁ < 1 + 1 / L := by
    have h1 : 0 < 1 / L := by positivity
    linarith
  have hBnn : 0 ≤ B := le_max_of_le_left (by positivity)
  have hB1 : C * (Real.log (2 * T + 3)) ^ 2 ≤ B := le_max_left _ _
  have hB2 : C₅ + 1 / δ ≤ B := le_max_right _ _
  -- the zero-free region applies at every height `≤ 2T` and abscissa `≥ σ₁`
  have hztD_le : ∀ h : ℝ, 4 ≤ h → h ≤ 2 * T → ztD h ≤ D := by
    intro h h4 hh
    rw [hDdef, twD]
    have h3 : Real.log (h + 3) ≤ Real.log (2 * T + 3) :=
      Real.log_le_log (by linarith) (by linarith)
    have hA : 1 ≤ Real.log (2 * T + 3) :=
      le_trans one_le_log_three
        (Real.log_le_log (by norm_num : (0 : ℝ) < 3) (by linarith : (3 : ℝ) ≤ 2 * T + 3))
    exact ztD_le_of_log_le h4 hA h3
  have hreg_app : ∀ t σ : ℝ, 4 ≤ |t| → |t| ≤ 2 * T → σ₁ ≤ σ → σ ≤ 2 →
      riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro t σ ht4 htT hσ1 hσ2
    refine hreg t σ ht4 ?_ hσ2
    have hzt : ztD |t| ≤ D := hztD_le |t| ht4 htT
    have hzp : 0 < ztD |t| := ztD_pos ht4
    have hδle : δ ≤ κ / ztD |t| := by
      have hδeq : δ = κ / (4 * D) := by rw [hδdef, twδ]
      rw [hδeq]
      exact div_le_div_of_nonneg_left hκ.le hzp (by linarith [hzt])
    linarith [hδle, hσinv, hσ1]
  have hlog_app : ∀ t σ : ℝ, 4 ≤ |t| → |t| ≤ 2 * T → σ₁ ≤ σ → σ ≤ 2 →
      ‖deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) /
        riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (Real.log (|t| + 3)) ^ 4 := by
    intro t σ ht4 htT hσ1 hσ2
    refine hlog t σ ht4 ?_ hσ2
    have hzt : ztD |t| ≤ D := hztD_le |t| ht4 htT
    have hzp : 0 < ztD |t| := ztD_pos ht4
    have hδle : δ ≤ κ / ztD |t| := by
      have hδeq : δ = κ / (4 * D) := by rw [hδdef, twδ]
      rw [hδeq]
      exact div_le_div_of_nonneg_left hκ.le hzp (by linarith [hzt])
    linarith [hδle, hσinv, hσ1]
  have hne1 : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ 1 + 1 / L → |s.im - u| ≤ T → s ≠ 1 →
      riemannZeta s ≠ 0 := by
    intro s hs1 hs2 hsim hsne hz0
    have h1L : 1 / L ≤ 1 := by
      rw [div_le_one hLpos]; exact hL1
    have hsle2 : s.re ≤ 2 := by linarith [hs2, h1L]
    have hz0' : riemannZeta ((s.re : ℂ) + (s.im : ℂ) * Complex.I) = 0 := by
      rw [Complex.re_add_im s]
      exact hz0
    by_cases h4 : 4 ≤ |s.im|
    · have h2T : |s.im| ≤ 2 * T := by
        have h3 : |s.im| - |u| ≤ |s.im - u| := abs_sub_abs_le_abs_sub s.im u
        have h6 : (0:ℝ) ≤ |u| := abs_nonneg u
        linarith [hsim, huT, abs_nonneg u]
      exact hreg_app s.im s.re h4 h2T hs1 hsle2 hz0'
    · push Not at h4
      exact hnearzz s.im s.re (le_of_lt h4) (by linarith [hs1, hσinv, hδδ₅]) hsle2 hz0'
  have hrect := zetaTwPerron_rect u y T σ₁ hy1 hTpos hσpos hσlt1 hσlt huT hne1
  have htr : ‖zetaTwPerron u y T - zetaTwSum u y‖ ≤ Ctr * (y * L ^ 2 / T + L) := by
    have h := htrunc u y T hy3 hyNat hT2
    rw [← hLdef] at h
    exact h
  -- the log-derivative bound along the left edge
  have hDleft : ∀ t : ℝ, |t| ≤ T →
      ‖deriv riemannZeta ((σ₁ : ℂ) + ((t + u : ℝ) : ℂ) * Complex.I) /
        riemannZeta ((σ₁ : ℂ) + ((t + u : ℝ) : ℂ) * Complex.I)‖ ≤
        B * (Real.log (|t + u| + 3)) ^ 2 := by
    intro t ht
    have h2T : |t + u| ≤ 2 * T := by
      calc |t + u| ≤ |t| + |u| := abs_add_le t u
        _ ≤ T + T := by linarith [le_of_lt huT]
        _ = 2 * T := by ring
    have hlogm : Real.log (|t + u| + 3) ≤ Real.log (2 * T + 3) :=
      Real.log_le_log (by positivity) (by linarith)
    have hpos : 0 ≤ Real.log (|t + u| + 3) :=
      Real.log_nonneg (by linarith [abs_nonneg (t + u)])
    have hsq : (Real.log (|t + u| + 3)) ^ 2 ≤ (Real.log (2 * T + 3)) ^ 2 := by nlinarith
    by_cases h4 : 4 ≤ |t + u|
    · have h := hlog_app (t + u) σ₁ h4 h2T le_rfl hσle2
      calc ‖deriv riemannZeta ((σ₁ : ℂ) + ((t + u : ℝ) : ℂ) * Complex.I) /
            riemannZeta ((σ₁ : ℂ) + ((t + u : ℝ) : ℂ) * Complex.I)‖
          ≤ C * (Real.log (|t + u| + 3)) ^ 4 := h
        _ = C * (Real.log (|t + u| + 3)) ^ 2 * (Real.log (|t + u| + 3)) ^ 2 := by ring
        _ ≤ C * (Real.log (2 * T + 3)) ^ 2 * (Real.log (|t + u| + 3)) ^ 2 := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              exact mul_le_mul_of_nonneg_left hsq hC.le
        _ ≤ B * (Real.log (|t + u| + 3)) ^ 2 :=
              mul_le_mul_of_nonneg_right hB1 (by positivity)
    · push Not at h4
      have h := hnearld (t + u) σ₁ (le_of_lt h4) (ne_of_lt hσlt1)
        (by linarith [hσinv, hδδ₅]) hσle2
      have hden : δ ≤ ‖((σ₁ : ℂ) + ((t + u : ℝ) : ℂ) * Complex.I) - 1‖ := by
        have hre : (((σ₁ : ℂ) + ((t + u : ℝ) : ℂ) * Complex.I) - 1).re = σ₁ - 1 := by simp
        calc δ = |σ₁ - 1| := by
              rw [abs_of_neg (by linarith)]
              linarith [hσinv]
          _ = |(((σ₁ : ℂ) + ((t + u : ℝ) : ℂ) * Complex.I) - 1).re| := by rw [hre]
          _ ≤ ‖((σ₁ : ℂ) + ((t + u : ℝ) : ℂ) * Complex.I) - 1‖ :=
                Complex.abs_re_le_norm _
      have h2 : 1 / ‖((σ₁ : ℂ) + ((t + u : ℝ) : ℂ) * Complex.I) - 1‖ ≤ 1 / δ :=
        one_div_le_one_div_of_le hδpos hden
      have hlog3 : 1 ≤ Real.log (|t + u| + 3) :=
        le_trans one_le_log_three
          (Real.log_le_log (by norm_num) (by linarith [abs_nonneg (t + u)]))
      have hsq1 : 1 ≤ (Real.log (|t + u| + 3)) ^ 2 := by nlinarith
      have hC5' : C₅ ≤ C₅ * (Real.log (|t + u| + 3)) ^ 2 := le_mul_of_one_le_right hC₅.le hsq1
      have hInv : 1 / ‖((σ₁ : ℂ) + ((t + u : ℝ) : ℂ) * Complex.I) - 1‖ ≤
          (1 / δ) * (Real.log (|t + u| + 3)) ^ 2 :=
        le_trans h2 (le_mul_of_one_le_right (by positivity) hsq1)
      have hsum : C₅ + 1 / ‖((σ₁ : ℂ) + ((t + u : ℝ) : ℂ) * Complex.I) - 1‖ ≤
          (C₅ + 1 / δ) * (Real.log (|t + u| + 3)) ^ 2 := by
        have hh : (C₅ + 1 / δ) * (Real.log (|t + u| + 3)) ^ 2 =
            C₅ * (Real.log (|t + u| + 3)) ^ 2 + (1 / δ) * (Real.log (|t + u| + 3)) ^ 2 := by ring
        rw [hh]; linarith
      calc ‖deriv riemannZeta ((σ₁ : ℂ) + ((t + u : ℝ) : ℂ) * Complex.I) /
            riemannZeta ((σ₁ : ℂ) + ((t + u : ℝ) : ℂ) * Complex.I)‖
          ≤ C₅ + 1 / ‖((σ₁ : ℂ) + ((t + u : ℝ) : ℂ) * Complex.I) - 1‖ := h
        _ ≤ (C₅ + 1 / δ) * (Real.log (|t + u| + 3)) ^ 2 := hsum
        _ ≤ B * (Real.log (|t + u| + 3)) ^ 2 :=
              mul_le_mul_of_nonneg_right hB2 (by positivity)
  have hleft := norm_zetaTwLeft_le (u := u) (x := y) (T := T) (σ₁ := σ₁) (B := B)
    hy1 hTpos hσpos hBnn hDleft
  -- the log-derivative bound along the horizontal edges
  have hDh : ∀ (r : ℝ), |r| = T → ∀ v : ℝ, σ₁ ≤ v → v ≤ 1 + 1 / L →
      ‖deriv riemannZeta ((v : ℂ) + ((r + u : ℝ) : ℂ) * Complex.I) /
        riemannZeta ((v : ℂ) + ((r + u : ℝ) : ℂ) * Complex.I)‖ ≤
        B * (Real.log (|r + u| + 3)) ^ 2 := by
    intro r hr v hv1 hv2
    have hru : T - |u| ≤ |r + u| := by
      have h2 : |r - -u| = |r + u| := by ring_nf
      have h1 := abs_sub_abs_le_abs_sub r (-u)
      rw [h2, abs_neg, hr] at h1
      exact h1
    have h4 : 4 ≤ |r + u| := by
      have hTu : T - |u| = L ^ 2 * Real.exp (L ^ (1 / 10 : ℝ)) + 7 := by
        rw [hTdef, twT]; ring
      have h7 : 7 ≤ T - |u| := by
        rw [hTu]
        have h1 : 0 ≤ L ^ 2 * Real.exp (L ^ (1 / 10 : ℝ)) := by positivity
        linarith
      linarith [hru, h7]
    have h2T : |r + u| ≤ 2 * T := by
      calc |r + u| ≤ |r| + |u| := abs_add_le r u
        _ ≤ T + T := by linarith [le_of_lt huT]
        _ = 2 * T := by ring
    have hv2' : v ≤ 2 := by
      have h1L : 1 / L ≤ 1 := by rw [div_le_one hLpos]; exact hL1
      linarith [hv2, h1L]
    have h := hlog_app (r + u) v h4 h2T hv1 hv2'
    have hlogm : Real.log (|r + u| + 3) ≤ Real.log (2 * T + 3) :=
      Real.log_le_log (by positivity) (by linarith)
    have hpos : 0 ≤ Real.log (|r + u| + 3) :=
      Real.log_nonneg (by linarith [abs_nonneg (r + u)])
    have hsq : (Real.log (|r + u| + 3)) ^ 2 ≤ (Real.log (2 * T + 3)) ^ 2 := by nlinarith
    calc ‖deriv riemannZeta ((v : ℂ) + ((r + u : ℝ) : ℂ) * Complex.I) /
          riemannZeta ((v : ℂ) + ((r + u : ℝ) : ℂ) * Complex.I)‖
        ≤ C * (Real.log (|r + u| + 3)) ^ 4 := h
      _ = C * (Real.log (|r + u| + 3)) ^ 2 * (Real.log (|r + u| + 3)) ^ 2 := by ring
      _ ≤ C * (Real.log (2 * T + 3)) ^ 2 * (Real.log (|r + u| + 3)) ^ 2 := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_left hsq hC.le
      _ ≤ B * (Real.log (|r + u| + 3)) ^ 2 :=
            mul_le_mul_of_nonneg_right hB1 (by positivity)
  have htop := norm_horiz_edge_le (u := u) (x := y) (T := T) (σ₁ := σ₁) (B := B) (r := T)
    hy1 hσpos hTpos (le_of_lt hσlt) hBnn (by rw [abs_of_pos hTpos]) (hDh T (abs_of_pos hTpos))
  have hbot := norm_horiz_edge_le (u := u) (x := y) (T := T) (σ₁ := σ₁) (B := B) (r := -T)
    hy1 hσpos hTpos (le_of_lt hσlt) hBnn (by rw [abs_neg, abs_of_pos hTpos])
      (hDh (-T) (by rw [abs_neg, abs_of_pos hTpos]))
  have htop' : ‖zetaTwTop u y T σ₁‖ ≤ B * (Real.log (|u| + T + 3)) ^ 2 *
      y ^ (1 + 1 / L) * ((1 + 1 / L) - σ₁) / T := htop
  have hbot' : ‖zetaTwBot u y T σ₁‖ ≤ B * (Real.log (|u| + T + 3)) ^ 2 *
      y ^ (1 + 1 / L) * ((1 + 1 / L) - σ₁) / T := by
    have hcongr : (∫ v in σ₁..(1 + 1 / Real.log y),
          zetaTwG u y ((v : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) =
        ∫ v in σ₁..(1 + 1 / Real.log y), zetaTwG u y ((v : ℂ) - (T : ℂ) * Complex.I) := by
      apply intervalIntegral.integral_congr
      intro v _
      beta_reduce
      rw [show ((v : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) = (v : ℂ) - (T : ℂ) * Complex.I by
        push_cast; ring]
    rw [zetaTwBot]
    rw [← hcongr]
    exact hbot
  -- exponent conversions
  have hyfac : y ^ (1 + 1 / L) = Real.exp 1 * y := by
    have hLy : Real.log y = L := by rw [hLdef]
    rw [Real.rpow_add hypos, Real.rpow_one, Real.rpow_def_of_pos hypos, hLy]
    rw [mul_one_div, div_self (ne_of_gt hLpos)]
    ring
  have hδL : 2 * ((κ / 16) * L ^ (1 / 12 : ℝ)) ≤ δ * L := by
    have hDL : D ≤ 2 * L ^ (11 / 12 : ℝ) := hP2
    have hδle : κ / (8 * L ^ (11 / 12 : ℝ)) ≤ δ := by
      have hδeq : δ = κ / (4 * D) := by rw [hδdef, twδ]
      rw [hδeq]
      refine div_le_div_of_nonneg_left hκ.le (by positivity) ?_
      linarith [hDL]
    have h1 : (κ / (8 * L ^ (11 / 12 : ℝ))) * L ≤ δ * L :=
      mul_le_mul_of_nonneg_right hδle (le_of_lt hLpos)
    have h2 : (κ / (8 * L ^ (11 / 12 : ℝ))) * L = (κ / 8) * L ^ (1 / 12 : ℝ) := by
      rw [div_mul_eq_mul_div, div_eq_iff (ne_of_gt (by positivity : (0 : ℝ) < 8 * L ^ (11 / 12 : ℝ)))]
      rw [show (κ / 8) * L ^ (1 / 12 : ℝ) * (8 * L ^ (11 / 12 : ℝ)) =
          κ * (L ^ (1 / 12 : ℝ) * L ^ (11 / 12 : ℝ)) by ring]
      rw [← Real.rpow_add hLpos]
      norm_num
    rw [h2] at h1
    have h3 : (κ / 16) * L ^ (1 / 12 : ℝ) ≤ (κ / 8) * L ^ (1 / 12 : ℝ) := by
      have hLp := Real.rpow_pos_of_pos hLpos (1 / 12 : ℝ)
      nlinarith [hκ]
    linarith
  have hylt : y ^ σ₁ = y * Real.exp (-(δ * L)) := by
    have hσ : σ₁ = 1 - δ := by linarith [hσinv]
    have hLy : Real.log y = L := by rw [hLdef]
    rw [hσ, Real.rpow_sub hypos, Real.rpow_one, Real.rpow_def_of_pos hypos, hLy, mul_comm L δ]
    rw [div_eq_mul_inv, ← Real.exp_neg]
  -- the left edge
  have hleftb : ‖zetaTwLeft u y T σ₁‖ ≤
      (1 / 32) * (y * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ)))) := by
    have h6 : B * (Real.log (|u| + T + 3)) ^ 2 *
        (2 * Real.sqrt 2 * Real.log (1 + T / σ₁)) ≤
        (1 / 32) * Real.exp ((κ / 16) * L ^ (1 / 12 : ℝ)) := by
      have heq : 4 * B * (Real.log (|u| + T + 3)) ^ 2 *
            (2 * Real.sqrt 2 * Real.log (1 + T / σ₁)) =
          4 * (B * (Real.log (|u| + T + 3)) ^ 2 *
            (2 * Real.sqrt 2 * Real.log (1 + T / σ₁))) := by ring
      rw [heq] at hP6
      linarith [hP6]
    have hexp2 : Real.exp ((κ / 16) * L ^ (1 / 12 : ℝ)) *
        Real.exp (-(2 * ((κ / 16) * L ^ (1 / 12 : ℝ)))) =
        Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have step : ((1 / 32) * Real.exp ((κ / 16) * L ^ (1 / 12 : ℝ))) *
          (y * Real.exp (-(2 * ((κ / 16) * L ^ (1 / 12 : ℝ))))) =
        (1 / 32) * (y * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ)))) := by
      calc ((1 / 32) * Real.exp ((κ / 16) * L ^ (1 / 12 : ℝ))) *
            (y * Real.exp (-(2 * ((κ / 16) * L ^ (1 / 12 : ℝ)))))
          = (1 / 32) * y * (Real.exp ((κ / 16) * L ^ (1 / 12 : ℝ)) *
              Real.exp (-(2 * ((κ / 16) * L ^ (1 / 12 : ℝ))))) := by ring
        _ = (1 / 32) * y * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ))) := by rw [hexp2]
        _ = (1 / 32) * (y * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ)))) := by ring
    have hmid : B * (Real.log (|u| + T + 3)) ^ 2 * y ^ σ₁ *
          (2 * Real.sqrt 2 * Real.log (1 + T / σ₁)) ≤
        ((1 / 32) * Real.exp ((κ / 16) * L ^ (1 / 12 : ℝ))) *
          (y * Real.exp (-(2 * ((κ / 16) * L ^ (1 / 12 : ℝ))))) := by
      have hle : y ^ σ₁ ≤ y * Real.exp (-(2 * ((κ / 16) * L ^ (1 / 12 : ℝ)))) := by
        rw [hylt]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [hδL])) (le_of_lt hypos)
      have hfac : 0 ≤ B * (Real.log (|u| + T + 3)) ^ 2 *
          (2 * Real.sqrt 2 * Real.log (1 + T / σ₁)) := by
        have hlog1 : 1 ≤ Real.log (1 + T / σ₁) :=
          le_trans one_le_log_three
            (Real.log_le_log (by norm_num) (by
              have h1 : (3 : ℝ) ≤ T / σ₁ := by
                rw [le_div_iff₀ hσpos]
                nlinarith [hTpos, hσpos, le_of_lt hσlt1, hT7]
              linarith))
        have h2 : 0 ≤ 2 * Real.sqrt 2 * Real.log (1 + T / σ₁) := by positivity
        have h3 : 0 ≤ (Real.log (|u| + T + 3)) ^ 2 := by positivity
        have h4 : 0 ≤ B := hBnn
        positivity
      calc B * (Real.log (|u| + T + 3)) ^ 2 * y ^ σ₁ *
            (2 * Real.sqrt 2 * Real.log (1 + T / σ₁))
          = (B * (Real.log (|u| + T + 3)) ^ 2 *
              (2 * Real.sqrt 2 * Real.log (1 + T / σ₁))) * y ^ σ₁ := by ring
        _ ≤ (B * (Real.log (|u| + T + 3)) ^ 2 *
              (2 * Real.sqrt 2 * Real.log (1 + T / σ₁))) *
            (y * Real.exp (-(2 * ((κ / 16) * L ^ (1 / 12 : ℝ))))) :=
              mul_le_mul_of_nonneg_left hle hfac
        _ ≤ ((1 / 32) * Real.exp ((κ / 16) * L ^ (1 / 12 : ℝ))) *
            (y * Real.exp (-(2 * ((κ / 16) * L ^ (1 / 12 : ℝ))))) :=
              mul_le_mul_of_nonneg_right h6 (by positivity)
    calc ‖zetaTwLeft u y T σ₁‖
        ≤ B * (Real.log (|u| + T + 3)) ^ 2 * y ^ σ₁ *
            (2 * Real.sqrt 2 * Real.log (1 + T / σ₁)) := hleft
      _ ≤ ((1 / 32) * Real.exp ((κ / 16) * L ^ (1 / 12 : ℝ))) *
            (y * Real.exp (-(2 * ((κ / 16) * L ^ (1 / 12 : ℝ))))) := hmid
      _ = (1 / 32) * (y * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ)))) := step
  -- the two horizontal edges
  have hterm2 : ‖zetaTwTop u y T σ₁‖ + ‖zetaTwBot u y T σ₁‖ ≤
      (1 / 8) * (y * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ)))) := by
    have h1 : (1 + 1 / L) - σ₁ = δ + 1 / L := by linarith [hσinv]
    have h5 : B * (Real.log (|u| + T + 3)) ^ 2 * ((δ + 1 / L) / T) ≤
        (1 / 64) * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ))) := by
      have heq : 8 * B * (Real.log (|u| + T + 3)) ^ 2 * ((δ + 1 / L) / T) =
          8 * (B * (Real.log (|u| + T + 3)) ^ 2 * ((δ + 1 / L) / T)) := by ring
      rw [heq] at hP5
      linarith [hP5]
    have h2 : B * (Real.log (|u| + T + 3)) ^ 2 * y ^ (1 + 1 / L) * ((1 + 1 / L) - σ₁) / T
        = y * (Real.exp 1) * (B * (Real.log (|u| + T + 3)) ^ 2 * ((δ + 1 / L) / T)) := by
      rw [h1, hyfac]
      ring
    have hsum : ‖zetaTwTop u y T σ₁‖ + ‖zetaTwBot u y T σ₁‖ ≤
        2 * (y * (Real.exp 1) * (B * (Real.log (|u| + T + 3)) ^ 2 * ((δ + 1 / L) / T))) := by
      have h := add_le_add htop' hbot'
      rw [h2] at h
      linarith [h]
    have hfin : 2 * (y * (Real.exp 1) * (B * (Real.log (|u| + T + 3)) ^ 2 * ((δ + 1 / L) / T))) ≤
        (1 / 8) * (y * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ)))) := by
      have he : Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
      have hE := Real.exp_pos (-((κ / 16) * L ^ (1 / 12 : ℝ)))
      have hstep : 2 * (y * Real.exp 1 *
            (B * (Real.log (|u| + T + 3)) ^ 2 * ((δ + 1 / L) / T))) ≤
          2 * (y * Real.exp 1 * ((1 / 64) * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ))))) := by
        have hc : 0 ≤ 2 * (y * Real.exp 1) := by positivity
        calc 2 * (y * Real.exp 1 * (B * (Real.log (|u| + T + 3)) ^ 2 * ((δ + 1 / L) / T)))
            = (2 * (y * Real.exp 1)) *
                (B * (Real.log (|u| + T + 3)) ^ 2 * ((δ + 1 / L) / T)) := by ring
          _ ≤ (2 * (y * Real.exp 1)) *
                ((1 / 64) * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ)))) :=
                mul_le_mul_of_nonneg_left h5 hc
          _ = 2 * (y * Real.exp 1 * ((1 / 64) * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ))))) := by ring
      have h3 : 2 * (y * Real.exp 1 * ((1 / 64) * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ))))) ≤
          (1 / 8) * (y * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ)))) := by
        have h1 : 2 * (y * Real.exp 1 * ((1 / 64) * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ))))) =
            (y * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ)))) * (Real.exp 1 / 32) := by ring
        rw [h1]
        have h2 : Real.exp 1 / 32 ≤ 1 / 8 := by linarith [he]
        have h3 : 0 ≤ y * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ))) := by positivity
        calc (y * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ)))) * (Real.exp 1 / 32)
            ≤ (y * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ)))) * (1 / 8) :=
              mul_le_mul_of_nonneg_left h2 h3
          _ = (1 / 8) * (y * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ)))) := by ring
      linarith [hstep, h3]
    linarith [hsum, hfin]
  -- the truncation error
  have hterm1 : ‖zetaTwPerron u y T - zetaTwSum u y‖ ≤
      (1 / 8) * (y * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ)))) := by
    have h4 := hP4
    rw [hylog] at h4
    exact htr.trans h4
  -- assembly
  have htotal : zetaTwSum u y - (y : ℂ) ^ (1 - Complex.I * (u : ℂ)) /
      (1 - Complex.I * (u : ℂ)) =
      (zetaTwSum u y - zetaTwPerron u y T) +
        (zetaTwTop u y T σ₁ - zetaTwBot u y T σ₁ + zetaTwLeft u y T σ₁) := by
    rw [hrect]; ring
  have htri : ‖zetaTwTop u y T σ₁ - zetaTwBot u y T σ₁ + zetaTwLeft u y T σ₁‖ ≤
      ‖zetaTwTop u y T σ₁‖ + ‖zetaTwBot u y T σ₁‖ + ‖zetaTwLeft u y T σ₁‖ := by
    calc ‖zetaTwTop u y T σ₁ - zetaTwBot u y T σ₁ + zetaTwLeft u y T σ₁‖
        ≤ ‖zetaTwTop u y T σ₁ - zetaTwBot u y T σ₁‖ + ‖zetaTwLeft u y T σ₁‖ := norm_add_le _ _
      _ ≤ (‖zetaTwTop u y T σ₁‖ + ‖zetaTwBot u y T σ₁‖) + ‖zetaTwLeft u y T σ₁‖ := by
            linarith [norm_sub_le (zetaTwTop u y T σ₁) (zetaTwBot u y T σ₁)]
      _ = ‖zetaTwTop u y T σ₁‖ + ‖zetaTwBot u y T σ₁‖ + ‖zetaTwLeft u y T σ₁‖ := by ring
  have hsum3 : ‖zetaTwTop u y T σ₁ - zetaTwBot u y T σ₁ + zetaTwLeft u y T σ₁‖ ≤
      (1 / 8) * (y * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ)))) +
        (1 / 32) * (y * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ)))) := by
    linarith [htri, hterm2, hleftb]
  have hper : ‖zetaTwSum u y - zetaTwPerron u y T‖ ≤
      (1 / 8) * (y * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ)))) := by
    rw [norm_sub_rev]
    exact hterm1
  calc ‖zetaTwSum u y - (y : ℂ) ^ (1 - Complex.I * (u : ℂ)) / (1 - Complex.I * (u : ℂ))‖
      = ‖(zetaTwSum u y - zetaTwPerron u y T) +
          (zetaTwTop u y T σ₁ - zetaTwBot u y T σ₁ + zetaTwLeft u y T σ₁)‖ := by rw [htotal]
    _ ≤ ‖zetaTwSum u y - zetaTwPerron u y T‖ +
          ‖zetaTwTop u y T σ₁ - zetaTwBot u y T σ₁ + zetaTwLeft u y T σ₁‖ := norm_add_le _ _
    _ ≤ (1 / 8) * (y * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ)))) +
          ((1 / 8) * (y * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ)))) +
            (1 / 32) * (y * Real.exp (-((κ / 16) * L ^ (1 / 12 : ℝ))))) := by
          linarith [hper, hsum3]
    _ ≤ y * Real.exp (-((κ / 16) * (Real.log y) ^ (1 / 12 : ℝ))) := by
          rw [hLdef]
          have hE : 0 < Real.exp (-((κ / 16) * (Real.log y) ^ (1 / 12 : ℝ))) := Real.exp_pos _
          nlinarith [le_of_lt hypos, hE]

/-- **V6. Principal-character main term** (`q = 1`): for `|u| ≤ exp((log x)^{21/20})`,
`Σ_{n ≤ x} Λ(n) n^{-iu} = x^{1-iu}/(1-iu) + O(x exp(−c (log x)^{1/12}))`.

Route: the truncated twisted Perron formula at `Re w = 1 + 1/log x`, the rectangle shift with the
single interior pole of `ζ` at `w = 1 - iu` (residue `x^{1-iu}/(1-iu)`), the bounds for the three
other edges from the `6/7`-shaped zero-free region / logarithmic-derivative bound for `ζ`
(`Work.BMF.logDeriv_LFunction_VK`, V4, at the trivial character mod `1`) and the near-axis data
`zeta_logDeriv_near_four`, and the elementary parameter package `Work.BMF.ztw_param`. -/
theorem mixing_v6_main (hV1 : Work.BMF.VKExpSumRestrictedN7) :
    ∃ c C : ℝ, 0 < c ∧ ∀ (x : ℝ), 2 ≤ x → ∀ (u : ℝ),
      |u| ≤ Real.exp (Real.log x ^ (21 / 20 : ℝ)) →
        ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            (n : ℂ) ^ (-(Complex.I * u)) - (x : ℂ) ^ (1 - Complex.I * u) / (1 - Complex.I * u)‖
          ≤ C * x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by
  -- V4 at the trivial character mod `1` gives the `6/7`-shaped data for `ζ`
  obtain ⟨A, c5, hgrA⟩ := v7chi_VKGrowth
  have hgr : VKGrowth A c5 := hgrA
  obtain ⟨CV, κV, hCV, hκV, hLVK⟩ :=
    Work.BMF.N7.logDeriv_LFunction_VK_of_growth_zf hgr
      Work.BMF.N7.zf_VK_N7_fleet
  have hden : ∀ t : ℝ, ztD |t| = (Real.log (|t| + 3)) ^ (6 / 7 : ℝ) *
      (Real.log ((1 : ℕ) + 2) + Real.log (Real.log (|t| + 3))) := by
    intro t
    rw [ztD]; norm_num
  have hreg : ∀ t σ : ℝ, 4 ≤ |t| → 1 - κV / ztD |t| ≤ σ → σ ≤ 2 →
      riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro t σ ht hσ hσ2
    have hσ' : 1 - κV / ((Real.log (|t| + 3)) ^ (6 / 7 : ℝ) *
        (Real.log ((1 : ℕ) + 2) + Real.log (Real.log (|t| + 3)))) ≤ σ := by
      rw [← hden t]; exact hσ
    have h := (hLVK 1 (1 : DirichletCharacter ℂ 1)
      DirichletCharacter.isPrimitive_one_level_one σ t ht hσ' hσ2).1
    rwa [DirichletCharacter.LFunction_modOne_eq] at h
  have hlog : ∀ t σ : ℝ, 4 ≤ |t| → 1 - κV / ztD |t| ≤ σ → σ ≤ 2 →
      ‖deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) /
        riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ CV * (Real.log (|t| + 3)) ^ 4 := by
    intro t σ ht hσ hσ2
    have hσ' : 1 - κV / ((Real.log (|t| + 3)) ^ (6 / 7 : ℝ) *
        (Real.log ((1 : ℕ) + 2) + Real.log (Real.log (|t| + 3)))) ≤ σ := by
      rw [← hden t]; exact hσ
    have h := (hLVK 1 (1 : DirichletCharacter ℂ 1)
      DirichletCharacter.isPrimitive_one_level_one σ t ht hσ' hσ2).2
    rw [DirichletCharacter.LFunction_modOne_eq, logDeriv_apply] at h
    simpa using h
  -- the auxiliary inputs
  obtain ⟨C₅, δ₅, hC₅, hδ₅, hnear_ld, hnear_zz⟩ := Work.BMF.liouville.zeta_logDeriv_near_four
  obtain ⟨Ctr, hCtr, htrunc⟩ := Work.BMF.liouville.zetaTwPerron_sub_sum
  have hparam := Work.BMF.N7.ztw_paramN7 κV δ₅ C₅ CV Ctr hκV hδ₅ hC₅ hCV hCtr
  obtain ⟨N₀, hN₀⟩ := zetaTwSum_main_le_of_region κV δ₅ C₅ CV Ctr hκV hδ₅ hC₅ hCV hCtr
    hreg hlog hnear_ld hnear_zz htrunc hparam
  -- the crude bound on a bounded range
  have hcrude : ∀ x : ℝ, 0 < x → ∀ u : ℝ,
      ‖zetaTwSum u x - (x : ℂ) ^ (1 - Complex.I * (u : ℂ)) / (1 - Complex.I * (u : ℂ))‖ ≤
        (Real.log 4 + 5) * x := by
    intro x hx u
    have h1 : ‖zetaTwSum u x - (x : ℂ) ^ (1 - Complex.I * (u : ℂ)) /
        (1 - Complex.I * (u : ℂ))‖ ≤ ‖zetaTwSum u x‖ +
        ‖(x : ℂ) ^ (1 - Complex.I * (u : ℂ)) / (1 - Complex.I * (u : ℂ))‖ :=
      norm_sub_le _ _
    have h2 : ‖zetaTwSum u x‖ ≤ Chebyshev.psi x :=
      Work.BMF.liouville.norm_zetaTwSum_le_psi u x
    have h3 : ‖(x : ℂ) ^ (1 - Complex.I * (u : ℂ)) / (1 - Complex.I * (u : ℂ))‖ ≤ x :=
      Work.BMF.liouville.norm_cpow_div_le x hx u
    have h4 : Chebyshev.psi x ≤ (Real.log 4 + 4) * x := Chebyshev.psi_le_const_mul_self hx.le
    linarith
  -- parameters
  set c₀ : ℝ := κV / 16 with hc₀def
  have hc₀pos : 0 < c₀ := by rw [hc₀def]; positivity
  set X₀ : ℝ := max (N₀ + 1) (max (Real.exp 100) 3) with hX₀def
  have hX₀3 : 3 ≤ X₀ := by
    rw [hX₀def]
    exact le_trans (le_max_right (Real.exp 100) 3) (le_max_right (N₀ + 1) (max (Real.exp 100) 3))
  have hX₀1 : 1 ≤ X₀ := le_trans (by norm_num : (1 : ℝ) ≤ 3) hX₀3
  have hX₀pos : 0 < X₀ := lt_of_lt_of_le zero_lt_one hX₀1
  have hN₀X : N₀ ≤ X₀ := by
    rw [hX₀def]; linarith [le_max_left (N₀ + 1) (max (Real.exp 100) 3)]
  set Kexp : ℝ := Real.exp (c₀ * (Real.log X₀) ^ (1 / 12 : ℝ)) with hKexpdef
  have hKpos : 0 < Kexp := by rw [hKexpdef]; positivity
  set Cfin : ℝ := (Real.log 4 + 5) * Kexp + 4 with hCfindef
  have hCfin1 : (1 : ℝ) ≤ Cfin := by
    rw [hCfindef]; nlinarith [hKpos, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
  have hCfin2 : (2 : ℝ) ≤ Cfin := by
    rw [hCfindef]; nlinarith [hKpos, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
  refine ⟨c₀, Cfin, hc₀pos, ?_⟩
  intro x hx2 u hu
  simp only [neg_mul]
  have hxpos : 0 < x := by linarith
  have hxlog0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  -- the exponential factor is at most one
  have hexp_le_one : ∀ z : ℝ, 1 ≤ z →
      Real.exp (-(c₀ * (Real.log z) ^ (1 / 12 : ℝ))) ≤ 1 := by
    intro z hz
    have h1 : 0 ≤ (Real.log z) ^ (1 / 12 : ℝ) :=
      Real.rpow_nonneg (Real.log_nonneg hz) _
    have h2 : 0 ≤ c₀ * (Real.log z) ^ (1 / 12 : ℝ) := mul_nonneg hc₀pos.le h1
    calc Real.exp (-(c₀ * (Real.log z) ^ (1 / 12 : ℝ))) ≤ Real.exp 0 :=
          Real.exp_le_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  change ‖zetaTwSum u x - (x : ℂ) ^ (1 - Complex.I * (u : ℂ)) / (1 - Complex.I * (u : ℂ))‖ ≤
    Cfin * x * Real.exp (-(c₀ * Real.log x ^ (1 / 12 : ℝ)))
  rw [show -(c₀ * Real.log x ^ (1 / 12 : ℝ)) = -(c₀ * (Real.log x) ^ (1 / 12 : ℝ)) by ring]
  by_cases hxX : X₀ ≤ x
  · -- main range
    have hxN₀ : N₀ ≤ x := le_trans hN₀X hxX
    have hE : 0 < Real.exp (-(c₀ * (Real.log x) ^ (1 / 12 : ℝ))) := Real.exp_pos _
    by_cases hint : ∃ n : ℕ, x = n
    · -- `x` is an integer: shift to `y = x + exp(-c₀(log x)^{1/12})/2`
      obtain ⟨n, rfl⟩ := hint
      have hn2 : (2 : ℝ) ≤ (n : ℝ) := by
        have h1 : (3 : ℝ) ≤ (n : ℝ) := le_trans hX₀3 hxX
        linarith
      have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
      have hnlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
      set ε : ℝ := Real.exp (-(c₀ * (Real.log (n : ℝ)) ^ (1 / 12 : ℝ))) / 2 with hεdef
      have hεpos : 0 < ε := by rw [hεdef]; positivity
      have hεle : ε ≤ 1 / 2 := by
        have h := hexp_le_one (n : ℝ) (by linarith)
        rw [hεdef]
        linarith
      set y : ℝ := (n : ℝ) + ε with hydef
      have hypos : 0 < y := by rw [hydef]; linarith
      have hxy : (n : ℝ) ≤ y := by rw [hydef]; linarith [hεpos]
      have hfloor : ⌊y⌋₊ = n := by
        rw [hydef, Nat.floor_eq_iff (by positivity)]
        constructor
        · linarith [hεpos]
        · linarith [hεle, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have hynat : ∀ m : ℕ, (m : ℝ) ≠ y := by
        intro m hm
        have h1 : ⌊y⌋₊ = m := by rw [← hm]; exact Nat.floor_natCast m
        have h2 : m = n := h1.symm.trans hfloor
        have h3 : y = (n : ℝ) := by rw [← hm, h2]
        rw [hydef] at h3
        linarith [hεpos, h3]
      have hNy : N₀ ≤ y := by linarith [hxN₀, hxy]
      have hlogy : Real.log (n : ℝ) ≤ Real.log y := Real.log_le_log hnpos (by linarith)
      have hu' : |u| ≤ Real.exp ((Real.log y) ^ (21 / 20 : ℝ)) := by
        refine le_trans hu (Real.exp_le_exp.mpr ?_)
        exact Real.rpow_le_rpow hnlog0 hlogy (by norm_num)
      have hb := hN₀ y hNy hynat u hu'
      have hsum : zetaTwSum u y = zetaTwSum u (n : ℝ) := by
        simp only [Work.BMF.liouville.zetaTwSum, hfloor, Nat.floor_natCast]
      have hmd : ‖(y : ℂ) ^ (1 - Complex.I * (u : ℂ)) / (1 - Complex.I * (u : ℂ)) -
          ((n : ℝ) : ℂ) ^ (1 - Complex.I * (u : ℂ)) / (1 - Complex.I * (u : ℂ))‖ ≤ ε := by
        have hnum := Work.BMF.liouville.cpow_one_sub_I_mul_sub_le (x := (n : ℝ)) (y := y)
          hnpos (by linarith) u
        have hd : (1 : ℝ) ≤ ‖1 - Complex.I * (u : ℂ)‖ := by
          simpa using Complex.abs_re_le_norm (1 - Complex.I * (u : ℂ))
        have hd0 : 0 < ‖1 - Complex.I * (u : ℂ)‖ := by linarith
        calc ‖(y : ℂ) ^ (1 - Complex.I * (u : ℂ)) / (1 - Complex.I * (u : ℂ)) -
              ((n : ℝ) : ℂ) ^ (1 - Complex.I * (u : ℂ)) / (1 - Complex.I * (u : ℂ))‖
            = ‖((y : ℂ) ^ (1 - Complex.I * (u : ℂ)) -
                ((n : ℝ) : ℂ) ^ (1 - Complex.I * (u : ℂ))) / (1 - Complex.I * (u : ℂ))‖ := by
              rw [sub_div]
          _ = ‖(y : ℂ) ^ (1 - Complex.I * (u : ℂ)) -
                ((n : ℝ) : ℂ) ^ (1 - Complex.I * (u : ℂ))‖ / ‖1 - Complex.I * (u : ℂ)‖ :=
                norm_div _ _
          _ ≤ (‖1 - Complex.I * (u : ℂ)‖ * (y - (n : ℝ))) / ‖1 - Complex.I * (u : ℂ)‖ :=
                div_le_div_of_nonneg_right hnum hd0.le
          _ = ε := by
                rw [div_eq_iff (ne_of_gt hd0)]
                rw [hydef]; ring
      have hexpy : Real.exp (-(c₀ * (Real.log y) ^ (1 / 12 : ℝ))) ≤
          Real.exp (-(c₀ * (Real.log (n : ℝ)) ^ (1 / 12 : ℝ))) := by
        apply Real.exp_le_exp.mpr
        have h2 : (Real.log (n : ℝ)) ^ (1 / 12 : ℝ) ≤ (Real.log y) ^ (1 / 12 : ℝ) :=
          Real.rpow_le_rpow hnlog0 hlogy (by norm_num)
        nlinarith [h2, hc₀pos.le]
      have hyx : y ≤ 2 * (n : ℝ) := by
        have h := hexp_le_one (n : ℝ) (by linarith)
        rw [hydef, hεdef]
        linarith [h, hn2]
      have hsplit : zetaTwSum u (n : ℝ) - ((n : ℝ) : ℂ) ^ (1 - Complex.I * (u : ℂ)) /
            (1 - Complex.I * (u : ℂ)) =
          (zetaTwSum u y - (y : ℂ) ^ (1 - Complex.I * (u : ℂ)) /
              (1 - Complex.I * (u : ℂ))) +
            ((y : ℂ) ^ (1 - Complex.I * (u : ℂ)) / (1 - Complex.I * (u : ℂ)) -
              ((n : ℝ) : ℂ) ^ (1 - Complex.I * (u : ℂ)) / (1 - Complex.I * (u : ℂ))) := by
        rw [← hsum]; ring
      rw [hsplit]
      have hmain : ‖(zetaTwSum u y - (y : ℂ) ^ (1 - Complex.I * (u : ℂ)) /
              (1 - Complex.I * (u : ℂ))) +
            ((y : ℂ) ^ (1 - Complex.I * (u : ℂ)) / (1 - Complex.I * (u : ℂ)) -
              ((n : ℝ) : ℂ) ^ (1 - Complex.I * (u : ℂ)) / (1 - Complex.I * (u : ℂ)))‖ ≤
          y * Real.exp (-(c₀ * (Real.log y) ^ (1 / 12 : ℝ))) + ε :=
        le_trans (norm_add_le _ _) (add_le_add hb hmd)
      have hfin : y * Real.exp (-(c₀ * (Real.log y) ^ (1 / 12 : ℝ))) + ε ≤
          Cfin * (n : ℝ) * Real.exp (-(c₀ * (Real.log (n : ℝ)) ^ (1 / 12 : ℝ))) := by
        have hEn : 0 < Real.exp (-(c₀ * (Real.log (n : ℝ)) ^ (1 / 12 : ℝ))) := Real.exp_pos _
        have h1 : y * Real.exp (-(c₀ * (Real.log y) ^ (1 / 12 : ℝ))) ≤
            2 * (n : ℝ) * Real.exp (-(c₀ * (Real.log (n : ℝ)) ^ (1 / 12 : ℝ))) := by
          have h := mul_le_mul hyx hexpy (Real.exp_pos _).le (by linarith : (0 : ℝ) ≤ 2 * (n:ℝ))
          linarith [h]
        have h2 : ε = Real.exp (-(c₀ * (Real.log (n : ℝ)) ^ (1 / 12 : ℝ))) / 2 := hεdef
        rw [h2]
        have h6 : Real.exp (-(c₀ * (Real.log (n : ℝ)) ^ (1 / 12 : ℝ))) / 2 ≤
            (n : ℝ) * Real.exp (-(c₀ * (Real.log (n : ℝ)) ^ (1 / 12 : ℝ))) := by
          have h7 : (1 : ℝ) ≤ (n : ℝ) := by linarith
          nlinarith [hEn, h7]
        have h8 : (3 : ℝ) ≤ Cfin := by
          rw [hCfindef]
          nlinarith [hKpos, Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
        nlinarith [h1, h6, h8, hEn, hn2]
      linarith [hmain, hfin]
    · -- `x` is not an integer: use the engine directly at `y = x`
      have hb := hN₀ x hxN₀ (fun n hn => hint ⟨n, hn.symm⟩) u hu
      have h1 : x * Real.exp (-(c₀ * (Real.log x) ^ (1 / 12 : ℝ))) ≤
          Cfin * x * Real.exp (-(c₀ * (Real.log x) ^ (1 / 12 : ℝ))) := by
        have h := mul_le_mul_of_nonneg_right hCfin1
          (by positivity : (0 : ℝ) ≤ x * Real.exp (-(c₀ * (Real.log x) ^ (1 / 12 : ℝ))))
        nlinarith [h]
      linarith [hb, h1]
  · -- bounded range
    push Not at hxX
    have h1 := hcrude x hxpos u
    have h2 : Real.exp (-(c₀ * (Real.log X₀) ^ (1 / 12 : ℝ))) ≤
        Real.exp (-(c₀ * (Real.log x) ^ (1 / 12 : ℝ))) := by
      apply Real.exp_le_exp.mpr
      have h3 : Real.log x ≤ Real.log X₀ := Real.log_le_log hxpos (le_of_lt hxX)
      have h4 : (Real.log x) ^ (1 / 12 : ℝ) ≤ (Real.log X₀) ^ (1 / 12 : ℝ) :=
        Real.rpow_le_rpow hxlog0 h3 (by norm_num)
      nlinarith [h4, hc₀pos.le]
    have h3 : (1 : ℝ) ≤ Real.exp (c₀ * (Real.log X₀) ^ (1 / 12 : ℝ)) *
        Real.exp (-(c₀ * (Real.log x) ^ (1 / 12 : ℝ))) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by
        have h4 : (Real.log x) ^ (1 / 12 : ℝ) ≤ (Real.log X₀) ^ (1 / 12 : ℝ) :=
          Real.rpow_le_rpow hxlog0 (Real.log_le_log hxpos (le_of_lt hxX)) (by norm_num)
        nlinarith [h4, hc₀pos.le])
    rw [← hKexpdef] at h3
    have h4 : (Real.log 4 + 5) ≤ Cfin * Real.exp (-(c₀ * (Real.log x) ^ (1 / 12 : ℝ))) := by
      have h5 : (Real.log 4 + 5) * Kexp ≤ Cfin := by
        rw [hCfindef]; nlinarith [hKpos]
      calc (Real.log 4 + 5) = (Real.log 4 + 5) * 1 := by ring
        _ ≤ (Real.log 4 + 5) *
              (Real.exp (c₀ * (Real.log X₀) ^ (1 / 12 : ℝ)) *
                Real.exp (-(c₀ * (Real.log x) ^ (1 / 12 : ℝ)))) :=
              mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = ((Real.log 4 + 5) * Kexp) *
              Real.exp (-(c₀ * (Real.log x) ^ (1 / 12 : ℝ))) := by rw [hKexpdef]; ring
        _ ≤ Cfin * Real.exp (-(c₀ * (Real.log x) ^ (1 / 12 : ℝ))) :=
              mul_le_mul_of_nonneg_right h5 (by positivity)
    calc ‖zetaTwSum u x - (x : ℂ) ^ (1 - Complex.I * (u : ℂ)) / (1 - Complex.I * (u : ℂ))‖
        ≤ (Real.log 4 + 5) * x := h1
      _ ≤ (Cfin * Real.exp (-(c₀ * (Real.log x) ^ (1 / 12 : ℝ)))) * x :=
            mul_le_mul_of_nonneg_right h4 (le_of_lt hxpos)
      _ = Cfin * x * Real.exp (-(c₀ * (Real.log x) ^ (1 / 12 : ℝ))) := by ring

end

end Work.BMF.N7
