import Mathlib
import Submission.Work.FIChain.Defs
import Submission.Work.FIChain.window_marginsC
import Submission.Work.FITop.BformAtilEqXsum
import Submission.Work.FITop.AtilTauPowFourLe
import Submission.Work.FITop.Defs
import Submission.ASP.S7c
import Submission.ASP.S8b
import Submission.ASP.S20
import Submission.ASP.S21
import Submission.ASP.S22
import Submission.ASP.S23
import Submission.ASP.S24
import Submission.ASP.S25
import Submission.Work.FITop.SingleDvdTauSqLe
import Submission.Work.FITop.WindowRangeMarginsChain
import Submission.Work.FITop.BprimeWindowDelta1
import Submission.Work.FITop.RangeCheckChain
import Submission.ASP.S30
import Submission.Work.FITop.WolkeSquarefreeTau
import Submission.Work.FITop.AdTauAggregate
import Submission.Work.FITop.SumIteDivDvd
import Submission.Work.FIChain.scale_factsC
import Submission.Work.FIChain.LocalS4
import Submission.Work.FIChain.LocalS5c
import Submission.Work.FIChain.remainder_all
import Submission.Work.FIChain.rhoWindowC_param
import Submission.Work.FIChain.LocalS6c
import Submission.ASP.S7e
import Submission.Commons.NumberTheory.Chebyshev.sum_prime_log_mul_g_Ioc_le
import Submission.Work.FIChain.chainRangeFactsC
import Submission.Work.FIChain.Tsum_uniformAll
import Submission.Work.FIChain.Tsum2_uniformAll
import Submission.Work.FIChain.FIgtil_prod_sub_le
import Submission.Work.FIChain.FIgtil_tau_div_sum_le

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.FIChain

open Finset Filter
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Auxiliary facts for the assembly -/

/-- `B^{-k} ≤ A^{-k}` for `0 < A ≤ B` and `k ≥ 0` (`zpow` form). -/
lemma zpow_neg_anti {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) (k : ℕ) :
    B ^ (-(k : ℤ)) ≤ A ^ (-(k : ℤ)) := by
  have hk : A ^ k ≤ B ^ k := pow_le_pow_left₀ hA.le hAB k
  have hBk : B ^ (-(k : ℤ)) = (B ^ k)⁻¹ := by rw [zpow_neg, zpow_natCast]
  have hAk : A ^ (-(k : ℤ)) = (A ^ k)⁻¹ := by rw [zpow_neg, zpow_natCast]
  rw [hBk, hAk]
  exact (inv_le_inv₀ (pow_pos (lt_of_lt_of_le hA hAB) k) (pow_pos hA k)).mpr hk

/-- `x^{-k} ≤ 1` for `x ≥ 1`. -/
lemma zpow_neg_le_one {x : ℝ} (hx : 1 ≤ x) (k : ℕ) : x ^ (-(k : ℤ)) ≤ 1 := by
  rw [zpow_neg, zpow_natCast]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ hx)

/-- `(m : ℝ) / 2 ≤ (⌊m⌋₊ : ℝ)` for `m ≥ 2`. -/
lemma half_le_floor {m : ℝ} (hm : 2 ≤ m) : m / 2 ≤ (⌊m⌋₊ : ℝ) := by
  have h := Nat.floor_le (show (0:ℝ) ≤ m by linarith)
  have h2 : m - 1 ≤ (⌊m⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one m
    linarith
  linarith

/-- `(⌈m⌉₊ : ℝ) ≤ 2 * m` for `1 ≤ m`. -/
lemma ceil_le_two_mul {m : ℝ} (hm : 1 ≤ m) : ((⌈m⌉₊ : ℕ) : ℝ) ≤ 2 * m := by
  have h := Nat.ceil_lt_add_one (show (0:ℝ) ≤ m by linarith)
  linarith

/-- Adding two bounds of the shape `a ≤ c·X`. -/
private lemma add_const_mul_le {a₁ a₂ c₁ c₂ X : ℝ} (h1 : a₁ ≤ c₁ * X) (h2 : a₂ ≤ c₂ * X) :
    a₁ + a₂ ≤ (c₁ + c₂) * X := by
  have h : (c₁ + c₂) * X = c₁ * X + c₂ * X := by ring
  rw [h]
  exact add_le_add h1 h2

/-- The `§6` bound for `L(x)` at the corrected parameters, with an explicit constant:
eventually in `x`, `L(x) = ∑_{sz<c≤x/(sy),♭} Λ(c)g̃(c) ≤ C·(1 + loglog x)` for every `sy ≥ s·y`.
This is `Submission.ASP.L6_le` with `lo = ⌊s·z⌋`, `hi = ⌈x/(s·y)⌉` and the range
`hi/lo ≤ 8·(log x)^{2B+4}` supplied by `scale_factsC`. -/
lemma L6_param_le (B C₀ : ℝ) (hB : 0 < B) (hC₀ : 0 < C₀)
    (hC₀b : ∀ y z : ℕ, 1 ≤ y → y ≤ z →
      (∑ p ∈ (Finset.Ioc y z).filter Nat.Prime,
          Real.log (p : ℝ) * Submission.ASP.FIgtil p)
        ≤ C₀ * (1 + Real.log ((z : ℝ) / (y : ℝ)))) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in Filter.atTop, ∀ sy : ℝ,
      Work.FIChain.sc x B * Work.FIChain.Yc x B ≤ sy →
      Submission.ASP.L6 Submission.ASP.FIgtil x
          (Work.FIChain.sc x B * Work.FIChain.zc x B) sy
        ≤ C * (1 + Real.log (Real.log (x : ℝ))) := by
  obtain ⟨X1, h1⟩ := Filter.eventually_atTop.mp (scale_factsC B hB)
  obtain ⟨X2, h2⟩ := Filter.eventually_atTop.mp
    (window_marginsC (1 / 64) B (by norm_num) (by norm_num) hB)
  have hKpos : (0 : ℝ) < C₀ * (1 + Real.log 8 + (2 * B + 4)) := by
    have h8 : (0 : ℝ) < Real.log 8 := Real.log_pos (by norm_num)
    have hb : (0 : ℝ) < 2 * B + 4 := by linarith
    exact mul_pos hC₀ (by linarith)
  refine ⟨C₀ * (1 + Real.log 8 + (2 * B + 4)), hKpos, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (max X1 X2)] with x hx sy hsy
  have hx1 : X1 ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : X2 ≤ x := le_trans (le_max_right _ _) hx
  obtain ⟨hsf1, hsf2, hsf3, hsf4, hsf5, hsf6, hsf7, hsf8, hsf9, hsf10, hsf11, hsf12, hsf13,
    hsf14, hsf15, hsf16⟩ := h1 x hx1
  obtain ⟨hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩ := h2 x hx2
  have hx3R : (3 : ℝ) ≤ (x : ℝ) := hw6
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hx1R : (1 : ℝ) ≤ (x : ℝ) := by linarith
  have hLpos : 0 < Real.log (x : ℝ) := Real.log_pos (by linarith : (1 : ℝ) < (x : ℝ))
  have hL1 : (1 : ℝ) ≤ Real.log (x : ℝ) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_three, hx3R])
  have hLL1 : (1 : ℝ) ≤ Real.log (Real.log (x : ℝ)) := by linarith [hw7]
  have hsc_pos : 0 < Work.FIChain.sc x B := by rw [Work.FIChain.sc]; positivity
  have hsc1 : (1 : ℝ) ≤ Work.FIChain.sc x B := by
    rw [Work.FIChain.sc]; exact one_le_pow₀ (by norm_num)
  have hYpos : 0 < Work.FIChain.Yc x B := by
    rw [Work.FIChain.Yc]
    exact div_pos (Real.sqrt_pos.mpr hxpos)
      (mul_pos hsc_pos (Real.rpow_pos_of_pos hLpos _))
  have hscYc : Work.FIChain.sc x B * Work.FIChain.Yc x B
      = Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ (B + 2) := by
    have hscne : Work.FIChain.sc x B ≠ 0 := ne_of_gt hsc_pos
    rw [Work.FIChain.Yc]
    field_simp
  have hscYc_pos : 0 < Work.FIChain.sc x B * Work.FIChain.Yc x B := mul_pos hsc_pos hYpos
  have hsypos : 0 < sy := lt_of_lt_of_le hscYc_pos hsy
  have hscYc_le_sqrt : Work.FIChain.sc x B * Work.FIChain.Yc x B ≤ Real.sqrt (x : ℝ) := by
    rw [hscYc]
    exact div_le_self (Real.sqrt_nonneg _) (Real.one_le_rpow hL1 (by linarith))
  have hsqrt_le : Real.sqrt (x : ℝ) ≤ (x : ℝ) := by
    nlinarith [Real.sq_sqrt hxpos.le, Real.sqrt_nonneg (x : ℝ)]
  have hzc256 : (256 : ℝ) ≤ Work.FIChain.zc x B := by
    rw [Work.FIChain.zc, Work.FIChain.Zc]
    exact_mod_cast hsf1
  have hzc_pos : 0 < Work.FIChain.zc x B := by linarith
  have hzc_le_Y : Work.FIChain.zc x B ≤ Work.FIChain.Yc x B := by
    rw [Work.FIChain.zc, Work.FIChain.Zc]; exact Nat.floor_le hYpos.le
  have hsz_ge2 : 2 ≤ Work.FIChain.sc x B * Work.FIChain.zc x B := by nlinarith
  set lo : ℕ := ⌊Work.FIChain.sc x B * Work.FIChain.zc x B⌋₊ with hlodef
  set hi : ℕ := ⌈(x : ℝ) / (Work.FIChain.sc x B * Work.FIChain.Yc x B)⌉₊ with hidef
  have hlo1 : 1 ≤ lo := by rw [hlodef]; exact hsf16
  have hlo_ge : (Work.FIChain.sc x B * Work.FIChain.zc x B) / 2 ≤ (lo : ℝ) := by
    rw [hlodef]; exact half_le_floor hsz_ge2
  have hlo_pos : (0 : ℝ) < (lo : ℝ) := by
    have : 0 < lo := lt_of_lt_of_le (by norm_num) hlo1
    exact_mod_cast this
  have hm_one : (1 : ℝ) ≤ (x : ℝ) / (Work.FIChain.sc x B * Work.FIChain.Yc x B) := by
    rw [le_div_iff₀ hscYc_pos]
    linarith [hscYc_le_sqrt, hsqrt_le]
  have hhi_bound : (hi : ℝ) ≤ 2 * ((x : ℝ) / (Work.FIChain.sc x B * Work.FIChain.Yc x B)) := by
    rw [hidef]
    have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (x : ℝ) / (Work.FIChain.sc x B * Work.FIChain.Yc x B) by positivity)
    linarith
  have hlohi : lo ≤ hi := by
    have h1' : (lo : ℝ) ≤ (x : ℝ) / (Work.FIChain.sc x B * Work.FIChain.Yc x B) := by
      have h2' : (lo : ℝ) ≤ Work.FIChain.sc x B * Work.FIChain.zc x B := by
        rw [hlodef]; exact Nat.floor_le (by positivity)
      have h3' : Work.FIChain.sc x B * Work.FIChain.zc x B
          ≤ Work.FIChain.sc x B * Work.FIChain.Yc x B :=
        mul_le_mul_of_nonneg_left hzc_le_Y hsc_pos.le
      have h4' : Work.FIChain.sc x B * Work.FIChain.Yc x B
          ≤ (x : ℝ) / (Work.FIChain.sc x B * Work.FIChain.Yc x B) := by
        rw [le_div_iff₀ hscYc_pos]
        calc (Work.FIChain.sc x B * Work.FIChain.Yc x B) * (Work.FIChain.sc x B * Work.FIChain.Yc x B)
            ≤ Real.sqrt (x : ℝ) * Real.sqrt (x : ℝ) :=
              mul_self_le_mul_self (by positivity) hscYc_le_sqrt
          _ = (x : ℝ) := by rw [← sq, Real.sq_sqrt hxpos.le]
      linarith
    have h2'' : (lo : ℝ) ≤ ((hi : ℕ) : ℝ) := by
      rw [hidef]
      exact le_trans h1' (Nat.le_ceil _)
    exact_mod_cast h2''
  have hratio : ((hi : ℝ) / (lo : ℝ)) ≤ 8 * (Real.log (x : ℝ)) ^ (2 * B + 4) := by
    have hsz2pos : (0 : ℝ) < Work.FIChain.sc x B * Work.FIChain.zc x B / 2 := by positivity
    have hstep1 : (hi : ℝ) / (lo : ℝ)
        ≤ (hi : ℝ) / ((Work.FIChain.sc x B * Work.FIChain.zc x B) / 2) := by
      refine div_le_div_of_nonneg_left (by positivity) hsz2pos ?_
      rw [hlodef]; exact half_le_floor hsz_ge2
    have hstep2 : (hi : ℝ) / ((Work.FIChain.sc x B * Work.FIChain.zc x B) / 2)
        ≤ (2 * ((x : ℝ) / (Work.FIChain.sc x B * Work.FIChain.Yc x B)))
            / ((Work.FIChain.sc x B * Work.FIChain.zc x B) / 2) :=
      div_le_div_of_nonneg_right hhi_bound hsz2pos.le
    have hstep3 : (2 * ((x : ℝ) / (Work.FIChain.sc x B * Work.FIChain.Yc x B)))
          / ((Work.FIChain.sc x B * Work.FIChain.zc x B) / 2)
        = 4 * (x : ℝ) / ((Work.FIChain.sc x B * Work.FIChain.Yc x B)
            * (Work.FIChain.sc x B * Work.FIChain.zc x B)) := by
      have h1n : Work.FIChain.sc x B * Work.FIChain.Yc x B ≠ 0 := ne_of_gt hscYc_pos
      have h2n : Work.FIChain.sc x B * Work.FIChain.zc x B ≠ 0 :=
        ne_of_gt (mul_pos hsc_pos hzc_pos)
      field_simp
      ring
    have hstep4 : 4 * (x : ℝ) / ((Work.FIChain.sc x B * Work.FIChain.Yc x B)
          * (Work.FIChain.sc x B * Work.FIChain.zc x B))
        ≤ 8 * (Real.log (x : ℝ)) ^ (2 * B + 4) := by
      have hden : 0 < (Work.FIChain.sc x B * Work.FIChain.Yc x B)
          * (Work.FIChain.sc x B * Work.FIChain.zc x B) :=
        mul_pos hscYc_pos (mul_pos hsc_pos hzc_pos)
      have hLp : 0 < (Real.log (x : ℝ)) ^ (2 * B + 4) := Real.rpow_pos_of_pos hLpos _
      rw [div_le_iff₀ hden]
      calc 4 * (x : ℝ)
          ≤ 4 * (2 * (Work.FIChain.sc x B ^ 2 * Work.FIChain.Yc x B * Work.FIChain.zc x B
              * (Real.log (x : ℝ)) ^ (2 * B + 4))) := by linarith [hsf13]
        _ = 8 * (Real.log (x : ℝ)) ^ (2 * B + 4)
              * ((Work.FIChain.sc x B * Work.FIChain.Yc x B)
                  * (Work.FIChain.sc x B * Work.FIChain.zc x B)) := by ring
    linarith [hstep1, hstep2, hstep3.le, hstep4]
  have hlogratio : Real.log ((hi : ℝ) / (lo : ℝ))
      ≤ Real.log 8 + (2 * B + 4) * Real.log (Real.log (x : ℝ)) := by
    have hmpos : (0 : ℝ) < (x : ℝ) / (Work.FIChain.sc x B * Work.FIChain.Yc x B) := by positivity
    have hpos : 0 < (hi : ℝ) / (lo : ℝ) := by
      apply div_pos _ hlo_pos
      rw [hidef]
      exact lt_of_lt_of_le hmpos (Nat.le_ceil _)
    have h8pos : (0 : ℝ) < (Real.log (x : ℝ)) ^ (2 * B + 4) := Real.rpow_pos_of_pos hLpos _
    have h1' : Real.log ((hi : ℝ) / (lo : ℝ)) ≤ Real.log (8 * (Real.log (x : ℝ)) ^ (2 * B + 4)) :=
      Real.log_le_log hpos (by linarith [hratio])
    rw [Real.log_mul (by norm_num) (ne_of_gt h8pos), Real.log_rpow hLpos] at h1'
    linarith [h1']
  have hmem : ∀ c ∈ Submission.ASP.cseg x (Work.FIChain.sc x B * Work.FIChain.zc x B) sy,
      lo < c ∧ c ≤ hi := by
    intro c hc
    rw [Submission.ASP.cseg, Finset.mem_filter, Submission.ASP.seg, Finset.mem_filter] at hc
    obtain ⟨⟨hcIcc, hcgt⟩, hcle⟩ := hc
    refine ⟨?_, ?_⟩
    · rw [hlodef]
      have h1' := Nat.floor_le (show (0 : ℝ) ≤ Work.FIChain.sc x B * Work.FIChain.zc x B by positivity)
      have h2' : ((⌊Work.FIChain.sc x B * Work.FIChain.zc x B⌋₊ : ℕ) : ℝ) < (c : ℝ) :=
        lt_of_le_of_lt h1' hcgt
      exact_mod_cast h2'
    · rw [hidef]
      have hcle' : (c : ℝ) ≤ (x : ℝ) / (Work.FIChain.sc x B * Work.FIChain.Yc x B) :=
        le_trans hcle (div_le_div_of_nonneg_left (by positivity) hscYc_pos hsy)
      have : (c : ℝ) ≤ ((⌈(x : ℝ) / (Work.FIChain.sc x B * Work.FIChain.Yc x B)⌉₊ : ℕ) : ℝ) :=
        le_trans hcle' (Nat.le_ceil _)
      exact_mod_cast this
  have hsum_eq : Submission.ASP.L6 Submission.ASP.FIgtil x
        (Work.FIChain.sc x B * Work.FIChain.zc x B) sy
      = ∑ c ∈ (Submission.ASP.cseg x (Work.FIChain.sc x B * Work.FIChain.zc x B) sy).filter Nat.Prime,
          Real.log (c : ℝ) * Submission.ASP.FIgtil c := by
    rw [Submission.ASP.L6]
    rw [Finset.sum_filter, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro c _
    by_cases hp : Nat.Prime c
    · rw [if_pos hp, if_pos ((Nat.prime_iff.mp hp).squarefree),
        ArithmeticFunction.vonMangoldt_apply_prime hp]
    · rw [if_neg hp]
      by_cases hsf : Squarefree c
      · rw [if_pos hsf]
        have hv : ArithmeticFunction.vonMangoldt c = 0 := by
          by_contra hv
          exact hp (Submission.ASP.prime_of_squarefree_vonMangoldt_ne_zero hsf hv)
        rw [hv, zero_mul]
      · rw [if_neg hsf]
  have hsum_le : ∑ c ∈ (Submission.ASP.cseg x (Work.FIChain.sc x B * Work.FIChain.zc x B) sy).filter Nat.Prime,
        Real.log (c : ℝ) * Submission.ASP.FIgtil c
      ≤ ∑ p ∈ (Finset.Ioc lo hi).filter Nat.Prime,
          Real.log (p : ℝ) * Submission.ASP.FIgtil p := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro c hc
      obtain ⟨hcc, hcp⟩ := Finset.mem_filter.mp hc
      obtain ⟨ha, hb⟩ := hmem c hcc
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨ha, hb⟩, hcp⟩
    · intro p hp _
      obtain ⟨hpIoc, hpprime⟩ := Finset.mem_filter.mp hp
      have hp1 : 1 ≤ p := le_trans hlo1 (le_of_lt (Finset.mem_Ioc.mp hpIoc).1)
      exact mul_nonneg (Real.log_nonneg (by exact_mod_cast hp1))
        (Submission.ASP.FIgtil_nonneg p)
  have hC₀b' := hC₀b lo hi hlo1 hlohi
  refine le_trans (le_trans (le_of_eq hsum_eq) (le_trans hsum_le hC₀b')) ?_
  have h8 : (0 : ℝ) < Real.log 8 := Real.log_pos (by norm_num)
  have hb : (0 : ℝ) < 2 * B + 4 := by linarith
  have h1'' : 1 + Real.log ((hi : ℝ) / (lo : ℝ))
      ≤ (1 + Real.log 8 + (2 * B + 4)) * (1 + Real.log (Real.log (x : ℝ))) := by
    have hLR := hlogratio
    nlinarith [hLL1, h8, hb]
  nlinarith [hC₀.le, h1'']


/-! ## Floor-invariance of the smoothed sums -/

private lemma logWeight_floorC (n : ℕ) (y : ℝ) (hy : 0 ≤ y) :
    Submission.ASP.logWeight n y = Submission.ASP.logWeight n (⌊y⌋₊ : ℝ) := by
  rw [Submission.ASP.logWeight, Submission.ASP.logWeight]
  congr 1
  refine Finset.filter_congr fun b _ => ?_
  rw [(Nat.le_floor_iff hy).symm, Nat.cast_le]

/-- `Tsum` depends on `y` only through `⌊y⌋₊`. -/
lemma Tsum_floorC (a lam : ℕ → ℝ) (x y : ℝ) (hy : 0 ≤ y) :
    Submission.ASP.Tsum a lam x y = Submission.ASP.Tsum a lam x (⌊y⌋₊ : ℝ) := by
  rw [Submission.ASP.Tsum, Submission.ASP.Tsum]
  exact Finset.sum_congr rfl fun n _ => by rw [logWeight_floorC n y hy]

/-- `Tsum2` depends on its `y`-parameter only through `⌊y⌋₊`. -/
lemma Tsum2_floor_yC (a lam : ℕ → ℝ) (x y z : ℝ) (hy : 0 ≤ y) :
    Submission.ASP.Tsum2 a lam x y z = Submission.ASP.Tsum2 a lam x (⌊y⌋₊ : ℝ) z := by
  rw [Submission.ASP.Tsum2, Submission.ASP.Tsum2]
  have hfil : (Finset.Icc 1 ⌊x⌋₊).filter (fun b => ((b : ℕ) : ℝ) ≤ y)
      = (Finset.Icc 1 ⌊x⌋₊).filter (fun b => ((b : ℕ) : ℝ) ≤ (⌊y⌋₊ : ℝ)) := by
    refine Finset.filter_congr fun b _ => ?_
    rw [(Nat.le_floor_iff hy).symm, Nat.cast_le]
  rw [hfil]

/-- `Tsum2` depends on its `z`-parameter only through `⌊z⌋₊`. -/
lemma Tsum2_floor_zC (a lam : ℕ → ℝ) (x y z : ℝ) (hz : 0 ≤ z) :
    Submission.ASP.Tsum2 a lam x y z = Submission.ASP.Tsum2 a lam x y (⌊z⌋₊ : ℝ) := by
  rw [Submission.ASP.Tsum2, Submission.ASP.Tsum2]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  have hfil : (Finset.Icc 1 ⌊x⌋₊).filter (fun c => ((c : ℕ) : ℝ) ≤ z)
      = (Finset.Icc 1 ⌊x⌋₊).filter (fun c => ((c : ℕ) : ℝ) ≤ (⌊z⌋₊ : ℝ)) := by
    refine Finset.filter_congr fun c _ => ?_
    rw [(Nat.le_floor_iff hz).symm, Nat.cast_le]
  rw [hfil]

/-- `ã = μ²·a` vanishes off squarefree integers. -/
lemma atilc_eq_zero_of_not_sqfree {n : ℕ} (hn : ¬ Squarefree n) :
    Work.FIChain.atilc n = 0 := by
  rw [Work.FIChain.atilc, Work.FITop.atilFIa, Submission.ASP.atil,
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn]
  ring

lemma atilc_nonneg (n : ℕ) : 0 ≤ Work.FIChain.atilc n :=
  Submission.ASP.atil_nonneg Submission.ASP.FIa_nonneg n

/-- `x^{-2} ≤ L/L·x^{-1}`-type comparison used throughout the endgame. -/
lemma zpow_two_le_div {LN LLN : ℝ} (hLN : 1 ≤ LN) (hLLN : 1 ≤ LLN) :
    LN ^ (-(2 : ℤ)) ≤ LLN / LN := by
  have hL0 : 0 < LN := by linarith
  have hkey : LN ^ (-(2 : ℤ)) = (LN ^ 2)⁻¹ := by simp [zpow_neg]
  rw [hkey, inv_eq_one_div, div_le_div_iff₀ (pow_pos hL0 2) hL0]
  nlinarith

/-- `A^{-n} ≤ c^n·B^{-n}` when `B/c ≤ A` and all quantities are positive. -/
lemma zpow_neg_le_const_mul {A B c : ℝ} (n : ℕ) (hc : 0 < c) (hA : 0 < A) (hB : 0 < B)
    (h : B / c ≤ A) : A ^ (-(n : ℤ)) ≤ c ^ n * B ^ (-(n : ℤ)) := by
  have hcn : (0 : ℝ) < c ^ n := pow_pos hc n
  have hBn : (0 : ℝ) < B ^ n := pow_pos hB n
  have h2 : (B / c) ^ n ≤ A ^ n := pow_le_pow_left₀ (le_of_lt (div_pos hB hc)) h n
  rw [div_pow] at h2
  calc A ^ (-(n : ℤ)) = 1 / A ^ n := by
        rw [show A ^ (-(n : ℤ)) = (A ^ n)⁻¹ by simp [zpow_neg], inv_eq_one_div]
    _ ≤ 1 / (B ^ n / c ^ n) := by
        refine div_le_div_of_nonneg_left (by norm_num) (div_pos hBn hcn) h2
    _ = c ^ n * B ^ (-(n : ℤ)) := by
        rw [show B ^ (-(n : ℤ)) = (B ^ n)⁻¹ by simp [zpow_neg]]
        field_simp

/-- The `τ`-weighted sieve sum with the extra local factor `1 + log(ν·Z + 2)` (the `B₂`-bound of
`(5.1)`): replacing `ν` by `Δ` in the factor and pulling it out of the sum. -/
lemma sum_local_factor_le {Dn Zn : ℕ} {CB1 LN : ℝ} {lam : ℕ → ℝ}
    (hlam_le : ∀ ν : ℕ, |lam ν| ≤ 1)
    (hgnn : ∀ n : ℕ, 0 ≤ Submission.ASP.FIgtil n)
    (hZ1 : (1 : ℝ) ≤ (Zn : ℝ)) (hD1 : (1 : ℝ) ≤ (Dn : ℝ))
    (hB1 : (∑ ν ∈ (Finset.Icc 1 Dn).filter Squarefree,
        |lam ν| * Submission.ASP.FIgtil ν * (ν.divisors.card : ℝ)
          * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)))) ≤ CB1 * LN ^ 3) :
    (∑ ν ∈ (Finset.Icc 1 Dn).filter Squarefree,
        |lam ν| * Submission.ASP.FIgtil ν * (ν.divisors.card : ℝ)
          * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)))
          * (1 + Real.log ((ν : ℝ) * (Zn : ℝ) + 2)))
      ≤ CB1 * LN ^ 3 * (1 + Real.log ((Dn : ℝ) * (Zn : ℝ) + 2)) := by
  have hstep : ∀ ν ∈ (Finset.Icc 1 Dn).filter Squarefree,
      |lam ν| * Submission.ASP.FIgtil ν * (ν.divisors.card : ℝ)
        * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)))
        * (1 + Real.log ((ν : ℝ) * (Zn : ℝ) + 2))
      ≤ (|lam ν| * Submission.ASP.FIgtil ν * (ν.divisors.card : ℝ)
        * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))))
        * (1 + Real.log ((Dn : ℝ) * (Zn : ℝ) + 2)) := by
    intro ν hν
    rw [Finset.mem_filter, Finset.mem_Icc] at hν
    obtain ⟨⟨hν1, hνD⟩, -⟩ := hν
    have hνR : (ν : ℝ) ≤ (Dn : ℝ) := by exact_mod_cast hνD
    have hν1R : (1 : ℝ) ≤ (ν : ℝ) := by exact_mod_cast hν1
    have hZ0 : (0 : ℝ) < (Zn : ℝ) := by linarith only [hZ1]
    have h5 : (ν : ℝ) * (Zn : ℝ) + 2 ≤ (Dn : ℝ) * (Zn : ℝ) + 2 := by
      have h := mul_le_mul_of_nonneg_right hνR hZ0.le
      linarith only [h]
    have h6 : 0 < (ν : ℝ) * (Zn : ℝ) + 2 := by nlinarith only [hν1R, hZ0]
    have hfac2 : 1 + Real.log ((ν : ℝ) * (Zn : ℝ) + 2)
        ≤ 1 + Real.log ((Dn : ℝ) * (Zn : ℝ) + 2) :=
      add_le_add (le_refl (1:ℝ)) (Real.log_le_log h6 h5)
    have hpos1 : 0 ≤ |lam ν| * Submission.ASP.FIgtil ν * (ν.divisors.card : ℝ)
        * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))) :=
      mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (hgnn ν)) (by positivity))
        (Finset.prod_nonneg (fun p _ => by positivity))
    have := mul_le_mul_of_nonneg_left hfac2 hpos1
    calc |lam ν| * Submission.ASP.FIgtil ν * (ν.divisors.card : ℝ)
          * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)))
          * (1 + Real.log ((ν : ℝ) * (Zn : ℝ) + 2))
        = (|lam ν| * Submission.ASP.FIgtil ν * (ν.divisors.card : ℝ)
          * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))))
          * (1 + Real.log ((ν : ℝ) * (Zn : ℝ) + 2)) := by ring
      _ ≤ (|lam ν| * Submission.ASP.FIgtil ν * (ν.divisors.card : ℝ)
          * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))))
          * (1 + Real.log ((Dn : ℝ) * (Zn : ℝ) + 2)) := this
  calc ∑ ν ∈ (Finset.Icc 1 Dn).filter Squarefree,
        |lam ν| * Submission.ASP.FIgtil ν * (ν.divisors.card : ℝ)
          * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)))
          * (1 + Real.log ((ν : ℝ) * (Zn : ℝ) + 2))
      ≤ ∑ ν ∈ (Finset.Icc 1 Dn).filter Squarefree,
          (|lam ν| * Submission.ASP.FIgtil ν * (ν.divisors.card : ℝ)
            * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))))
            * (1 + Real.log ((Dn : ℝ) * (Zn : ℝ) + 2)) := Finset.sum_le_sum hstep
    _ = (∑ ν ∈ (Finset.Icc 1 Dn).filter Squarefree,
          |lam ν| * Submission.ASP.FIgtil ν * (ν.divisors.card : ℝ)
            * (∏ p ∈ ν.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))))
          * (1 + Real.log ((Dn : ℝ) * (Zn : ℝ) + 2)) := by rw [Finset.sum_mul]
    _ ≤ CB1 * LN ^ 3 * (1 + Real.log ((Dn : ℝ) * (Zn : ℝ) + 2)) := by
        have h3 : (1 : ℝ) ≤ (Dn : ℝ) * (Zn : ℝ) + 2 := by
          have h4 : (1 : ℝ) * 1 ≤ (Dn : ℝ) * (Zn : ℝ) :=
            mul_le_mul hD1 hZ1 (by norm_num) (by linarith only [hD1])
          linarith only [h4]
        have h5 : (0 : ℝ) ≤ 1 + Real.log ((Dn : ℝ) * (Zn : ℝ) + 2) := by
          have h4 : 0 ≤ Real.log ((Dn : ℝ) * (Zn : ℝ) + 2) := Real.log_nonneg h3
          linarith only [h4]
        exact mul_le_mul_of_nonneg_right hB1 h5

/-- The `(7.2)`-rate arithmetic: `LN·J·(E(1+log Δ)) ≤ 4Kbp·Ã·(loglog/log)`. -/
lemma E4_rate_aux {LN LLN J Kbp Abar LΔ : ℝ} (hLN : 1 ≤ LN) (hLLN : 1 ≤ LLN)
    (_hJ : 0 ≤ J) (hJle : J ≤ LN) (hLΔ1 : 0 ≤ LΔ) (hLΔ : 1 + LΔ ≤ 2 * LN)
    (hA : 0 ≤ Abar) (hK : 0 ≤ Kbp) :
    LN * (J * ((Kbp * Abar * LN ^ (-(4 : ℤ))) * (1 + LΔ)))
      ≤ (4 * Kbp) * (Abar * (LLN / LN)) := by
  have hLNp : 0 < LN := lt_of_lt_of_le zero_lt_one hLN
  have hLLN0 : 0 ≤ LLN := by linarith only [hLLN]
  have h2b : J * (1 + LΔ) ≤ 2 * LN ^ 2 := by
    have h := mul_le_mul hJle hLΔ (by linarith only [hLΔ1]) hLNp.le
    have he : LN * (2 * LN) = 2 * LN ^ 2 := by ring
    linarith only [h, he]
  have hfac : 0 ≤ LN * (Kbp * Abar) * (LN ^ (-(4 : ℤ))) := by
    refine mul_nonneg (mul_nonneg hLNp.le (mul_nonneg hK hA)) ?_
    rw [show LN ^ (-(4 : ℤ)) = (LN ^ 4)⁻¹ by simp [zpow_neg]]
    exact inv_nonneg.mpr (pow_nonneg hLNp.le 4)
  calc LN * (J * ((Kbp * Abar * LN ^ (-(4 : ℤ))) * (1 + LΔ)))
      = LN * (Kbp * Abar) * (LN ^ (-(4 : ℤ))) * (J * (1 + LΔ)) := by ring
    _ ≤ LN * (Kbp * Abar) * (LN ^ (-(4 : ℤ))) * (2 * LN ^ 2) :=
        mul_le_mul_of_nonneg_left h2b hfac
    _ = 2 * Kbp * Abar * LN ^ (-(1 : ℤ)) := by
        rw [show LN ^ (-(4 : ℤ)) = (LN ^ 4)⁻¹ by simp [zpow_neg],
          show LN ^ (-(1 : ℤ)) = LN⁻¹ by simp [zpow_neg], inv_eq_one_div, inv_eq_one_div]
        field_simp
    _ ≤ 2 * Kbp * Abar * (LLN / LN) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (mul_nonneg (by norm_num) hK) hA)
        rw [show LN ^ (-(1 : ℤ)) = LN⁻¹ by simp [zpow_neg], div_eq_mul_inv]
        calc LN⁻¹ = 1 * LN⁻¹ := by ring
          _ ≤ LLN * LN⁻¹ := mul_le_mul_of_nonneg_right hLLN (inv_nonneg.mpr hLNp.le)
    _ ≤ (4 * Kbp) * (Abar * (LLN / LN)) := by
        have hnn : 0 ≤ Abar * (LLN / LN) := mul_nonneg hA (div_nonneg hLLN0 hLNp.le)
        have he : 2 * Kbp * Abar * (LLN / LN) = 2 * (Kbp * (Abar * (LLN / LN))) := by ring
        rw [he]
        have he2 : (4 * Kbp) * (Abar * (LLN / LN)) = 4 * (Kbp * (Abar * (LLN / LN))) := by ring
        rw [he2]
        have hk : 0 ≤ Kbp * (Abar * (LLN / LN)) := mul_nonneg hK hnn
        linarith only [hk]

/-- The `(8.5)`-rate arithmetic: `J·(K3·Ã·LN^{-4})·log⌊sz⌋ ≤ K3·Ã·(loglog/log)`. -/
lemma E5_rate_aux {LN LLN J K3 Abar szlog : ℝ} (hLN : 1 ≤ LN) (hLLN : 1 ≤ LLN)
    (_hJ : 0 ≤ J) (hJle : J ≤ LN) (hsz : szlog ≤ LN / 2) (hsz0 : 0 ≤ szlog)
    (hA : 0 ≤ Abar) (hK : 0 ≤ K3) :
    J * (K3 * Abar * LN ^ (-(4 : ℤ))) * szlog ≤ K3 * (Abar * (LLN / LN)) := by
  have hLNp : 0 < LN := lt_of_lt_of_le zero_lt_one hLN
  have hLLN0 : 0 ≤ LLN := by linarith only [hLLN]
  have h2b : J * szlog ≤ LN ^ 2 / 2 := by
    have h := mul_le_mul hJle hsz hsz0 hLNp.le
    have he : LN * (LN / 2) = LN ^ 2 / 2 := by ring
    linarith only [h, he]
  have hfac : 0 ≤ K3 * Abar * (LN ^ (-(4 : ℤ))) := by
    refine mul_nonneg (mul_nonneg hK hA) ?_
    rw [show LN ^ (-(4 : ℤ)) = (LN ^ 4)⁻¹ by simp [zpow_neg]]
    exact inv_nonneg.mpr (pow_nonneg hLNp.le 4)
  have hAux : LN ^ (-(2 : ℤ)) / 2 ≤ LLN / LN := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    rw [show LN ^ (-(2 : ℤ)) = (LN ^ 2)⁻¹ by simp [zpow_neg]]
    rw [show (LLN / LN) * 2 = 2 * LLN / LN by ring]
    rw [le_div_iff₀ hLNp]
    have h2 : (LN ^ 2)⁻¹ * LN = LN⁻¹ := by field_simp
    rw [h2]
    have h1 : LN⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hLN
    have h3 : (1 : ℝ) ≤ 2 * LLN := by linarith only [hLLN]
    linarith only [h1, h3]
  calc J * (K3 * Abar * LN ^ (-(4 : ℤ))) * szlog
      = K3 * Abar * (LN ^ (-(4 : ℤ))) * (J * szlog) := by ring
    _ ≤ K3 * Abar * (LN ^ (-(4 : ℤ))) * (LN ^ 2 / 2) := mul_le_mul_of_nonneg_left h2b hfac
    _ = K3 * Abar * (LN ^ (-(2 : ℤ)) / 2) := by
        rw [show LN ^ (-(4 : ℤ)) = (LN ^ 4)⁻¹ by simp [zpow_neg],
          show LN ^ (-(2 : ℤ)) = (LN ^ 2)⁻¹ by simp [zpow_neg]]
        field_simp
    _ ≤ K3 * Abar * (LLN / LN) := mul_le_mul_of_nonneg_left hAux (mul_nonneg hK hA)
    _ = K3 * (Abar * (LLN / LN)) := by ring

end

end Work.FIChain
