import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Submission.Commons.Analysis.ExpLog.log_le_rpow_div
import Submission.Commons.Analysis.ExpLog.integrableOn_log_exp_neg_Ioi
import Submission.Commons.Analysis.ExpLog.tendsto_log_mul_sub_one_rpow
import Submission.Commons.Analysis.ExpLog.tendsto_integral_log_exp_neg_Ioi

/-! # Asymptotics of `∑ log log k (k^{-ε} − (k+1)^{-ε}) + log ε` as `ε → 0⁺` -/

noncomputable section

open Filter Set MeasureTheory Real
open scoped Topology BigOperators ENNReal

namespace Commons.Analysis.InfiniteSum

/-- `Δ_k(ε) = k^{-ε} − (k+1)^{-ε}` -/
private def delta (k : ℕ) (ε : ℝ) : ℝ :=
  (k : ℝ) ^ (-ε) - (((k + 1 : ℕ) : ℝ) ^ (-ε))

/-- term `log log k · Δ_k(ε)` -/
private def termk (k : ℕ) (ε : ℝ) : ℝ :=
  Real.log (Real.log (k : ℝ)) * delta k ε

/-- The series in the statement -/
private def ser (ε : ℝ) : ℝ :=
  ∑' k : ℕ, if 2 ≤ k then termk k ε else 0

/-- smooth function `log log x` -/
private def g (x : ℝ) : ℝ := Real.log (Real.log x)

/-- the main smooth integral from 3 to infinity -/
private def Cmain (ε : ℝ) : ℝ :=
  ∫ x : ℝ in Set.Ioi 3, ε * g x * x ^ (-ε - 1)

/-- partial sums of the series tail (indices `3..N`) -/
private def Xseq (ε : ℝ) (N : ℕ) : ℝ := ∑ k ∈ Finset.Icc 3 N, termk k ε

/-! ## Elementary estimates on `log` and `log log` -/

private lemma log_k_gt_one {k : ℕ} (hk : 3 ≤ k) : (1 : ℝ) < Real.log (k : ℝ) := by
  have hek : Real.exp 1 < (k : ℝ) := lt_of_lt_of_le Real.exp_one_lt_three (by exact_mod_cast hk)
  have hle : Real.log (Real.exp 1) < Real.log (k : ℝ) :=
    Real.log_lt_log (Real.exp_pos 1) hek
  simpa using hle

private lemma loglog_k_nonneg {k : ℕ} (hk : 3 ≤ k) : 0 ≤ Real.log (Real.log (k : ℝ)) := by
  have := Real.log_le_log (by norm_num : (0 : ℝ) < 1) (le_of_lt (log_k_gt_one hk))
  simpa using this

private lemma loglog_k_pos {k : ℕ} (hk : 3 ≤ k) : 0 < Real.log (Real.log (k : ℝ)) := by
  have := Real.log_lt_log (by norm_num : (0 : ℝ) < 1) (log_k_gt_one hk)
  simpa using this

/-- `log log (k+1) − log log k ≤ 1/(k log k)` for `3 ≤ k` -/
private lemma loglog_succ_sub_le {k : ℕ} (hk : 3 ≤ k) :
    Real.log (Real.log ((k + 1 : ℕ) : ℝ)) - Real.log (Real.log (k : ℝ))
      ≤ 1 / ((k : ℝ) * Real.log (k : ℝ)) := by
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hk1 : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 1 < k)
  have hlogk : 0 < Real.log (k : ℝ) := Real.log_pos hk1
  have hlogk1 : Real.log (k : ℝ) ≠ 0 := ne_of_gt hlogk
  have hlog_succ_sub : Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) ≤ 1 / (k : ℝ) := by
    have hdiv : Real.log (((k + 1 : ℕ) : ℝ) / (k : ℝ)) =
        Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) := by
      exact Real.log_div (by positivity : ((k + 1 : ℕ) : ℝ) ≠ 0) hk0
    have hpos : 0 < (((k + 1 : ℕ) : ℝ) / (k : ℝ)) := by positivity
    have hle := Real.log_le_sub_one_of_pos hpos
    rw [← hdiv]
    calc
      Real.log (((k + 1 : ℕ) : ℝ) / (k : ℝ)) ≤ (((k + 1 : ℕ) : ℝ) / (k : ℝ)) - 1 := hle
      _ = 1 / (k : ℝ) := by
        field_simp [hk0]
        norm_num
  have hlogk_succ : 0 < Real.log ((k + 1 : ℕ) : ℝ) := by
    have h1 : (1 : ℝ) < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < k + 1)
    exact Real.log_pos h1
  have hratio_pos : 0 < Real.log ((k + 1 : ℕ) : ℝ) / Real.log (k : ℝ) := div_pos hlogk_succ hlogk
  have hle2 := Real.log_le_sub_one_of_pos hratio_pos
  have hlogratio : Real.log (Real.log ((k + 1 : ℕ) : ℝ) / Real.log (k : ℝ)) =
      Real.log (Real.log ((k + 1 : ℕ) : ℝ)) - Real.log (Real.log (k : ℝ)) := by
    exact Real.log_div (ne_of_gt hlogk_succ) hlogk1
  have hnum : Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) ≤ 1 / (k : ℝ) := hlog_succ_sub
  have hratio_le : Real.log ((k + 1 : ℕ) : ℝ) / Real.log (k : ℝ) - 1 ≤
      1 / ((k : ℝ) * Real.log (k : ℝ)) := by
    have hden0 : Real.log (k : ℝ) ≠ 0 := hlogk1
    calc
      Real.log ((k + 1 : ℕ) : ℝ) / Real.log (k : ℝ) - 1
          = (Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ)) / Real.log (k : ℝ) := by
              field_simp [hden0]
      _ ≤ (1 / (k : ℝ)) / Real.log (k : ℝ) := by
              exact div_le_div_of_nonneg_right hnum (le_of_lt hlogk)
      _ = 1 / ((k : ℝ) * Real.log (k : ℝ)) := by
              field_simp [hden0, hk0]
  calc
    Real.log (Real.log ((k + 1 : ℕ) : ℝ)) - Real.log (Real.log (k : ℝ))
        = Real.log (Real.log ((k + 1 : ℕ) : ℝ) / Real.log (k : ℝ)) := hlogratio.symm
    _ ≤ Real.log ((k + 1 : ℕ) : ℝ) / Real.log (k : ℝ) - 1 := hle2
    _ ≤ 1 / ((k : ℝ) * Real.log (k : ℝ)) := hratio_le

/-- `x ↦ log log x` is monotone on `x > 1` -/
private lemma g_mono {x y : ℝ} (hx : 1 < x) (hxy : x ≤ y) : g x ≤ g y := by
  unfold g
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hlogle : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
  exact Real.log_le_log hlogx hlogle

/-- `g x ≤ g (k+1)` for `k ≤ x ≤ k+1`, `k ≥ 3` -/
private lemma g_le_succ {k : ℕ} (hk : 3 ≤ k) {x : ℝ} (hxk : (k : ℝ) ≤ x)
    (hx : x ≤ ((k + 1 : ℕ) : ℝ)) : g x ≤ g ((k + 1 : ℕ) : ℝ) := by
  have hk1 : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 1 < k)
  exact g_mono (lt_of_lt_of_le hk1 hxk) hx

/-- oscillation bound: `0 ≤ g x − g k ≤ 1/(k log k)` for `k ≤ x ≤ k+1`, `3 ≤ k` -/
private lemma g_osc_cell {k : ℕ} (hk : 3 ≤ k) {x : ℝ} (hxk : (k : ℝ) ≤ x)
    (hx : x ≤ ((k + 1 : ℕ) : ℝ)) :
    g x - g (k : ℝ) ≤ 1 / ((k : ℝ) * Real.log (k : ℝ)) := by
  have hmono := g_le_succ hk hxk hx
  have hsucc : g ((k + 1 : ℕ) : ℝ) - g (k : ℝ) ≤ 1 / ((k : ℝ) * Real.log (k : ℝ)) := by
    simpa [g] using loglog_succ_sub_le hk
  have hge : g (k : ℝ) ≤ g x := by
    have hk1 : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 1 < k)
    exact g_mono hk1 hxk
  linarith

/-! ## Calculus: per-cell integral identities -/

/-- `∫_k^{k+1} ε x^{-ε-1} dx = Δ_k(ε)`, for `1 ≤ k` -/
private lemma delta_eq_cell_int (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) :
    delta k ε = (∫ x : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), ε * x ^ (-ε - 1)) := by
  rw [show (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 by norm_num]
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hk)
  have hderiv : ∀ x ∈ Set.uIcc (k : ℝ) ((k : ℝ) + 1),
      HasDerivAt (fun x : ℝ => -(x ^ (-ε))) (ε * x ^ (-ε - 1)) x := by
    intro x hx
    have hxpos : 0 < x := by
      rw [uIcc_of_le (by norm_num)] at hx
      exact lt_of_lt_of_le hkpos hx.1
    have hd := Real.hasDerivAt_rpow_const (x := x) (p := -ε) (Or.inl (ne_of_gt hxpos))
    exact hd.neg.congr_deriv (by ring)
  have hint : IntervalIntegrable (fun x : ℝ => ε * x ^ (-ε - 1)) volume (k : ℝ) ((k : ℝ) + 1) := by
    have h0not : (0 : ℝ) ∉ Set.uIcc (k : ℝ) ((k : ℝ) + 1) := by
      rw [uIcc_of_le (by norm_num)]
      simp [Set.mem_Icc, not_le_of_gt hkpos]
    have hir : IntervalIntegrable (fun x : ℝ => x ^ (-ε - 1)) volume (k : ℝ) ((k : ℝ) + 1) :=
      intervalIntegral.intervalIntegrable_rpow (r := -ε - 1) (Or.inr h0not)
    exact hir.const_mul ε
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  unfold delta
  norm_num [Nat.cast_add]
  ring

/-- `x ↦ x^p` is nonincreasing on `[1, ∞)` for `p ≤ 0` -/
private lemma rpow_anti_on_one_le {a b p : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hp : p ≤ 0) :
    b ^ p ≤ a ^ p := by
  have hb : 0 < b := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_trans ha hab)
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ha
  rw [Real.rpow_def_of_pos hb, Real.rpow_def_of_pos ha0]
  refine Real.exp_le_exp.mpr ?_
  have hlogle : Real.log a ≤ Real.log b := Real.log_le_log ha0 hab
  calc
    Real.log b * p ≤ Real.log a * p := mul_le_mul_of_nonpos_right hlogle hp
    _ = Real.log a * p := rfl

/-- `Δ_k(ε) ≥ 0` for `1 ≤ k`, `0 ≤ ε` -/
private lemma delta_nonneg (k : ℕ) (hk : 1 ≤ k) {ε : ℝ} (hε : 0 ≤ ε) : 0 ≤ delta k ε := by
  unfold delta
  have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkc : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.le_succ k)
  have hanti : ((k + 1 : ℕ) : ℝ) ^ (-ε) ≤ (k : ℝ) ^ (-ε) :=
    rpow_anti_on_one_le hk1R hkc (neg_nonpos.mpr hε)
  linarith

/-! ## positivity of the terms and monotonicity of partial sums -/

private lemma termk_nonneg {ε : ℝ} (hε : 0 ≤ ε) {k : ℕ} (hk : 3 ≤ k) : 0 ≤ termk k ε := by
  unfold termk
  exact mul_nonneg (loglog_k_nonneg hk) (delta_nonneg k (by omega) hε)

private lemma Xseq_mono {ε : ℝ} (hε : 0 ≤ ε) : Monotone (Xseq ε) := by
  intro m n hmn
  unfold Xseq
  have hsub : Finset.Icc 3 m ⊆ Finset.Icc 3 n := Finset.Icc_subset_Icc (by norm_num) hmn
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by
    intro k hk hknot
    have h3 : 3 ≤ k := (Finset.mem_Icc.mp hk).1
    exact termk_nonneg hε h3)

/-! ## `Δ_k(ε) ≤ ε·k^{-ε-1}` and integrability on cells -/

/-- integrability of the rpow integrand on a cell -/
private lemma cell_rpow_int (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) :
    IntervalIntegrable (fun x : ℝ => ε * x ^ (-ε - 1)) volume (k : ℝ) (((k + 1 : ℕ) : ℝ)) := by
  rw [show (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 by norm_num]
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hk)
  have h0not : (0 : ℝ) ∉ Set.uIcc (k : ℝ) ((k : ℝ) + 1) := by
    rw [uIcc_of_le (by norm_num)]
    simp [Set.mem_Icc, not_le_of_gt hkpos]
  have hir : IntervalIntegrable (fun x : ℝ => x ^ (-ε - 1)) volume (k : ℝ) ((k : ℝ) + 1) :=
    intervalIntegral.intervalIntegrable_rpow (r := -ε - 1) (Or.inr h0not)
  exact hir.const_mul ε

/-- integrability of the smooth integrand on a cell (k ≥ 3) -/
private lemma cell_g_int (ε : ℝ) (k : ℕ) (hk : 3 ≤ k) :
    IntervalIntegrable (fun x : ℝ => ε * g x * x ^ (-ε - 1)) volume (k : ℝ) (((k + 1 : ℕ) : ℝ)) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  refine ContinuousOn.intervalIntegrable ?_
  intro x hx
  have hxk : (k : ℝ) ≤ x := by
    rw [uIcc_of_le (by norm_num : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ))] at hx
    exact hx.1
  have hxpos : 0 < x := lt_of_lt_of_le hkpos hxk
  have hx_gt_one : 1 < x := by
    have hk3R : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 3 ≤ k)
    linarith
  have hcont_g : ContinuousAt g x := by
    unfold g
    have hinner : ContinuousAt Real.log x := Real.continuousAt_log (ne_of_gt hxpos)
    exact (Real.continuousAt_log (ne_of_gt (Real.log_pos hx_gt_one))).comp hinner
  have hcont_r : ContinuousAt (fun y : ℝ => y ^ (-ε - 1)) x :=
    Real.continuousAt_rpow_const x (-ε - 1) (Or.inl (ne_of_gt hxpos))
  exact (continuousWithinAt_const.mul hcont_g.continuousWithinAt).mul hcont_r.continuousWithinAt

/-- `Δ_k(ε) ≤ ε·k^{-ε-1}` for `1 ≤ k`, `0 ≤ ε` -/
private lemma delta_le_mul_rpow (k : ℕ) (hk : 1 ≤ k) {ε : ℝ} (hε : 0 ≤ ε) :
    delta k ε ≤ ε * (k : ℝ) ^ (-ε - 1) := by
  have hbd : ∀ x ∈ Set.Icc (k : ℝ) (((k + 1 : ℕ) : ℝ)),
      ε * x ^ (-ε - 1) ≤ ε * (k : ℝ) ^ (-ε - 1) := by
    intro x hx
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hpx : x ^ (-ε - 1) ≤ (k : ℝ) ^ (-ε - 1) :=
      rpow_anti_on_one_le hk1 hx.1 (by linarith : -ε - 1 ≤ 0)
    exact mul_le_mul_of_nonneg_left hpx hε
  have hle : (∫ x : ℝ in (k : ℝ)..(((k + 1 : ℕ) : ℝ)), ε * x ^ (-ε - 1))
      ≤ ∫ x : ℝ in (k : ℝ)..(((k + 1 : ℕ) : ℝ)), ε * (k : ℝ) ^ (-ε - 1) := by
    refine intervalIntegral.integral_mono_on ?hab ?hf ?hg hbd
    · exact_mod_cast (Nat.le_succ k)
    · exact cell_rpow_int k hk ε
    · exact intervalIntegrable_const
  have hconst : (∫ x : ℝ in (k : ℝ)..(((k + 1 : ℕ) : ℝ)), ε * (k : ℝ) ^ (-ε - 1)) =
      ε * (k : ℝ) ^ (-ε - 1) := by
    rw [intervalIntegral.integral_const]
    norm_num
  calc
    delta k ε ≤ (∫ x : ℝ in (k : ℝ)..(((k + 1 : ℕ) : ℝ)), ε * x ^ (-ε - 1)) := by
      rw [delta_eq_cell_int k hk]
    _ ≤ (∫ x : ℝ in (k : ℝ)..(((k + 1 : ℕ) : ℝ)), ε * (k : ℝ) ^ (-ε - 1)) := hle
    _ = ε * (k : ℝ) ^ (-ε - 1) := hconst

/-! ## cell difference estimates -/

/-- smooth cell integral -/
private def Ycell (ε : ℝ) (k : ℕ) : ℝ :=
  ∫ x : ℝ in (k : ℝ)..(((k + 1 : ℕ) : ℝ)), ε * g x * x ^ (-ε - 1)

/-- the Y-side partial sums (cell sum) -/
private def Yseq (ε : ℝ) (N : ℕ) : ℝ := ∑ k ∈ Finset.Icc 3 N, Ycell ε k

/-- cell difference `termk k ε - Ycell ε k` -/
private def cellDiff (ε : ℝ) (k : ℕ) : ℝ :=
  ∫ x : ℝ in (k : ℝ)..(((k + 1 : ℕ) : ℝ)), ε * (g (k : ℝ) - g x) * x ^ (-ε - 1)

/-- `termk k ε = ∫_k^{k+1} ε·g(k)·x^{-ε-1}` for `1 ≤ k` -/
private lemma termk_eq_cell (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) :
    termk k ε = (∫ x : ℝ in (k : ℝ)..(((k + 1 : ℕ) : ℝ)),
      ε * g (k : ℝ) * x ^ (-ε - 1)) := by
  have hout : (∫ x : ℝ in (k : ℝ)..(((k + 1 : ℕ) : ℝ)), ε * g (k : ℝ) * x ^ (-ε - 1))
      = g (k : ℝ) * (∫ x : ℝ in (k : ℝ)..(((k + 1 : ℕ) : ℝ)), ε * x ^ (-ε - 1)) := by
    calc
      (∫ x : ℝ in (k : ℝ)..(((k + 1 : ℕ) : ℝ)), ε * g (k : ℝ) * x ^ (-ε - 1))
          = (∫ x : ℝ in (k : ℝ)..(((k + 1 : ℕ) : ℝ)), g (k : ℝ) * (ε * x ^ (-ε - 1))) := by
            apply intervalIntegral.integral_congr
            intro x hx
            ring
      _ = g (k : ℝ) * (∫ x : ℝ in (k : ℝ)..(((k + 1 : ℕ) : ℝ)), ε * x ^ (-ε - 1)) := by
            rw [intervalIntegral.integral_const_mul]
  unfold termk
  rw [delta_eq_cell_int k hk]
  exact hout.symm

/-- `Xseq - Yseq = ∑ cells of cellDiff` -/
private lemma Xseq_sub_Yseq_eq (ε : ℝ) (N : ℕ) :
    Xseq ε N - Yseq ε N = ∑ k ∈ Finset.Icc 3 N, cellDiff ε k := by
  unfold Xseq Yseq cellDiff
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hk3 : 3 ≤ k := (Finset.mem_Icc.mp hk).1
  have hk1 : 1 ≤ k := by omega
  have hterm : termk k ε = (∫ x : ℝ in (k : ℝ)..(((k + 1 : ℕ) : ℝ)),
      ε * g (k : ℝ) * x ^ (-ε - 1)) := termk_eq_cell k hk1 ε
  rw [hterm]
  have hf : IntervalIntegrable (fun x : ℝ => ε * g (k : ℝ) * x ^ (-ε - 1)) volume
      (k : ℝ) (((k + 1 : ℕ) : ℝ)) := by
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have h0not : (0 : ℝ) ∉ Set.uIcc (k : ℝ) (((k + 1 : ℕ) : ℝ)) := by
      rw [uIcc_of_le (by exact_mod_cast (Nat.le_succ k) : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ))]
      simp [Set.mem_Icc, not_le_of_gt hkpos]
    have hir : IntervalIntegrable (fun x : ℝ => x ^ (-ε - 1)) volume (k : ℝ) (((k + 1 : ℕ) : ℝ)) :=
      intervalIntegral.intervalIntegrable_rpow (r := -ε - 1) (Or.inr h0not)
    exact hir.const_mul (ε * g (k : ℝ))
  have hg : IntervalIntegrable (fun x : ℝ => ε * g x * x ^ (-ε - 1)) volume (k : ℝ) (((k + 1 : ℕ) : ℝ)) :=
    cell_g_int ε k hk3
  have hsub := intervalIntegral.integral_sub hf hg
  calc
    (∫ x : ℝ in (k : ℝ)..(((k + 1 : ℕ) : ℝ)), ε * g (k : ℝ) * x ^ (-ε - 1))
        - (∫ x : ℝ in (k : ℝ)..(((k + 1 : ℕ) : ℝ)), ε * g x * x ^ (-ε - 1))
        = (∫ x : ℝ in (k : ℝ)..(((k + 1 : ℕ) : ℝ)),
            ε * g (k : ℝ) * x ^ (-ε - 1) - ε * g x * x ^ (-ε - 1)) := hsub.symm
    _ = (∫ x : ℝ in (k : ℝ)..(((k + 1 : ℕ) : ℝ)),
            ε * (g (k : ℝ) - g x) * x ^ (-ε - 1)) := by
          apply intervalIntegral.integral_congr
          intro x hx
          ring

/-- `|g k − g x| ≤ 1/(k log k)` on the cell -/
private lemma abs_g_sub_gk_le (k : ℕ) (hk : 3 ≤ k) {x : ℝ} (hxk : (k : ℝ) ≤ x)
    (hx : x ≤ ((k + 1 : ℕ) : ℝ)) : |g (k : ℝ) - g x| ≤ 1 / ((k : ℝ) * Real.log (k : ℝ)) := by
  have hge : g (k : ℝ) ≤ g x := by
    have h1 : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 1 < k)
    exact g_mono h1 hxk
  have hosc : g x - g (k : ℝ) ≤ 1 / ((k : ℝ) * Real.log (k : ℝ)) := g_osc_cell hk hxk hx
  rw [abs_of_nonpos (sub_nonpos.mpr hge)]
  linarith

/-- bound `|cellDiff ε k| ≤ ε/k²` for `3 ≤ k`, `0 ≤ ε` -/
private lemma abs_cellDiff_le (ε : ℝ) (hε : 0 ≤ ε) {k : ℕ} (hk : 3 ≤ k) :
    ‖cellDiff ε k‖ ≤ ε / (k : ℝ) ^ 2 := by
  let osc : ℝ := 1 / ((k : ℝ) * Real.log (k : ℝ))
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
  have hk1 : 1 ≤ k := by omega
  have hlog : (1 : ℝ) ≤ Real.log (k : ℝ) := le_of_lt (log_k_gt_one hk)
  have hprod : (k : ℝ) ≤ (k : ℝ) * Real.log (k : ℝ) := by
    calc
      (k : ℝ) = (k : ℝ) * 1 := by ring
      _ ≤ (k : ℝ) * Real.log (k : ℝ) := mul_le_mul_of_nonneg_left hlog (le_of_lt hkpos)
  have hosc_le : osc ≤ 1 / (k : ℝ) := by
    unfold osc
    exact one_div_le_one_div_of_le hkpos hprod
  -- pointwise domination of the integrand's norm by `fun x => ε * osc * x^{-ε-1}`
  have hbd : ∀ x ∈ Set.Icc (k : ℝ) (((k + 1 : ℕ) : ℝ)),
      ‖ε * (g (k : ℝ) - g x) * x ^ (-ε - 1)‖ ≤ ε * osc * x ^ (-ε - 1) := by
    intro x hx
    have hx0 : 0 ≤ x := le_of_lt (lt_of_lt_of_le hkpos hx.1)
    have h1 : |ε * (g (k : ℝ) - g x)| ≤ ε * osc := by
      calc
        |ε * (g (k : ℝ) - g x)| = |ε| * |g (k : ℝ) - g x| := by rw [abs_mul]
        _ = ε * |g (k : ℝ) - g x| := by rw [abs_of_nonneg hε]
        _ ≤ ε * osc := mul_le_mul_of_nonneg_left (abs_g_sub_gk_le k hk hx.1 hx.2) hε
    have h2 : |x ^ (-ε - 1)| = x ^ (-ε - 1) := abs_of_nonneg (Real.rpow_nonneg hx0 (-ε - 1))
    calc
      ‖ε * (g (k : ℝ) - g x) * x ^ (-ε - 1)‖ = |ε * (g (k : ℝ) - g x) * x ^ (-ε - 1)| := by
        exact Real.norm_eq_abs _
      _ = |ε * (g (k : ℝ) - g x)| * |x ^ (-ε - 1)| := by rw [abs_mul]
      _ ≤ (ε * osc) * |x ^ (-ε - 1)| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ = ε * osc * x ^ (-ε - 1) := by rw [h2]
  have hii : IntervalIntegrable (fun x : ℝ => ε * osc * x ^ (-ε - 1)) volume (k : ℝ) (((k + 1 : ℕ) : ℝ)) := by
    have h0not : (0 : ℝ) ∉ Set.uIcc (k : ℝ) (((k + 1 : ℕ) : ℝ)) := by
      rw [uIcc_of_le (by exact_mod_cast (Nat.le_succ k) : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ))]
      simp [Set.mem_Icc, not_le_of_gt hkpos]
    have hir : IntervalIntegrable (fun x : ℝ => x ^ (-ε - 1)) volume (k : ℝ) (((k + 1 : ℕ) : ℝ)) :=
      intervalIntegral.intervalIntegrable_rpow (r := -ε - 1) (Or.inr h0not)
    exact hir.const_mul (ε * osc)
  have hab : (k : ℝ) ≤ (((k + 1 : ℕ) : ℝ)) := by exact_mod_cast (Nat.le_succ k)
  have hle : ‖∫ x : ℝ in (k : ℝ)..(((k + 1 : ℕ) : ℝ)),
        ε * (g (k : ℝ) - g x) * x ^ (-ε - 1)‖
      ≤ ∫ x : ℝ in (k : ℝ)..(((k + 1 : ℕ) : ℝ)), ε * osc * x ^ (-ε - 1) := by
    refine intervalIntegral.norm_integral_le_of_norm_le hab ?_ hii
    filter_upwards with x hx
    have hxcc : x ∈ Set.Icc (k : ℝ) (((k + 1 : ℕ) : ℝ)) := by
      exact (Set.mem_Icc.mpr ⟨le_of_lt (Set.mem_Ioc.mp hx).1, (Set.mem_Ioc.mp hx).2⟩)
    exact hbd x hxcc
  have hrhs : (∫ x : ℝ in (k : ℝ)..(((k + 1 : ℕ) : ℝ)), ε * osc * x ^ (-ε - 1))
      = osc * delta k ε := by
    calc
      (∫ x : ℝ in (k : ℝ)..(((k + 1 : ℕ) : ℝ)), ε * osc * x ^ (-ε - 1))
          = (∫ x : ℝ in (k : ℝ)..(((k + 1 : ℕ) : ℝ)), osc * (ε * x ^ (-ε - 1))) := by
            apply intervalIntegral.integral_congr
            intro x hx
            ring
      _ = osc * (∫ x : ℝ in (k : ℝ)..(((k + 1 : ℕ) : ℝ)), ε * x ^ (-ε - 1)) := by
            rw [intervalIntegral.integral_const_mul]
      _ = osc * delta k ε := by rw [delta_eq_cell_int k hk1]
  have hosc_delta : osc * delta k ε ≤ osc * (ε * (k : ℝ) ^ (-ε - 1)) := by
    have hosc0 : 0 ≤ osc := by
      unfold osc
      positivity
    exact mul_le_mul_of_nonneg_left (delta_le_mul_rpow k hk1 hε) hosc0
  have hfin : osc * (ε * (k : ℝ) ^ (-ε - 1)) ≤ ε / (k : ℝ) ^ 2 := by
    have h1 : osc * (ε * (k : ℝ) ^ (-ε - 1)) ≤ (1 / (k : ℝ)) * (ε * (k : ℝ) ^ (-ε - 1)) := by
      exact mul_le_mul_of_nonneg_right hosc_le (mul_nonneg hε (Real.rpow_nonneg (le_of_lt hkpos) (-ε - 1)))
    have h2 : (1 / (k : ℝ)) * (ε * (k : ℝ) ^ (-ε - 1 : ℝ)) = ε * (k : ℝ) ^ (-ε - 2 : ℝ) := by
      have hmain : (k : ℝ) ^ (-ε - 1 : ℝ) / (k : ℝ) = (k : ℝ) ^ (-ε - 2 : ℝ) := by
        rw [← Real.rpow_sub_one (ne_of_gt hkpos) (-ε - 1 : ℝ)]
        rw [show (-ε - 1 : ℝ) - 1 = -ε - 2 by ring]
      calc
        (1 / (k : ℝ)) * (ε * (k : ℝ) ^ (-ε - 1 : ℝ)) = ε * ((k : ℝ) ^ (-ε - 1 : ℝ) / (k : ℝ)) := by
          field_simp [ne_of_gt hkpos]
        _ = ε * (k : ℝ) ^ (-ε - 2 : ℝ) := by rw [hmain]
    have h3 : ε * (k : ℝ) ^ (-ε - 2) ≤ ε / (k : ℝ) ^ 2 := by
      have hanti : (k : ℝ) ^ (-ε - 2 : ℝ) ≤ (k : ℝ) ^ (-2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hk1R (by linarith : (-ε - 2 : ℝ) ≤ (-2 : ℝ))
      have hnn : ε * (k : ℝ) ^ (-2 : ℝ) = ε / (k : ℝ) ^ 2 := by
        have hpow : (k : ℝ) ^ (-2 : ℝ) = (1 : ℝ) / (k : ℝ) ^ 2 := by
          rw [show (-2 : ℝ) = (-1 : ℝ) + (-1 : ℝ) by norm_num]
          rw [Real.rpow_add hkpos]
          rw [Real.rpow_neg_one]
          field_simp [ne_of_gt hkpos]
        rw [hpow]
        ring
      calc
        ε * (k : ℝ) ^ (-ε - 2 : ℝ) ≤ ε * (k : ℝ) ^ (-2 : ℝ) := mul_le_mul_of_nonneg_left hanti hε
        _ = ε / (k : ℝ) ^ 2 := hnn
    calc
      osc * (ε * (k : ℝ) ^ (-ε - 1)) ≤ (1 / (k : ℝ)) * (ε * (k : ℝ) ^ (-ε - 1)) := h1
      _ = ε * (k : ℝ) ^ (-ε - 2) := h2
      _ ≤ ε / (k : ℝ) ^ 2 := h3
  calc
    ‖cellDiff ε k‖ ≤ ∫ x : ℝ in (k : ℝ)..(((k + 1 : ℕ) : ℝ)), ε * osc * x ^ (-ε - 1) := by
      simpa [cellDiff] using hle
    _ = osc * delta k ε := hrhs
    _ ≤ osc * (ε * (k : ℝ) ^ (-ε - 1)) := hosc_delta
    _ ≤ ε / (k : ℝ) ^ 2 := hfin

/-- `∑_{k=3}^N 1/k² ≤ 1/2` -/
private lemma sum_inv_sq_Icc_ge3_le_half (N : ℕ) :
    (∑ k ∈ Finset.Icc 3 N, (1 : ℝ) / (k : ℝ) ^ 2) ≤ 1 / 2 := by
  by_cases hN : N < 3
  · have hsub : Finset.Icc 3 N = (∅ : Finset ℕ) := by
      ext k
      constructor
      · intro hk
        have h3 : 3 ≤ k := (Finset.mem_Icc.mp hk).1
        have hkN : k ≤ N := (Finset.mem_Icc.mp hk).2
        omega
      · intro hk
        simpa using hk
    rw [hsub]
    simp
  · have hN2 : 2 ≤ N := by omega
    have hs := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := 2) (n := N) (by norm_num) hN2
    -- convert our sum to the Ioc form
    have hset : Finset.Icc 3 N = Finset.Ioc 2 N := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_Ioc]
      omega
    calc
      (∑ k ∈ Finset.Icc 3 N, (1 : ℝ) / (k : ℝ) ^ 2)
          = ∑ k ∈ Finset.Ioc 2 N, ((k : ℝ) ^ 2)⁻¹ := by
            rw [hset]
            apply Finset.sum_congr rfl
            intro k hk
            rw [one_div]
      _ ≤ (2 : ℝ)⁻¹ - (N : ℝ)⁻¹ := hs
      _ ≤ 1 / 2 := by
        have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
        have hNinv : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr (le_of_lt hNpos)
        have h2inv : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
        rw [h2inv]
        linarith

/-- summed bound: `|Xseq ε N − Yseq ε N| ≤ ε/2` for `N ≥ 3`, `0 ≤ ε` -/
private lemma abs_Xseq_sub_Yseq_le (ε : ℝ) (hε : 0 ≤ ε) (N : ℕ) (hN : 3 ≤ N) :
    ‖Xseq ε N - Yseq ε N‖ ≤ ε / 2 := by
  rw [Xseq_sub_Yseq_eq]
  have hsum : ‖∑ k ∈ Finset.Icc 3 N, cellDiff ε k‖ ≤ ∑ k ∈ Finset.Icc 3 N, ε / (k : ℝ) ^ 2 := by
    calc
      ‖∑ k ∈ Finset.Icc 3 N, cellDiff ε k‖ ≤ ∑ k ∈ Finset.Icc 3 N, ‖cellDiff ε k‖ := by
        simpa [Real.norm_eq_abs] using (norm_sum_le (Finset.Icc 3 N) (fun k => cellDiff ε k))
      _ ≤ ∑ k ∈ Finset.Icc 3 N, ε / (k : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro k hk
        exact abs_cellDiff_le ε hε (k := k) (Finset.mem_Icc.mp hk).1
  have hgeom : ∑ k ∈ Finset.Icc 3 N, ε / (k : ℝ) ^ 2 ≤ ε / 2 := by
    calc
      ∑ k ∈ Finset.Icc 3 N, ε / (k : ℝ) ^ 2
          = ε * (∑ k ∈ Finset.Icc 3 N, (1 : ℝ) / (k : ℝ) ^ 2) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k hk
            ring
      _ ≤ ε * (1 / 2) := by
            exact mul_le_mul_of_nonneg_left (sum_inv_sq_Icc_ge3_le_half N) hε
      _ = ε / 2 := by ring
  exact le_trans hsum hgeom

/-! ## u-space integrability and substitution -/

/-- `|log u| ≤ |log c| + 2·u^(1/2)` for `u ≥ c > 0` -/
private lemma log_u_abs_bound {c u : ℝ} (hc : 0 < c) (hcu : c ≤ u) :
    |Real.log u| ≤ |Real.log c| + 2 * u ^ (1 / 2 : ℝ) := by
  by_cases hu : u < 1
  · have hu0 : 0 < u := lt_of_lt_of_le hc hcu
    have hneg : Real.log u < 0 := Real.log_neg hu0 hu
    have hc1 : c < 1 := lt_of_le_of_lt hcu hu
    have hnegc : Real.log c < 0 := Real.log_neg hc hc1
    have hmain : -Real.log u ≤ -Real.log c := by
      have hlogc : Real.log c ≤ Real.log u := Real.log_le_log hc hcu
      linarith
    have hnn : 0 ≤ 2 * u ^ (1 / 2 : ℝ) := by positivity
    calc
      |Real.log u| = -Real.log u := abs_of_neg hneg
      _ ≤ -Real.log c := hmain
      _ = |Real.log c| := (abs_of_neg hnegc).symm
      _ ≤ |Real.log c| + 2 * u ^ (1 / 2 : ℝ) := by linarith
  · have hu1 : 1 ≤ u := le_of_not_gt hu
    have hpos : 0 ≤ Real.log u := Real.log_nonneg hu1
    have hle : Real.log u ≤ 2 * u ^ (1 / 2 : ℝ) := by
      have hll := Commons.Analysis.ExpLog.log_le_rpow_div (w := u) (a := (1 / 2 : ℝ))
        (hw := hu1) (ha := by norm_num)
      have hdiv : u ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) = 2 * u ^ (1 / 2 : ℝ) := by
        rw [div_eq_mul_inv]
        norm_num
        ring
      rw [hdiv] at hll
      exact hll
    calc
      |Real.log u| = Real.log u := abs_of_nonneg hpos
      _ ≤ 2 * u ^ (1 / 2 : ℝ) := hle
      _ ≤ |Real.log c| + 2 * u ^ (1 / 2 : ℝ) := by
        have hnn : 0 ≤ |Real.log c| := abs_nonneg _
        linarith

/-- integrability of `u ↦ u^(1/2)·e^{-u}` on `(0,∞)` -/
private lemma integrableOn_rpow_half_exp_neg_Ioi :
    MeasureTheory.IntegrableOn (fun u : ℝ => u ^ (1 / 2 : ℝ) * Real.exp (-u)) (Set.Ioi 0)
      MeasureTheory.volume := by
  have h := integrableOn_rpow_mul_exp_neg_rpow (by norm_num : (-1 : ℝ) < (1 / 2 : ℝ))
    (by norm_num : (0 : ℝ) < 1)
  simpa [Real.rpow_one] using h

/-- integrability of `u ↦ log u·e^{-u}` on `(c,∞)` for `0 < c` -/
private lemma integrableOn_log_exp_neg_Ioi (c : ℝ) (hc : 0 < c) :
    MeasureTheory.IntegrableOn (fun u : ℝ => Real.log u * Real.exp (-u)) (Set.Ioi c)
      MeasureTheory.volume := by
  have hbd0 : ∀ u, c < u → ‖Real.log u * Real.exp (-u)‖ ≤
        |Real.log c| * Real.exp (-u) + 2 * u ^ (1 / 2 : ℝ) * Real.exp (-u) := by
    intro u hu
    have h1 := log_u_abs_bound hc (le_of_lt hu)
    rw [Real.norm_eq_abs]
    rw [abs_mul, abs_of_pos (Real.exp_pos (-u))]
    calc
      |Real.log u| * Real.exp (-u) ≤ (|Real.log c| + 2 * u ^ (1 / 2 : ℝ)) * Real.exp (-u) := by
        exact mul_le_mul_of_nonneg_right h1 (le_of_lt (Real.exp_pos (-u)))
      _ = |Real.log c| * Real.exp (-u) + 2 * u ^ (1 / 2 : ℝ) * Real.exp (-u) := by ring
  have hb : ∀ᵐ u ∂(MeasureTheory.volume.restrict (Set.Ioi c)),
      ‖Real.log u * Real.exp (-u)‖ ≤
        |Real.log c| * Real.exp (-u) + 2 * u ^ (1 / 2 : ℝ) * Real.exp (-u) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    exact Eventually.of_forall hbd0
  have hf : AEStronglyMeasurable (fun u : ℝ => Real.log u * Real.exp (-u))
      (MeasureTheory.volume.restrict (Set.Ioi c)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro u hu
    have hcu : c ≤ u := le_of_lt hu
    have hc1 : ContinuousWithinAt Real.log (Set.Ioi c) u :=
      (Real.continuousAt_log (ne_of_gt (lt_of_lt_of_le hc hcu))).continuousWithinAt
    have hc2 : ContinuousWithinAt (fun y : ℝ => Real.exp (-y)) (Set.Ioi c) u :=
      (Real.continuous_exp.continuousAt.comp continuousAt_id.neg).continuousWithinAt
    exact hc1.mul hc2
  have hG1 : MeasureTheory.IntegrableOn (fun u : ℝ => |Real.log c| * Real.exp (-u)) (Set.Ioi c)
      MeasureTheory.volume := (integrableOn_exp_neg_Ioi c).const_mul |Real.log c|
  have hG2 : MeasureTheory.IntegrableOn (fun u : ℝ => 2 * u ^ (1 / 2 : ℝ) * Real.exp (-u)) (Set.Ioi c)
      MeasureTheory.volume := by
    have hh : MeasureTheory.IntegrableOn (fun u : ℝ => u ^ (1 / 2 : ℝ) * Real.exp (-u)) (Set.Ioi c)
        MeasureTheory.volume :=
      integrableOn_rpow_half_exp_neg_Ioi.mono_set (Set.Ioi_subset_Ioi (le_of_lt hc))
    have hh2 : MeasureTheory.IntegrableOn (fun u : ℝ => 2 * (u ^ (1 / 2 : ℝ) * Real.exp (-u)))
        (Set.Ioi c) MeasureTheory.volume := hh.const_mul 2
    refine MeasureTheory.IntegrableOn.congr_fun_ae hh2 ?_
    filter_upwards with u
    ring
  have hG : MeasureTheory.IntegrableOn
      (fun u : ℝ => |Real.log c| * Real.exp (-u) + 2 * u ^ (1 / 2 : ℝ) * Real.exp (-u))
      (Set.Ioi c) MeasureTheory.volume := hG1.add hG2
  -- IntegrableOn = Integrable on the restricted measure
  exact ⟨hf, HasFiniteIntegral.mono' hG.hasFiniteIntegral hb⟩

/-! ## change of variables: the smooth integral in `u`-space -/

/-- image of `(3,∞)` under `x ↦ ε·log x` is `(ε·log 3, ∞)`, for `0 < ε` -/
private lemma log_mul_image_Ioi {ε : ℝ} (hε : 0 < ε) :
    (fun x : ℝ => ε * Real.log x) '' Set.Ioi 3 = Set.Ioi (ε * Real.log 3) := by
  ext u
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hlog : Real.log 3 < Real.log x := Real.log_lt_log (by norm_num : (0 : ℝ) < 3) hx
    exact mul_lt_mul_of_pos_left hlog hε
  · intro hu
    have hle : ε * Real.log 3 < u := hu
    have hdiv : Real.log 3 < u / ε := (lt_div_iff₀ hε).mpr (by simpa [mul_comm] using hle)
    have hx3 : 3 < Real.exp (u / ε) := by
      have he := Real.exp_lt_exp.mpr hdiv
      simpa [Real.exp_log (by norm_num : (0 : ℝ) < 3)] using he
    refine ⟨Real.exp (u / ε), hx3, ?_⟩
    change ε * Real.log (Real.exp (u / ε)) = u
    rw [Real.log_exp]
    field_simp [ne_of_gt hε]

/-- the substitution algebra: `(ε/x)·(log(ε·log x)−log ε)·e^{-ε·log x} = ε·loglog x·x^{-ε-1}` -/
private lemma jac_ident {ε x : ℝ} (hε : 0 < ε) (hx : 3 < x) :
    (ε / x) * ((Real.log (ε * Real.log x) - Real.log ε) * Real.exp (-ε * Real.log x)) =
      ε * g x * x ^ (-ε - 1) := by
  have hx1 : (1 : ℝ) < x := lt_trans (by norm_num : (1 : ℝ) < 3) hx
  have hx0 : 0 < x := lt_trans (by norm_num : (0 : ℝ) < 1) hx1
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hlogxm : Real.log (ε * Real.log x) = Real.log ε + Real.log (Real.log x) := by
    exact Real.log_mul (ne_of_gt hε) (ne_of_gt hlogx)
  have hpow : Real.exp (-ε * Real.log x) = x ^ (-ε) := by
    rw [Real.rpow_def_of_pos hx0]
    rw [mul_comm]
  rw [g, hlogxm, hpow]
  have hred : (Real.log ε + Real.log (Real.log x) - Real.log ε) = Real.log (Real.log x) := by ring
  have hx0' : x ≠ 0 := ne_of_gt hx0
  calc
    (ε / x) * ((Real.log ε + Real.log (Real.log x) - Real.log ε) * x ^ (-ε))
        = (ε * Real.log (Real.log x)) * (x ^ (-ε) / x) := by rw [hred]; ring
    _ = ε * Real.log (Real.log x) * x ^ (-ε - 1) := by
        congr 1
        rw [← Real.rpow_sub_one hx0' (-ε)]
    _ = ε * g x * x ^ (-ε - 1) := by rw [g]

/-- `Cmain(ε) = ∫_{u>ε·log 3} (log u − log ε)·e^{-u}`, for `0 < ε` -/
private lemma Cmain_eq_uspace {ε : ℝ} (hε : 0 < ε) :
    Cmain ε = (∫ u : ℝ in Set.Ioi (ε * Real.log 3),
      (Real.log u - Real.log ε) * Real.exp (-u)) := by
  have hderiv : ∀ x ∈ Set.Ioi (3 : ℝ), HasDerivWithinAt (fun x : ℝ => ε * Real.log x)
      (ε / x) (Set.Ioi (3 : ℝ)) x := by
    intro x hx
    have hx0 : x ≠ 0 := by
      have : (3 : ℝ) < x := hx
      linarith
    have hd : HasDerivAt (fun x : ℝ => ε * Real.log x) (ε / x) x := by
      have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0
      exact (hlog.const_mul ε).congr_deriv (by rw [div_eq_mul_inv])
    exact hd.hasDerivWithinAt
  have hinj : Set.InjOn (fun x : ℝ => ε * Real.log x) (Set.Ioi (3 : ℝ)) := by
    intro x hx y hy hxy
    have hx3 : (3 : ℝ) < x := hx
    have hy3 : (3 : ℝ) < y := hy
    have hx0 : 0 < x := by linarith
    have hy0 : 0 < y := by linarith
    have hlogeq : Real.log x = Real.log y := by
      -- ε·log x = ε·log y
      have hc : ε * Real.log x = ε * Real.log y := hxy
      exact (mul_left_cancel₀ (ne_of_gt hε) hc)
    exact Real.log_injOn_pos hx0 hy0 hlogeq
  have hJ := MeasureTheory.integral_image_eq_integral_abs_deriv_smul (s := Set.Ioi (3 : ℝ))
    measurableSet_Ioi hderiv hinj (g := fun u : ℝ =>
      (Real.log u - Real.log ε) * Real.exp (-u))
  have himage : (fun x : ℝ => ε * Real.log x) '' Set.Ioi 3 = Set.Ioi (ε * Real.log 3) :=
    log_mul_image_Ioi hε
  rw [himage] at hJ
  have hR : (∫ x : ℝ in Set.Ioi 3,
        (ε / x) * ((Real.log (ε * Real.log x) - Real.log ε) * Real.exp (-ε * Real.log x)))
      = (∫ x : ℝ in Set.Ioi 3,
          |ε / x| • ((Real.log (ε * Real.log x) - Real.log ε) * Real.exp (-(ε * Real.log x)))) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx3 : (3 : ℝ) < x := hx
    have hx0 : 0 < x := by linarith
    have habs : |ε / x| = ε / x := abs_of_pos (div_pos hε hx0)
    simp only [smul_eq_mul]
    rw [habs]
    congr 1
    congr 1
    rw [neg_mul]
  calc
    Cmain ε = (∫ x : ℝ in Set.Ioi 3, ε * g x * x ^ (-ε - 1)) := by rfl
    _ = (∫ x : ℝ in Set.Ioi 3,
            (ε / x) * ((Real.log (ε * Real.log x) - Real.log ε) * Real.exp (-ε * Real.log x))) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x hx
          exact (jac_ident hε hx).symm
    _ = (∫ x : ℝ in Set.Ioi 3,
          |ε / x| • ((Real.log (ε * Real.log x) - Real.log ε) * Real.exp (-(ε * Real.log x)))) := hR
    _ = (∫ u : ℝ in Set.Ioi (ε * Real.log 3),
          (Real.log u - Real.log ε) * Real.exp (-u)) := hJ.symm

/-! ## the smooth integral tends to `-γ` -/

/-- `∫_{u > c} e^{-u} = e^{-c}` (instantiated lemma) -/
private lemma integral_exp_neg_Ioi_eq (c : ℝ) :
    (∫ u : ℝ in Set.Ioi c, Real.exp (-u)) = Real.exp (-c) :=
  integral_exp_neg_Ioi c

/-- integrability of the `u`-integrand `(log u − log ε)·e^{-u}` on `(c,∞)` -/
private lemma integrableOn_uspace (ε : ℝ) (c : ℝ) (hε : 0 < ε) (hc : 0 < c) :
    MeasureTheory.IntegrableOn (fun u : ℝ => (Real.log u - Real.log ε) * Real.exp (-u))
      (Set.Ioi c) MeasureTheory.volume := by
  have h1 := Commons.Analysis.ExpLog.integrableOn_log_exp_neg_Ioi c hc
  have h2 := integrableOn_exp_neg_Ioi c
  have hA : MeasureTheory.IntegrableOn (fun u : ℝ => Real.log u * Real.exp (-u)) (Set.Ioi c)
      MeasureTheory.volume := h1
  have hB : MeasureTheory.IntegrableOn (fun u : ℝ => Real.exp (-u)) (Set.Ioi c)
      MeasureTheory.volume := h2
  -- integrand = log u e^{-u} − log ε · e^{-u}
  have hsplit : MeasureTheory.IntegrableOn
      (fun u : ℝ => Real.log u * Real.exp (-u) + (-Real.log ε) * Real.exp (-u))
      (Set.Ioi c) MeasureTheory.volume := by
    have hB' : MeasureTheory.IntegrableOn (fun u : ℝ => (-Real.log ε) * Real.exp (-u)) (Set.Ioi c)
        MeasureTheory.volume := hB.const_mul (-Real.log ε)
    exact hA.add hB'
  refine MeasureTheory.IntegrableOn.congr_fun_ae hsplit ?_
  filter_upwards with u
  ring

/-- algebraic identity: `(log u − log ε)·e^{-u} = log u·e^{-u} − log ε·e^{-u}` -/
private lemma uspace_lin (ε u : ℝ) :
    (Real.log u - Real.log ε) * Real.exp (-u)
      = Real.log u * Real.exp (-u) + (-Real.log ε) * Real.exp (-u) := by ring

/-- `Cmain(ε) + log ε → -γ` as `ε → 0⁺` -/
private lemma tendsto_Cmain_add_log :
    Filter.Tendsto (fun ε : ℝ => Cmain ε + Real.log ε)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds (-Real.eulerMascheroniConstant)) := by
  -- A(ε) := ∫_{u>ε log 3} log u e^{-u}; A(ε) → -γ by the commons lemma and the
  -- change of the lower bound `c = ε · log 3 → 0⁺`.
  have hid : Filter.Tendsto (fun ε : ℝ => ε) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    continuousAt_id.tendsto.mono_left (nhdsWithin_le_nhds (a := 0) (s := Set.Ioi 0))
  have h1 : Filter.Tendsto (fun ε : ℝ => ε * Real.log 3) (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds 0) := by
    have hc : Filter.Tendsto (fun _ : ℝ => Real.log 3) (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
        (nhds (Real.log 3)) := tendsto_const_nhds
    simpa [mul_comm] using hc.mul hid
  have hcomp : Filter.Tendsto (fun ε : ℝ => ε * Real.log 3) (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact h1
    · rw [eventually_nhdsWithin_iff]
      filter_upwards with ε hε
      exact mul_pos hε (Real.log_pos (by norm_num : (1 : ℝ) < 3))
  have hA : Filter.Tendsto (fun ε : ℝ => (∫ u : ℝ in Set.Ioi (ε * Real.log 3),
        Real.log u * Real.exp (-u))) (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds (-Real.eulerMascheroniConstant)) :=
    Commons.Analysis.ExpLog.tendsto_integral_log_exp_neg_Ioi.comp hcomp
  have hmain : Filter.Tendsto (fun ε : ℝ => Cmain ε + Real.log ε)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds (-Real.eulerMascheroniConstant)) := by
    -- Cmain ε + log ε = A ε + log ε (1 − 3^{-ε})
    have hsplit : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        (∫ u : ℝ in Set.Ioi (ε * Real.log 3), Real.log u * Real.exp (-u))
            + Real.log ε * (1 - (3 : ℝ) ^ (-ε)) = Cmain ε + Real.log ε := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards with ε hε
      have hε0 : 0 < ε := hε
      have hc : 0 < ε * Real.log 3 := mul_pos hε0 (Real.log_pos (by norm_num : (1 : ℝ) < 3))
      have hC := Cmain_eq_uspace hε0
      have h1u := Commons.Analysis.ExpLog.integrableOn_log_exp_neg_Ioi (ε * Real.log 3) hc
      have h2u := integrableOn_exp_neg_Ioi (ε * Real.log 3)
      have hsumInt : (∫ u : ℝ in Set.Ioi (ε * Real.log 3),
            Real.log u * Real.exp (-u) + (-Real.log ε) * Real.exp (-u))
          = (∫ u : ℝ in Set.Ioi (ε * Real.log 3), Real.log u * Real.exp (-u))
            + (∫ u : ℝ in Set.Ioi (ε * Real.log 3), (-Real.log ε) * Real.exp (-u)) := by
        rw [integral_add]
        · exact h1u
        · exact h2u.const_mul (-Real.log ε)
      have hcmul : (∫ u : ℝ in Set.Ioi (ε * Real.log 3), (-Real.log ε) * Real.exp (-u))
          = (-Real.log ε) * (∫ u : ℝ in Set.Ioi (ε * Real.log 3), Real.exp (-u)) := by
        rw [MeasureTheory.integral_const_mul]
      have hE : (∫ u : ℝ in Set.Ioi (ε * Real.log 3), Real.exp (-u)) = (3 : ℝ) ^ (-ε) := by
        rw [integral_exp_neg_Ioi_eq]
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
        congr 1
        ring
      have hC' : Cmain ε = (∫ u : ℝ in Set.Ioi (ε * Real.log 3), Real.log u * Real.exp (-u))
          - Real.log ε * (3 : ℝ) ^ (-ε) := by
        calc
          Cmain ε = (∫ u : ℝ in Set.Ioi (ε * Real.log 3), (Real.log u - Real.log ε) * Real.exp (-u)) := hC
          _ = (∫ u : ℝ in Set.Ioi (ε * Real.log 3),
                Real.log u * Real.exp (-u) + (-Real.log ε) * Real.exp (-u)) := by
                apply setIntegral_congr_fun measurableSet_Ioi
                intro u hu
                exact uspace_lin ε u
          _ = (∫ u : ℝ in Set.Ioi (ε * Real.log 3), Real.log u * Real.exp (-u))
              + (∫ u : ℝ in Set.Ioi (ε * Real.log 3), (-Real.log ε) * Real.exp (-u)) := hsumInt
          _ = (∫ u : ℝ in Set.Ioi (ε * Real.log 3), Real.log u * Real.exp (-u))
              - Real.log ε * (3 : ℝ) ^ (-ε) := by
                rw [hcmul, hE]
                ring
      calc
        (∫ u : ℝ in Set.Ioi (ε * Real.log 3), Real.log u * Real.exp (-u))
            + Real.log ε * (1 - (3 : ℝ) ^ (-ε))
            = (∫ u : ℝ in Set.Ioi (ε * Real.log 3), Real.log u * Real.exp (-u))
              - Real.log ε * (3 : ℝ) ^ (-ε) + Real.log ε := by ring
        _ = Cmain ε + Real.log ε := by rw [← hC']
    have h2 := Commons.Analysis.ExpLog.tendsto_log_mul_sub_one_rpow
    have hsum : Filter.Tendsto (fun ε : ℝ =>
        (∫ u : ℝ in Set.Ioi (ε * Real.log 3), Real.log u * Real.exp (-u))
            + Real.log ε * (1 - (3 : ℝ) ^ (-ε)))
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
        (nhds (-Real.eulerMascheroniConstant)) := by
      simpa using (hA.add h2)
    exact hsum.congr' hsplit
  exact hmain

/-! ## half-line integral vs partial sums -/

/-- the `x`-integrand is integrable on `(3,∞)` for `0 < ε` -/
private lemma integrableOn_Cmain_f {ε : ℝ} (hε : 0 < ε) :
    MeasureTheory.IntegrableOn (fun x : ℝ => ε * g x * x ^ (-ε - 1)) (Set.Ioi 3)
      MeasureTheory.volume := by
  let h : ℝ → ℝ := fun u : ℝ => (Real.log u - Real.log ε) * Real.exp (-u)
  have hc : 0 < ε * Real.log 3 := mul_pos hε (Real.log_pos (by norm_num : (1 : ℝ) < 3))
  have hU : MeasureTheory.IntegrableOn h (Set.Ioi (ε * Real.log 3)) MeasureTheory.volume :=
    integrableOn_uspace ε (ε * Real.log 3) hε hc
  have hderiv : ∀ x ∈ Set.Ioi (3 : ℝ), HasDerivWithinAt (fun x : ℝ => ε * Real.log x)
      (ε / x) (Set.Ioi (3 : ℝ)) x := by
    intro x hx
    have hx0 : x ≠ 0 := by
      have : (3 : ℝ) < x := hx
      linarith
    have hd : HasDerivAt (fun x : ℝ => ε * Real.log x) (ε / x) x := by
      have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0
      exact (hlog.const_mul ε).congr_deriv (by rw [div_eq_mul_inv])
    exact hd.hasDerivWithinAt
  have hinj : Set.InjOn (fun x : ℝ => ε * Real.log x) (Set.Ioi (3 : ℝ)) := by
    intro x hx y hy hxy
    have hx0 : 0 < x := by
      have : (3 : ℝ) < x := hx
      linarith
    have hy0 : 0 < y := by
      have : (3 : ℝ) < y := hy
      linarith
    have hlogeq : Real.log x = Real.log y := mul_left_cancel₀ (ne_of_gt hε) hxy
    exact Real.log_injOn_pos hx0 hy0 hlogeq
  have himage : (fun x : ℝ => ε * Real.log x) '' Set.Ioi 3 = Set.Ioi (ε * Real.log 3) :=
    log_mul_image_Ioi hε
  have hiff := MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul (s := Set.Ioi (3 : ℝ))
    measurableSet_Ioi hderiv hinj h
  have hRHS : MeasureTheory.IntegrableOn (fun x : ℝ => |ε / x| • h (ε * Real.log x)) (Set.Ioi 3)
      MeasureTheory.volume := by
    rw [himage] at hiff
    exact hiff.mp hU
  -- |ε/x| • h(ε log x) = ε g x x^{-ε-1} pointwise on (3,∞)
  have hEq_on : ∀ x ∈ Set.Ioi (3 : ℝ),
      |ε / x| • h (ε * Real.log x) = ε * g x * x ^ (-ε - 1) := by
    intro x hx
    have hx3 : 3 < x := hx
    have hx0 : 0 < x := by linarith
    have habs : |ε / x| = ε / x := abs_of_pos (div_pos hε hx0)
    have hjac : (ε / x) * ((Real.log (ε * Real.log x) - Real.log ε) * Real.exp (-ε * Real.log x))
        = ε * g x * x ^ (-ε - 1) := jac_ident hε hx3
    have hexp : Real.exp (-(ε * Real.log x)) = Real.exp (-ε * Real.log x) := by
      congr 1
      ring
    calc
      |ε / x| • h (ε * Real.log x)
          = (ε / x) * ((Real.log (ε * Real.log x) - Real.log ε) * Real.exp (-ε * Real.log x)) := by
            simp [h, habs, smul_eq_mul, hexp]
      _ = ε * g x * x ^ (-ε - 1) := hjac
  have hEq : (fun x : ℝ => |ε / x| • h (ε * Real.log x)) =ᵐ[MeasureTheory.volume.restrict (Set.Ioi 3)]
      (fun x : ℝ => ε * g x * x ^ (-ε - 1)) := by
    change (∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.Ioi (3 : ℝ))),
        |ε / x| • h (ε * Real.log x) = ε * g x * x ^ (-ε - 1))
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with x hx
    exact hEq_on x hx
  exact MeasureTheory.IntegrableOn.congr_fun_ae hRHS hEq

/-! ## partial sums tend to the half-line integral -/

/-- cell-integral identity: `Yseq ε N = ∫_3^{N+1} ε·g·x^{-ε-1}` for `N ≥ 3` -/
private lemma Yseq_eq_interval_int (ε : ℝ) (N : ℕ) (hN : 3 ≤ N) :
    Yseq ε N = (∫ x : ℝ in (3 : ℝ)..(((N + 1 : ℕ) : ℝ)), ε * g x * x ^ (-ε - 1)) := by
  have hcell : ∀ k < N - 2, IntervalIntegrable (fun x : ℝ => ε * g x * x ^ (-ε - 1)) volume
      (((3 + k : ℕ) : ℝ)) (((3 + (k + 1) : ℕ) : ℝ)) := by
    intro k hk
    have hk3 : 3 ≤ 3 + k := by omega
    have hcg := cell_g_int ε (3 + k) hk3
    convert hcg using 1 <;> norm_num [Nat.add_assoc]
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (f := fun x : ℝ => ε * g x * x ^ (-ε - 1)) (a := fun k : ℕ => (((3 + k : ℕ) : ℝ)))
    (n := N - 2) (by intro k hk; simpa using hcell k hk)
  have hNminus : (3 + (N - 2) : ℕ) = N + 1 := by omega
  have hterm : ∀ k : ℕ, Ycell ε (k + 3) = (∫ x : ℝ in ((3 + k : ℕ) : ℝ)..(((3 + (k + 1) : ℕ) : ℝ)),
        ε * g x * x ^ (-ε - 1)) := by
    intro k
    have hl : (((3 + k : ℕ) : ℝ)) = (((k + 3 : ℕ) : ℝ)) := by congr 1 <;> omega
    have hu : (((3 + (k + 1) : ℕ) : ℝ)) = (((k + 4 : ℕ) : ℝ)) := by congr 1 <;> omega
    have hu' : (((k + 3 + 1 : ℕ) : ℝ)) = (((k + 4 : ℕ) : ℝ)) := by congr 1 <;> omega
    unfold Ycell
    rw [hl, hu, hu']
  have himage : Finset.Icc 3 N = (Finset.range (N - 2)).image (fun k : ℕ => k + 3) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hj
      rcases hj with ⟨h3, hjN⟩
      refine ⟨j - 3, ?_, ?_⟩ <;> omega
    · rintro ⟨k, hk, rfl⟩
      omega
  have hleft : (∑ j ∈ Finset.Icc 3 N, Ycell ε j)
      = ∑ k ∈ Finset.range (N - 2), (∫ x : ℝ in ((3 + k : ℕ) : ℝ)..(((3 + (k + 1) : ℕ) : ℝ)),
          ε * g x * x ^ (-ε - 1)) := by
    calc
      (∑ j ∈ Finset.Icc 3 N, Ycell ε j)
          = ∑ j ∈ (Finset.range (N - 2)).image (fun k : ℕ => k + 3), Ycell ε j := by rw [himage]
      _ = ∑ k ∈ Finset.range (N - 2), Ycell ε (k + 3) := by
            have hinj : Set.InjOn (fun k : ℕ => k + 3) ↑(Finset.range (N - 2)) := by
              intro x hx y hy h
              change x + 3 = y + 3 at h
              omega
            exact (Finset.sum_image (s := Finset.range (N - 2)) (g := fun k : ℕ => k + 3)
              (f := fun j : ℕ => Ycell ε j) hinj)
      _ = ∑ k ∈ Finset.range (N - 2), (∫ x : ℝ in ((3 + k : ℕ) : ℝ)..(((3 + (k + 1) : ℕ) : ℝ)),
          ε * g x * x ^ (-ε - 1)) := by
            apply Finset.sum_congr rfl
            intro k hk
            exact hterm k
  calc
    Yseq ε N = ∑ j ∈ Finset.Icc 3 N, Ycell ε j := by rfl
    _ = ∑ k ∈ Finset.range (N - 2), (∫ x : ℝ in ((3 + k : ℕ) : ℝ)..(((3 + (k + 1) : ℕ) : ℝ)),
        ε * g x * x ^ (-ε - 1)) := hleft
    _ = ∫ x : ℝ in ((3 : ℕ) : ℝ)..(((3 + (N - 2) : ℕ) : ℝ)), ε * g x * x ^ (-ε - 1) := by
          rw [← hsum]
    _ = ∫ x : ℝ in (3 : ℝ)..(((N + 1 : ℕ) : ℝ)), ε * g x * x ^ (-ε - 1) := by
          rw [hNminus]
          rfl

/-- `Yseq ε N` tends to `Cmain ε` as `N → ∞` -/
private lemma tendsto_Yseq (ε : ℝ) (hε : 0 < ε) :
    Filter.Tendsto (fun N : ℕ => Yseq ε N) Filter.atTop (nhds (Cmain ε)) := by
  have hb : Filter.Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ))) Filter.atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hI := intervalIntegral_tendsto_integral_Ioi (a := (3 : ℝ))
    (hfi := integrableOn_Cmain_f hε) (b := fun N : ℕ => (((N + 1 : ℕ) : ℝ))) hb
  have hC : Cmain ε = ∫ x : ℝ in Set.Ioi 3, ε * g x * x ^ (-ε - 1) := by rfl
  rw [← hC] at hI
  refine hI.congr' ?_
  filter_upwards [eventually_ge_atTop 3] with N hN
  exact (Yseq_eq_interval_int ε N hN).symm

/-! ## the discrete sum is `ε/2`-close to the smooth integral -/

/-- `Xseq` is bounded above -/
private lemma Xseq_bdd_above {ε : ℝ} (hε : 0 < ε) : ∃ M : ℝ, ∀ N : ℕ, Xseq ε N ≤ M := by
  have hY := tendsto_Yseq ε hε
  have hb : ∃ M₀ : ℝ, ∀ᶠ N in Filter.atTop, Yseq ε N ≤ M₀ := by
    exact hY.isBoundedUnder_le
  rcases hb with ⟨M₀, hM₀⟩
  rcases (Filter.eventually_atTop.1 hM₀) with ⟨N₀, hN₀⟩
  let B : ℕ := max 3 N₀
  have hB3 : 3 ≤ B := le_max_left _ _
  have hBN₀ : N₀ ≤ B := le_max_right _ _
  have hmono := Xseq_mono (le_of_lt hε)
  have hXB : Xseq ε B ≤ M₀ + ε / 2 := by
    have hbY : Yseq ε B ≤ M₀ := hN₀ B hBN₀
    have habs := abs_Xseq_sub_Yseq_le ε (le_of_lt hε) B hB3
    have hle : Xseq ε B - Yseq ε B ≤ ε / 2 := by
      have : Xseq ε B - Yseq ε B ≤ ‖Xseq ε B - Yseq ε B‖ := le_abs_self _
      exact le_trans this habs
    linarith
  refine ⟨M₀ + ε / 2, ?_⟩
  intro N
  by_cases hNB : N ≤ B
  · exact le_trans (hmono hNB) hXB
  · have hBN : B ≤ N := le_of_not_ge hNB
    have hbY : Yseq ε N ≤ M₀ := hN₀ N (le_trans hBN₀ hBN)
    have habs := abs_Xseq_sub_Yseq_le ε (le_of_lt hε) N (by omega : 3 ≤ N)
    have hle : Xseq ε N - Yseq ε N ≤ ε / 2 := by
      have : Xseq ε N - Yseq ε N ≤ ‖Xseq ε N - Yseq ε N‖ := le_abs_self _
      exact le_trans this habs
    linarith

/-- `Xseq ε N` converges; its limit has `HasSum` for the guarded tail -/
private lemma Xseq_tendsto_exists {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℝ, Filter.Tendsto (fun N : ℕ => Xseq ε N) Filter.atTop (nhds L) := by
  rcases Xseq_bdd_above hε with ⟨M, hM⟩
  have hmono : Monotone (fun N : ℕ => Xseq ε N) := Xseq_mono (le_of_lt hε)
  have hup : M ∈ upperBounds (Set.range fun N : ℕ => Xseq ε N) := by
    intro x hx
    rcases hx with ⟨N, rfl⟩
    exact hM N
  have hconv := tendsto_atTop_ciSup hmono ⟨M, hup⟩
  exact ⟨⨆ N : ℕ, Xseq ε N, by simpa using hconv⟩

/-- the guarded tail sum equals the limit of `Xseq` -/
private lemma tailSum_eq_limit {ε : ℝ} (hε : 0 < ε) :
    (∑' k : ℕ, if 3 ≤ k then termk k ε else 0) = (limUnder atTop (fun N : ℕ => Xseq ε N)) := by
  rcases Xseq_tendsto_exists hε with ⟨L, hL⟩
  have hlim : Filter.Tendsto (fun N : ℕ => Xseq ε N) Filter.atTop
      (nhds (limUnder atTop (fun N : ℕ => Xseq ε N))) := tendsto_nhds_limUnder ⟨L, hL⟩
  have hLlim : L = limUnder atTop (fun N : ℕ => Xseq ε N) := tendsto_nhds_unique hL hlim
  have hnonneg : ∀ i : ℕ, 0 ≤ (if 3 ≤ i then termk i ε else 0) := by
    intro i
    by_cases hi : 3 ≤ i
    · simp [hi, termk_nonneg (le_of_lt hε) hi]
    · simp [hi]
  have hpart : ∀ n : ℕ, 1 ≤ n →
      (∑ i ∈ Finset.range n, (if 3 ≤ i then termk i ε else 0)) = Xseq ε (n - 1) := by
    intro n hn
    have hset : (Finset.range n).filter (fun i : ℕ => 3 ≤ i) = Finset.Icc 3 (n - 1) := by
      ext i
      constructor
      · intro hi
        have hi1 : i ∈ Finset.range n := (Finset.mem_filter.mp hi).1
        have hi2 : 3 ≤ i := (Finset.mem_filter.mp hi).2
        have hlt : i < n := Finset.mem_range.mp hi1
        exact Finset.mem_Icc.mpr ⟨hi2, Nat.le_pred_of_lt hlt⟩
      · intro hi
        have h31 : 3 ≤ i := (Finset.mem_Icc.mp hi).1
        have hi2 : i ≤ n - 1 := (Finset.mem_Icc.mp hi).2
        have hlt : n - 1 < n := Nat.sub_lt (by omega : 0 < n) (by norm_num : 0 < 1)
        have hlt2 : i < n := lt_of_le_of_lt hi2 hlt
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt2, h31⟩
    calc
      (∑ i ∈ Finset.range n, (if 3 ≤ i then termk i ε else 0))
          = ∑ i ∈ (Finset.range n).filter (fun i : ℕ => 3 ≤ i), termk i ε := by
            rw [Finset.sum_filter]
      _ = ∑ k ∈ Finset.Icc 3 (n - 1), termk k ε := by rw [hset]
      _ = Xseq ε (n - 1) := by rfl
  have hfun : Filter.Tendsto (fun n : ℕ =>
        ∑ i ∈ Finset.range n, (if 3 ≤ i then termk i ε else 0)) Filter.atTop (nhds L) := by
    refine Metric.tendsto_atTop.mpr ?_
    intro ε hε
    rcases (Metric.tendsto_atTop.mp hL) ε hε with ⟨M, hM⟩
    refine ⟨M + 1, ?_⟩
    intro n hn
    have hn1 : 1 ≤ n := by omega
    have hpart' := hpart n hn1
    have hMn : M ≤ n - 1 := by omega
    have hd := hM (n - 1) hMn
    rw [← hpart'] at hd
    exact hd
  have hHas : HasSum (fun k : ℕ => if 3 ≤ k then termk k ε else 0) L := by
    rw [hasSum_iff_tendsto_nat_of_nonneg hnonneg L]
    exact hfun
  have htsum : (∑' k : ℕ, if 3 ≤ k then termk k ε else 0) = L := hHas.tsum_eq
  rw [hLlim] at htsum
  exact htsum

/-! ## the discrete sum is `ε/2`-close to `Cmain`; assembly -/

/-- `|tailSum − Cmain| ≤ ε/2` -/
private lemma tailSum_sub_Cmain_le {ε : ℝ} (hε : 0 < ε) :
    ‖(∑' k : ℕ, if 3 ≤ k then termk k ε else 0) - Cmain ε‖ ≤ ε / 2 := by
  have hts := tailSum_eq_limit hε
  let L : ℝ := ∑' k : ℕ, if 3 ≤ k then termk k ε else 0
  have hlim0 : Filter.Tendsto (fun N : ℕ => Xseq ε N) Filter.atTop
      (nhds (limUnder atTop (fun N : ℕ => Xseq ε N))) := by
    rcases Xseq_tendsto_exists hε with ⟨L0, hL0⟩
    exact tendsto_nhds_limUnder ⟨L0, hL0⟩
  have hL : Filter.Tendsto (fun N : ℕ => Xseq ε N) Filter.atTop (nhds L) := by
    simpa [L, ← hts] using hlim0
  have hY : Filter.Tendsto (fun N : ℕ => Yseq ε N) Filter.atTop (nhds (Cmain ε)) :=
    tendsto_Yseq ε hε
  have hinc : ∀ N : ℕ, 3 ≤ N →
      ‖Xseq ε N - Cmain ε‖ ≤ ε / 2 + ‖Yseq ε N - Cmain ε‖ := by
    intro N hN
    have h1 := abs_Xseq_sub_Yseq_le ε (le_of_lt hε) N hN
    calc
      ‖Xseq ε N - Cmain ε‖ = ‖(Xseq ε N - Yseq ε N) + (Yseq ε N - Cmain ε)‖ := by
        congr 1
        ring
      _ ≤ ‖Xseq ε N - Yseq ε N‖ + ‖Yseq ε N - Cmain ε‖ := norm_add_le _ _
      _ ≤ ε / 2 + ‖Yseq ε N - Cmain ε‖ := by
        have h2 : ‖Yseq ε N - Cmain ε‖ + ‖Xseq ε N - Yseq ε N‖ ≤ ‖Yseq ε N - Cmain ε‖ + ε / 2 :=
          add_le_add_right h1 _
        nlinarith
  have hXc : Filter.Tendsto (fun N : ℕ => ‖Xseq ε N - Cmain ε‖) Filter.atTop
      (nhds ‖L - Cmain ε‖) := by
    have hsub0 : Filter.Tendsto (fun N : ℕ => Xseq ε N - Cmain ε) Filter.atTop
        (nhds (L - Cmain ε)) :=
      hL.sub (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => Cmain ε) Filter.atTop
        (nhds (Cmain ε)))
    exact hsub0.norm
  have hYc : Filter.Tendsto (fun N : ℕ => ε / 2 + ‖Yseq ε N - Cmain ε‖) Filter.atTop
      (nhds (ε / 2)) := by
    have hsub0 : Filter.Tendsto (fun N : ℕ => Yseq ε N - Cmain ε) Filter.atTop (nhds 0) := by
      simpa using (hY.sub (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => Cmain ε)
        Filter.atTop (nhds (Cmain ε))))
    have hnorm : Filter.Tendsto (fun N : ℕ => ‖Yseq ε N - Cmain ε‖) Filter.atTop (nhds 0) := by
      simpa using hsub0.norm
    have hadd := (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => ε / 2) Filter.atTop
      (nhds (ε / 2))).add hnorm
    simpa using hadd
  have hevt : (fun N : ℕ => ‖Xseq ε N - Cmain ε‖) ≤ᶠ[Filter.atTop]
      (fun N : ℕ => ε / 2 + ‖Yseq ε N - Cmain ε‖) := by
    filter_upwards [eventually_ge_atTop 3] with N hN
    exact hinc N hN
  have hbnd := le_of_tendsto_of_tendsto hXc hYc hevt
  simpa [L] using hbnd

/-- `ser ε = termk 2 ε + tail` for `0 < ε` -/
private lemma ser_eq_t2_add_tail {ε : ℝ} (hε : 0 < ε) :
    ser ε = termk 2 ε + (∑' k : ℕ, if 3 ≤ k then termk k ε else 0) := by
  let L : ℝ := limUnder atTop (fun N : ℕ => Xseq ε N)
  have hnonneg : ∀ i : ℕ, 0 ≤ (if 3 ≤ i then termk i ε else 0) := by
    intro i
    by_cases hi : 3 ≤ i
    · simp [hi, termk_nonneg (le_of_lt hε) hi]
    · simp [hi]
  have hpart : ∀ n : ℕ, 1 ≤ n →
      (∑ i ∈ Finset.range n, (if 3 ≤ i then termk i ε else 0)) = Xseq ε (n - 1) := by
    intro n hn
    have hset : (Finset.range n).filter (fun i : ℕ => 3 ≤ i) = Finset.Icc 3 (n - 1) := by
      ext i
      constructor
      · intro hi
        have hi1 : i ∈ Finset.range n := (Finset.mem_filter.mp hi).1
        have hi2 : 3 ≤ i := (Finset.mem_filter.mp hi).2
        have hlt : i < n := Finset.mem_range.mp hi1
        exact Finset.mem_Icc.mpr ⟨hi2, Nat.le_pred_of_lt hlt⟩
      · intro hi
        have h31 : 3 ≤ i := (Finset.mem_Icc.mp hi).1
        have hi2 : i ≤ n - 1 := (Finset.mem_Icc.mp hi).2
        have hlt : n - 1 < n := Nat.sub_lt (by omega : 0 < n) (by norm_num : 0 < 1)
        have hlt2 : i < n := lt_of_le_of_lt hi2 hlt
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt2, h31⟩
    calc
      (∑ i ∈ Finset.range n, (if 3 ≤ i then termk i ε else 0))
          = ∑ i ∈ (Finset.range n).filter (fun i : ℕ => 3 ≤ i), termk i ε := by
            rw [Finset.sum_filter]
      _ = ∑ k ∈ Finset.Icc 3 (n - 1), termk k ε := by rw [hset]
      _ = Xseq ε (n - 1) := by rfl
  have hfun : Filter.Tendsto (fun n : ℕ =>
        ∑ i ∈ Finset.range n, (if 3 ≤ i then termk i ε else 0)) Filter.atTop (nhds L) := by
    rcases Xseq_tendsto_exists hε with ⟨L0, hL0⟩
    have hlim0 : Filter.Tendsto (fun N : ℕ => Xseq ε N) Filter.atTop (nhds L) := by
      simpa [L, tendsto_nhds_unique hL0 (tendsto_nhds_limUnder ⟨L0, hL0⟩)] using hL0
    refine Metric.tendsto_atTop.mpr ?_
    intro δ hδ
    rcases (Metric.tendsto_atTop.mp hlim0) δ hδ with ⟨M, hM⟩
    refine ⟨M + 1, ?_⟩
    intro n hn
    have hn1 : 1 ≤ n := by omega
    have hpart' := hpart n hn1
    have hMn : M ≤ n - 1 := by omega
    have hd := hM (n - 1) hMn
    rw [← hpart'] at hd
    exact hd
  have hHas3 : HasSum (fun k : ℕ => if 3 ≤ k then termk k ε else 0) L := by
    rw [hasSum_iff_tendsto_nat_of_nonneg hnonneg L]
    exact hfun
  -- delta at 2
  have hsumpt : ∀ k : ℕ, (if 3 ≤ k then termk k ε else 0) + (if k = 2 then termk 2 ε else 0)
      = (if 2 ≤ k then termk k ε else 0) := by
    intro k
    by_cases h3 : 3 ≤ k
    · have h2 : 2 ≤ k := by omega
      have hnk : k ≠ 2 := by omega
      simp [h3, h2, hnk]
    · by_cases h2 : 2 ≤ k
      · have hk2 : k = 2 := by omega
        subst k
        simp
      · have hnk : k ≠ 2 := by omega
        simp [h3, h2, hnk]
  have hHasδ : HasSum (fun k : ℕ => if k = 2 then termk 2 ε else 0) (termk 2 ε) := by
    apply hasSum_single (b := 2)
    intro b' hb'
    simp [hb']
  have hHas : HasSum (fun k : ℕ => if 2 ≤ k then termk k ε else 0) (termk 2 ε + L) := by
    have h := HasSum.add hHas3 hHasδ
    convert h using 1
    · ext k
      exact (hsumpt k).symm
    · ring
  unfold ser
  rw [hHas.tsum_eq]
  congr 1
  simpa [L] using (tailSum_eq_limit hε).symm

private def rightFilter : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi 0)

/-- `b^{-ε} → 1` as `ε → 0⁺` for `b > 0` -/
private lemma tendsto_rpow_neg_one_base (b : ℝ) (hb0 : 0 < b) :
    Filter.Tendsto (fun ε : ℝ => b ^ (-ε)) rightFilter (nhds 1) := by
  have hid : Filter.Tendsto (fun ε : ℝ => ε) rightFilter (nhds 0) :=
    continuousAt_id.tendsto.mono_left (nhdsWithin_le_nhds (a := 0) (s := Set.Ioi 0))
  have hmul : Filter.Tendsto (fun ε : ℝ => ε * (-Real.log b)) rightFilter (nhds 0) := by
    have hc : Filter.Tendsto (fun _ : ℝ => -Real.log b) rightFilter (nhds (-Real.log b)) :=
      tendsto_const_nhds
    simpa [mul_comm] using hc.mul hid
  have he : Filter.Tendsto (fun ε : ℝ => Real.exp (ε * (-Real.log b))) rightFilter (nhds 1) := by
    have hExp : Filter.Tendsto Real.exp (nhds (0 : ℝ)) (nhds (Real.exp 0)) :=
      Real.continuous_exp.tendsto 0
    have hc2 : Filter.Tendsto (fun ε : ℝ => Real.exp (ε * (-Real.log b))) rightFilter
        (nhds (Real.exp 0)) := (hExp.comp hmul).congr' (Eventually.of_forall (fun ε => by rfl))
    simpa using hc2
  refine he.congr' ?_
  change ∀ᶠ ε in rightFilter, Real.exp (ε * (-Real.log b)) = b ^ (-ε)
  unfold rightFilter
  rw [eventually_nhdsWithin_iff]
  filter_upwards with ε hε
  rw [Real.rpow_def_of_pos hb0]
  congr 1
  ring

/-- `termk 2 ε → 0` as `ε → 0⁺` -/
private lemma tendsto_term2 :
    Filter.Tendsto (fun ε : ℝ => termk 2 ε) rightFilter (nhds 0) := by
  have h2 := tendsto_rpow_neg_one_base (2 : ℝ) (by norm_num)
  have h3 := tendsto_rpow_neg_one_base (3 : ℝ) (by norm_num)
  have hdiff : Filter.Tendsto (fun ε : ℝ => (2 : ℝ) ^ (-ε) - (3 : ℝ) ^ (-ε))
      rightFilter (nhds 0) := by
    simpa using (h2.sub h3)
  have hmain : Filter.Tendsto (fun ε : ℝ => Real.log (Real.log (2 : ℝ)) *
      ((2 : ℝ) ^ (-ε) - (3 : ℝ) ^ (-ε))) rightFilter (nhds 0) := by
    have hc : Filter.Tendsto (fun _ : ℝ => Real.log (Real.log (2 : ℝ))) rightFilter
        (nhds (Real.log (Real.log (2 : ℝ)))) := tendsto_const_nhds
    simpa [mul_zero] using hc.mul hdiff
  refine hmain.congr' ?_
  change ∀ᶠ ε in rightFilter,
      Real.log (Real.log (2 : ℝ)) * ((2 : ℝ) ^ (-ε) - (3 : ℝ) ^ (-ε)) = termk 2 ε
  unfold rightFilter
  rw [eventually_nhdsWithin_iff]
  filter_upwards with ε hε
  unfold termk delta
  congr 1

/-- A function `d` with `‖d ε‖ ≤ ε/2` for all `ε > 0` tends to `0` along the right filter. -/
private lemma tendsto_zero_of_abs_le_half_pos {d : ℝ → ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ‖d ε‖ ≤ ε / 2) : Filter.Tendsto d rightFilter (nhds 0) := by
  let d' : ℝ → ℝ := fun ε => if 0 < ε then d ε else 0
  have hlow : ∀ ε : ℝ, -(|ε| / 2) ≤ d' ε := by
    intro ε
    by_cases hε : 0 < ε
    · have habs : ‖d ε‖ ≤ ε / 2 := h ε hε
      have hlb : -(ε / 2) ≤ d ε := (abs_le.mp habs).1
      have hE : |ε| / 2 = ε / 2 := by rw [abs_of_pos hε]
      rw [hE]
      simpa [d', hε] using hlb
    · have hle : ε ≤ 0 := le_of_not_gt hε
      have hE : |ε| = -ε := abs_of_nonpos hle
      have hm : -((-ε) / 2) ≤ 0 := by ring_nf; linarith
      rw [hE]
      simpa [d', hε] using hm
  have hup : ∀ ε : ℝ, d' ε ≤ |ε| / 2 := by
    intro ε
    by_cases hε : 0 < ε
    · have habs : ‖d ε‖ ≤ ε / 2 := h ε hε
      have hub : d ε ≤ ε / 2 := (abs_le.mp habs).2
      have hE : |ε| / 2 = ε / 2 := by rw [abs_of_pos hε]
      rw [hE]
      simpa [d', hε] using hub
    · have hz : 0 ≤ |ε| / 2 := div_nonneg (abs_nonneg ε) (by norm_num)
      simpa [d', hε] using hz
  have hid : Filter.Tendsto (fun ε : ℝ => ε) rightFilter (nhds 0) :=
    continuousAt_id.tendsto.mono_left (nhdsWithin_le_nhds (a := 0) (s := Set.Ioi 0))
  have habslim : Filter.Tendsto (fun ε : ℝ => |ε|) rightFilter (nhds 0) := by
    simpa using hid.abs
  have hhalf : Filter.Tendsto (fun ε : ℝ => |ε| / 2) rightFilter (nhds 0) := by
    have hc : Filter.Tendsto (fun _ : ℝ => (1 / 2 : ℝ)) rightFilter (nhds (1 / 2 : ℝ)) :=
      tendsto_const_nhds
    simpa [div_eq_mul_inv, mul_comm] using hc.mul habslim
  have hd' : Filter.Tendsto d' rightFilter (nhds 0) := by
    have hg : Filter.Tendsto (fun ε : ℝ => -(|ε| / 2)) rightFilter (nhds 0) := by
      simpa using hhalf.neg
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun ε : ℝ => -(|ε| / 2)) (f := d') (h := fun ε : ℝ => |ε| / 2)
      hg hhalf hlow hup
  have heq : ∀ᶠ ε in rightFilter, d' ε = d ε := by
    change ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), d' ε = d ε
    rw [eventually_nhdsWithin_iff]
    filter_upwards with ε hε
    have hpos : 0 < ε := hε
    simp [d', hpos]
  exact hd'.congr' heq

/-- main theorem: `Σ log log k (k^{-ε} - (k+1)^{-ε}) + log ε → -γ` as `ε → 0⁺` -/
theorem rpowDiff_loglog_add_log_tendsto :
    Filter.Tendsto (fun ε : ℝ =>
      (∑' k : ℕ, if 2 ≤ k then
        Real.log (Real.log (k : ℝ)) *
          (((k : ℝ) ^ (-ε)) - ((((k + 1) : ℕ) : ℝ) ^ (-ε))) else 0) + Real.log ε)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds (-Real.eulerMascheroniConstant)) := by
  change Filter.Tendsto (fun ε : ℝ => ser ε + Real.log ε) rightFilter
    (nhds (-Real.eulerMascheroniConstant))
  have ht2 : Filter.Tendsto (fun ε : ℝ => termk 2 ε) rightFilter (nhds 0) := tendsto_term2
  let d : ℝ → ℝ := fun ε => (∑' k : ℕ, if 3 ≤ k then termk k ε else 0) - Cmain ε
  have hbnd : ∀ ε : ℝ, 0 < ε → ‖d ε‖ ≤ ε / 2 := by
    intro ε hε
    exact tailSum_sub_Cmain_le hε
  have hdiff : Filter.Tendsto d rightFilter (nhds 0) := tendsto_zero_of_abs_le_half_pos hbnd
  have hmain := tendsto_Cmain_add_log
  have hdec : ∀ᶠ ε in rightFilter,
      (termk 2 ε + d ε) + (Cmain ε + Real.log ε) = ser ε + Real.log ε := by
    change ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      (termk 2 ε + d ε) + (Cmain ε + Real.log ε) = ser ε + Real.log ε
    rw [eventually_nhdsWithin_iff]
    filter_upwards with ε hε
    have hser := ser_eq_t2_add_tail hε
    calc
      (termk 2 ε + d ε) + (Cmain ε + Real.log ε)
          = termk 2 ε + (∑' k : ℕ, if 3 ≤ k then termk k ε else 0) + Real.log ε := by
            dsimp [d]
            ring
      _ = ser ε + Real.log ε := by rw [hser]
  have hsum : Filter.Tendsto (fun ε : ℝ => (termk 2 ε + d ε) + (Cmain ε + Real.log ε))
      rightFilter (nhds (-Real.eulerMascheroniConstant)) := by
    have h01 := ht2.add hdiff
    have hsumm := h01.add hmain
    simpa [add_assoc, add_comm, add_left_comm] using hsumm
  exact hsum.congr' hdec

end Commons.Analysis.InfiniteSum

end