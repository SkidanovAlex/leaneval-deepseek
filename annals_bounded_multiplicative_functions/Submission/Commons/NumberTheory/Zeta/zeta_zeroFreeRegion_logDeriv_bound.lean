import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_zeroFreeRegion_largeHeight
import Submission.Commons.NumberTheory.Zeta.zeta_zeroFree_near_axis
import Submission.Commons.NumberTheory.Zeta.zeta_lower_bound_right_of_one
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_strip_bound_rh
import Submission.Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound_analytic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Complex Filter Metric Set
open scoped Real Topology BigOperators
noncomputable section
set_option maxHeartbeats 0

namespace Commons.NumberTheory.Zeta

/-! # Zero-free region of log width and the log-derivative bound

We prove the classical log-shaped zero-free region
`σ ≥ 1 - c / log(|t|+3)  ⇒  ζ(σ + it) ≠ 0`   (|t| ≥ 1),
together with the bound `‖ζ'/ζ(σ+it)‖ ≤ C (log(|t|+3)+1)^4` inside it.
-/

/-- log size function -/
private def zLL (t : ℝ) : ℝ := Real.log (|t| + 3)

private lemma zLL_pos {t : ℝ} (ht : 1 ≤ |t|) : 0 < zLL t := by
  dsimp [zLL]
  exact Real.log_pos (by linarith [ht])

private lemma zLL_nonneg {t : ℝ} : 0 ≤ zLL t := by
  dsimp [zLL]
  exact Real.log_nonneg (by linarith [abs_nonneg t])

private lemma zLL_pos_of_half {t : ℝ} (ht : (1 / 2 : ℝ) ≤ |t|) : 0 < zLL t := by
  dsimp [zLL]
  exact Real.log_pos (by linarith [ht])

/-- `1 ≤ L+1` -/
private lemma zLL_add_one_ge_one {t : ℝ} : (1 : ℝ) ≤ zLL t + 1 := by
  have h := zLL_nonneg (t := t)
  linarith

/-- `1 ≤ (L+1)^2`, `1 ≤ (L+1)^3` etc. -/
private lemma zLL_add_one_ge_half {t : ℝ} : (1 / 2 : ℝ) ≤ zLL t + 1 := by
  have h := zLL_nonneg (t := t)
  linarith

/-- `(L+1)^2 ≤ (L+1)^4`. -/
private lemma zLL_sq_le_four {t : ℝ} : (zLL t + 1) ^ 2 ≤ (zLL t + 1) ^ 4 := by
  have h : (0 : ℝ) ≤ (zLL t + 1) ^ 2 := sq_nonneg _
  have h1 : (1 : ℝ) ≤ (zLL t + 1) ^ 2 := by
    have hb : 1 ≤ (zLL t + 1) := zLL_add_one_ge_one (t := t)
    exact le_trans hb (le_self_pow₀ hb (by norm_num : (2 : ℕ) ≠ 0))
  calc
    (zLL t + 1) ^ 2 = (zLL t + 1) ^ 2 * 1 := by ring
    _ ≤ (zLL t + 1) ^ 2 * (zLL t + 1) ^ 2 := mul_le_mul_of_nonneg_left h1 h
    _ = (zLL t + 1) ^ 4 := by ring

/-- **ζ has no zeros in a strip `1-ε ≤ Re ≤ 2` for `|Im| ≤ T`** (any `T ≥ 4`). -/
private lemma zfr_bounded_strip (T : ℝ) (hT : 4 ≤ T) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 2 ∧
      ∀ (t σ : ℝ), |t| ≤ T → (1 / 2 : ℝ) ≤ |t| → 1 - ε ≤ σ → σ ≤ 2 →
        riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ) ≠ 0 := by
  let S₀ : Set ℂ := (fun p : ℝ × ℝ => (p.1 : ℂ) + Complex.I * (p.2 : ℂ)) ''
    (Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (-T) T)
  have hS₀compact : IsCompact S₀ := by
    dsimp [S₀]
    exact (IsCompact.prod isCompact_Icc isCompact_Icc).image
      (by fun_prop : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) + Complex.I * (p.2 : ℂ)))
  let Z : Set ℂ := S₀ ∩ riemannZetaZeros
  have hZfin : Z.Finite := by
    dsimp [Z]
    exact hS₀compact.inter_riemannZetaZeros_finite
  have hZm : ∀ z : ℂ, z ∈ Z →
      (1 / 2 : ℝ) ≤ z.re ∧ z.re ≤ 2 ∧ |z.im| ≤ T ∧ riemannZeta z = 0 := by
    intro z hz
    rcases hz.1 with ⟨p, hp, hpeq⟩
    have hzre : z.re = p.1 := by rw [← hpeq]; simp
    have hzim : z.im = p.2 := by rw [← hpeq]; simp
    have hz0 : riemannZeta z = 0 := by simpa [riemannZetaZeros] using hz.2
    constructor
    · linarith [hp.1.1, hzre]
    constructor
    · linarith [hp.1.2, hzre]
    constructor
    · exact abs_le.mpr (by simpa [hzim] using hp.2)
    · exact hz0
  have hZ_re_lt_one : ∀ z : ℂ, z ∈ Z → z.re < 1 := by
    intro z hz
    have hz0 : riemannZeta z = 0 := (hZm z hz).2.2.2
    exact lt_of_not_ge (fun hge : (1 : ℝ) ≤ z.re =>
      riemannZeta_ne_zero_of_one_le_re (s := z) hge hz0)
  by_cases hZempty : Z = ∅
  · refine ⟨(1 / 2 : ℝ), by norm_num, by norm_num, ?_⟩
    intro t σ ht hthalf hσlo hσhi hz0
    let s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
    have hsZ : s ∈ Z := by
      constructor
      · dsimp [S₀]
        refine ⟨(σ, t), ?_, rfl⟩
        constructor
        · constructor <;> linarith
        · exact abs_le.mp ht
      · simpa [Z, riemannZetaZeros, s] using hz0
    rw [hZempty] at hsZ
    exact hsZ
  · have hZn : Z.Nonempty := Set.nonempty_iff_ne_empty.mpr hZempty
    let fz : Finset ℂ := hZfin.toFinset
    have hfz_mem_iff : ∀ z : ℂ, z ∈ fz ↔ z ∈ Z := by
      intro z
      exact hZfin.mem_toFinset
    have hg_ne : (fz.image (fun z : ℂ => 1 - z.re)).Nonempty := by
      rcases hZn with ⟨z, hz⟩
      refine ⟨1 - z.re, Finset.mem_image.mpr ⟨z, (hfz_mem_iff z).2 hz, rfl⟩⟩
    let d : ℝ := (fz.image (fun z : ℂ => 1 - z.re)).min' hg_ne
    have hd_mem : d ∈ fz.image (fun z : ℂ => 1 - z.re) := by
      dsimp [d]
      exact Finset.min'_mem _ hg_ne
    rcases Finset.mem_image.mp hd_mem with ⟨z₀, hz₀f, hz₀eq⟩
    have hz₀Z : z₀ ∈ Z := (hfz_mem_iff z₀).1 hz₀f
    have hd0 : 0 < d := by
      have hz₀re : z₀.re < 1 := hZ_re_lt_one z₀ hz₀Z
      have hd : d = 1 - z₀.re := by simpa [d] using hz₀eq.symm
      linarith
    have hd_le_half : d ≤ 1 / 2 := by
      have hz₀ge : (1 / 2 : ℝ) ≤ z₀.re := (hZm z₀ hz₀Z).1
      have hd : d = 1 - z₀.re := by simpa [d] using hz₀eq.symm
      linarith
    have hd_le : ∀ z : ℂ, z ∈ Z → d ≤ 1 - z.re := by
      intro z hz
      dsimp [d]
      exact Finset.min'_le (fz.image (fun z : ℂ => 1 - z.re))
        (1 - z.re) (Finset.mem_image.mpr ⟨z, (hfz_mem_iff z).2 hz, rfl⟩)
    refine ⟨d / 2, by positivity, by linarith, ?_⟩
    intro t σ ht hthalf hσlo hσhi hz0
    let s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
    have hsZ : s ∈ Z := by
      constructor
      · dsimp [S₀]
        refine ⟨(σ, t), ?_, rfl⟩
        constructor
        · constructor <;> linarith
        · exact abs_le.mp ht
      · simpa [Z, riemannZetaZeros, s] using hz0
    have hre : s.re = σ := by simp [s]
    have h1 : d ≤ 1 - σ := by
      have hd' := hd_le s hsZ
      rwa [hre] at hd'
    have h2 : 1 - σ ≤ d / 2 := by linarith
    linarith

/-- bounds: `log 4 ≥ 1` and `log (7/2) ≥ 1/2` and monotone facts used below. -/
private lemma log4_ge_one : (1 : ℝ) ≤ Real.log 4 := by
  have h := Real.log_two_gt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
    rw [Real.log_pow]
    ring
  rw [h4]
  nlinarith

private lemma zLL_ge_one {t : ℝ} (ht : 1 ≤ |t|) : (1 : ℝ) ≤ zLL t := by
  dsimp [zLL]
  have hle : 4 ≤ |t| + 3 := by linarith [ht]
  exact le_trans log4_ge_one (Real.log_le_log (by norm_num) hle)

private lemma log72_ge_half : (1 / 2 : ℝ) ≤ Real.log (7 / 2 : ℝ) := by
  have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  have hm : Real.log 2 ≤ Real.log (7 / 2 : ℝ) := by
    have hle : (2 : ℝ) ≤ (7 / 2 : ℝ) := by norm_num
    have hpos : 0 < (2 : ℝ) := by norm_num
    exact Real.log_le_log hpos hle
  linarith

/-- `zLL y ≤ 2 * zLL t` when `|y| ≤ |t| + 1` and `1 ≤ |t|`. -/
private lemma zLL_ratio_two {t y : ℝ} (ht : 1 ≤ |t|) (hy : |y| ≤ |t| + 1) :
    zLL y ≤ 2 * zLL t := by
  have hy' : |y| + 3 ≤ |t| + 4 := by linarith
  have hle1 : |t| + 4 ≤ (|t| + 3) ^ 2 := by
    have hx0 : 0 ≤ |t| := abs_nonneg t
    nlinarith
  have hpos2 : 0 < |y| + 3 := by linarith [abs_nonneg y]
  have hpos3 : 0 < |t| + 3 := by linarith [ht]
  have hlog : Real.log (|y| + 3) ≤ Real.log ((|t| + 3) ^ 2) := by
    exact Real.log_le_log hpos2 (le_trans hy' hle1)
  have hsq : Real.log ((|t| + 3) ^ 2) = 2 * Real.log (|t| + 3) := by
    rw [Real.log_pow]
    ring
  dsimp [zLL]
  rw [hsq] at hlog
  exact hlog

/-- **Zero-free region for all heights `|t| ≥ 1/2` with log width** (from the large-height
region and the bounded-height strip). -/
private lemma zfr_allHeights (c₀ T₀ : ℝ) (hc₀ : 0 < c₀) (hT₀ : 0 < T₀)
    (hZ : ∀ t : ℝ, T₀ ≤ |t| → ∀ σ : ℝ, 1 - c₀ / zLL t ≤ σ →
      riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ) ≠ 0) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 / 8 ∧
      ∀ t σ : ℝ, (1 / 2 : ℝ) ≤ |t| → 1 - c₁ / zLL t ≤ σ →
        riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ) ≠ 0 := by
  rcases zfr_bounded_strip (T₀ + 4) (by linarith [hT₀]) with ⟨ε, hε0, hε12, hstrip⟩
  let c₁ : ℝ := min (min c₀ (ε * (1 / 4))) (1 / 8)
  have hc₁0 : 0 < c₁ := by
    dsimp [c₁]
    positivity
  have hc1c0 : c₁ ≤ c₀ := by
    dsimp [c₁]
    exact le_trans (min_le_left (min c₀ (ε * (1 / 4))) (1 / 8))
      (min_le_left c₀ (ε * (1 / 4)))
  have hc1e : c₁ ≤ ε * (1 / 4) := by
    dsimp [c₁]
    exact le_trans (min_le_left (min c₀ (ε * (1 / 4))) (1 / 8))
      (min_le_right c₀ (ε * (1 / 4)))
  have hc1le : c₁ ≤ 1 / 8 := by dsimp [c₁]; linarith
  refine ⟨c₁, hc₁0, hc1le, ?_⟩
  intro t σ hthalf hσ
  by_cases htT : T₀ ≤ |t|
  · -- large height: use hZ (need c₁ ≤ c₀)
    have hL0 : 0 < zLL t := zLL_pos_of_half hthalf
    have hmono : c₁ / zLL t ≤ c₀ / zLL t := div_le_div_of_nonneg_right hc1c0 (le_of_lt hL0)
    have hσ' : 1 - c₀ / zLL t ≤ σ := by linarith
    exact hZ t htT σ hσ'
  · -- bounded height: use the strip
    have htb : |t| ≤ T₀ + 4 := by linarith [not_le.mp htT]
    by_cases hσ2 : σ ≤ 2
    · -- apply strip; need σ ≥ 1 - ε
      have hL72 : (1 / 2 : ℝ) ≤ zLL t := by
        have htmp : |t| + 3 ≥ 7 / 2 := by linarith [hthalf]
        have hpos : 0 < (7 / 2 : ℝ) := by norm_num
        dsimp [zLL]
        have hlog : Real.log (7 / 2 : ℝ) ≤ Real.log (|t| + 3) := Real.log_le_log hpos htmp
        linarith [log72_ge_half]
      have hLle : 1 / zLL t ≤ 2 := by
        rw [div_le_iff₀ (zLL_pos_of_half hthalf)]
        linarith
      have hc1L : c₁ / zLL t ≤ ε / 2 := by
        calc
          c₁ / zLL t ≤ (ε * (1 / 4)) / zLL t := div_le_div_of_nonneg_right hc1e (le_of_lt (zLL_pos_of_half hthalf))
          _ = (ε * (1 / 4)) * (1 / zLL t) := by ring
          _ ≤ (ε * (1 / 4)) * 2 := by
            exact mul_le_mul_of_nonneg_left hLle (by positivity)
          _ = ε / 2 := by ring
      have hεσ : 1 - ε ≤ σ := by
        have h1 : 1 - c₁ / zLL t ≤ σ := hσ
        have h2 : 1 - ε ≤ 1 - c₁ / zLL t := by
          have hc : c₁ / zLL t ≤ ε / 2 := hc1L
          linarith
        linarith
      exact hstrip t σ htb hthalf hεσ hσ2
    · -- σ > 2: ζ ≠ 0 on Re ≥ 1
      have hσ1 : (1 : ℝ) ≤ σ := by linarith
      have hre : (1 : ℝ) ≤ (((σ : ℂ) + Complex.I * (t : ℂ))).re := by simp [hσ1]
      exact riemannZeta_ne_zero_of_one_le_re hre

/-- `|t|+5 ≤ (|t|+3)^2` -/
private lemma add_five_le_sq_three (t : ℝ) : |t| + 5 ≤ (|t| + 3) ^ 2 := by
  have hx0 : 0 ≤ |t| := abs_nonneg t
  nlinarith

/-- `zLL y ≤ 2 * zLL t` when `|y| ≤ |t| + 2` and `1 ≤ |t|`. -/
private lemma zLL_ratio_two' {t y : ℝ} (ht : 1 ≤ |t|) (hy : |y| ≤ |t| + 2) :
    zLL y ≤ 2 * zLL t := by
  have hpos2 : 0 < |y| + 3 := by linarith [abs_nonneg y]
  have hle1 : |y| + 3 ≤ (|t| + 3) ^ 2 := by
    have : |y| + 3 ≤ |t| + 5 := by linarith
    exact le_trans this (add_five_le_sq_three t)
  have hlog : Real.log (|y| + 3) ≤ Real.log ((|t| + 3) ^ 2) := Real.log_le_log hpos2 hle1
  have hsq : Real.log ((|t| + 3) ^ 2) = 2 * Real.log (|t| + 3) := by
    rw [Real.log_pow]
    ring
  dsimp [zLL]
  rw [hsq] at hlog
  exact hlog

/-- `log(|t|+5) ≤ 3·(zLL t + 1)`. -/
private lemma log_add_five_le_three_add {t : ℝ} (ht : 1 ≤ |t|) :
    Real.log (|t| + 5) ≤ 3 * (zLL t + 1) := by
  have hpos2 : 0 < |t| + 5 := by linarith [abs_nonneg t]
  have hpos3 : 0 < |t| + 3 := by linarith [abs_nonneg t]
  have hsq1 : |t| + 5 ≤ (|t| + 3) ^ 2 := by
    have hx0 : 0 ≤ |t| := abs_nonneg t
    nlinarith
  have hq1 : (1 : ℝ) ≤ |t| + 3 := by linarith [ht]
  have hle1 : |t| + 5 ≤ (|t| + 3) ^ 3 := by
    calc
      |t| + 5 ≤ (|t| + 3) ^ 2 := hsq1
      _ ≤ (|t| + 3) ^ 3 := by
        have hp : 0 ≤ (|t| + 3) ^ 2 := sq_nonneg _
        have hle : (|t| + 3) ^ 2 ≤ (|t| + 3) ^ 2 * (|t| + 3) := by
          exact le_mul_of_one_le_right hp hq1
        simpa [pow_succ] using hle
  have hlog : Real.log (|t| + 5) ≤ Real.log ((|t| + 3) ^ 3) := Real.log_le_log hpos2 hle1
  have hsq : Real.log ((|t| + 3) ^ 3) = 3 * Real.log (|t| + 3) := by
    rw [Real.log_pow]
    ring
  rw [hsq] at hlog
  have hL : 0 ≤ zLL t := zLL_nonneg (t := t)
  have hLp : zLL t ≤ zLL t + 1 := by linarith
  have hm : Real.log (|t| + 3) ≤ zLL t + 1 := by
    dsimp [zLL]
    linarith
  calc
    Real.log (|t| + 5) ≤ 3 * Real.log (|t| + 3) := hlog
    _ ≤ 3 * (zLL t + 1) := by
      exact mul_le_mul_of_nonneg_left hm (by norm_num)

/-- log-ratio bound: `log (2(a+b)) - log b ≤ log 4 + max 0 (log a - log b)` for `a,b>0`. -/
private lemma log_ratio_bound (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.log (2 * (a + b)) - Real.log b ≤ Real.log 4 + max 0 (Real.log a - Real.log b) := by
  by_cases hb_le_a : b ≤ a
  · have hle : 2 * (a + b) ≤ 4 * a := by nlinarith
    have hpos : 0 < 2 * (a + b) := by positivity
    have hlog : Real.log (2 * (a + b)) ≤ Real.log (4 * a) := Real.log_le_log hpos hle
    have hnonneg : 0 ≤ Real.log a - Real.log b := by
      have : Real.log b ≤ Real.log a := Real.log_le_log hb hb_le_a
      linarith
    have h4a : Real.log (4 * a) = Real.log 4 + Real.log a := by
      rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt ha)]
    have hmax : max 0 (Real.log a - Real.log b) = Real.log a - Real.log b := max_eq_right hnonneg
    calc
      Real.log (2 * (a + b)) - Real.log b ≤ Real.log (4 * a) - Real.log b := by linarith
      _ = Real.log 4 + (Real.log a - Real.log b) := by rw [h4a]; ring
      _ = Real.log 4 + max 0 (Real.log a - Real.log b) := by rw [hmax]
  · have hale_b : a ≤ b := le_of_not_ge hb_le_a
    have hle : 2 * (a + b) ≤ 4 * b := by nlinarith
    have hpos : 0 < 2 * (a + b) := by positivity
    have hlog : Real.log (2 * (a + b)) ≤ Real.log (4 * b) := Real.log_le_log hpos hle
    have hnonpos : Real.log a - Real.log b ≤ 0 := by
      have : Real.log a ≤ Real.log b := Real.log_le_log ha hale_b
      linarith
    have h4b : Real.log (4 * b) = Real.log 4 + Real.log b := by
      rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt hb)]
    have hmax : max 0 (Real.log a - Real.log b) = 0 := max_eq_left hnonpos
    calc
      Real.log (2 * (a + b)) - Real.log b ≤ Real.log (4 * b) - Real.log b := by linarith
      _ = Real.log 4 := by rw [h4b]; ring
      _ = Real.log 4 + max 0 (Real.log a - Real.log b) := by rw [hmax]; ring

/-- **wide-strip polynomial growth of ζ**, `σ ∈ [-1, 4]`, `|t| ≥ 1`. -/
private lemma zeta_norm_poly_wide :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ t : ℝ), -1 ≤ σ → σ ≤ 4 → 1 ≤ |t| →
      ‖riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)‖ ≤ C * (|t| + 3) ^ 4 := by
  rcases zeta_strip_polyGrowth with ⟨C₁, hC₁0, hC₁spec⟩
  rcases zeta_norm_le_const_of_three_le_re with ⟨C₂, hC₂0, hC₂spec⟩
  let C : ℝ := max C₁ C₂
  have hC0 : 0 < C := lt_max_of_lt_left hC₁0
  refine ⟨C, hC0, ?_⟩
  intro σ t hσlo hσhi ht
  by_cases hσ3 : σ ≤ 3
  · have hb := hC₁spec σ t hσlo hσ3 ht
    calc
      ‖riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)‖ ≤ C₁ * (|t| + 3) ^ 4 := hb
      _ ≤ C * (|t| + 3) ^ 4 := by
        exact mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) (pow_nonneg (by linarith) 4)
  · have h3 : 3 ≤ σ := by linarith
    have hb := hC₂spec (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ) (by
      have : (((σ : ℂ) + Complex.I * (t : ℂ))).re = σ := by simp
      linarith)
    have hpow : 1 ≤ (|t| + 3) ^ 4 := by
      have h : 1 ≤ |t| + 3 := by linarith [ht]
      exact one_le_pow₀ h
    calc
      ‖riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)‖ ≤ C₂ := hb
      _ ≤ C₂ * (|t| + 3) ^ 4 := by
        exact le_mul_of_one_le_right (le_of_lt hC₂0) hpow
      _ ≤ C * (|t| + 3) ^ 4 := by
        exact mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) (pow_nonneg (by linarith) 4)

/-- **growth of ζ on a ball around `2+it`**: with the strip-growth constants `G`, `G₃`
provided, for `8 ≤ |t|`, radius `R ≤ 2`, `‖ζ w‖ ≤ X·(|t|+5)^4` where `X = max G (max G₃ 1)`. -/
private lemma zeta_ball_growth (G G₃ : ℝ) (hG0 : 0 < G) (hG₃0 : 0 < G₃)
    (hGspec : ∀ (σ t : ℝ), -1 ≤ σ → σ ≤ 4 → 1 ≤ |t| →
      ‖riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)‖ ≤ G * (|t| + 3) ^ 4)
    (hG₃spec : ∀ s : ℂ, 3 ≤ s.re → ‖riemannZeta s‖ ≤ G₃)
    (t : ℝ) (ht : 8 ≤ |t|) {R : ℝ} (hR : R ≤ 2)
    {w : ℂ} (hw : w ∈ Metric.ball ((2 : ℂ) + Complex.I * (t : ℂ)) R) :
    ‖riemannZeta w‖ ≤ (max G (max G₃ 1)) * (|t| + 5) ^ 4 := by
  let X : ℝ := max G (max G₃ 1)
  have hX0 : 0 < X := by dsimp [X]; positivity
  have hXG : G ≤ X := by dsimp [X]; exact le_max_left G (max G₃ 1)
  have hXG3 : G₃ ≤ X := by dsimp [X]; exact le_trans (le_max_left G₃ 1) (le_max_right G (max G₃ 1))
  have hXge1 : (1 : ℝ) ≤ X := by
    have h1 : 1 ≤ max G₃ 1 := le_max_right G₃ 1
    have h2 : max G₃ 1 ≤ X := by dsimp [X]; exact le_max_right G (max G₃ 1)
    linarith
  have hw1 : ‖w - ((2 : ℂ) + Complex.I * (t : ℂ))‖ < R := by
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  have hIm : |w.im| ≤ |t| + 2 := by
    have h2 : |w.im - t| ≤ ‖w - ((2 : ℂ) + Complex.I * (t : ℂ))‖ := by
      have h1 : |(w - ((2 : ℂ) + Complex.I * (t : ℂ))).im| ≤ ‖w - ((2 : ℂ) + Complex.I * (t : ℂ))‖ :=
        Complex.abs_im_le_norm (w - ((2 : ℂ) + Complex.I * (t : ℂ)))
      have hh : (w - ((2 : ℂ) + Complex.I * (t : ℂ))).im = w.im - t := by simp
      simpa [hh] using h1
    have hb : |w.im - t| < R := lt_of_le_of_lt h2 hw1
    have hred : |w.im| - |t| ≤ |w.im - t| := by
      have h0 : |w.im| - |t| ≤ |t - w.im| := by simpa [abs_sub_comm] using (abs_sub_abs_le_abs_sub w.im t)
      simpa [abs_sub_comm] using h0
    linarith
  have hrew : w.re ≤ 2 + R := by
    have h2 : |w.re - 2| ≤ ‖w - ((2 : ℂ) + Complex.I * (t : ℂ))‖ := by
      have h1 : |(w - ((2 : ℂ) + Complex.I * (t : ℂ))).re| ≤ ‖w - ((2 : ℂ) + Complex.I * (t : ℂ))‖ :=
        Complex.abs_re_le_norm (w - ((2 : ℂ) + Complex.I * (t : ℂ)))
      have hh : (w - ((2 : ℂ) + Complex.I * (t : ℂ))).re = w.re - 2 := by simp
      simpa [hh] using h1
    have h3 : w.re - 2 ≤ |w.re - 2| := le_abs_self (w.re - 2)
    linarith
  have hrew2 : w.re ≥ 2 - R := by
    have h2 : |w.re - 2| ≤ ‖w - ((2 : ℂ) + Complex.I * (t : ℂ))‖ := by
      have h1 : |(w - ((2 : ℂ) + Complex.I * (t : ℂ))).re| ≤ ‖w - ((2 : ℂ) + Complex.I * (t : ℂ))‖ :=
        Complex.abs_re_le_norm (w - ((2 : ℂ) + Complex.I * (t : ℂ)))
      have hh : (w - ((2 : ℂ) + Complex.I * (t : ℂ))).re = w.re - 2 := by simp
      simpa [hh] using h1
    have h3 : -(w.re - 2) ≤ |w.re - 2| := neg_le_abs (w.re - 2)
    linarith
  have hrew4 : w.re ≤ 4 := by linarith [hrew, hR]
  have hrewlo : -1 ≤ w.re := by linarith [hrew2, hR]
  have hIm1 : 1 ≤ |w.im| := by
    have h0 : |w.im| ≥ |t| - R := by
      have h2 : |w.im - t| < R := by
        have h1 : |(w - ((2 : ℂ) + Complex.I * (t : ℂ))).im| ≤ ‖w - ((2 : ℂ) + Complex.I * (t : ℂ))‖ :=
          Complex.abs_im_le_norm (w - ((2 : ℂ) + Complex.I * (t : ℂ)))
        have hh : (w - ((2 : ℂ) + Complex.I * (t : ℂ))).im = w.im - t := by simp
        have h2' : |w.im - t| ≤ ‖w - ((2 : ℂ) + Complex.I * (t : ℂ))‖ := by simpa [hh] using h1
        exact lt_of_le_of_lt h2' hw1
      have hred : |t| - |w.im| ≤ |w.im - t| := by
        have h0 : |t| - |w.im| ≤ |t - w.im| := abs_sub_abs_le_abs_sub t w.im
        simpa [abs_sub_comm] using h0
      linarith
    linarith [ht, hR]
  by_cases hre3 : w.re ≤ 3
  · have hb := hGspec w.re w.im hrewlo hrew4 hIm1
    have hw' : w = ((w.re : ℂ) + Complex.I * (w.im : ℂ)) := by
      apply Complex.ext <;> simp
    have hpow : (|w.im| + 3) ^ 4 ≤ (|t| + 5) ^ 4 := by
      have hle : |w.im| + 3 ≤ |t| + 5 := by linarith
      exact pow_le_pow_left₀ (by linarith) hle 4
    calc
      ‖riemannZeta w‖ = ‖riemannZeta (((w.re : ℂ) + Complex.I * (w.im : ℂ)) : ℂ)‖ := by
        congr 2 <;> exact hw' 
      _ ≤ G * (|w.im| + 3) ^ 4 := hb
      _ ≤ X * (|t| + 5) ^ 4 := by
        calc
          G * (|w.im| + 3) ^ 4 ≤ X * (|w.im| + 3) ^ 4 := by
            exact mul_le_mul_of_nonneg_right hXG (pow_nonneg (by linarith) 4)
          _ ≤ X * (|t| + 5) ^ 4 := by
            exact mul_le_mul_of_nonneg_left hpow (le_of_lt hX0)
  · have h3 : 3 ≤ w.re := by linarith
    have hb := hG₃spec (((w.re : ℂ) + Complex.I * (w.im : ℂ)) : ℂ) (by
      have : (((w.re : ℂ) + Complex.I * (w.im : ℂ))).re = w.re := by simp
      linarith)
    have hw' : w = ((w.re : ℂ) + Complex.I * (w.im : ℂ)) := by
      apply Complex.ext <;> simp
    have hpow : (1 : ℝ) ≤ (|t| + 5) ^ 4 := by
      have h : 1 ≤ |t| + 5 := by linarith [ht]
      exact one_le_pow₀ h
    calc
      ‖riemannZeta w‖ = ‖riemannZeta (((w.re : ℂ) + Complex.I * (w.im : ℂ)) : ℂ)‖ := by
        congr 2 <;> exact hw' 
      _ ≤ G₃ := hb
      _ ≤ X * (|t| + 5) ^ 4 := by
        have hXge0 : 0 ≤ X := le_of_lt hX0
        calc
          G₃ = G₃ * 1 := by ring
          _ ≤ X * 1 := by
            exact mul_le_mul_of_nonneg_right hXG3 (by norm_num)
          _ ≤ X * (|t| + 5) ^ 4 := by
            exact mul_le_mul_of_nonneg_left hpow hXge0

/-- **ζ ≠ 0 on the ball around `2+it`** of radius `R ≤ 1 + 4·(cA/64)/(zLL t)`, given the
zero-free region of width `cA` (`0 < cA ≤ 1`). -/
private lemma zeta_ne_zero_on_disk {cA : ℝ} (hcA0 : 0 < cA) (hcAle : cA ≤ 1)
    (hZ : ∀ t σ : ℝ, (1 / 2 : ℝ) ≤ |t| → 1 - cA / zLL t ≤ σ →
      riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ) ≠ 0)
    {t : ℝ} (ht : 8 ≤ |t|) {R : ℝ} (hR : R ≤ 1 + 4 * (cA / 64) / zLL t)
    {w : ℂ} (hw : w ∈ Metric.ball ((2 : ℂ) + Complex.I * (t : ℂ)) R) :
    riemannZeta w ≠ 0 := by
  let c : ℂ := (2 : ℂ) + Complex.I * (t : ℂ)
  let L : ℝ := zLL t
  let cb : ℝ := cA / 64
  have ht1 : 1 ≤ |t| := by linarith
  have hL0 : 0 < L := by dsimp [L]; exact zLL_pos ht1
  have hL1 : 1 ≤ L := by dsimp [L]; exact zLL_ge_one (t := t) ht1
  have hcb0 : 0 ≤ cb := by dsimp [cb]; positivity
  have hcb16 : cb ≤ 1 / 16 := by
    dsimp [cb]
    have hb : 16 * (cA / 64) ≤ 1 := by
      have : cA / 64 ≤ 1 / 64 := by
        rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 64) (by norm_num : (0 : ℝ) < 64)]
        norm_num
        exact hcAle
      nlinarith
    have hq : (cA / 64) * 16 ≤ 1 := by
      -- cA/64 ≤ 1/64, multiply by 16
      have hm : (cA / 64) * 16 = 16 * (cA / 64) := by ring
      rw [hm]
      exact hb
    have hq2 : cA / 64 ≤ 1 / 16 := by
      have : (cA / 64) * 16 ≤ 1 := hq
      nlinarith
    exact hq2
  have h4cBL : 4 * cb / L ≤ 1 / 2 := by
    have hA : 4 * cb / L ≤ 4 * cb := by
      rw [div_le_iff₀ hL0]
      have hq0 : 0 ≤ 4 * cb := by positivity
      have hq : 4 * cb ≤ 4 * cb * L := by
        exact le_mul_of_one_le_right hq0 hL1
      simpa [mul_assoc] using hq
    have hB : 4 * cb ≤ 1 / 2 := by
      have hc : cb ≤ 1 / 16 := hcb16
      nlinarith
    linarith
  have hR32 : R ≤ 3 / 2 := by
    have hb : 1 + 4 * cb / L ≤ 3 / 2 := by linarith
    exact le_trans hR hb
  have hw1 : ‖w - c‖ < R := by simpa [c, Metric.mem_ball, dist_eq_norm] using hw
  have hIm_le : |w.im| ≤ |t| + 2 := by
    have h2 : |w.im - t| ≤ ‖w - c‖ := by
      have h1 : |(w - c).im| ≤ ‖w - c‖ := Complex.abs_im_le_norm (w - c)
      have hh : (w - c).im = w.im - t := by simp [c]
      simpa [hh] using h1
    have hb : |w.im - t| < R := lt_of_le_of_lt h2 hw1
    have hred : |w.im| - |t| ≤ |w.im - t| := by
      have h0 : |w.im| - |t| ≤ |t - w.im| := by simpa [abs_sub_comm] using (abs_sub_abs_le_abs_sub w.im t)
      simpa [abs_sub_comm] using h0
    linarith
  have hIm_ge : (1 / 2 : ℝ) ≤ |w.im| := by
    have h0 : |w.im| ≥ |t| - R := by
      have h2 : |w.im - t| < R := by
        have h1 : |(w - c).im| ≤ ‖w - c‖ := Complex.abs_im_le_norm (w - c)
        have hh : (w - c).im = w.im - t := by simp [c]
        have h2' : |w.im - t| ≤ ‖w - c‖ := by simpa [hh] using h1
        exact lt_of_le_of_lt h2' hw1
      have hred : |t| - |w.im| ≤ |w.im - t| := by
        have h0 : |t| - |w.im| ≤ |t - w.im| := abs_sub_abs_le_abs_sub t w.im
        simpa [abs_sub_comm] using h0
      linarith
    linarith [ht, hR32]
  have hLLy : zLL w.im ≤ 2 * L := by
    have : |w.im| ≤ |t| + 2 := hIm_le
    dsimp [L]
    exact zLL_ratio_two' ht1 this
  have hrew : w.re ≥ 2 - R := by
    have h2 : |w.re - 2| ≤ ‖w - c‖ := by
      have h1 : |(w - c).re| ≤ ‖w - c‖ := Complex.abs_re_le_norm (w - c)
      have hh : (w - c).re = w.re - 2 := by simp [c]
      simpa [hh] using h1
    have h3 : -(w.re - 2) ≤ |w.re - 2| := neg_le_abs (w.re - 2)
    linarith
  have hLL0 : 0 < zLL w.im := zLL_pos_of_half hIm_ge
  have hcA_LL : 4 * cb / L ≤ cA / zLL w.im := by
    rw [div_le_div_iff₀ hL0 hLL0]
    calc
      4 * cb * zLL w.im ≤ 4 * cb * (2 * L) := by
        exact mul_le_mul_of_nonneg_left hLLy (mul_nonneg (by norm_num) hcb0)
      _ = 8 * cb * L := by ring
      _ ≤ cA * L := by
        have hq : 8 * cb ≤ cA := by
          dsimp [cb]
          nlinarith [hcA0]
        -- 8·cb·L ≤ cA·L : since 8cb ≤ cA and L ≥ 0
        exact mul_le_mul_of_nonneg_right hq (le_of_lt hL0)
  have hσ : 1 - cA / zLL w.im ≤ w.re := by
    have h1 : 1 - 4 * cb / L ≤ w.re := by linarith
    have h2 : 1 - cA / zLL w.im ≤ 1 - 4 * cb / L := by linarith
    linarith
  have hZat : riemannZeta (((w.re : ℂ) + Complex.I * (w.im : ℂ)) : ℂ) ≠ 0 := hZ w.im w.re hIm_ge hσ
  have hwf : w = ((w.re : ℂ) + Complex.I * (w.im : ℂ)) := by
    apply Complex.ext <;> simp
  rw [hwf]
  exact hZat


/-- `max 0 (u + S) ≤ max 0 u + S` when `0 ≤ S`. -/
private lemma max0_add_le {u S : ℝ} (hS : 0 ≤ S) : max 0 (u + S) ≤ max 0 u + S := by
  by_cases hu : 0 ≤ u
  · have h : 0 ≤ u + S := by linarith
    simp [max_eq_right hu, max_eq_right h]
  · have hu' : u ≤ 0 := le_of_not_ge hu
    have hm : max 0 u = 0 := max_eq_left hu'
    have hle : max 0 (u + S) ≤ S := by
      by_cases h : 0 ≤ u + S
      · rw [max_eq_right h]
        linarith
      · rw [max_eq_left (le_of_not_ge h)]
        exact hS
    calc
      max 0 (u + S) ≤ S := hle
      _ = max 0 u + S := by rw [hm]; ring

/-- `zLL t ≤ 64` when `|t| ≤ 10`. -/
private lemma zLL_le_64 {t : ℝ} (ht : |t| ≤ 10) : zLL t ≤ 64 := by
  dsimp [zLL]
  have hx : 0 < |t| + 3 := by linarith [abs_nonneg t]
  have hle13 : |t| + 3 ≤ 13 := by linarith
  have hlog13 : Real.log 13 ≤ 12 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 13)
    linarith
  have hle : Real.log (|t| + 3) ≤ Real.log 13 := Real.log_le_log hx hle13
  linarith

/-- `|t| ≥ 8 → 1 ≤ |t|`. -/
private lemma one_le_abs_of_ge_eight {t : ℝ} (ht : 8 ≤ |t|) : 1 ≤ |t| := by linarith

/-- **Log-derivative bound in the width-`cA/64` region for `|t| ≥ 8`** (disk argument via
`logDeriv_zeroFree_ball_bound_analytic`). -/
private lemma zeta_logDeriv_bound_largeHeight {cA : ℝ} (hcA0 : 0 < cA) (hcAle : cA ≤ 1)
    (hZ : ∀ t σ : ℝ, (1 / 2 : ℝ) ≤ |t| → 1 - cA / zLL t ≤ σ →
      riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ) ≠ 0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ t σ : ℝ, 8 ≤ |t| → σ ≤ 2 → 1 - (cA / 64) / zLL t ≤ σ →
        ‖(deriv riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)) /
            riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)‖ ≤ C * (zLL t + 1) ^ 4 := by
  rcases zeta_norm_poly_wide with ⟨G, hG0, hGspec⟩
  rcases zeta_norm_le_const_of_three_le_re with ⟨G₃, hG₃0, hG₃spec⟩
  rcases zeta_lower_re_two with ⟨c₂, hc₂0, hc₂spec⟩
  let X : ℝ := max G (max G₃ 1)
  have hX0 : 0 < X := by
    dsimp [X]
    positivity
  have hX0le : 0 ≤ X := le_of_lt hX0
  let K0 : ℝ := Real.log 4 + max 0 (Real.log X - Real.log c₂)
  have hK0 : 0 ≤ K0 := by
    dsimp [K0]
    have h1 : 0 ≤ Real.log 4 := by positivity
    have h2 : 0 ≤ max 0 (Real.log X - Real.log c₂) := by positivity
    linarith
  have hK0pos : 0 < K0 := by
    dsimp [K0]
    have h1 : 0 < Real.log 4 := Real.log_pos (by norm_num : (1 : ℝ) < 4)
    have h2 : 0 ≤ max 0 (Real.log X - Real.log c₂) := by positivity
    linarith
  let B : ℝ := 2 * (K0 + 12)
  have hB0 : 0 < B := by
    dsimp [B]
    nlinarith [hK0pos]
  let cb0 : ℝ := cA / 64
  have hcb00 : 0 < cb0 := by
    dsimp [cb0]
    positivity
  have hcb0le : 0 ≤ cb0 := le_of_lt hcb00
  have hcb064 : cb0 ≤ 1 / 64 := by
    dsimp [cb0]
    exact div_le_div_of_nonneg_right hcAle (by norm_num : (0 : ℝ) ≤ 64)
  let C : ℝ := 33 * B / (64 * cb0 ^ 2) + 1
  have hC0 : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC0, ?_⟩
  intro t σ ht hσ2 hσlo
  let L : ℝ := zLL t
  let δ : ℝ := cb0 / L
  let s₀ : ℂ := ((σ : ℂ) + Complex.I * (t : ℂ))
  let c : ℂ := ((2 : ℂ) + Complex.I * (t : ℂ))
  let R : ℝ := 1 + 4 * δ
  have ht1 : 1 ≤ |t| := one_le_abs_of_ge_eight ht
  have hL0 : 0 < L := by dsimp [L]; exact zLL_pos ht1
  have hL1 : (1 : ℝ) ≤ L := by dsimp [L]; exact zLL_ge_one (t := t) ht1
  have hL0le : 0 ≤ L := le_of_lt hL0
  have hLp1 : (1 : ℝ) ≤ L + 1 := by dsimp [L]; exact zLL_add_one_ge_one (t := t)
  have hLp_pos : 0 < L + 1 := by linarith
  have hδ0 : 0 < δ := by
    dsimp [δ]
    exact div_pos hcb00 hL0
  have hδ_nonneg : 0 ≤ δ := le_of_lt hδ0
  have hδ_le : δ ≤ 1 / 64 := by
    dsimp [δ]
    have hdiv : cb0 / L ≤ cb0 := by
      rw [div_le_iff₀ hL0]
      exact le_mul_of_one_le_right hcb0le hL1
    exact le_trans hdiv hcb064
  have hδ_le_q : δ ≤ 1 / 4 := by linarith
  have hR0 : 0 < R := by dsimp [R]; positivity
  have hR2 : R ≤ 2 := by
    dsimp [R]
    have h4δ : 4 * δ ≤ 4 * (1 / 64) := by exact mul_le_mul_of_nonneg_left hδ_le (by norm_num)
    linarith
  have hRzfr : R ≤ 1 + 4 * (cA / 64) / zLL t := by
    dsimp [R, δ, cb0]
    have hz : zLL t ≠ 0 := by
      dsimp [L] at hL0
      exact ne_of_gt hL0
    have heq : 1 + 4 * ((cA / 64) / zLL t) = 1 + 4 * (cA / 64) / zLL t := by
      field_simp [hz]
    rw [heq]
  have hsc : ‖s₀ - c‖ = 2 - σ := by
    dsimp [s₀, c]
    have h : (((σ : ℂ) + Complex.I * (t : ℂ)) - ((2 : ℂ) + Complex.I * (t : ℂ)))
        = ((σ - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [h]
    rw [norm_real]
    rw [Real.norm_eq_abs]
    have hσm2 : σ - 2 ≤ 0 := by linarith
    rw [abs_of_nonpos hσm2]
    ring
  have hdle : ‖s₀ - c‖ ≤ 1 + δ := by
    rw [hsc]
    dsimp [δ]
    have hσ' : 1 - cb0 / L ≤ σ := by simpa [cb0, L] using hσlo
    linarith
  have hρR : δ < R - ‖s₀ - c‖ := by
    dsimp [R]
    have hRd : 1 + 4 * δ - ‖s₀ - c‖ ≥ 3 * δ := by
      have hd1 : ‖s₀ - c‖ ≤ 1 + δ := hdle
      nlinarith
    have h3d : 3 * δ > δ := by nlinarith [hδ0]
    linarith
  have hsc_lt : ‖s₀ - c‖ < R := by
    dsimp [R]
    nlinarith [hδ0, hdle]
  have hz₀ball : s₀ ∈ Metric.ball c R := by
    rw [Metric.mem_ball]
    simpa [dist_eq_norm] using hsc_lt
  have h1c : 8 ≤ ‖(1 : ℂ) - c‖ := by
    have hb' : |((1 : ℂ) - c).im| = |t| := by simp [c]
    calc
      8 ≤ |t| := ht
      _ = |((1 : ℂ) - c).im| := hb'.symm
      _ ≤ ‖(1 : ℂ) - c‖ := by
        simpa using (Complex.abs_im_le_norm ((1 : ℂ) - c))
  have h1not : (1 : ℂ) ∉ Metric.ball c R := by
    intro h1b
    have h : ‖(1 : ℂ) - c‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using h1b
    linarith
  have hball_sub : Metric.ball c R ⊆ ({1}ᶜ : Set ℂ) := by
    intro w hw
    rw [mem_compl_iff, mem_singleton_iff]
    intro hw1
    exact h1not (by simpa [hw1] using hw)
  have hg : AnalyticOnNhd ℂ riemannZeta (Metric.ball c R) :=
    analyticOn_riemannZeta.mono hball_sub
  have hgne : ∀ w : ℂ, w ∈ Metric.ball c R → riemannZeta w ≠ 0 := by
    intro w hw
    exact zeta_ne_zero_on_disk hcA0 hcAle hZ ht hRzfr hw
  have hgrow : ∀ w : ℂ, w ∈ Metric.ball c R → ‖riemannZeta w‖ ≤ X * (|t| + 5) ^ 4 := by
    intro w hw
    simpa [X] using (zeta_ball_growth G G₃ hG0 hG₃0 hGspec hG₃spec t ht hR2 (hw := hw))
  let M : ℝ := X * (|t| + 5) ^ 4 + c₂
  have hgM : ∀ w : ℂ, w ∈ Metric.ball c R → ‖riemannZeta w‖ ≤ M := by
    intro w hw
    have hb := hgrow w hw
    have hle : X * (|t| + 5) ^ 4 ≤ M := by
      dsimp [M]
      linarith [hX0le]
    exact le_trans hb hle
  have hgmc : c₂ ≤ ‖riemannZeta c‖ := by
    have h := hc₂spec t
    simpa [c] using h
  have hMm : c₂ ≤ M := by
    dsimp [M]
    have hpos : 0 ≤ X * (|t| + 5) ^ 4 := by positivity
    nlinarith
  have hball := Commons.Analysis.Complex.logDeriv_zeroFree_ball_bound_analytic (g := riemannZeta) (c := c) (R := R)
      (m := c₂) (M := M) hR0 hc₂0 hMm hg hgne hgM hgmc
  have hmain := hball (z₀ := s₀) hz₀ball δ hδ0 hρR
  -- estimate chain
  let t5 : ℝ := |t| + 5
  have ht50 : 0 < t5 := by dsimp [t5]; linarith [abs_nonneg t]
  have ht5ne : t5 ≠ 0 := ne_of_gt ht50
  have ht5p : (0 : ℝ) ≤ t5 := le_of_lt ht50
  have hXt5 : 0 < X * t5 ^ 4 := by positivity
  have hlog_t5 : Real.log t5 ≤ 3 * (L + 1) := by
    dsimp [t5]
    have hb := log_add_five_le_three_add (t := t) ht1
    simpa [L] using hb
  have h4log : 4 * Real.log t5 ≤ 12 * (L + 1) := by nlinarith [hlog_t5]
  let u : ℝ := Real.log X - Real.log c₂
  have hlogX : Real.log (X * t5 ^ 4) = Real.log X + Real.log (t5 ^ 4) := by
    exact Real.log_mul (ne_of_gt hX0) (pow_ne_zero 4 ht5ne)
  have hlogXp : Real.log (t5 ^ 4) = 4 * Real.log t5 := by
    rw [Real.log_pow]
    norm_num
  have hloga : Real.log (X * t5 ^ 4) - Real.log c₂ ≤ u + 12 * (L + 1) := by
    dsimp [u]
    calc
      Real.log (X * t5 ^ 4) - Real.log c₂ = (Real.log X + Real.log (t5 ^ 4)) - Real.log c₂ := by rw [hlogX]
      _ = (Real.log X - Real.log c₂) + Real.log (t5 ^ 4) := by ring
      _ = (Real.log X - Real.log c₂) + 4 * Real.log t5 := by rw [hlogXp]
      _ ≤ (Real.log X - Real.log c₂) + 12 * (L + 1) := by linarith [h4log]
  have hmaxle : max 0 (Real.log (X * t5 ^ 4) - Real.log c₂) ≤ max 0 u + 12 * (L + 1) := by
    have hmono : max 0 (Real.log (X * t5 ^ 4) - Real.log c₂) ≤ max 0 (u + 12 * (L + 1)) := by
      exact max_le_max le_rfl hloga
    have hS : 0 ≤ 12 * (L + 1) := by positivity
    have hma := max0_add_le (u := u) (S := 12 * (L + 1)) hS
    exact le_trans hmono hma
  have hlr := log_ratio_bound (X * t5 ^ 4) c₂ hXt5 hc₂0
  have h2M : 2 * M = 2 * ((X * t5 ^ 4) + c₂) := by
    dsimp [M, t5]
  have hlogle : Real.log (2 * M) - Real.log c₂ ≤ Real.log 4 + max 0 (Real.log (X * t5 ^ 4) - Real.log c₂) := by
    have hconv : Real.log (2 * (X * t5 ^ 4 + c₂)) - Real.log c₂ = Real.log (2 * M) - Real.log c₂ := by
      rw [← h2M]
    rw [← hconv]
    simpa using hlr
  have hlogpart : Real.log (2 * M) - Real.log c₂ ≤ K0 + 12 * (L + 1) := by
    calc
      Real.log (2 * M) - Real.log c₂ ≤ Real.log 4 + max 0 (Real.log (X * t5 ^ 4) - Real.log c₂) := hlogle
      _ ≤ Real.log 4 + (max 0 u + 12 * (L + 1)) := by
        exact add_le_add_right hmaxle (Real.log 4)
      _ = K0 + 12 * (L + 1) := by dsimp [K0, u]; ring
  have hK0le : K0 ≤ K0 * (L + 1) := by
    exact le_mul_of_one_le_right hK0 hLp1
  have hlogpart2 : Real.log (2 * M) - Real.log c₂ ≤ (K0 + 12) * (L + 1) := by
    calc
      Real.log (2 * M) - Real.log c₂ ≤ K0 + 12 * (L + 1) := hlogpart
      _ = K0 * 1 + 12 * (L + 1) := by ring
      _ ≤ K0 * (L + 1) + 12 * (L + 1) := by nlinarith [hK0le]
      _ = (K0 + 12) * (L + 1) := by ring
  have hlogb : 2 * (Real.log (2 * M) - Real.log c₂) ≤ B * (L + 1) := by
    dsimp [B]
    nlinarith [hlogpart2]
  have hlogpart_nonneg : 0 ≤ Real.log (2 * M) - Real.log c₂ := by
    have hM : c₂ ≤ 2 * M := by
      dsimp [M]
      have hpos : 0 ≤ X * (|t| + 5) ^ 4 := by positivity
      nlinarith
    have h2Mpos : 0 < 2 * M := by positivity
    have hlogle : Real.log c₂ ≤ Real.log (2 * M) := Real.log_le_log hc₂0 hM
    linarith
  -- geometric factor
  have hden_pos : 0 < (R - ‖s₀ - c‖ - δ) * δ := by
    have h1 : 0 < R - ‖s₀ - c‖ - δ := by linarith [hρR]
    exact mul_pos h1 hδ0
  have hnum_pos : 0 < ‖s₀ - c‖ + δ := by positivity
  have htop : ‖s₀ - c‖ + δ ≤ 1 + 2 * δ := by nlinarith [hdle]
  have hbot : (R - ‖s₀ - c‖ - δ) * δ ≥ 2 * δ ^ 2 := by
    have h1 : R - ‖s₀ - c‖ - δ ≥ 2 * δ := by
      dsimp [R]
      nlinarith [hdle]
    have hδ2 : 0 ≤ δ ^ 2 := sq_nonneg δ
    calc
      (R - ‖s₀ - c‖ - δ) * δ ≥ (2 * δ) * δ := by
        exact mul_le_mul_of_nonneg_right h1 hδ_nonneg
      _ = 2 * δ ^ 2 := by ring
  have htop_num : 1 + 2 * δ ≤ 33 / 32 := by
    have h2δ : 2 * δ ≤ 2 * (1 / 64) := by exact mul_le_mul_of_nonneg_left hδ_le (by norm_num)
    norm_num
    linarith
  have h2δ2pos : 0 < 2 * δ ^ 2 := by positivity
  have hfrac : (‖s₀ - c‖ + δ) / ((R - ‖s₀ - c‖ - δ) * δ) ≤ (33 / 32) / (2 * δ ^ 2) := by
    have h1 : ‖s₀ - c‖ + δ ≤ 33 / 32 := by linarith [htop, htop_num]
    have hDle : (2 * δ ^ 2) ≤ (R - ‖s₀ - c‖ - δ) * δ := by linarith [hbot]
    have hcross : (‖s₀ - c‖ + δ) * (2 * δ ^ 2) ≤ (33 / 32) * ((R - ‖s₀ - c‖ - δ) * δ) := by
      have h4 : (‖s₀ - c‖ + δ) * (2 * δ ^ 2) ≤ (33 / 32) * (2 * δ ^ 2) := by
        exact mul_le_mul_of_nonneg_right h1 (le_of_lt h2δ2pos)
      have h3 : (33 / 32) * (2 * δ ^ 2) ≤ (33 / 32) * ((R - ‖s₀ - c‖ - δ) * δ) := by
        exact mul_le_mul_of_nonneg_left hDle (by norm_num : (0 : ℝ) ≤ 33 / 32)
      exact le_trans h4 h3
    exact (div_le_div_iff₀ hden_pos h2δ2pos).2 hcross
  have hδ2 : δ ^ 2 = cb0 ^ 2 / L ^ 2 := by
    dsimp [δ]
    field_simp [hL0.ne']
  have hfrac2 : (33 / 32) / (2 * δ ^ 2) ≤ 33 * (L + 1) ^ 2 / (64 * cb0 ^ 2) := by
    -- (33/32)/(2δ²) = 33/(64 δ²) = 33 L²/(64 cb0²) ≤ 33 (L+1)²/(64 cb0²)
    have hdenpos : 0 < 2 * δ ^ 2 := by positivity
    have h : (33 / 32) / (2 * δ ^ 2) = 33 / (64 * δ ^ 2) := by
      field_simp
      ring
    rw [h]
    have h2 : 33 / (64 * δ ^ 2) = 33 * (L ^ 2) / (64 * cb0 ^ 2) := by
      rw [hδ2]
      field_simp [hL0.ne', pow_ne_zero 2 hcb00.ne']
    rw [h2]
    have hLsq : L ^ 2 ≤ (L + 1) ^ 2 := by
      have hLp : 0 ≤ L + 1 := by linarith
      exact pow_le_pow_left₀ hL0le (by linarith) 2
    have hcoef : 0 ≤ 33 / (64 * cb0 ^ 2) := by positivity
    have h64 : 0 < 64 * cb0 ^ 2 := by positivity
    have hnumle : 33 * L ^ 2 ≤ 33 * (L + 1) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hLsq (by norm_num : (0 : ℝ) ≤ 33)
    exact div_le_div_of_nonneg_right hnumle (le_of_lt h64)
  have hgeo : (‖s₀ - c‖ + δ) / ((R - ‖s₀ - c‖ - δ) * δ) ≤ 33 * (L + 1) ^ 2 / (64 * cb0 ^ 2) := by
    exact le_trans hfrac hfrac2
  -- multiply
  let x : ℝ := 2 * (Real.log (2 * M) - Real.log c₂)
  let y : ℝ := (‖s₀ - c‖ + δ) / ((R - ‖s₀ - c‖ - δ) * δ)
  let x0 : ℝ := B * (L + 1)
  let y0 : ℝ := 33 * (L + 1) ^ 2 / (64 * cb0 ^ 2)
  have hx0le : 0 ≤ x0 := by dsimp [x0]; positivity
  have hy0le : 0 ≤ y0 := by dsimp [y0]; positivity
  have hy_nonneg : 0 ≤ y := by dsimp [y]; positivity
  have hmul : x * y ≤ x0 * y0 := by
    have hx_le : x ≤ x0 := by simpa [x, x0] using hlogb
    have hy_le : y ≤ y0 := by simpa [y, y0] using hgeo
    -- mul_le_mul hx_le hy_le hy_nonneg hx0le? need x0 ≥ 0 and y ≥ 0
    exact mul_le_mul hx_le hy_le hy_nonneg hx0le
  have hxy : x0 * y0 = (33 * B / (64 * cb0 ^ 2)) * (L + 1) ^ 3 := by
    dsimp [x0, y0]
    field_simp [hcb00.ne']
  have hpow34 : (L + 1) ^ 3 ≤ (L + 1) ^ 4 := by
    have h : (L + 1) ^ 3 = (L + 1) ^ 3 * 1 := by ring
    calc
      (L + 1) ^ 3 = (L + 1) ^ 3 * 1 := by ring
      _ ≤ (L + 1) ^ 3 * (L + 1) := by
        exact mul_le_mul_of_nonneg_left hLp1 (by positivity : 0 ≤ (L + 1) ^ 3)
      _ = (L + 1) ^ 4 := by ring
  have hcoef0 : 0 ≤ 33 * B / (64 * cb0 ^ 2) := by positivity
  have hstep1 : (33 * B / (64 * cb0 ^ 2)) * (L + 1) ^ 3 ≤ (33 * B / (64 * cb0 ^ 2)) * (L + 1) ^ 4 := by
    exact mul_le_mul_of_nonneg_left hpow34 hcoef0
  have hstep2 : (33 * B / (64 * cb0 ^ 2)) * (L + 1) ^ 4 ≤ C * (L + 1) ^ 4 := by
    have hle : 33 * B / (64 * cb0 ^ 2) ≤ C := by dsimp [C]; linarith
    exact mul_le_mul_of_nonneg_right hle (pow_nonneg (by linarith : (0 : ℝ) ≤ L + 1) 4)
  have hmainxy : ‖(deriv riemannZeta s₀) / riemannZeta s₀‖ ≤ x * y := by
    have heq : x * y = 2 * (Real.log (2 * M) - Real.log c₂) * (‖s₀ - c‖ + δ) /
        ((R - ‖s₀ - c‖ - δ) * δ) := by
      dsimp [x, y]
      ring
    rw [heq]
    simpa [M, R, δ, cb0, L] using hmain
  calc
    ‖(deriv riemannZeta s₀) / riemannZeta s₀‖ ≤ x * y := hmainxy
    _ ≤ x0 * y0 := hmul
    _ = (33 * B / (64 * cb0 ^ 2)) * (L + 1) ^ 3 := hxy
    _ ≤ (33 * B / (64 * cb0 ^ 2)) * (L + 1) ^ 4 := hstep1
    _ ≤ C * (L + 1) ^ 4 := hstep2


/-- **Log-derivative bound in the width-`cA/64` region for `1 ≤ |t| ≤ 10`** (compactness of
`ζ'/ζ` on a pole-free, zero-free rectangle). -/
private lemma zeta_logDeriv_bound_boundedHeight {cA : ℝ} (hcA0 : 0 < cA) (hcAle : cA ≤ 1)
    (hZ : ∀ t σ : ℝ, (1 / 2 : ℝ) ≤ |t| → 1 - cA / zLL t ≤ σ →
      riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ) ≠ 0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ t σ : ℝ, 1 ≤ |t| → |t| ≤ 10 → σ ≤ 2 → 1 - (cA / 64) / zLL t ≤ σ →
        ‖(deriv riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)) /
            riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)‖ ≤ C * (zLL t + 1) ^ 4 := by
  let K : Set ℂ := {z : ℂ | 1 - cA / 64 ≤ z.re ∧ z.re ≤ 2 ∧ 1 ≤ |z.im| ∧ |z.im| ≤ 10}
  have hKclosed : IsClosed K := by
    dsimp [K]
    rw [show ({z : ℂ | 1 - cA / 64 ≤ z.re ∧ z.re ≤ 2 ∧ 1 ≤ |z.im| ∧ |z.im| ≤ 10} : Set ℂ)
        = {z : ℂ | 1 - cA / 64 ≤ z.re} ∩ {z : ℂ | z.re ≤ 2} ∩ {z : ℂ | 1 ≤ |z.im|} ∩
          {z : ℂ | |z.im| ≤ 10} by
          ext z
          simp [and_assoc]]
    refine IsClosed.inter ?_ ?_
    · refine IsClosed.inter ?_ ?_
      · refine IsClosed.inter ?_ ?_
        · exact isClosed_le continuous_const Complex.continuous_re
        · exact isClosed_le Complex.continuous_re continuous_const
      · exact isClosed_le continuous_const (Continuous.comp continuous_abs Complex.continuous_im)
    · exact isClosed_le (Continuous.comp continuous_abs Complex.continuous_im) continuous_const
  have hKbdd : Bornology.IsBounded K := by
    refine isBounded_iff_forall_norm_le.mpr ⟨12, ?_⟩
    intro z hz
    dsimp [K] at hz
    obtain ⟨hz1, hz2, hz3, hz4⟩ := hz
    have hrelo : 0 ≤ z.re := by
      have h0 : 0 ≤ 1 - cA / 64 := by
        have : cA / 64 ≤ 1 := by
          have h1 : cA / 64 ≤ 1 / 64 := div_le_div_of_nonneg_right hcAle (by norm_num : (0 : ℝ) ≤ 64)
          linarith
        linarith
      linarith
    have hre_abs : |z.re| ≤ 2 := by
      rw [abs_of_nonneg hrelo]
      exact hz2
    have him_abs : |z.im| ≤ 10 := hz4
    have hnorm : ‖z‖ ≤ |z.re| + |z.im| := by
      calc
        ‖z‖ = ‖(z.re : ℂ) + Complex.I * (z.im : ℂ)‖ := by
          congr 1
          apply Complex.ext <;> simp
        _ ≤ ‖(z.re : ℂ)‖ + ‖Complex.I * (z.im : ℂ)‖ := norm_add_le _ _
        _ = |z.re| + |z.im| := by simp
    linarith
  have hKcompact : IsCompact K := by
    rw [Metric.isCompact_iff_isClosed_bounded]
    exact ⟨hKclosed, hKbdd⟩
  have hKsub : K ⊆ ({1}ᶜ : Set ℂ) := by
    intro z hz
    dsimp [K] at hz
    intro hz1
    obtain ⟨hz1', hz2', hz3', hz4'⟩ := hz
    have him : (1 : ℝ) ≤ |z.im| := hz3'
    simp at hz1
    rw [hz1] at him
    simp at him
    linarith
  have hdgC : ContinuousOn (deriv riemannZeta) K :=
    ((analyticOn_riemannZeta.mono hKsub).deriv).continuousOn
  have hzC : ContinuousOn riemannZeta K := (analyticOn_riemannZeta.mono hKsub).continuousOn
  have hneK : ∀ z ∈ K, riemannZeta z ≠ 0 := by
    intro z hz
    dsimp [K] at hz
    obtain ⟨hz1', hz2', hz3', hz4'⟩ := hz
    have him1 : (1 / 2 : ℝ) ≤ |z.im| := by linarith
    have hzL : zLL z.im ≤ 64 := zLL_le_64 hz4'
    have hzLpos : 0 < zLL z.im := zLL_pos_of_half him1
    have h2 : cA / 64 ≤ cA / zLL z.im := by
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 64) hzLpos]
      nlinarith [hzL, hcA0.le]
    have hσ : 1 - cA / zLL z.im ≤ z.re := by linarith
    have hval := hZ z.im z.re him1 hσ
    have hzr : z = ((z.re : ℂ) + Complex.I * (z.im : ℂ)) := by
      apply Complex.ext <;> simp
    rwa [hzr]
  have hcont : ContinuousOn (fun z : ℂ => deriv riemannZeta z / riemannZeta z) K :=
    ContinuousOn.div hdgC hzC hneK
  rcases IsCompact.exists_bound_of_continuousOn hKcompact hcont with ⟨C₀, hC₀⟩
  have hKne : K.Nonempty := by
    refine ⟨((2 : ℂ) + Complex.I * (1 : ℂ)), ?_⟩
    dsimp [K]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h0 : 0 ≤ 1 - cA / 64 := by
        have h1 : cA / 64 ≤ 1 / 64 := div_le_div_of_nonneg_right hcAle (by norm_num : (0 : ℝ) ≤ 64)
        linarith
      simp
      linarith
    · simp
    · simp
    · simp
  have hC₀nonneg : 0 ≤ C₀ := by
    rcases hKne with ⟨z, hz⟩
    exact le_trans (norm_nonneg _) (hC₀ z hz)
  refine ⟨max C₀ 1, by positivity, ?_⟩
  intro t σ ht ht10 hσ2 hσlo
  let s : ℂ := ((σ : ℂ) + Complex.I * (t : ℂ))
  have hsre : s.re = σ := by simp [s]
  have hsim : s.im = t := by simp [s]
  have hsK : s ∈ K := by
    dsimp [K]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hzL1 : (1 : ℝ) ≤ zLL t := zLL_ge_one ht
      have hzLpos : 0 < zLL t := zLL_pos ht
      have hq : (cA / 64) / zLL t ≤ cA / 64 := by
        rw [div_le_iff₀ hzLpos]
        exact le_mul_of_one_le_right (by positivity : (0 : ℝ) ≤ cA / 64) hzL1
      rw [hsre]
      linarith
    · rw [hsre]; exact hσ2
    · rw [hsim]; exact ht
    · rw [hsim]; exact ht10
  have hbd := hC₀ s hsK
  have hLp : (1 : ℝ) ≤ zLL t + 1 := zLL_add_one_ge_one (t := t)
  have hpow : (1 : ℝ) ≤ (zLL t + 1) ^ 4 := one_le_pow₀ hLp
  have hC₀le : C₀ ≤ max C₀ 1 := le_max_left C₀ 1
  calc
    ‖(deriv riemannZeta s) / riemannZeta s‖ ≤ C₀ := hbd
    _ ≤ C₀ * (zLL t + 1) ^ 4 := le_mul_of_one_le_right hC₀nonneg hpow
    _ ≤ (max C₀ 1) * (zLL t + 1) ^ 4 := by
      exact mul_le_mul_of_nonneg_right hC₀le (pow_nonneg (by linarith) 4)


/-- **Zero-free region of logarithmic width for ζ, together with a bound for `ζ'/ζ` inside it.**

There are constants `c, C > 0` such that `ζ(σ+it) ≠ 0` for all `|t| ≥ 1` and
`σ ≥ 1 - c/log(|t|+3)`, and on the same region (with `σ ≤ 2`)
`‖ζ'/ζ(σ+it)‖ ≤ C (log(|t|+3)+1)^4`. -/
theorem zeta_zeroFreeRegion_logDeriv_bound :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      (∀ t : ℝ, 1 ≤ |t| → ∀ σ : ℝ, 1 - c / (Real.log (|t| + 3)) ≤ σ →
        riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ) ≠ 0) ∧
      (∀ t : ℝ, 1 ≤ |t| → ∀ σ : ℝ, 1 - c / (Real.log (|t| + 3)) ≤ σ → σ ≤ 2 →
        ‖(deriv riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)) /
            riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)‖ ≤
          C * (Real.log (|t| + 3) + 1) ^ 4) := by
  rcases zeta_zeroFreeRegion_largeHeight with ⟨c₀, T₀, hc₀, hT₀, hZlarge⟩
  have hZlarge' : ∀ t : ℝ, T₀ ≤ |t| → ∀ σ : ℝ, 1 - c₀ / zLL t ≤ σ →
      riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ) ≠ 0 := by
    intro t ht σ hσ
    exact hZlarge t ht σ (by simpa [zLL] using hσ)
  rcases zfr_allHeights c₀ T₀ hc₀ hT₀ hZlarge' with ⟨c₁, hc₁0, hc₁8, hZ₁⟩
  have hc₁le : c₁ ≤ 1 := by linarith
  rcases zeta_logDeriv_bound_largeHeight hc₁0 hc₁le hZ₁ with ⟨CL, hCL0, hLarge⟩
  rcases zeta_logDeriv_bound_boundedHeight hc₁0 hc₁le hZ₁ with ⟨CB, hCB0, hBounded⟩
  refine ⟨c₁ / 64, max CL CB, by positivity, lt_max_of_lt_left hCL0, ?_, ?_⟩
  · intro t ht σ hσ
    have hthalf : (1 / 2 : ℝ) ≤ |t| := by linarith
    have hzLpos : 0 < zLL t := zLL_pos ht
    have hmono : (c₁ / 64) / zLL t ≤ c₁ / zLL t :=
      div_le_div_of_nonneg_right (by linarith) (le_of_lt hzLpos)
    have hσz : 1 - (c₁ / 64) / zLL t ≤ σ := by simpa [zLL] using hσ
    have hσ' : 1 - c₁ / zLL t ≤ σ := by linarith
    exact hZ₁ t σ hthalf hσ'
  · intro t ht σ hσ hσ2
    have hzLnonneg : 0 ≤ zLL t + 1 := by linarith [zLL_nonneg (t := t)]
    have hσz : 1 - (c₁ / 64) / zLL t ≤ σ := by simpa [zLL] using hσ
    by_cases ht10 : |t| ≤ 10
    · have hb := hBounded t σ ht ht10 hσ2 hσz
      calc
        ‖(deriv riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)) /
            riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)‖
            ≤ CB * (zLL t + 1) ^ 4 := hb
        _ ≤ max CL CB * (zLL t + 1) ^ 4 :=
            mul_le_mul_of_nonneg_right (le_max_right CL CB) (pow_nonneg hzLnonneg 4)
    · have ht8 : 8 ≤ |t| := by
        have h : 10 < |t| := lt_of_not_ge ht10
        linarith
      have hb := hLarge t σ ht8 hσ2 hσz
      calc
        ‖(deriv riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)) /
            riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ)‖
            ≤ CL * (zLL t + 1) ^ 4 := hb
        _ ≤ max CL CB * (zLL t + 1) ^ 4 :=
            mul_le_mul_of_nonneg_right (le_max_left CL CB) (pow_nonneg hzLnonneg 4)

end Commons.NumberTheory.Zeta
