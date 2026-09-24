import Mathlib
import Submission.Commons.NumberTheory.Zeta.mangoldt_series_re
import Submission.Commons.NumberTheory.Zeta.summable_vonMangoldt_div_rpow
import Submission.Commons.NumberTheory.Zeta.zeta_zeroFree_near_axis
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_re_bounds

noncomputable section
open Complex Filter Metric Set
open scoped Real Topology BigOperators

namespace Commons.NumberTheory.Zeta

/-- `Re(−ζ′/ζ)(σ + i·t)`. -/
private def logDerivRe (σ t : ℝ) : ℝ :=
  (-deriv riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I)) /
    riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I))).re

private lemma cos_3_4_1 (θ : ℝ) : 3 + 4 * Real.cos θ + Real.cos (2 * θ) =
    2 * (1 + Real.cos θ) ^ 2 := by
  rw [Real.cos_two_mul]
  ring

private lemma cos_341_nonneg (θ : ℝ) : 0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  rw [cos_3_4_1]
  positivity

private lemma summable_mangoldt_cos (σ : ℝ) (hσ : 1 < σ) (t : ℝ) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) *
      Real.cos (t * Real.log ((n + 1 : ℕ) : ℝ)) / ((n + 1 : ℕ) : ℝ) ^ σ) := by
  have hbase : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) /
      ((n + 1 : ℕ) : ℝ) ^ σ) := by
    exact (summable_nat_add_iff 1).2 (summable_vonMangoldt_div_rpow (σ := σ) hσ)
  refine Summable.of_norm ?_
  let f : ℕ → ℝ := fun n : ℕ => (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) *
      Real.cos (t * Real.log ((n + 1 : ℕ) : ℝ)) / ((n + 1 : ℕ) : ℝ) ^ σ
  change Summable (fun n => ‖f n‖)
  apply Summable.of_nonneg_of_le (g := fun n => ‖f n‖)
      (f := fun n => (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ σ)
  · intro n
    exact norm_nonneg _
  · intro n
    have hpos : 0 < (((n + 1 : ℕ) : ℝ) ^ σ) := Real.rpow_pos_of_pos (by positivity : 0 < ((n+1:ℕ):ℝ)) σ
    have hΛ0 : 0 ≤ (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
    have hcos : |Real.cos (t * Real.log ((n + 1 : ℕ) : ℝ))| ≤ 1 := Real.abs_cos_le_one _
    change |(ArithmeticFunction.vonMangoldt (n + 1) : ℝ) * Real.cos (t * Real.log ((n + 1 : ℕ) : ℝ)) /
          (((n + 1 : ℕ) : ℝ) ^ σ)| ≤
        (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) / (((n + 1 : ℕ) : ℝ) ^ σ)
    calc
      |(ArithmeticFunction.vonMangoldt (n + 1) : ℝ) * Real.cos (t * Real.log ((n + 1 : ℕ) : ℝ)) /
          (((n + 1 : ℕ) : ℝ) ^ σ)|
          = (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) * |Real.cos (t * Real.log ((n + 1 : ℕ) : ℝ))| /
              (((n + 1 : ℕ) : ℝ) ^ σ) := by
              rw [abs_div, abs_mul, abs_of_nonneg hΛ0]
              rw [abs_of_nonneg (le_of_lt hpos)]
      _ ≤ (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) / (((n + 1 : ℕ) : ℝ) ^ σ) := by
            have hm : (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) * |Real.cos (t * Real.log ((n + 1 : ℕ) : ℝ))|
                ≤ (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) := by
              exact mul_le_of_le_one_right hΛ0 hcos
            exact div_le_div_of_nonneg_right hm (le_of_lt hpos)
  · simpa [f] using hbase

/-- For `1 < σ` and real `t`: Re(−ζ′/ζ) is the cosine von-Mangoldt series. -/
private lemma logDerivRe_eq_series (σ : ℝ) (hσ : 1 < σ) (t : ℝ) :
    logDerivRe σ t =
      ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) *
        Real.cos (t * Real.log (((n + 1 : ℕ) : ℝ)))) /
          ((((n + 1 : ℕ) : ℝ) ^ σ)) := by
  unfold logDerivRe
  exact mangoldt_series_re σ hσ t

private lemma tsum_three_lin {f g h : ℕ → ℝ} (hf : Summable f) (hg : Summable g) (hh : Summable h)
    (c1 c2 c3 : ℝ) :
    c1 * (∑' n, f n) + c2 * (∑' n, g n) + c3 * (∑' n, h n) =
      ∑' n, (c1 * f n + c2 * g n + c3 * h n) := by
  have hfg : Summable (fun n => c1 * f n + c2 * g n) :=
    (hf.mul_left c1).add (hg.mul_left c2)
  calc
    c1 * (∑' n, f n) + c2 * (∑' n, g n) + c3 * (∑' n, h n)
        = (∑' n, c1 * f n) + (∑' n, c2 * g n) + (∑' n, c3 * h n) := by
            rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
    _ = (∑' n, (c1 * f n + c2 * g n)) + (∑' n, c3 * h n) := by
            rw [← hf.mul_left c1 |>.tsum_add (hg.mul_left c2)]
    _ = ∑' n, (c1 * f n + c2 * g n + c3 * h n) := by
            rw [← hfg.tsum_add (hh.mul_left c3)]

/-- For `1 < σ`: the 3-4-1 inequality `3·ld(σ,0) + 4·ld(σ,t) + ld(σ,2t) ≥ 0`. -/
private lemma logDerivRe_341 (σ : ℝ) (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3 * logDerivRe σ 0 + 4 * logDerivRe σ t + logDerivRe σ (2 * t) := by
  let f0 : ℕ → ℝ := fun n : ℕ => (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) *
      Real.cos ((0 : ℝ) * Real.log ((n + 1 : ℕ) : ℝ)) / ((n + 1 : ℕ) : ℝ) ^ σ
  let ft : ℕ → ℝ := fun n : ℕ => (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) *
      Real.cos (t * Real.log ((n + 1 : ℕ) : ℝ)) / ((n + 1 : ℕ) : ℝ) ^ σ
  let f2 : ℕ → ℝ := fun n : ℕ => (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) *
      Real.cos ((2 * t) * Real.log ((n + 1 : ℕ) : ℝ)) / ((n + 1 : ℕ) : ℝ) ^ σ
  have hs0 : Summable f0 := by simpa [f0] using (summable_mangoldt_cos σ hσ 0)
  have hst : Summable ft := by simpa [ft] using (summable_mangoldt_cos σ hσ t)
  have hs2 : Summable f2 := by simpa [f2] using (summable_mangoldt_cos σ hσ (2 * t))
  rw [logDerivRe_eq_series σ hσ 0, logDerivRe_eq_series σ hσ t, logDerivRe_eq_series σ hσ (2 * t)]
  change 0 ≤ 3 * (∑' n, f0 n) + 4 * (∑' n, ft n) + (∑' n, f2 n)
  rw [← one_mul (∑' n, f2 n)]
  rw [tsum_three_lin hs0 hst hs2 (3 : ℝ) 4 1]
  apply tsum_nonneg
  intro n
  have hΛ0 : 0 ≤ (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
  have hpow : 0 < (((n + 1 : ℕ) : ℝ) ^ σ) := Real.rpow_pos_of_pos (by positivity : 0 < ((n+1:ℕ):ℝ)) σ
  have hco0 : Real.cos ((0 : ℝ) * Real.log ((n + 1 : ℕ) : ℝ)) = 1 := by simp
  have hc2a : Real.cos ((2 * t) * Real.log ((n + 1 : ℕ) : ℝ)) =
      Real.cos (2 * (t * Real.log ((n + 1 : ℕ) : ℝ))) := by
    congr 1
    ring
  have hfacθ : 0 ≤ 3 + 4 * Real.cos (t * Real.log ((n + 1 : ℕ) : ℝ)) +
      Real.cos (2 * (t * Real.log ((n + 1 : ℕ) : ℝ))) := cos_341_nonneg _
  dsimp [f0, ft, f2]
  rw [hco0, hc2a]
  have hmain : (0 : ℝ) ≤ (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) *
      (3 + 4 * Real.cos (t * Real.log ((n + 1 : ℕ) : ℝ)) +
        Real.cos (2 * (t * Real.log ((n + 1 : ℕ) : ℝ)))) /
      (((n + 1 : ℕ) : ℝ) ^ σ) := by
    exact div_nonneg (mul_nonneg hΛ0 hfacθ) (le_of_lt hpow)
  have heq : 3 * ((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) * 1 / (((n + 1 : ℕ) : ℝ) ^ σ)) +
        4 * ((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) *
          Real.cos (t * Real.log ((n + 1 : ℕ) : ℝ)) / (((n + 1 : ℕ) : ℝ) ^ σ)) +
        1 * ((ArithmeticFunction.vonMangoldt (n + 1) : ℝ) *
          Real.cos (2 * (t * Real.log ((n + 1 : ℕ) : ℝ))) / (((n + 1 : ℕ) : ℝ) ^ σ)) =
      (ArithmeticFunction.vonMangoldt (n + 1) : ℝ) *
        (3 + 4 * Real.cos (t * Real.log ((n + 1 : ℕ) : ℝ)) +
          Real.cos (2 * (t * Real.log ((n + 1 : ℕ) : ℝ)))) /
        (((n + 1 : ℕ) : ℝ) ^ σ) := by
    ring_nf
  rwa [heq]

/-- `ζ₁(σ) ≠ 0` for real `σ ∈ [1,2]`. -/
private lemma zeta1_ne_zero_real_seg (σ : ℝ) (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) :
    riemannZeta₁ (σ : ℂ) ≠ 0 := by
  by_cases hσ : σ = 1
  · subst σ
    simp [riemannZeta₁_one]
  · have hs1 : (σ : ℂ) ≠ 1 := by exact_mod_cast hσ
    have hne : riemannZeta (σ : ℂ) ≠ 0 := by
      exact riemannZeta_ne_zero_of_one_le_re (by simpa using hσ1)
    intro hz
    have hz' : riemannZeta (σ : ℂ) = 0 := by
      rw [riemannZeta_eq_inv_sub_mul hs1, hz]
      simp
    exact hne hz'

/-- A uniform bound for `‖ζ₁′/ζ₁(σ)‖` on the real interval `[1,2]`. -/
private lemma zeta1_logDeriv_real_seg_bound :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ σ : ℝ, 1 ≤ σ → σ ≤ 2 →
      ‖deriv riemannZeta₁ (σ : ℂ) / riemannZeta₁ (σ : ℂ)‖ ≤ C₁ := by
  let f : ℝ → ℝ := fun σ : ℝ => ‖deriv riemannZeta₁ ((σ : ℂ)) / riemannZeta₁ ((σ : ℂ))‖
  have hmap : ContinuousOn (fun σ : ℝ => ((σ : ℂ))) (Set.Icc (1 : ℝ) 2) := by
    fun_prop
  have h1 : ContinuousOn (fun σ : ℝ => deriv riemannZeta₁ ((σ : ℂ))) (Set.Icc (1 : ℝ) 2) := by
    exact differentiable_riemannZeta₁.deriv.continuous.comp_continuousOn hmap
  have h2 : ContinuousOn (fun σ : ℝ => riemannZeta₁ ((σ : ℂ))) (Set.Icc (1 : ℝ) 2) := by
    exact differentiable_riemannZeta₁.continuous.comp_continuousOn hmap
  have hnz : ∀ σ ∈ Set.Icc (1 : ℝ) 2, riemannZeta₁ ((σ : ℂ)) ≠ 0 := by
    intro σ hσ
    exact zeta1_ne_zero_real_seg σ hσ.1 hσ.2
  have hfcont : ContinuousOn f (Set.Icc (1 : ℝ) 2) := by
    simpa [f] using (h1.div h2 hnz).norm
  have hKne : (Set.Icc (1 : ℝ) 2).Nonempty := ⟨1, by norm_num⟩
  rcases isCompact_Icc.exists_isMaxOn hKne hfcont with ⟨x, hx, hxmax⟩
  refine ⟨f x, norm_nonneg _, ?_⟩
  intro σ hσ1 hσ2
  exact hxmax ⟨hσ1, hσ2⟩

/-- real-axis log-derivative upper bound: `Re(−ζ′/ζ)(σ) ≤ 1/(σ−1) + C₁` for `1<σ≤2`. -/
private lemma logDerivRe_axis_bound :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      logDerivRe σ 0 ≤ 1 / (σ - 1) + C₁ := by
  rcases zeta1_logDeriv_real_seg_bound with ⟨C₁, hC₁0, hC₁⟩
  refine ⟨C₁, hC₁0, ?_⟩
  intro σ hσ1 hσ2
  have hne1 : (σ : ℂ) ≠ 1 := by
    intro h
    have : (σ : ℝ) = 1 := by exact_mod_cast congrArg Complex.re h
    linarith
  have hζ₁0 : riemannZeta₁ ((σ : ℂ)) ≠ 0 := zeta1_ne_zero_real_seg σ (le_of_lt hσ1) hσ2
  have hid : deriv riemannZeta ((σ : ℂ)) / riemannZeta ((σ : ℂ)) =
      -(((σ : ℂ) - 1)⁻¹) + deriv riemannZeta₁ ((σ : ℂ)) / riemannZeta₁ ((σ : ℂ)) := by
    have hζ : riemannZeta ((σ : ℂ)) = ((σ : ℂ) - 1)⁻¹ * riemannZeta₁ ((σ : ℂ)) :=
      riemannZeta_eq_inv_sub_mul hne1
    have hζder : deriv riemannZeta ((σ : ℂ)) =
        -((σ : ℂ) - 1)⁻¹ ^ 2 * riemannZeta₁ ((σ : ℂ)) + ((σ : ℂ) - 1)⁻¹ * deriv riemannZeta₁ ((σ : ℂ)) :=
      deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hne1
    rw [hζ, hζder]
    field_simp [hζ₁0, hne1]
  have harg : (((σ : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)) = (σ : ℂ) := by simp
  have hnorm : ‖deriv riemannZeta ((σ : ℂ)) / riemannZeta ((σ : ℂ))‖ ≤ 1 / (σ - 1) + C₁ := by
    calc
      ‖deriv riemannZeta ((σ : ℂ)) / riemannZeta ((σ : ℂ))‖
          = ‖-(((σ : ℂ) - 1)⁻¹) + deriv riemannZeta₁ ((σ : ℂ)) / riemannZeta₁ ((σ : ℂ))‖ := by rw [hid]
      _ ≤ ‖-(((σ : ℂ) - 1)⁻¹)‖ + ‖deriv riemannZeta₁ ((σ : ℂ)) / riemannZeta₁ ((σ : ℂ))‖ := by
            exact norm_add_le _ _
      _ ≤ 1 / (σ - 1) + ‖deriv riemannZeta₁ ((σ : ℂ)) / riemannZeta₁ ((σ : ℂ))‖ := by
            have hnn : ‖-(((σ : ℂ) - 1)⁻¹)‖ = 1 / (σ - 1) := by
              have hsub : ((σ : ℂ) - 1) = (((σ - 1 : ℝ) : ℂ)) := by
                apply Complex.ext <;> simp
              rw [norm_neg, hsub]
              rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (by linarith : 0 ≤ σ - 1)]
              ring
            rw [hnn]
      _ ≤ 1 / (σ - 1) + C₁ := by
            exact add_le_add_right (hC₁ σ (le_of_lt hσ1) hσ2) (1 / (σ - 1))
  have hre : logDerivRe σ 0 ≤ ‖-deriv riemannZeta ((σ : ℂ)) / riemannZeta ((σ : ℂ))‖ := by
    unfold logDerivRe
    rw [harg]
    exact Complex.re_le_norm _
  calc
    logDerivRe σ 0 ≤ ‖-deriv riemannZeta ((σ : ℂ)) / riemannZeta ((σ : ℂ))‖ := hre
    _ = ‖deriv riemannZeta ((σ : ℂ)) / riemannZeta ((σ : ℂ))‖ := by rw [neg_div, norm_neg]
    _ ≤ 1 / (σ - 1) + C₁ := hnorm

/-- log lower bound: `log(|γ|+3) ≥ 1` for all real `γ` (since `|γ|+3 ≥ 3 > e`). -/
private lemma log_ge_one (γ : ℝ) : (1 : ℝ) ≤ Real.log (|γ| + 3) := by
  have hpos : 0 < |γ| + 3 := by nlinarith [abs_nonneg γ]
  have he : Real.exp 1 ≤ (3 : ℝ) := le_of_lt Real.exp_one_lt_three
  have hle : Real.exp 1 ≤ |γ| + 3 := by nlinarith [abs_nonneg γ]
  have hlog := Real.log_le_log (by positivity : 0 < Real.exp 1) hle
  rwa [Real.log_exp] at hlog

/-- `L' := log(|γ|+3)+1 ≥ 2`. -/
private lemma Lp_ge_two (γ : ℝ) : (2 : ℝ) ≤ Real.log (|γ| + 3) + 1 := by
  linarith [log_ge_one γ]

/-- `log(|2γ|+3) + 1 ≤ 2·(log(|γ|+3) + 1)`. -/
private lemma log2t_bound (γ : ℝ) : Real.log (|2 * γ| + 3) + 1 ≤ 2 * (Real.log (|γ| + 3) + 1) := by
  have hpos : 0 < |γ| + 3 := by nlinarith [abs_nonneg γ]
  have h2 : |2 * γ| = 2 * |γ| := by
    calc |2 * γ| = |(2 : ℝ)| * |γ| := abs_mul _ _
      _ = 2 * |γ| := by rw [abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
  have hle : |2 * γ| + 3 ≤ (|γ| + 3) ^ 2 := by
    nlinarith [abs_nonneg γ]
  have hpos2 : 0 < |2 * γ| + 3 := by nlinarith [abs_nonneg γ]
  have hlog := Real.log_le_log hpos2 hle
  have hpow : Real.log ((|γ| + 3) ^ 2) = 2 * Real.log (|γ| + 3) := by
    rw [Real.log_pow (|γ| + 3) 2]
    norm_num
  have hmain : Real.log (|2 * γ| + 3) ≤ 2 * Real.log (|γ| + 3) := by
    rwa [hpow] at hlog
  linarith

/-- zero-free region in a fixed strip for bounded height `H` (compactness, general H). -/
private theorem zeta_zeroFree_compact_width (H : ℝ) (hH : (4 : ℝ) ≤ H) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ (t σ : ℝ), |t| ≤ H → 1 - ε₀ ≤ σ → σ ≤ 2 →
        riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ) ≠ 0 := by
  let S₀ : Set ℂ := (fun p : ℝ × ℝ => (p.1 : ℂ) + Complex.I * (p.2 : ℂ)) ''
    (Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (-H) H)
  have hS₀compact : IsCompact S₀ := by
    dsimp [S₀]
    exact (IsCompact.prod isCompact_Icc isCompact_Icc).image
      (by fun_prop : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) + Complex.I * (p.2 : ℂ)))
  let Z : Set ℂ := S₀ ∩ riemannZetaZeros
  have hZfin : Z.Finite := by
    dsimp [Z]
    exact hS₀compact.inter_riemannZetaZeros_finite
  have hZm : ∀ z : ℂ, z ∈ Z →
      (1 / 2 : ℝ) ≤ z.re ∧ z.re ≤ 2 ∧ |z.im| ≤ H ∧ riemannZeta z = 0 := by
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
  · refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
    intro t σ ht hσlo hσhi hz0
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
      have hz₀re_lo : (1 / 2 : ℝ) ≤ z₀.re := (hZm z₀ hz₀Z).1
      have hd : d = 1 - z₀.re := by simpa [d] using hz₀eq.symm
      linarith
    have hd_le : ∀ z : ℂ, z ∈ Z → d ≤ 1 - z.re := by
      intro z hz
      dsimp [d]
      exact Finset.min'_le (fz.image (fun z : ℂ => 1 - z.re))
        (1 - z.re) (Finset.mem_image.mpr ⟨z, (hfz_mem_iff z).2 hz, rfl⟩)
    refine ⟨d / 2, by positivity, ?_⟩
    intro t σ ht hσlo hσhi hz0
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


/-- Algebraic heart of the large-height zero-free region. -/
private lemma region_main_algebra
    {A C C1 L δ : ℝ}
    (hC : 0 < C) (hC1 : 0 ≤ C1) (hL1 : (1 : ℝ) ≤ L)
    (hδ : 0 ≤ δ) (hAeq : A = 6*C + 3*C1 + 2)
    (hineq : 4 / (1 / (A * (L + 1)) + δ) ≤ (3*A + 6*C) * (L + 1) + 3*C1) :
    δ ≥ (A - 6*C) / (4 * A * (3*A + 6*C + 3*C1) * L) := by
  have hLpos : 0 < L := by linarith
  have hApos : 0 < A := by nlinarith
  have hLp : 0 < L + 1 := by linarith
  let D : ℝ := (3*A + 6*C) * (L + 1) + 3*C1
  have hDpos : 0 < D := by
    have h1 : 0 < (3*A + 6*C) * (L + 1) := by
      have hpos3 : 0 < 3*A + 6*C := by nlinarith
      exact mul_pos hpos3 hLp
    dsimp [D]
    linarith
  have hxδpos : 0 < 1 / (A * (L + 1)) + δ := by positivity
  have hineqD : 4 / (1 / (A * (L + 1)) + δ) ≤ D := by simpa [D] using hineq
  have hstep : 1 / (A * (L + 1)) + δ ≥ 4 / D := by
    have hfour : (4 : ℝ) ≤ D * (1 / (A * (L + 1)) + δ) := by
      exact (div_le_iff₀ hxδpos).1 hineqD
    apply (div_le_iff₀ hDpos).2
    nlinarith
  have hδlow : δ ≥ 4 / D - 1 / (A * (L + 1)) := by linarith
  have hmain1 : δ ≥ ((A - 6*C) * (L + 1) - 3*C1) / (A * (L + 1) * D) := by
    have hfrac : 4 / D - 1 / (A * (L + 1)) =
        ((A - 6*C) * (L + 1) - 3*C1) / (A * (L + 1) * D) := by
      dsimp [D]
      field_simp [ne_of_gt hApos, ne_of_gt hLp]
      ring
    rwa [← hfrac]
  have hnum : (A - 6*C) * (L + 1) - 3*C1 ≥ (A - 6*C) * (L + 1) / 2 := by
    have hA6 : A - 6*C = 3*C1 + 2 := by nlinarith
    have hbig : (A - 6*C) * (L + 1) ≥ 6*C1 := by nlinarith
    nlinarith
  have hden : A * (L + 1) * D ≤ A * (3*A + 6*C + 3*C1) * (L + 1) * (L + 1) := by
    have hle1 : (3*A + 6*C) * (L + 1) + 3*C1 ≤ (3*A + 6*C + 3*C1) * (L + 1) := by nlinarith
    dsimp [D]
    nlinarith
  have hPpos : 0 < A * (L + 1) * D := mul_pos (mul_pos hApos hLp) hDpos
  let N : ℝ := (A - 6*C) * (L + 1) - 3*C1
  let N0 : ℝ := (A - 6*C) * (L + 1) / 2
  let P0 : ℝ := A * (3*A + 6*C + 3*C1) * (L + 1) * (L + 1)
  have hA6 : A - 6*C = 3*C1 + 2 := by nlinarith
  have hA6pos : 0 < A - 6*C := by nlinarith
  have hP0pos : 0 < P0 := by
    have h1 : 0 < A * (3*A + 6*C + 3*C1) := by
      have h2 : 0 < 3*A + 6*C + 3*C1 := by nlinarith
      exact mul_pos hApos h2
    dsimp [P0]
    exact mul_pos (mul_pos h1 hLp) hLp
  have hN0pos : 0 ≤ N0 := by
    dsimp [N0]
    positivity
  have hstepN : N0 ≤ N := by
    dsimp [N, N0]
    nlinarith
  have hstepP : A * (L + 1) * D ≤ P0 := by
    dsimp [P0]
    exact hden
  have hdiv2 : N0 / P0 ≤ N / (A * (L + 1) * D) := by
    rw [div_le_div_iff₀ hP0pos hPpos]
    have h1 : N0 * (A * (L + 1) * D) ≤ N0 * P0 := by
      exact mul_le_mul_of_nonneg_left hstepP hN0pos
    have h2 : N0 * P0 ≤ N * P0 := by
      exact mul_le_mul_of_nonneg_right hstepN (le_of_lt hP0pos)
    nlinarith
  have hfracN0 : N0 / P0 = (A - 6*C) / (2 * A * (3*A + 6*C + 3*C1) * (L + 1)) := by
    dsimp [N0, P0]
    field_simp [ne_of_gt hApos, ne_of_gt hLp, ne_of_gt (by nlinarith : 0 < 3*A + 6*C + 3*C1)]
  have hden2pos : 0 < 2 * A * (3*A + 6*C + 3*C1) * (L + 1) := by
    have h2 : 0 < 3*A + 6*C + 3*C1 := by nlinarith
    exact mul_pos (mul_pos (mul_pos (by norm_num) hApos) h2) hLp
  have htarget_mid : (A - 6*C) / (4 * A * (3*A + 6*C + 3*C1) * L) ≤
      (A - 6*C) / (2 * A * (3*A + 6*C + 3*C1) * (L + 1)) := by
    have hb : 2 * A * (3*A + 6*C + 3*C1) * (L + 1) ≤ 4 * A * (3*A + 6*C + 3*C1) * L := by nlinarith
    exact div_le_div_of_nonneg_left (le_of_lt hA6pos) hden2pos hb
  have hfinal1 : N0 / P0 ≤ δ := le_trans hdiv2 hmain1
  have hfinal2 : (A - 6*C) / (2 * A * (3*A + 6*C + 3*C1) * (L + 1)) ≤ δ := by
    rw [← hfracN0]
    exact hfinal1
  exact le_trans htarget_mid hfinal2

/-- Large-height zero-free region for ζ: zeros at height `≥ H` satisfy
`1 − β ≥ c/log(|γ|+3)`. -/
private lemma large_height_zero_free
    {C H : ℝ} (hC : 0 < C) (hH : (2 : ℝ) ≤ H)
    (hA : ∀ t σ : ℝ, H ≤ |t| → 1 < σ → σ ≤ 2 →
        logDerivRe σ t ≤ C * (Real.log (|t| + 3) + 1))
    (hB : ∀ t β : ℝ, H ≤ |t| → (1 / 2 : ℝ) ≤ β → β < 1 →
        riemannZeta (((β : ℂ) + (t : ℂ) * Complex.I)) = 0 →
        ∀ x : ℝ, 0 < x → x ≤ 1 / 2 →
        logDerivRe (1 + x) t ≤ - (1 / (x + (1 - β))) + C * (Real.log (|t| + 3) + 1))
    {C1 : ℝ} (hC1 : 0 ≤ C1)
    (h1 : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → logDerivRe σ 0 ≤ 1 / (σ - 1) + C1) :
    ∃ c : ℝ, 0 < c ∧ ∀ γ β : ℝ, H ≤ |γ| → (1 / 2 : ℝ) ≤ β → β < 1 →
        riemannZeta (((β : ℂ) + (γ : ℂ) * Complex.I)) = 0 →
        (1 - β) ≥ c / Real.log (|γ| + 3) := by
  let A : ℝ := 6*C + 3*C1 + 2
  have hApos : 0 < A := by
    dsimp [A]
    nlinarith
  have hC1p : 0 < 3*C1 + 2 := by nlinarith
  refine ⟨(A - 6*C) / (4 * A * (3*A + 6*C + 3*C1)), ?hcpos, ?hclaim⟩
  · have hA6 : 0 < A - 6*C := by
      dsimp [A]
      nlinarith
    have hdenpos : 0 < 4 * A * (3*A + 6*C + 3*C1) := by
      have h2 : 0 < 3*A + 6*C + 3*C1 := by
        dsimp [A]
        nlinarith
      exact mul_pos (mul_pos (by norm_num) hApos) h2
    positivity
  · intro γ β hHγ hβ1 hβ2 hzero
    let L : ℝ := Real.log (|γ| + 3)
    let δ : ℝ := 1 - β
    have hL1 : (1 : ℝ) ≤ L := by
      dsimp [L]
      exact log_ge_one γ
    have hLpos : 0 < L := by linarith
    have hδ0 : 0 ≤ δ := by
      dsimp [δ]
      linarith
    have hAeq : A = 6*C + 3*C1 + 2 := by rfl
    let x : ℝ := 1 / (A * (L + 1))
    have hx0 : 0 < x := by
      dsimp [x]
      positivity
    have hxhalf : x ≤ 1 / 2 := by
      dsimp [x]
      have hden : 0 < A * (L + 1) := mul_pos hApos (by linarith)
      rw [div_le_iff₀ hden]
      -- 1 ≤ (A*(L+1)) / 2: 
      nlinarith [hApos, hL1]
    have hx1 : x ≤ 1 := by linarith
    have hσlt : 1 < 1 + x := by linarith
    have hσle : 1 + x ≤ 2 := by linarith
    have hld0 : logDerivRe (1 + x) 0 ≤ 1 / x + C1 := by
      have hb := h1 (1 + x) hσlt hσle
      have hxeq : (1 + x) - 1 = x := by ring
      rwa [hxeq] at hb
    have hldB : logDerivRe (1 + x) γ ≤ - (1 / (x + δ)) + C * (L + 1) := by
      have hb := hB γ β hHγ hβ1 hβ2 hzero x hx0 hxhalf
      have hlog : Real.log (|γ| + 3) + 1 = L + 1 := by rfl
      have hdel : x + (1 - β) = x + δ := by rfl
      rw [hdel]
      rwa [hlog] at hb
    have hldK : logDerivRe (1 + x) (2 * γ) ≤ 2 * C * (L + 1) := by
      have hH2g : H ≤ |2 * γ| := by
        have h : |2 * γ| = 2 * |γ| := by
          calc |2 * γ| = |(2 : ℝ)| * |γ| := abs_mul _ _
            _ = 2 * |γ| := by rw [abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
        rw [h]
        nlinarith
      have hb := hA (2 * γ) (1 + x) hH2g hσlt hσle
      have hlog2 := log2t_bound γ
      have hc : 0 ≤ C := le_of_lt hC
      calc
        logDerivRe (1 + x) (2 * γ) ≤ C * (Real.log (|2 * γ| + 3) + 1) := hb
        _ ≤ C * (2 * (Real.log (|γ| + 3) + 1)) := mul_le_mul_of_nonneg_left hlog2 hc
        _ = 2 * C * (L + 1) := by
          dsimp [L]
          ring
    have h341 := logDerivRe_341 (1 + x) hσlt γ
    -- combine:
    have hb0 : 3 * logDerivRe (1 + x) 0 ≤ 3 * (1 / x + C1) := by
      exact mul_le_mul_of_nonneg_left hld0 (by norm_num)
    have hbB : 4 * logDerivRe (1 + x) γ ≤ 4 * (- (1 / (x + δ)) + C * (L + 1)) := by
      exact mul_le_mul_of_nonneg_left hldB (by norm_num)
    have hbK : logDerivRe (1 + x) (2 * γ) ≤ 2 * C * (L + 1) := hldK
    have htop : 3 * logDerivRe (1 + x) 0 + 4 * logDerivRe (1 + x) γ + logDerivRe (1 + x) (2 * γ) ≤
        3 * (1 / x + C1) + 4 * (- (1 / (x + δ)) + C * (L + 1)) + 2 * C * (L + 1) := by
      nlinarith
    have hineq0 : 0 ≤ 3 * (1 / x + C1) + 4 * (- (1 / (x + δ)) + C * (L + 1)) + 2 * C * (L + 1) := by
      exact le_trans h341 htop
    -- rewrite 3/x = 3A(L+1):
    have hxeq : x = 1 / (A * (L + 1)) := by rfl
    have hineq : 4 / (x + δ) ≤ (3*A + 6*C) * (L + 1) + 3*C1 := by
      have hre : 3 * (1 / x + C1) + 4 * (- (1 / (x + δ)) + C * (L + 1)) + 2 * C * (L + 1)
          = 3 / x + 3*C1 - 4 / (x + δ) + 6 * C * (L + 1) := by ring
      have h0' : 0 ≤ 3 / x + 3*C1 - 4 / (x + δ) + 6 * C * (L + 1) := by
        rwa [hre] at hineq0
      have hlin : 4 / (x + δ) ≤ 3 / x + 3*C1 + 6*C * (L + 1) := by
        nlinarith
      have h3x : 3 / x = 3 * A * (L + 1) := by
        rw [hxeq]
        field_simp [hApos.ne', (by linarith : (L + 1 : ℝ) ≠ 0)]
      rw [h3x] at hlin
      nlinarith
    have hineq2 : 4 / (1 / (A * (L + 1)) + δ) ≤ (3*A + 6*C) * (L + 1) + 3*C1 := by
      dsimp [x] at hineq
      exact hineq
    have hdelta := region_main_algebra (C := C) (C1 := C1) (A := A) (L := L) (δ := δ)
      hC hC1 hL1 hδ0 hAeq hineq2
    have hdiv_eq : (A - 6*C) / (4 * A * (3*A + 6*C + 3*C1)) / L =
        (A - 6*C) / (4 * A * (3*A + 6*C + 3*C1) * L) := by
      field_simp [hLpos.ne']
    have hdelta' : (1 - β) ≥ (A - 6*C) / (4 * A * (3*A + 6*C + 3*C1)) / L := by
      dsimp [δ] at hdelta
      rwa [hdiv_eq]
    simpa using hdelta'


/-- **The large-height zero-free region for the Riemann zeta function**
(de la Vallée Poussin): there are constants `c₀ > 0`, `T₀ > 0` such that
`ζ(σ + i·t) ≠ 0` whenever `T₀ ≤ |t|` and `1 − c₀/log(|t|+3) ≤ σ`. -/
theorem zeta_zeroFreeRegion_largeHeight :
    ∃ c₀ T₀ : ℝ, 0 < c₀ ∧ 0 < T₀ ∧
      ∀ t : ℝ, T₀ ≤ |t| → ∀ σ : ℝ, 1 - c₀ / Real.log (|t| + 3) ≤ σ →
        riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ) ≠ 0 := by
  obtain ⟨C1, hC10, h1⟩ := logDerivRe_axis_bound
  obtain ⟨C, hCpos, H, hH2, hA, hB⟩ := zeta_logDeriv_re_bounds
  obtain ⟨cM, hcMpos, hMain⟩ :=
    large_height_zero_free hCpos hH2
      (fun t σ ht hσ1 hσ2 => hA t ht σ hσ1 hσ2)
      (fun t β ht hβ1 hβ2 hz x hx0 hxh => hB t ht β hβ1 hβ2 hz x hx0 hxh)
      hC10 h1
  let T₀ : ℝ := max H 4
  have hT₀geH : H ≤ T₀ := le_max_left H 4
  have hT₀ge4 : (4 : ℝ) ≤ T₀ := le_max_right H 4
  have hT₀pos : 0 < T₀ := by
    dsimp [T₀]
    positivity
  obtain ⟨ε, hεpos, hBox⟩ := zeta_zeroFree_compact_width T₀ hT₀ge4
  have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  let c₀ : ℝ := min (min (cM / 2) (ε * Real.log 3 / 2)) ((Real.log 3) / 2)
  have hc0pos : 0 < c₀ := by
    dsimp [c₀]
    have h1p : 0 < cM / 2 := half_pos hcMpos
    have h2p : 0 < ε * Real.log 3 / 2 := by positivity
    have h3p : 0 < (Real.log 3) / 2 := half_pos hlog3pos
    exact lt_min (lt_min h1p h2p) h3p
  have hc0_le_cM : c₀ ≤ cM / 2 := by
    dsimp [c₀]
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hc0_le_box : c₀ ≤ ε * Real.log 3 / 2 := by
    dsimp [c₀]
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hc0_le_half : c₀ ≤ (Real.log 3) / 2 := by
    dsimp [c₀]
    exact min_le_right _ _
  refine ⟨c₀, T₀, hc0pos, hT₀pos, ?_⟩
  intro t ht σ hσ
  have hLtpos : 0 < Real.log (|t| + 3) := by
    apply Real.log_pos
    nlinarith [abs_nonneg t]
  have hLge3 : Real.log 3 ≤ Real.log (|t| + 3) := by
    exact Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg t])
  by_cases hσ1 : 1 ≤ σ
  · exact riemannZeta_ne_zero_of_one_le_re (s := ((σ : ℂ) + Complex.I * (t : ℂ))) (by simpa using hσ1)
  · have hσlt1 : σ < 1 := lt_of_not_ge hσ1
    by_cases htT : |t| ≤ T₀
    · apply hBox t σ htT ?_ ?_
      · have hle1 : c₀ / Real.log (|t| + 3) ≤ ε := by
          have hc_le : c₀ ≤ ε * Real.log (|t| + 3) := by
            have hc01 : c₀ ≤ ε * Real.log 3 / 2 := hc0_le_box
            have hB : ε * Real.log 3 / 2 ≤ ε * Real.log (|t| + 3) := by
              have hA0 : ε * Real.log 3 / 2 ≤ ε * Real.log 3 := by
                have hlog3n : 0 ≤ Real.log 3 := le_of_lt hlog3pos
                nlinarith
              have hA1 : ε * Real.log 3 ≤ ε * Real.log (|t| + 3) := by
                exact mul_le_mul_of_nonneg_left hLge3 (le_of_lt hεpos)
              linarith
            linarith
          exact (div_le_iff₀ hLtpos).2 hc_le
        linarith
      · linarith
    · have hTle : T₀ ≤ |t| := le_of_not_ge htT
      have hHle : H ≤ |t| := le_trans hT₀geH hTle
      have hσhalf : (1 / 2 : ℝ) ≤ σ := by
        have hle2 : c₀ / Real.log (|t| + 3) ≤ 1 / 2 := by
          have hc_le : c₀ ≤ (Real.log (|t| + 3)) / 2 := by
            have hmono : Real.log 3 / 2 ≤ Real.log (|t| + 3) / 2 := by
              exact div_le_div_of_nonneg_right hLge3 (by norm_num)
            linarith
          exact (div_le_iff₀ hLtpos).2 (by nlinarith)
        linarith
      intro hz0
      have hz0' : riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I)) = 0 := by
        have harg : ((σ : ℂ) + Complex.I * (t : ℂ)) = ((σ : ℂ) + (t : ℂ) * Complex.I) := by ring
        simpa [harg] using hz0
      have hbig := hMain t σ hHle hσhalf hσlt1 hz0'
      have hcontra1 : 1 - σ ≤ c₀ / Real.log (|t| + 3) := by linarith
      have hsmall2 : c₀ / Real.log (|t| + 3) < cM / Real.log (|t| + 3) := by
        have hc : c₀ < cM := by
          have h1p : cM / 2 < cM := half_lt_self hcMpos
          linarith [hc0_le_cM]
        rw [div_lt_div_iff₀ hLtpos hLtpos]
        nlinarith
      exact (not_lt_of_ge (le_trans hbig hcontra1)) hsmall2

end Commons.NumberTheory.Zeta
