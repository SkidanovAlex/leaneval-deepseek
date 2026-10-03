import Mathlib
import Submission.Work.KMTPlan.A6.LowSmallAux
import Submission.Work.KMTAreas.A7.kmtA7_periodize_bumps_memLp

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger

/-! ## Elementary facts about the bumps

The two symbols `varphiNt` and `varphitildeNt` are measurable (they are `C²`), bounded by `2`, and
supported in a ball of radius `2^{k - Log N}` resp. `2^{d(k₂ - Log N)}`; the latter is at most
`2^k` resp. `2^{d k₂}` because `Log N ≥ 0`. -/

private lemma norm_ee_eq_one' (a : ℝ) : ‖Work.KMTAreas.A7.ee a‖ = 1 := by
  rw [Work.KMTAreas.A7.ee, Complex.norm_exp]
  have h : (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  rw [h, Real.exp_zero]

/-- The modulated bump `varphiNt` is bounded by `2`. -/
private lemma norm_varphiNt_le_two' (N k : ℕ) (t : ℝ) (ξ : ℝ) :
    ‖Work.KMTAreas.A7.varphiNt N k t ξ‖ ≤ 2 := by
  rw [Work.KMTAreas.A7.varphiNt, norm_mul, norm_ee_eq_one', mul_one]
  exact Work.KMTAreas.A7.norm_varphiN_le_two N k ξ

/-- The `d`-fold rescaled bump `varphitildeN` is bounded by `2`. -/
private lemma norm_varphitildeN_le_two' (d N k : ℕ) (ξ : ℝ) :
    ‖Work.KMTAreas.A7.varphitildeN d N k ξ‖ ≤ 2 := by
  unfold Work.KMTAreas.A7.varphitildeN
  split_ifs with hk
  · exact le_trans (Work.KMTContract.norm_kmtEta_le _) (by norm_num)
  · calc ‖Work.KMTContract.kmtEta _ - Work.KMTContract.kmtEta _‖
        ≤ ‖Work.KMTContract.kmtEta _‖ + ‖Work.KMTContract.kmtEta _‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (Work.KMTContract.norm_kmtEta_le _)
          (Work.KMTContract.norm_kmtEta_le _)
      _ = 2 := by norm_num

/-- The modulated `d`-fold bump `varphitildeNt` is bounded by `2`. -/
private lemma norm_varphitildeNt_le_two' (P : Polynomial ℤ) (d N k : ℕ) (t : ℝ) (ξ : ℝ) :
    ‖Work.KMTAreas.A7.varphitildeNt P d N k t ξ‖ ≤ 2 := by
  rw [Work.KMTAreas.A7.varphitildeNt, norm_mul, norm_ee_eq_one', mul_one]
  exact norm_varphitildeN_le_two' d N k ξ

/-- The modulated `d`-fold bump `varphitildeNt` is continuous, hence measurable. -/
private lemma measurable_varphitildeNt' (P : Polynomial ℤ) (d N k : ℕ) (t : ℝ) :
    Measurable (Work.KMTAreas.A7.varphitildeNt P d N k t) := by
  rw [show Work.KMTAreas.A7.varphitildeNt P d N k t
      = fun ξ : ℝ => Work.KMTAreas.A7.varphitildeN d N k ξ *
          Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((N : ℝ) * t) * ξ) from rfl]
  exact ((Work.KMTAreas.A7.contDiff_varphitildeN d N k).continuous.measurable).mul
    (((Work.KMTAreas.A7.contDiff_ee_const_mul 2
        (Work.KMTAreas.A7.PevalR P ((N : ℝ) * t))).continuous).measurable)

/-- **The periodisation of a randomised symbol is in `L^∞(ℝ/ℤ)`.**  If every member `φ n` of the
family is measurable, bounded by `B` and supported in `|ξ| ≤ R`, then the finite sum
`randSymb φ ε K = ∑_{n < K} ε n • (φ (n+1) - φ n)` is supported in `|ξ| ≤ R` too (a nonzero value
forces one of the `φ n`, `n ≤ K`, to be nonzero) and bounded by `∑_{n<K} 2‖ε n‖B`.  No hypothesis
on the coefficients `ε` is needed. -/
private lemma memLp_periodize_randSymb_of {φ : ℕ → ℝ → ℂ} {R B : ℝ} (hR : 0 ≤ R)
    (hmeas : ∀ n : ℕ, Measurable (φ n))
    (harc : ∀ (n : ℕ) (ξ : ℝ), φ n ξ ≠ 0 → |ξ| ≤ R)
    (hbd : ∀ (n : ℕ) (ξ : ℝ), ‖φ n ξ‖ ≤ B) (ε : ℕ → ℂ) (K : ℕ) :
    MeasureTheory.MemLp
      (Work.Analysis.IonescuWainger.periodize (Work.KMTAreas.A7.randSymb φ ε K)) ⊤
      Work.Analysis.IonescuWainger.circleMeasure := by
  refine Work.Analysis.IonescuWainger.memLp_periodize ?_ hR ?_
    (C := ∑ n ∈ Finset.range K, ‖ε n‖ * (B + B)) ?_
  · unfold Work.KMTAreas.A7.randSymb
    exact Finset.measurable_sum _ fun n _ => ((hmeas (n + 1)).sub (hmeas n)).const_mul (ε n)
  · intro x hx
    unfold Work.KMTAreas.A7.randSymb
    refine Finset.sum_eq_zero fun n _ => ?_
    by_contra hne
    have h1 : φ (n + 1) x ≠ 0 ∨ φ n x ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (by simp [h.1, h.2])
    rcases h1 with h1 | h1
    · exact absurd (harc (n + 1) x h1) (not_le.mpr hx)
    · exact absurd (harc n x h1) (not_le.mpr hx)
  · intro x
    unfold Work.KMTAreas.A7.randSymb
    calc ‖∑ n ∈ Finset.range K, ε n * (φ (n + 1) x - φ n x)‖
        ≤ ∑ n ∈ Finset.range K, ‖ε n * (φ (n + 1) x - φ n x)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range K, ‖ε n‖ * (B + B) := by
          refine Finset.sum_le_sum fun n _ => ?_
          rw [norm_mul]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          calc ‖φ (n + 1) x - φ n x‖ ≤ ‖φ (n + 1) x‖ + ‖φ n x‖ := norm_sub_le _ _
            _ ≤ B + B := add_le_add (hbd (n + 1) x) (hbd n x)

/-! `randSymb φ ε K = ∑_{n<K} ε n • (φ (n+1) - φ n)` is a finite sum of bounded, compactly
supported, measurable functions (each `lowSymbF`/`lowSymbG` value is `0` or one of the modulated
bumps `varphiNt`/`varphitildeNt`, which are differences of rescalings of the fixed cutoff `kmtEta`),
so its periodisation lies in `L^∞(circleMeasure)`; use
`Work.Analysis.IonescuWainger.memLp_periodize` (instantiated for these bumps in
`Work.KMTAreas.A7.kmtA7_memLp_periodize_varphiNt` /
`…kmtA7_memLp_periodize_varphitildeNt`) together with `MeasureTheory.MemLp` closure under finite
sums, differences and scalar multiples (see the `Finset`-sum forms in `MeasureTheory.MemLp`).
No lacunarity or `ρ`-hypothesis is needed. -/
theorem memLp_periodize_randSymb_lowSymb (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal)
    (l₁ l₂ k₁ k₂ K : ℕ) (t : ℝ) (ε : ℕ → ℂ) :
    (MeasureTheory.MemLp (Work.Analysis.IonescuWainger.periodize
        (Work.KMTAreas.A7.randSymb (Work.KMTPlan.A6.lowSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε K)) ⊤
        Work.Analysis.IonescuWainger.circleMeasure) ∧
    (MeasureTheory.MemLp (Work.Analysis.IonescuWainger.periodize
        (Work.KMTAreas.A7.randSymb (Work.KMTPlan.A6.lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε K)) ⊤
        Work.Analysis.IonescuWainger.circleMeasure) := by
  have hmeasF : ∀ n : ℕ, Measurable (lowSymbF ρ C₀ a l₁ l₂ k₁ k₂ t n) := by
    intro n
    by_cases hn0 : n = 0
    · subst hn0
      rw [lowSymbF_zero]
      exact measurable_zero
    · by_cases hls : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n
      · have hfun : lowSymbF ρ C₀ a l₁ l₂ k₁ k₂ t n
            = Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t := by
          funext ξ
          simp [lowSymbF, hn0, hls]
        rw [hfun]
        exact (Work.KMTAreas.A7.contDiff_varphiNt (Nat.floor (a n)) k₁ t).continuous.measurable
      · have hfun : lowSymbF ρ C₀ a l₁ l₂ k₁ k₂ t n = 0 := by
          funext ξ
          simp [lowSymbF, hn0, hls]
        rw [hfun]
        exact measurable_zero
  have harcF : ∀ (n : ℕ) (ξ : ℝ), lowSymbF ρ C₀ a l₁ l₂ k₁ k₂ t n ξ ≠ 0 →
      |ξ| ≤ (2 : ℝ) ^ (k₁ : ℝ) := by
    intro n ξ hne
    simp only [lowSymbF] at hne
    by_cases hn0 : n = 0
    · rw [if_pos hn0] at hne
      exact absurd rfl hne
    · rw [if_neg hn0] at hne
      by_cases hls : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n
      · rw [if_pos hls] at hne
        refine (Work.KMTAreas.A7.varphiNt_support (Nat.floor (a n)) k₁ t ξ hne).trans ?_
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        have hl := Work.Analysis.EndVar.logN_nonneg (Nat.floor (a n))
        have hl' : (0 : ℝ) ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ) := by
          exact_mod_cast hl
        linarith
      · rw [if_neg hls] at hne
        exact absurd rfl hne
  have hbdF : ∀ (n : ℕ) (ξ : ℝ), ‖lowSymbF ρ C₀ a l₁ l₂ k₁ k₂ t n ξ‖ ≤ 2 := by
    intro n ξ
    simp only [lowSymbF]
    by_cases hn0 : n = 0
    · rw [if_pos hn0]
      norm_num
    · rw [if_neg hn0]
      by_cases hls : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n
      · rw [if_pos hls]
        exact norm_varphiNt_le_two' (Nat.floor (a n)) k₁ t ξ
      · rw [if_neg hls]
        norm_num
  have hmeasG : ∀ n : ℕ, Measurable (lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t n) := by
    intro n
    by_cases hn0 : n = 0
    · subst hn0
      rw [lowSymbG_zero]
      exact measurable_zero
    · by_cases hls : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n
      · have hfun : lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t n
            = Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t := by
          funext ξ
          simp [lowSymbG, hn0, hls]
        rw [hfun]
        exact measurable_varphitildeNt' P P.natDegree (Nat.floor (a n)) k₂ t
      · have hfun : lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t n = 0 := by
          funext ξ
          simp [lowSymbG, hn0, hls]
        rw [hfun]
        exact measurable_zero
  have harcG : ∀ (n : ℕ) (ξ : ℝ), lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t n ξ ≠ 0 →
      |ξ| ≤ (2 : ℝ) ^ ((P.natDegree : ℝ) * (k₂ : ℝ)) := by
    intro n ξ hne
    simp only [lowSymbG] at hne
    by_cases hn0 : n = 0
    · rw [if_pos hn0] at hne
      exact absurd rfl hne
    · rw [if_neg hn0] at hne
      by_cases hls : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n
      · rw [if_pos hls] at hne
        refine (Work.KMTAreas.A7.varphitildeNt_support_all P P.natDegree
          (Nat.floor (a n)) k₂ t ξ hne).trans ?_
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        have hl := Work.Analysis.EndVar.logN_nonneg (Nat.floor (a n))
        have hl' : (0 : ℝ) ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ) := by
          exact_mod_cast hl
        have hd : (0 : ℝ) ≤ (P.natDegree : ℝ) := by positivity
        nlinarith
      · rw [if_neg hls] at hne
        exact absurd rfl hne
  have hbdG : ∀ (n : ℕ) (ξ : ℝ), ‖lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t n ξ‖ ≤ 2 := by
    intro n ξ
    simp only [lowSymbG]
    by_cases hn0 : n = 0
    · rw [if_pos hn0]
      norm_num
    · rw [if_neg hn0]
      by_cases hls : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n
      · rw [if_pos hls]
        exact norm_varphitildeNt_le_two' P P.natDegree (Nat.floor (a n)) k₂ t ξ
      · rw [if_neg hls]
        norm_num
  exact ⟨memLp_periodize_randSymb_of (φ := lowSymbF ρ C₀ a l₁ l₂ k₁ k₂ t)
      (R := (2 : ℝ) ^ (k₁ : ℝ)) (B := 2) (Real.rpow_nonneg (by norm_num) _)
      hmeasF harcF hbdF ε K,
    memLp_periodize_randSymb_of (φ := lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t)
      (R := (2 : ℝ) ^ ((P.natDegree : ℝ) * (k₂ : ℝ))) (B := 2)
      (Real.rpow_nonneg (by norm_num) _) hmeasG harcG hbdG ε K⟩

end Work.KMTPlan.A6
