/-
# Plumbing for the Ionescu--Wainger fibre route to the §7 single-scale estimate

This module collects the elementary identifications on which the assembly
`Work.KMTAreas.A7.smallModelSingleScale_of_fibre` rests:

* `fiberOpD_eq_sub_fiberOpCum` — the *exact-height* fibre `fiberOpD ρ l m n₀` (kernel
  `j ↦ C_l(n₀-j) cw m j`, `C_l` the exact-height arithmetic character) is the difference of the two
  *cumulative-height* fibres `fiberOpCum ρ l` and `fiberOpCum ρ (l-1)` (for `l ≥ 1`); this is
  `Finset.sum_sdiff` in the frequency set plus the `tsum` linearity along the `j`-sum.
* `eLpNorm_fiberOpD_le_of_fiberOpCum` — consequently the `ℓ^p` bound for the exact-height fibre
  follows from the two cumulative bounds (subadditivity of `eLpNorm`).
* `mStargF_eq_mStarF` — `mStargF d u = mStarF (d*u)`, so the `g`-side fibre is covered by the
  `fStar`-symbol estimate.
* the degenerate-case helpers (`eq_zero_of_eLpNorm_count_eq_zero`: on `ℤ` with counting measure an
  `ℒ^p`-vanishing function vanishes *pointwise*; `smallBtwist` vanishes when an argument vanishes).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.SmallFibreDefs
import Submission.Work.KMTAreas.A7.FibreCum
import Submission.Work.KMTAreas.A7.LoErrAux
import Submission.Work.KMTAreas.A7.Tle_varphitildeNt_bounded
import Submission.Work.KMTAreas.A7.bounded_of_eLpNorm_count_lt_top
import Submission.Work.KMTAreas.A7.FiberGeneral

set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace Work.KMTAreas.A7

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger

noncomputable section

/-! ## Degenerate cases -/

/-- On `ℤ` with counting measure a function of vanishing `ℒ^p` seminorm (`p ≠ 0`) is identically
zero: every set is measurable (the measurable space of `ℤ` is discrete) and the counting measure
has no non-empty null sets. -/
theorem eq_zero_of_eLpNorm_count_eq_zero {p : ENNReal} (hp : p ≠ 0) {u : ℤ → ℂ}
    (h : eLpNorm u p (Measure.count : Measure ℤ) = 0) : u = 0 := by
  have hsm : AEStronglyMeasurable u (Measure.count : Measure ℤ) :=
    AEStronglyMeasurable.of_discrete
  have h0 : u =ᵐ[Measure.count] 0 := (eLpNorm_eq_zero_iff hp).mp h
  have hnull : Measure.count {m : ℤ | u m ≠ 0} = 0 := ae_iff.mp h0
  funext n
  by_contra hn
  have hne : Measure.count {m : ℤ | u m ≠ 0} ≠ 0 := by
    rw [Measure.count_ne_zero_iff]
    exact ⟨n, hn⟩
  exact hne hnull

/-- `smallBtwist` vanishes when its first argument vanishes. -/
theorem smallBtwist_eq_zero_of_left (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (k : ℤ → ℂ) : smallBtwist ρ P l₁ l₂ m₁ m₂ 0 k = 0 := by
  funext x
  simp only [smallBtwist]
  simp

/-- `smallBtwist` vanishes when its second argument vanishes. -/
theorem smallBtwist_eq_zero_of_right (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (h : ℤ → ℂ) : smallBtwist ρ P l₁ l₂ m₁ m₂ h 0 = 0 := by
  funext x
  simp only [smallBtwist]
  simp

/-- The `g`-side model symbol at height `d·2·u` is the `f`-side model symbol at height `2·(d·u)`. -/
theorem mStargF_eq_mStarF (P : Polynomial ℤ) (u : ℕ) :
    mStargF P.natDegree u = mStarF (P.natDegree * u) := by
  unfold mStargF mStarF
  congr 1
  push_cast
  ring

/-! ## The exact-height fibre as a difference of cumulative fibres -/

/-- Summability of the kernel of the cumulative fibre `fiberOpCum ρ l m n₀ v` at a point `x`, for
bounded `v` and `ℓ¹`-summable `cw m`. -/
theorem summable_char_mul {A : Finset Work.Analysis.IonescuWainger.Circle} {m : ℝ → ℂ} {v : ℤ → ℂ} {n₀ x : ℤ} {Cv : ℝ}
    (hv : ∀ y : ℤ, ‖v y‖ ≤ Cv) (hcw : Summable (fun j : ℤ => ‖cw m j‖)) :
    Summable (fun j : ℤ => (∑ α ∈ A, fourier (T := 1) (n₀ - j) α) * cw m j * v (x - j)) := by
  refine Summable.of_norm_bounded (hcw.mul_left ((A.card : ℝ) * max Cv 1)) (fun j => ?_)
  have h1 : ‖∑ α ∈ A, fourier (T := 1) (n₀ - j) α‖ ≤ (A.card : ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    simp only [norm_fourier_apply_]
    simp
  have hv' : ‖v (x - j)‖ ≤ max Cv 1 := le_trans (hv _) (le_max_left _ _)
  calc ‖(∑ α ∈ A, fourier (T := 1) (n₀ - j) α) * cw m j * v (x - j)‖
      = ‖∑ α ∈ A, fourier (T := 1) (n₀ - j) α‖ * ‖cw m j‖ * ‖v (x - j)‖ := by
        rw [norm_mul, norm_mul]
    _ ≤ (A.card : ℝ) * ‖cw m j‖ * max Cv 1 := by
        have h3 : (0 : ℝ) ≤ (A.card : ℝ) * ‖cw m j‖ := by positivity
        exact mul_le_mul (mul_le_mul h1 le_rfl (norm_nonneg _) (by positivity)) hv'
          (norm_nonneg _) h3
    _ = ((A.card : ℝ) * max Cv 1) * ‖cw m j‖ := by ring

/-- **The exact-height fibre is the difference of two cumulative-height fibres.**  For `l ≥ 1`,
`diffFreqs ρ l = (ℚ/ℤ)_{≤l} \ (ℚ/ℤ)_{≤l-1}`, so the exact-height arithmetic character is the
difference of the two cumulative ones, and the `tsum` over `j` splits. -/
theorem fiberOpD_eq_sub_fiberOpCum {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {l : ℕ} (hl : 1 ≤ l)
    (m : ℝ → ℂ) (n₀ : ℤ) (v : ℤ → ℂ) {Cv : ℝ} (hv : ∀ y : ℤ, ‖v y‖ ≤ Cv)
    (hcw : Summable (fun j : ℤ => ‖cw m j‖)) :
    fiberOpD ρ l m n₀ v = fiberOpCum ρ l m n₀ v - fiberOpCum ρ (l - 1) m n₀ v := by
  funext x
  have hsub : iwArithFreqs ρ (l - 1) ⊆ iwArithFreqs ρ l :=
    iwArithFreqs_mono hρ hρ1 (Nat.sub_le l 1)
  have hsum_l : Summable (fun j : ℤ =>
      (∑ α ∈ iwArithFreqs ρ l, fourier (T := 1) (n₀ - j) α) * cw m j * v (x - j)) :=
    summable_char_mul hv hcw
  have hsum_l' : Summable (fun j : ℤ =>
      (∑ α ∈ iwArithFreqs ρ (l - 1), fourier (T := 1) (n₀ - j) α) * cw m j * v (x - j)) :=
    summable_char_mul hv hcw
  show (∑' j : ℤ, arithCharD ρ l (n₀ - j) * cw m j * v (x - j))
      = (∑' j : ℤ, (∑ α ∈ iwArithFreqs ρ l, fourier (T := 1) (n₀ - j) α)
            * cw m j * v (x - j))
        - (∑' j : ℤ, (∑ α ∈ iwArithFreqs ρ (l - 1), fourier (T := 1) (n₀ - j) α)
            * cw m j * v (x - j))
  rw [← Summable.tsum_sub hsum_l hsum_l']
  refine tsum_congr (fun j => ?_)
  have hdiff : diffFreqs ρ l = iwArithFreqs ρ l \ iwArithFreqs ρ (l - 1) := by
    simp only [diffFreqs, if_neg (by omega : ¬ l = 0)]
  have hdecomp : (∑ α ∈ iwArithFreqs ρ l, fourier (T := 1) (n₀ - j) α)
      = (∑ α ∈ iwArithFreqs ρ (l - 1), fourier (T := 1) (n₀ - j) α)
        + (∑ α ∈ iwArithFreqs ρ l \ iwArithFreqs ρ (l - 1), fourier (T := 1) (n₀ - j) α) := by
    rw [← Finset.sum_sdiff hsub]
    ring
  rw [arithCharD, hdiff, hdecomp]
  ring

/-- **The `ℓ^p` bound for the exact-height fibre from the cumulative ones.** -/
theorem eLpNorm_fiberOpD_le_of_fiberOpCum {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {l : ℕ} (hl : 1 ≤ l)
    {p : ENNReal} (hp : 1 ≤ p) (m : ℝ → ℂ) (n₀ : ℤ) (v : ℤ → ℂ) {Cv : ℝ}
    (hv : ∀ y : ℤ, ‖v y‖ ≤ Cv) (hcw : Summable (fun j : ℤ => ‖cw m j‖)) (C C' : ENNReal)
    (h₁ : eLpNorm (fun x : ℤ => fiberOpCum ρ l m n₀ v x) p Measure.count
      ≤ C * eLpNorm v p Measure.count)
    (h₂ : eLpNorm (fun x : ℤ => fiberOpCum ρ (l - 1) m n₀ v x) p Measure.count
      ≤ C' * eLpNorm v p Measure.count) :
    eLpNorm (fun x : ℤ => fiberOpD ρ l m n₀ v x) p Measure.count
      ≤ (C + C') * eLpNorm v p Measure.count := by
  have hfun : (fun x : ℤ => fiberOpD ρ l m n₀ v x)
      = (fun x : ℤ => fiberOpCum ρ l m n₀ v x)
        - (fun x : ℤ => fiberOpCum ρ (l - 1) m n₀ v x) := by
    funext x
    exact congrFun (fiberOpD_eq_sub_fiberOpCum hρ hρ1 hl m n₀ v hv hcw) x
  rw [hfun]
  calc eLpNorm (fun x : ℤ => fiberOpCum ρ l m n₀ v x - fiberOpCum ρ (l - 1) m n₀ v x)
        p Measure.count
      ≤ eLpNorm (fun x : ℤ => fiberOpCum ρ l m n₀ v x) p Measure.count
        + eLpNorm (fun x : ℤ => fiberOpCum ρ (l - 1) m n₀ v x) p Measure.count :=
        eLpNorm_sub_le hp
    _ ≤ C * eLpNorm v p Measure.count + C' * eLpNorm v p Measure.count := add_le_add h₁ h₂
    _ = (C + C') * eLpNorm v p Measure.count := by rw [add_mul]


/-! ## The level-`0` fibre, and the `ℓ¹` summability of the model coefficients -/

/-- At level `0` the exact-height and cumulative fibres agree (both are the plain multiplier with
symbol `m`): `(ℚ/ℤ)_{≤0} = (ℚ/ℤ)_0 = {0}`. -/
theorem fiberOpD_zero_eq_fiberOpCum (ρ : ℝ) (m : ℝ → ℂ) (n₀ : ℤ) (v : ℤ → ℂ) :
    fiberOpD ρ 0 m n₀ v = fiberOpCum ρ 0 m n₀ v := by
  funext x
  refine tsum_congr (fun j => ?_)
  have h1 : diffFreqs ρ 0 = iwArithFreqs ρ 0 := by
    show (if (0 : ℕ) = 0 then iwArithFreqs ρ 0
      else iwArithFreqs ρ 0 \ iwArithFreqs ρ (0 - 1)) = iwArithFreqs ρ 0
    rw [if_pos rfl]
  rw [arithCharD, h1]

/-- **`ℓ¹`-summability of the coefficient kernel of `mStarF u`** (`= η_{≤-2u}`). -/
theorem summable_norm_cw_mStarF (u : ℕ) : Summable (fun j : ℤ => ‖cw (mStarF u) j‖) := by
  obtain ⟨C, hC, hdec⟩ := cw_etaCut_decay (-(2 * (u : ℤ)))
  have hmaj : Summable (fun j : ℤ => C / (1 + |(j : ℝ)|) ^ 2) := by
    have h := summable_one_div_sq_int.mul_left C
    have heq : (fun j : ℤ => C / (1 + |(j : ℝ)|) ^ 2)
        = fun j : ℤ => C * (1 / (1 + |(j : ℝ)|) ^ 2) := by
      funext j; rw [div_eq_mul_inv, one_div]
    rw [heq]; exact h
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_) hmaj
  simpa only [mStarF] using hdec j

/-- **`ℓ¹`-summability of the coefficient kernel of `mStargF d u`** (`= η_{≤-2du}`). -/
theorem summable_norm_cw_mStargF (P : Polynomial ℤ) (u : ℕ) :
    Summable (fun j : ℤ => ‖cw (mStargF P.natDegree u) j‖) := by
  obtain ⟨C, hC, hdec⟩ := cw_etaCut_decay (-(((P.natDegree : ℤ)) * 2 * (u : ℤ)))
  have hmaj : Summable (fun j : ℤ => C / (1 + |(j : ℝ)|) ^ 2) := by
    have h := summable_one_div_sq_int.mul_left C
    have heq : (fun j : ℤ => C / (1 + |(j : ℝ)|) ^ 2)
        = fun j : ℤ => C * (1 / (1 + |(j : ℝ)|) ^ 2) := by
      funext j; rw [div_eq_mul_inv, one_div]
    rw [heq]; exact h
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_) hmaj
  simpa only [mStargF] using hdec j

/-! ## Monotonicity of the good-major-arcs predicate -/

/-- `GoodMajorArcs ρ Cρ l k` is monotone in the arc radius: smaller `Cρ` (a weaker hypothesis) and
smaller `k` (a narrower arc) are both implied. -/
theorem GoodMajorArcs.mono_Cρ {ρ Cρ Cρ' : ℝ} (h : Cρ ≤ Cρ') {l : ℕ} {k : ℤ}
    (hk : GoodMajorArcs ρ Cρ' l k) : GoodMajorArcs ρ Cρ l k :=
  hk.trans (by
    have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (ρ * (l : ℝ)) := by positivity
    nlinarith)

/-- Weakening the arc radius preserves good major arcs. -/
theorem GoodMajorArcs.mono_k {ρ Cρ : ℝ} {l : ℕ} {k k' : ℤ} (hk : GoodMajorArcs ρ Cρ l k')
    (h : k ≤ k') : GoodMajorArcs ρ Cρ l k :=
  (by exact_mod_cast h : (k : ℝ) ≤ (k' : ℝ)).trans hk


/-- `Tm` vanishes on the zero input (for every symbol). -/
theorem Tm_apply_zero (ρ : ℝ) (l : ℕ) (φ : ℝ → ℂ) : Tm ρ l φ 0 = 0 := by
  funext n
  simp only [Tm, Work.Analysis.IWMultiplier.iwConv, Pi.zero_apply, smul_zero, tsum_zero]


/-- The `P`-twisted fibre is the untwisted fibre at the shifted residue `P(n₀)`. -/
theorem fiberOpPD_eq_fiberOpD (ρ : ℝ) (P : Polynomial ℤ) (l : ℕ) (m : ℝ → ℂ) (n₀ : ℤ)
    (v : ℤ → ℂ) : fiberOpPD ρ P l m n₀ v = fiberOpD ρ l m (P.eval n₀) v := rfl

end

end Work.KMTAreas.A7
