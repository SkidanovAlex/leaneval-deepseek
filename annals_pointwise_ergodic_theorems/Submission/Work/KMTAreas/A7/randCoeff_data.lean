/-
# The coefficient bounds of the randomised small-scale symbol

This module proves the two elementary facts about the coefficients

  `randCoeff ρ C₀ a l₁ l₂ k₁ k₂ ε K m
     = 1_{randAct … m} · (ε (m-1) · 1_{m ≤ K} - ε m · 1_{m < K})`

of the randomised symbol `randSymb (smallSymbF …) ε K` of the small-scale tuple that the
analysis of that symbol uses:

* `randCoeff_data` — the coefficients are bounded by `2`, and their partial sums over any
  interval `Icc c e` are bounded by `4`, uniformly in `K`, in the coefficients `ε` of norm `≤ 1`,
  and in every parameter.

The mechanism (paper §7, the randomised cut-off of the Rademacher–Menshov inequality) is:

* the truncation `m ↦ 1_{m ≤ K}` is a *difference*: with `G m := 1_{m < K} · ε m`,
  `randCoeff m = 1_{randAct … m} · (G (m-1) - G m)`;
* the index condition `randAct` is an *interval* of `ℕ` (`randAct_interval`, from the monotonicity
  of `a`: `smallCond` is the conjunction of the two upward closed conditions `inIndexSet`,
  `mainRegime` with the downward closed condition `⌊a m⌋ ≤ splitCut`),
  so `(Icc c e).filter (randAct …) = Icc a b` is again an interval, and the difference form
  telescopes over it: `∑_{m ∈ Icc a b} (G (m-1) - G m) = G (a-1) - G b`, of norm `≤ 2`.

The `l₁` bound of `2` on a whole interval — which is what makes the symbol bounded, and a Mikhlin
multiplier, even when the number of lacunary scales is unbounded — is exactly this telescoping.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.randSymb_coeff_aux

set_option maxHeartbeats 1000000

open Finset

namespace Work.KMTAreas.A7

noncomputable section

/-- **The coefficient is a truncated difference.**  Writing `G m := 1_{m < K} · ε m` (the
coefficients `ε` cut off at `K`), the `m`-th coefficient is `1_{randAct … m} · (G (m-1) - G m)`.

(For `m ∉ randAct` it vanishes; for `m < K` the two indicators of the definition are both `1` and
the value is `ε (m-1) - ε m`; for `m = K ≥ 1` it is `ε (K-1)`; for `m > K` it is `0`.) -/
lemma randCoeff_eq_trunc_sub (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ)
    (ε : ℕ → ℂ) (K m : ℕ) :
    randCoeff ρ C₀ a l₁ l₂ k₁ k₂ ε K m =
      (if randAct ρ C₀ a l₁ l₂ k₁ k₂ m then
        ((if m - 1 < K then ε (m - 1) else 0) - (if m < K then ε m else 0)) else 0) := by
  unfold randCoeff
  by_cases hA : randAct ρ C₀ a l₁ l₂ k₁ k₂ m
  · rw [if_pos hA, if_pos hA, mul_boole, mul_boole]
    have hm0 : m ≠ 0 := hA.1
    have hiff1 : m ≤ K → m - 1 < K := by omega
    have hiff2 : m - 1 < K → m ≤ K := by omega
    by_cases hmK : m ≤ K
    · rw [if_pos hmK, if_pos (hiff1 hmK)]
    · rw [if_neg hmK, if_neg (fun h => hmK (hiff2 h))]
  · rw [if_neg hA, if_neg hA]

/-- **The filter of an interval by an interval-like predicate is an interval.**  If the level set
of `P` is an interval of `ℕ` then `(Icc c e).filter P` is the interval spanned by its minimum and
its maximum. -/
lemma randCoeff_filter_Icc_eq_Icc {P : ℕ → Prop} [DecidablePred P]
    (hP : ∀ {j m k : ℕ}, j ≤ m → m ≤ k → P j → P k → P m) {c e : ℕ}
    (hne : ((Finset.Icc c e).filter P).Nonempty) :
    (Finset.Icc c e).filter P
      = Finset.Icc (((Finset.Icc c e).filter P).min' hne)
                    (((Finset.Icc c e).filter P).max' hne) := by
  ext m
  constructor
  · intro hm
    exact Finset.mem_Icc.mpr ⟨Finset.min'_le _ m hm, Finset.le_max' _ m hm⟩
  · intro hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
    obtain ⟨hmince, hPmin⟩ := Finset.mem_filter.mp (Finset.min'_mem _ hne)
    obtain ⟨hmaxce, hPmax⟩ := Finset.mem_filter.mp (Finset.max'_mem _ hne)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨le_trans (Finset.mem_Icc.mp hmince).1 hm1, le_trans hm2 (Finset.mem_Icc.mp hmaxce).2⟩,
      hP hm1 hm2 hPmin hPmax⟩

/-- **Telescoping the truncated differences over an interval.** -/
lemma randCoeff_sum_Icc_trunc_sub (ε : ℕ → ℂ) (K : ℕ) {c e : ℕ} (hce : c ≤ e) :
    ∑ m ∈ Finset.Icc c e,
        ((if m - 1 < K then ε (m - 1) else 0) - (if m < K then ε m else 0))
      = (if c - 1 < K then ε (c - 1) else 0) - (if e < K then ε e else 0) :=
  sum_Icc_sub_succ_sub (fun m => if m < K then ε m else 0) c e hce

/-- The truncated coefficient `1_{n < K} · ε n` is bounded by `1` when `‖ε‖ ≤ 1`. -/
lemma randCoeff_norm_trunc_le_one (ε : ℕ → ℂ) (K : ℕ) (hε : ∀ n, ‖ε n‖ ≤ 1) (n : ℕ) :
    ‖(if n < K then ε n else 0 : ℂ)‖ ≤ 1 := by
  split_ifs with h
  · exact hε n
  · simp

/-- **The partial sums of the truncated differences over an interval-like index set are bounded
by `2`.** -/
lemma randCoeff_norm_sum_filter_le_two {P : ℕ → Prop} [DecidablePred P]
    (hP : ∀ {j m k : ℕ}, j ≤ m → m ≤ k → P j → P k → P m)
    {ε : ℕ → ℂ} (hε : ∀ n, ‖ε n‖ ≤ 1) (K c e : ℕ) :
    ‖∑ m ∈ (Finset.Icc c e).filter P,
        ((if m - 1 < K then ε (m - 1) else 0) - (if m < K then ε m else 0))‖ ≤ 2 := by
  rcases Finset.eq_empty_or_nonempty ((Finset.Icc c e).filter P) with h | h
  · rw [h]; simp
  · have hEq := randCoeff_filter_Icc_eq_Icc hP h
    have hab : ((Finset.Icc c e).filter P).min' h ≤ ((Finset.Icc c e).filter P).max' h :=
      Finset.min'_le _ _ (Finset.max'_mem _ h)
    rw [hEq, randCoeff_sum_Icc_trunc_sub ε K hab]
    have h1 : ‖(if ((Finset.Icc c e).filter P).min' h - 1 < K then
        ε (((Finset.Icc c e).filter P).min' h - 1) else 0 : ℂ)‖ ≤ 1 :=
      randCoeff_norm_trunc_le_one ε K hε _
    have h2 : ‖(if ((Finset.Icc c e).filter P).max' h < K then
        ε (((Finset.Icc c e).filter P).max' h) else 0 : ℂ)‖ ≤ 1 :=
      randCoeff_norm_trunc_le_one ε K hε _
    linarith [norm_sub_le
      (if ((Finset.Icc c e).filter P).min' h - 1 < K then
        ε (((Finset.Icc c e).filter P).min' h - 1) else 0 : ℂ)
      (if ((Finset.Icc c e).filter P).max' h < K then
        ε (((Finset.Icc c e).filter P).max' h) else 0 : ℂ)]

/-- **The coefficient data of the randomised small-scale symbol.**  The coefficients `randCoeff`
of `randSymb (smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε K` are bounded by `2` pointwise and their
partial sums over any interval `Icc c e` are bounded by `4`, uniformly in `K` and in the
coefficients `ε` of norm `≤ 1`. -/
theorem randCoeff_data (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ)
    (ε : ℕ → ℂ) (hε : ∀ n, ‖ε n‖ ≤ 1) (ha : Monotone a) (K : ℕ) :
    (∀ m : ℕ, ‖Work.KMTAreas.A7.randCoeff ρ C₀ a l₁ l₂ k₁ k₂ ε K m‖ ≤ 2) ∧
    (∀ c e : ℕ,
      ‖∑ m ∈ Finset.Icc c e, Work.KMTAreas.A7.randCoeff ρ C₀ a l₁ l₂ k₁ k₂ ε K m‖ ≤ 4) := by
  have hP : ∀ {j m k : ℕ}, j ≤ m → m ≤ k → randAct ρ C₀ a l₁ l₂ k₁ k₂ j →
      randAct ρ C₀ a l₁ l₂ k₁ k₂ k → randAct ρ C₀ a l₁ l₂ k₁ k₂ m :=
    fun hjm hmk hj hk => randAct_interval ha hjm hmk hj hk
  constructor
  · intro m
    rw [randCoeff_eq_trunc_sub ρ C₀ a l₁ l₂ k₁ k₂ ε K m]
    by_cases hA : randAct ρ C₀ a l₁ l₂ k₁ k₂ m
    · rw [if_pos hA]
      have h1 := randCoeff_norm_trunc_le_one ε K hε (m - 1)
      have h2 := randCoeff_norm_trunc_le_one ε K hε m
      linarith [norm_sub_le (if m - 1 < K then ε (m - 1) else 0 : ℂ)
        (if m < K then ε m else 0 : ℂ)]
    · rw [if_neg hA]; simp
  · intro c e
    have hcongr : (∑ m ∈ Finset.Icc c e, randCoeff ρ C₀ a l₁ l₂ k₁ k₂ ε K m)
        = ∑ m ∈ (Finset.Icc c e).filter (randAct ρ C₀ a l₁ l₂ k₁ k₂),
            ((if m - 1 < K then ε (m - 1) else 0) - (if m < K then ε m else 0)) := by
      rw [Finset.sum_congr rfl (fun m _ => randCoeff_eq_trunc_sub ρ C₀ a l₁ l₂ k₁ k₂ ε K m)]
      rw [Finset.sum_filter]
    rw [hcongr]
    exact le_trans (randCoeff_norm_sum_filter_le_two hP hε K c e) (by norm_num)

end

end Work.KMTAreas.A7
