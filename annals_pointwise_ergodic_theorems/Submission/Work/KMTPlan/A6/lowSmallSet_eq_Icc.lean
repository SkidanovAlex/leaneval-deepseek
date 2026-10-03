import Mathlib
import Submission.Work.KMTPlan.A6.lowSmallSet_le_log

/-!
# `lowSmallSet` is an interval of scales

The admissible small-scale index set of the low case,

`lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n = I^{max(l₁,l₂),k₁,k₂}(⌊a n⌋) ∧ ⌊a n⌋ ≤ splitCut ρ L`,

is an interval in `n`: it is the intersection of the *upward closed* set
`{n | inIndexSet C₀ (max l₁ l₂) k₁ k₂ ⌊a n⌋}` (the height scale `l_{(N)} = C₀ LogLog N` is
monotone in `N`, and `a` is monotone) with the *downward closed* set
`{n | ⌊a n⌋ ≤ splitCut ρ L}` (the floor of the lacunary sequence `a` is monotone, and
`Λ^n ≤ a n` shows that it is unbounded).  An intersection of an upward closed and a downward
closed subset of `ℕ` is an interval; the empty interval is encoded by `c > e`.
-/

namespace Work.KMTPlan.A6

open scoped NNReal
open Work.Analysis.EndVar

/-- The floor of a monotone `ℝ≥0`-valued sequence is monotone. -/
private theorem lowSmallSet_floor_mono_nnreal {x y : NNReal} (h : x ≤ y) :
    Nat.floor x ≤ Nat.floor y := by
  exact_mod_cast (Nat.floor_mono (R := ℝ) (show (x : ℝ) ≤ (y : ℝ) from h))

/-- A `Λ`-lacunary sequence (`Λ > 1`) bounded below by `1` is monotone. -/
private theorem lowSmallSet_monotone_a {Λ : NNReal} (hΛ : 1 < Λ) {a : ℕ → NNReal}
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) : Monotone a := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  have hpos : (0 : NNReal) < a n := lt_of_lt_of_le zero_lt_one (ha1 n)
  have hstep : Λ * a n < a (n + 1) := (lt_div_iff₀ hpos).mp (ha n)
  calc a n = 1 * a n := (one_mul _).symm
    _ ≤ Λ * a n := mul_le_mul_of_nonneg_right (le_of_lt hΛ) (le_of_lt hpos)
    _ ≤ a (n + 1) := le_of_lt hstep

/-- The index set `I^{l,s₁,s₂}(N)` is monotone in the scale `N`: the height scale
`l_{(N)} = C₀ LogLog N` is nondecreasing. -/
private theorem lowSmallSet_inIndexSet_mono {C₀ : ℕ} {l s₁ s₂ : ℤ} {N M : ℕ} (hNM : N ≤ M)
    (h : inIndexSet C₀ l s₁ s₂ N) : inIndexSet C₀ l s₁ s₂ M := by
  obtain ⟨h1, h2, h3⟩ := h
  have hh : (heightScale C₀ N : ℤ) ≤ (heightScale C₀ M : ℤ) := by
    exact_mod_cast heightScale_mono C₀ hNM
  exact ⟨le_trans h1 hh, le_trans h2 hh, le_trans h3 hh⟩

/-- **The admissible small-scale set is bounded above.**  On it `⌊a n⌋ ≤ splitCut ρ L`, and
`Λ ^ n ≤ a n < ⌊a n⌋ + 1`, so `n ≲ log_Λ (splitCut ρ L + 1)`. -/
private theorem lowSmallSet_bdd (Λ : NNReal) (hΛ : 1 < Λ) (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal)
    (l₁ l₂ k₁ k₂ : ℕ) (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) :
    ∃ M : ℕ, ∀ n : ℕ, lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n → n ≤ M := by
  refine ⟨Nat.ceil (Real.log ((Work.KMTAreas.A7.splitCut ρ (lcL l₁ l₂ k₁ k₂) : ℝ) + 1)
    / Real.log (Λ : ℝ)), ?_⟩
  intro n hn
  have hle : Nat.floor (a n) ≤ Work.KMTAreas.A7.splitCut ρ (lcL l₁ l₂ k₁ k₂) :=
    (lowSmallSet_iff.mp hn).2
  have hΛR : (1 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ
  have hlogΛ : 0 < Real.log (Λ : ℝ) := Real.log_pos hΛR
  have hpow : (Λ : ℝ) ^ n ≤ (a n : ℝ) := by
    have h := lowSmallSet_lacunary_pow_le ha ha1 n
    have h' : ((Λ ^ n : NNReal) : ℝ) ≤ ((a n : NNReal) : ℝ) := by exact_mod_cast h
    simpa using h'
  have han : (a n : ℝ) < (Work.KMTAreas.A7.splitCut ρ (lcL l₁ l₂ k₁ k₂) : ℝ) + 1 := by
    have h1 : (a n : ℝ) < ((Nat.floor (a n) : ℕ) : ℝ) + 1 := by
      exact_mod_cast Nat.lt_floor_add_one (a n)
    have h2 : ((Nat.floor (a n) : ℕ) : ℝ)
        ≤ (Work.KMTAreas.A7.splitCut ρ (lcL l₁ l₂ k₁ k₂) : ℝ) := by exact_mod_cast hle
    linarith
  have hlt : (Λ : ℝ) ^ n < (Work.KMTAreas.A7.splitCut ρ (lcL l₁ l₂ k₁ k₂) : ℝ) + 1 :=
    lt_of_le_of_lt hpow han
  have hlog : (n : ℝ) * Real.log (Λ : ℝ)
      ≤ Real.log ((Work.KMTAreas.A7.splitCut ρ (lcL l₁ l₂ k₁ k₂) : ℝ) + 1) := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (Λ : ℝ) ^ n) (le_of_lt hlt)
    rwa [Real.log_pow] at h
  have hdiv : (n : ℝ) ≤ Real.log ((Work.KMTAreas.A7.splitCut ρ (lcL l₁ l₂ k₁ k₂) : ℝ) + 1)
      / Real.log (Λ : ℝ) := (le_div_iff₀ hlogΛ).mpr hlog
  exact_mod_cast le_trans hdiv (Nat.le_ceil _)

/-- **A convex, bounded-above subset of `ℕ` is an interval.** -/
private theorem lowSmallSet_exists_Icc_of_convex_bdd (S : ℕ → Prop) [DecidablePred S]
    (hconv : ∀ n j m : ℕ, n ≤ j → j ≤ m → S n → S m → S j)
    (hbdd : ∃ M : ℕ, ∀ n : ℕ, S n → n ≤ M) :
    ∃ c e : ℕ, ∀ m : ℕ, S m ↔ c ≤ m ∧ m ≤ e := by
  obtain ⟨M, hM⟩ := hbdd
  by_cases hne : ∃ n, S n
  · refine ⟨Nat.find hne, Nat.findGreatest S M, fun m => ?_⟩
    have hSc : S (Nat.find hne) := Nat.find_spec hne
    have hSe : S (Nat.findGreatest S M) := by
      obtain ⟨n₀, hn₀⟩ := hne
      exact Nat.findGreatest_spec (hM n₀ hn₀) hn₀
    constructor
    · intro hm
      exact ⟨Nat.find_min' hne hm, Nat.le_findGreatest (hM m hm) hm⟩
    · rintro ⟨hcm, hme⟩
      exact hconv _ _ _ hcm hme hSc hSe
  · refine ⟨1, 0, fun m => ?_⟩
    have hnm : ¬ S m := fun hm => hne ⟨m, hm⟩
    exact ⟨fun hm => absurd hm hnm, fun hh => absurd hh.1 (by omega)⟩

/-- **The admissible small-scale index set of the low case is an interval of scales.**

`lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂` is the intersection of the upward closed set
`{n | inIndexSet C₀ (max l₁ l₂) k₁ k₂ ⌊a n⌋}` with the downward closed set
`{n | ⌊a n⌋ ≤ splitCut ρ L}`; the former is upward closed because `heightScale C₀` and `a` are
monotone, the latter is downward closed because `⌊a ·⌋` is monotone, and it is bounded above
because `a` grows at least like `Λ ⁿ`.  (When the set is empty, `c > e` encodes it.) -/
theorem lowSmallSet_eq_Icc (Λ : NNReal) (hΛ : 1 < Λ) (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal)
    (l₁ l₂ k₁ k₂ : ℕ) (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) :
    ∃ c e : ℕ, ∀ m : ℕ, Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ m ↔ c ≤ m ∧ m ≤ e := by
  have hmonoA : Monotone a := lowSmallSet_monotone_a hΛ ha ha1
  have hmonof : Monotone (fun n : ℕ => Nat.floor (a n)) :=
    fun n m hnm => lowSmallSet_floor_mono_nnreal (hmonoA hnm)
  refine lowSmallSet_exists_Icc_of_convex_bdd
    (fun n : ℕ => lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n) ?_
    (lowSmallSet_bdd Λ hΛ ρ C₀ a l₁ l₂ k₁ k₂ ha ha1)
  intro n j m hnj hjm hn hm
  rw [lowSmallSet_iff] at hn hm
  -- `inIndexSet` is upward closed, so `A j` follows from `A n = (S n).1` and `n ≤ j`;
  -- `⌊a ·⌋ ≤ splitCut ρ L` is downward closed, so `B j` follows from `B m = (S m).2` and `j ≤ m`.
  have hfloor₁ : Nat.floor (a n) ≤ Nat.floor (a j) := hmonof hnj
  have hfloor₂ : Nat.floor (a j) ≤ Nat.floor (a m) := hmonof hjm
  exact ⟨lowSmallSet_inIndexSet_mono hfloor₁ hn.1, le_trans hfloor₂ hm.2⟩

end Work.KMTPlan.A6
