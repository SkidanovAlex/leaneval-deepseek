/-
# The `ℓ²`-bound for the randomised `f`-side packets of Case B (area A6)

The target `Work.KMTPlan.A6.LowModRandL2F` (the interface used by `lowModelVarCaseB`) is proved
here directly, with a constant depending only on `ρ`, `C₀` and `Λ` -- in particular without the
`AreaA1` hypothesis of the neighbouring conditional interface `LowModRandL2F'` (the two are the
same proposition).

The route is the two-part argument of the target's docstring:

* **(a) the pointwise bound of the randomised symbol.**  The total variation of the *unclamped*
  modified bump family `n ↦ φ_{N n,k,j,t}(x)` along a lacunary sequence is bounded by a constant
  depending only on `Λ` (`lowModVarBoundHigh` for `k ≥ 1`, `lowModVarBoundZero` for `k = 0, j = 1`,
  and the already-proved `varBound` for `j = 0`), so `randSymb_bounded_of_varBound_mod` (proved in
  `lowModSymbFAux.lean`) bounds the randomised symbol of the *clamped* family by `Cv + 2 * 8`
  (`lowModSymbF_randSup`).

* **(b) the passage to `Tm`.**  On `lowSmallSet` the family is supported in the tiny arc
  `|x| ≤ 2^{-3·uScale ρ L}` (`lowModSymbF_support`, from `varphiNt_support_lowSmall` and
  `varphiNt_support_le_all`), the exact-height frequency set is non-aliasing at that scale
  (`nonAliasing_diffFreqs`), so the narrow-symbol bound `iwSymbolSet_narrow_bound` gives a
  pointwise bound for the symbol of `Tm`, and `eLpNorm_iwConv_two_le_of_symbol_bound` converts the
  symbol bound into the `ℓ²`-bound of `Tm`.

The degenerate case `C₀ = 0` is treated separately: then `lowSmallSet` forces
`l₁ = l₂ = k₁ = k₂ = 0` (hence the family vanishes unless all four indices vanish), and in the
remaining case `diffFreqs ρ 0 = {0}`, so that `iwSymbolSet {0} Ψ = Ψ` and the periodised symbol is
bounded by `norm_periodize_le`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.lowModSymbFAux
import Submission.Work.KMTPlan.A6.iwSymbolSet_narrow_bound
import Submission.Work.KMTPlan.A6.nonAliasing_diffFreqs
import Submission.Work.KMTPlan.A6.varphiNt_support_lowSmall

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators Interval
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger
open Work.KMTAreas.A7
open Work.Analysis.EndVar
open Work.KMTContract

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-! ## Elementary facts about the degenerate index set and the level-`0` frequencies -/

/-- The height-`≤ 0` arithmetic frequency set is `{0}` (`iwP ρ 0 = {1}` and the only `1`-torsion
element of `ℝ/ℤ` is `0`). -/
theorem diffFreqs_zero_eq (ρ : ℝ) : diffFreqs ρ 0 = ({(0 : Circ)} : Finset Circ) := by
  rw [diffFreqs, if_pos rfl]
  unfold iwArithFreqs iwP
  rw [if_pos (Nat.zero_le _)]
  rw [show (2 : ℕ) ^ 0 = 1 from rfl]
  ext γ
  simp only [Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_image, Finset.mem_range,
    Finset.mem_singleton]
  constructor
  · rintro ⟨q, ⟨h1, h2⟩, a, ha, rfl⟩
    have hq : q = 1 := by omega
    subst hq
    have ha0 : a = 0 := by simpa using ha
    subst ha0
    simp
  · rintro rfl
    exact ⟨1, by norm_num, 0, by simp, by simp⟩

/-- If `lcL l₁ l₂ k₁ k₂ = 0` then all four indices vanish. -/
theorem lcL_eq_zero {l₁ l₂ k₁ k₂ : ℕ} (h : lcL l₁ l₂ k₁ k₂ = 0) :
    l₁ = 0 ∧ l₂ = 0 ∧ k₁ = 0 ∧ k₂ = 0 := by
  have h' : max (max l₁ l₂) (max k₁ k₂) = 0 := by rw [← lcL]; exact h
  have h1 : max l₁ l₂ = 0 :=
    le_antisymm (le_trans (le_max_left _ _) (le_of_eq h')) zero_le
  have h2 : max k₁ k₂ = 0 :=
    le_antisymm (le_trans (le_max_right _ _) (le_of_eq h')) zero_le
  exact ⟨le_antisymm (le_trans (le_max_left _ _) (le_of_eq h1)) zero_le,
    le_antisymm (le_trans (le_max_right _ _) (le_of_eq h1)) zero_le,
    le_antisymm (le_trans (le_max_left _ _) (le_of_eq h2)) zero_le,
    le_antisymm (le_trans (le_max_right _ _) (le_of_eq h2)) zero_le⟩

/-- `inIndexSet` at `C₀ = 0` forces all four indices to vanish (since `heightScale 0 N = 0`). -/
theorem inIndexSet_zero_eq {l₁ l₂ k₁ k₂ Nr : ℕ}
    (h : Work.Analysis.EndVar.inIndexSet 0 (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) Nr) :
    l₁ = 0 ∧ l₂ = 0 ∧ k₁ = 0 ∧ k₂ = 0 := by
  have h1 : (max (l₁ : ℤ) (l₂ : ℤ)) ≤ 0 := by
    simpa [Work.Analysis.EndVar.heightScale] using h.1
  have h2 : (k₁ : ℤ) ≤ 0 := by simpa [Work.Analysis.EndVar.heightScale] using h.2.1
  have h3 : (k₂ : ℤ) ≤ 0 := by simpa [Work.Analysis.EndVar.heightScale] using h.2.2
  have hl₁ : l₁ = 0 := by
    have : (l₁ : ℤ) ≤ 0 := le_trans (le_max_left _ _) h1
    omega
  have hl₂ : l₂ = 0 := by
    have : (l₂ : ℤ) ≤ 0 := le_trans (le_max_right _ _) h1
    omega
  exact ⟨hl₁, hl₂, by omega, by omega⟩

/-! ## The level comparison for the active scales at height `k ≥ 1` -/

/-- **The levels of two active scales at height `k ≥ 1` differ by at most one.**  If
`φ_{N,k}(x) ≠ 0` for two scales `N₁`, `N₂`, then `1/4 < |2^{Log N - k} x| < 1` at both, so the
ratio `2^{Log N₂ - Log N₁}` is `< 4 = 2^2`, whence `Log N₂ ≤ Log N₁ + 1`. -/
theorem level_close_kpos {k : ℕ} (hk : 1 ≤ k) {x : ℝ} {N₁ N₂ : ℕ}
    (h₁ : varphiN N₁ k x ≠ 0) (h₂ : varphiN N₂ k x ≠ 0) :
    Work.Analysis.EndVar.logN N₂ ≤ Work.Analysis.EndVar.logN N₁ + 1 := by
  have hann₁ := varphiN_supp_annulus hk h₁
  have hann₂ := varphiN_supp_annulus hk h₂
  set L₁ : ℤ := Work.Analysis.EndVar.logN N₁ with hL₁
  set L₂ : ℤ := Work.Analysis.EndVar.logN N₂ with hL₂
  have hpos₁ : 0 < (2 : ℝ) ^ ((L₁ : ℝ) - (k : ℝ)) * |x| :=
    lt_trans (by norm_num) hann₁.1
  have hfac : (2 : ℝ) ^ ((L₂ : ℝ) - (k : ℝ))
      = (2 : ℝ) ^ ((L₂ : ℝ) - (L₁ : ℝ)) * (2 : ℝ) ^ ((L₁ : ℝ) - (k : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hratio : (2 : ℝ) ^ ((L₂ : ℝ) - (L₁ : ℝ))
      = ((2 : ℝ) ^ ((L₂ : ℝ) - (k : ℝ)) * |x|)
        / ((2 : ℝ) ^ ((L₁ : ℝ) - (k : ℝ)) * |x|) := by
    rw [eq_div_iff (ne_of_gt hpos₁)]
    rw [hfac]
    ring
  have hlt : (2 : ℝ) ^ ((L₂ : ℝ) - (L₁ : ℝ)) < 4 := by
    rw [hratio, div_lt_iff₀ hpos₁]
    nlinarith [hann₂.2]
  have hlt2 : (L₂ : ℝ) - (L₁ : ℝ) < 2 := by
    have hlt' : (2 : ℝ) ^ ((L₂ : ℝ) - (L₁ : ℝ)) < (2 : ℝ) ^ (2 : ℝ) := by
      have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num
      rw [h4] at hlt
      exact hlt
    exact (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp hlt'
  have hZ : L₂ < L₁ + 2 := by
    have hc : (L₂ : ℝ) < ((L₁ + 2 : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast hc
  omega

/-! ## The support of the randomised clamped modified family in the tiny arc -/

/-- **The randomised symbol of the clamped modified bump family is supported in the tiny arc.**
Beyond the `(ρ, C₀)`-dependent threshold `B` of the small-scale index set, the randomised cut-off
of the anchored clamped modified bump family of Case B is supported in
`|ξ| ≤ 2^{-3·uScale ρ L}`, `L = lcL l₁ l₂ k₁ k₂`.  This is the modified-bump analogue of
`Work.KMTPlan.A6.lowSymbF_support`, using
`varphiNtj N k j t = (2^{-k}Nξ)^j · varphiNt N k t`. -/
theorem lowModSymbF_support (ρ : ℝ) (hρ : 0 < ρ) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    (hρC₀ : ρ * (C₀ : ℝ) ≤ 1 / 8) :
    ∃ B : ℕ, ∀ (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (j : ℤ) (ε : ℕ → ℂ) (K : ℕ),
      B ≤ lcL l₁ l₂ k₁ k₂ →
      ∀ ξ : ℝ, randSymb (lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j t) ε K ξ ≠ 0 →
        |ξ| ≤ (2 : ℝ) ^ (-(3 * (uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ))) := by
  obtain ⟨B, hB⟩ := varphiNt_support_lowSmall ρ hρ C₀ hC₀ hρC₀
  refine ⟨B, fun a l₁ l₂ k₁ k₂ t j ε K hBL ξ hξ => ?_⟩
  obtain ⟨n, _hnK, hn⟩ := exists_ne_zero_of_randSymb_ne_zero hξ
  obtain ⟨-, hls, hne⟩ := support_lowModSymbF hn
  have hsupp := varphiNt_support_le_all k₁ (Nat.floor (a n)) t ξ
    (varphiNt_ne_zero_of_varphiNtj_ne_zero _ _ _ _ _ hne)
  have harith := hB l₁ l₂ k₁ k₂ (Nat.floor (a n)) hls.1 hls.2 hBL
  have hk1 : k₁ ≤ max k₁ k₂ := le_max_left _ _
  have hlog : ((k₁ : ℤ) + 3 * (uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ)
      ≤ Work.Analysis.EndVar.logN (Nat.floor (a n))) := by
    have h1 : (k₁ + 3 * uScale ρ (lcL l₁ l₂ k₁ k₂)
        ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat) :=
      le_trans (Nat.add_le_add_right hk1 _) harith
    have h2 : ((Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat : ℤ)
        = Work.Analysis.EndVar.logN (Nat.floor (a n)) :=
      Int.toNat_of_nonneg (Work.Analysis.EndVar.logN_nonneg _)
    have h3 : ((k₁ + 3 * uScale ρ (lcL l₁ l₂ k₁ k₂) : ℕ) : ℤ)
        ≤ ((Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat : ℤ) := by
      exact_mod_cast h1
    push_cast at h3
    rwa [h2] at h3
  have hgoal : (k₁ : ℝ) - (Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ)
      ≤ ((-(3 * (uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ)) : ℤ) : ℝ) := by
    have h4 : (((k₁ : ℤ) + 3 * (uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ) : ℤ) : ℝ)
        ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ) := by
      exact_mod_cast hlog
    push_cast at h4 ⊢
    linarith
  have hrf := Real.rpow_le_rpow_of_exponent_le (x := 2) (by norm_num : (1 : ℝ) ≤ 2) hgoal
  rw [Real.rpow_intCast] at hrf
  exact hsupp.trans hrf

/-! ## The variation bound at positive height -/

/-- **The total variation of the modified bump family at height `k ≥ 1` is bounded by a constant
depending only on `Λ`.**  The active scales are those with `1/4 < |2^{Log N - k}x| < 1`, and the
scaled variable depends only on the dyadic level `Log N`; two active levels differ by at most one
(`level_close_kpos`), so by `lacunaryLevel` at most `3 * M Λ` indices are active.  The crude bound
`∑ ‖D (n+1) - D n‖ ≤ 2 * 8 * #{n ≤ K : D n ≠ 0}` then finishes. -/
theorem lowModVarBoundHigh (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ Cv : ℝ, 0 ≤ Cv ∧ ∀ (a : ℕ → NNReal) (k : ℕ), 1 ≤ k → ∀ (j : ℤ),
      j ∈ ({-1, 0, 1} : Finset ℤ) → ∀ (t x : ℝ) (K : ℕ),
      PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) → t ∈ Set.Icc (1 / 2 : ℝ) 1 →
      ∑ n ∈ Finset.range K,
        ‖varphiNtj (Nat.floor (a (n + 1))) k j t x
          - varphiNtj (Nat.floor (a n)) k j t x‖ ≤ Cv := by
  classical
  obtain ⟨M, hM⟩ := lacunaryLevel
  refine ⟨16 * (3 * (M Λ : ℝ)) + 1, by positivity, ?_⟩
  intro a k hk j hj t x K ha ha1 ht
  set S : Finset ℕ := (Finset.range (K + 2)).filter (fun n => varphiN (Nat.floor (a n)) k x ≠ 0)
    with hS
  have hDzero : ∀ n : ℕ, n ≤ K + 1 → n ∉ S → varphiNtj (Nat.floor (a n)) k j t x = 0 := by
    intro n hnle hnS
    have hφ : varphiN (Nat.floor (a n)) k x = 0 := by
      by_contra hc
      exact hnS (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hc⟩)
    rw [varphiNtj, varphiNt, hφ, zero_mul, mul_zero]
  have hDbdd : ∀ n ∈ S, ‖varphiNtj (Nat.floor (a n)) k j t x‖ ≤ 8 := by
    intro n hn
    have hN1 : 1 ≤ Nat.floor (a n) := Nat.le_floor (by exact_mod_cast ha1 n)
    exact norm_varphiNtj_le_eight (Nat.floor (a n)) k j hj (Or.inl (by omega)) hN1 t x
  have hScard : S.card ≤ 3 * M Λ := by
    rcases Finset.eq_empty_or_nonempty S with hem | hne
    · rw [hem]; simp
    · obtain ⟨n₀, hn₀⟩ := hne
      have hn₀φ : varphiN (Nat.floor (a n₀)) k x ≠ 0 := (Finset.mem_filter.mp hn₀).2
      set m₀ : ℤ := Work.Analysis.EndVar.logN (Nat.floor (a n₀)) with hm₀
      have hlevsub : S ⊆ (Finset.Icc (m₀ - 1) (m₀ + 1)).biUnion
          (fun m => (Finset.range (K + 2)).filter
            (fun n => Work.Analysis.EndVar.logN (Nat.floor (a n)) = m)) := by
        intro n hn
        have hnφ : varphiN (Nat.floor (a n)) k x ≠ 0 := (Finset.mem_filter.mp hn).2
        have hclose := level_close_kpos hk hnφ hn₀φ
        have hclose' := level_close_kpos hk hn₀φ hnφ
        rw [← hm₀] at hclose hclose'
        have hLmem : Work.Analysis.EndVar.logN (Nat.floor (a n))
            ∈ Finset.Icc (m₀ - 1) (m₀ + 1) := by
          rw [Finset.mem_Icc]
          exact ⟨by omega, by omega⟩
        exact Finset.mem_biUnion.mpr
          ⟨_, hLmem, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn).1, rfl⟩⟩
      calc S.card ≤ ((Finset.Icc (m₀ - 1) (m₀ + 1)).biUnion
              (fun m => (Finset.range (K + 2)).filter
                (fun n => Work.Analysis.EndVar.logN (Nat.floor (a n)) = m))).card :=
            Finset.card_le_card hlevsub
        _ ≤ ∑ m ∈ Finset.Icc (m₀ - 1) (m₀ + 1), ((Finset.range (K + 2)).filter
              (fun n => Work.Analysis.EndVar.logN (Nat.floor (a n)) = m)).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ _m ∈ Finset.Icc (m₀ - 1) (m₀ + 1), M Λ :=
            Finset.sum_le_sum (fun m _ => hM a Λ hΛ ha ha1 m (Finset.range (K + 2)))
        _ = 3 * M Λ := by
            rw [Finset.sum_const, smul_eq_mul]
            have hc : (Finset.Icc (m₀ - 1) (m₀ + 1) : Finset ℤ).card = 3 := by
              rw [Int.card_Icc]
              have h3 : m₀ + 1 + 1 - (m₀ - 1) = (3 : ℤ) := by ring
              rw [h3]
              decide
            rw [hc]
  have hterm : ∀ n ∈ Finset.range K,
      ‖varphiNtj (Nat.floor (a (n + 1))) k j t x - varphiNtj (Nat.floor (a n)) k j t x‖
        ≤ 8 * ((if (n + 1) ∈ S then (1 : ℝ) else 0) + (if n ∈ S then (1 : ℝ) else 0)) := by
    intro n hn
    have hnK : n < K := Finset.mem_range.mp hn
    by_cases h1 : (n + 1) ∈ S
    · by_cases h2 : n ∈ S
      · have hb1 := hDbdd (n + 1) h1
        have hb2 := hDbdd n h2
        rw [if_pos h1, if_pos h2]
        have hsub := norm_sub_le (varphiNtj (Nat.floor (a (n + 1))) k j t x)
          (varphiNtj (Nat.floor (a n)) k j t x)
        linarith
      · have hb1 := hDbdd (n + 1) h1
        have hz := hDzero n (by omega) h2
        rw [if_pos h1, if_neg h2, hz, sub_zero]
        linarith
    · by_cases h2 : n ∈ S
      · have hb2 := hDbdd n h2
        have hz := hDzero (n + 1) (by omega) h1
        rw [if_neg h1, if_pos h2, hz, zero_sub, norm_neg]
        linarith
      · have hz1 := hDzero (n + 1) (by omega) h1
        have hz2 := hDzero n (by omega) h2
        rw [if_neg h1, if_neg h2, hz1, hz2, sub_zero, norm_zero]
        norm_num
  have hsum1 : ∑ n ∈ Finset.range K, (if (n + 1) ∈ S then (1 : ℝ) else 0) ≤ (S.card : ℝ) := by
    rw [sum_ite_one_zero]
    have hle : ((Finset.range K).filter (fun n => (n + 1) ∈ S)).card ≤ S.card :=
      Finset.card_le_card_of_injOn (fun n => n + 1) (fun n hn => (Finset.mem_filter.mp hn).2)
        (fun p _ q _ h => Nat.succ.inj h)
    exact_mod_cast hle
  have hsum2 : ∑ n ∈ Finset.range K, (if n ∈ S then (1 : ℝ) else 0) ≤ (S.card : ℝ) := by
    rw [sum_ite_one_zero]
    have hle : ((Finset.range K).filter (fun n => n ∈ S)).card ≤ S.card :=
      Finset.card_le_card (fun n hn => (Finset.mem_filter.mp hn).2)
    exact_mod_cast hle
  calc ∑ n ∈ Finset.range K,
        ‖varphiNtj (Nat.floor (a (n + 1))) k j t x - varphiNtj (Nat.floor (a n)) k j t x‖
      ≤ ∑ n ∈ Finset.range K, 8 * ((if (n + 1) ∈ S then (1 : ℝ) else 0)
          + (if n ∈ S then (1 : ℝ) else 0)) := Finset.sum_le_sum hterm
    _ = 8 * ((∑ n ∈ Finset.range K, (if (n + 1) ∈ S then (1 : ℝ) else 0))
          + ∑ n ∈ Finset.range K, (if n ∈ S then (1 : ℝ) else 0)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ 8 * ((S.card : ℝ) + (S.card : ℝ)) := by
        have := add_le_add hsum1 hsum2
        linarith
    _ ≤ 16 * (3 * (M Λ : ℝ)) := by
        have hc : (S.card : ℝ) ≤ (3 * M Λ : ℕ) := by exact_mod_cast hScard
        push_cast at hc
        linarith
    _ ≤ 16 * (3 * (M Λ : ℝ)) + 1 := by linarith

/-! ## The variation bound at the bottom height `k = 0`, twist `j = 1` -/

/-- **The total variation of the modified bump family at `k = 0`, `j = 1` is bounded by a constant
depending only on `Λ`.**  Here `φ_{N,0,1,t}(x) = (Nx)·η(2^{Log N}x)·e(Ntx)`, and the vanishing of
`η` on `W n = N|x| > 2` makes the walk `W` telescope: the bound
`‖D (n+1) - D n‖ ≤ 2‖V (n+1) - V n‖ + (W (n+1) - W n)` off the single crossing of the level `2`
combines with `varBound` (for the unmodified family `V`), `sum_diff_filter_le` and
`card_crossing_le_one`. -/
theorem lowModVarBoundZero (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ Cv : ℝ, 0 ≤ Cv ∧ ∀ (a : ℕ → NNReal) (t x : ℝ) (K : ℕ),
      PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) → t ∈ Set.Icc (1 / 2 : ℝ) 1 →
      ∑ n ∈ Finset.range K,
        ‖varphiNtj (Nat.floor (a (n + 1))) 0 1 t x
          - varphiNtj (Nat.floor (a n)) 0 1 t x‖ ≤ Cv := by
  classical
  obtain ⟨Lη, hLη, hLηb⟩ := kmtEta_lipschitz
  set Cv₀ : ℝ := 3 * Lη + 2 + max (2 * (Real.log 40 / Real.log ((Λ : ℝ)) + 1))
    (4 * Real.pi + 2) with hCv₀
  have hCv₀0 : 0 ≤ Cv₀ := by
    rw [hCv₀]
    have h1 : 0 ≤ 2 * (Real.log 40 / Real.log ((Λ : ℝ)) + 1) := by
      have hlogΛ : 0 < Real.log ((Λ : ℝ)) := Real.log_pos (by exact_mod_cast hΛ)
      have h40 : 0 ≤ Real.log 40 := Real.log_nonneg (by norm_num)
      have hdiv : 0 ≤ Real.log 40 / Real.log ((Λ : ℝ)) := div_nonneg h40 hlogΛ.le
      linarith
    have h2 : 0 ≤ max (2 * (Real.log 40 / Real.log ((Λ : ℝ)) + 1)) (4 * Real.pi + 2) :=
      le_max_of_le_left h1
    linarith [hLη, h2]
  refine ⟨2 * Cv₀ + 4, by linarith, ?_⟩
  intro a t x K ha ha1 ht
  have hNmono : Monotone (fun n => Nat.floor (a n)) := lacunary_floor_mono Λ hΛ ha
  set W : ℕ → ℝ := fun n => (Nat.floor (a n) : ℝ) * |x| with hW
  set G : ℕ → ℝ := fun n => (Nat.floor (a n) : ℝ) * x with hG
  set V : ℕ → ℂ := fun n => varphiNt (Nat.floor (a n)) 0 t x with hVdef
  set D : ℕ → ℂ := fun n => varphiNtj (Nat.floor (a n)) 0 1 t x with hDdef
  have hWmono : Monotone W := by
    intro p q hpq
    have h1 : Nat.floor (a p) ≤ Nat.floor (a q) := hNmono hpq
    have h2 : ((Nat.floor (a p) : ℕ) : ℝ) ≤ ((Nat.floor (a q) : ℕ) : ℝ) := by exact_mod_cast h1
    rw [hW]
    exact mul_le_mul_of_nonneg_right h2 (abs_nonneg x)
  have hW0 : 0 ≤ W 0 := by rw [hW]; positivity
  have hGn : ∀ n : ℕ, |G n| = W n := by
    intro n
    rw [hG, hW, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  have hVn : ∀ n : ℕ, V n = varphiN (Nat.floor (a n)) 0 x
      * ee ((Nat.floor (a n) : ℝ) * t * x) := by
    intro n
    rw [hVdef]
    rfl
  have hone : (2 : ℝ) ^ (-((0 : ℕ) : ℝ)) = 1 := by norm_num
  have hD : ∀ n : ℕ, D n = ((G n : ℝ) : ℂ) * V n := by
    intro n
    rw [hDdef, hG, hVn n]
    simp only [varphiNtj, varphiNt, zpow_one, hone, one_mul]
  -- the family vanishes where `W n > 2`
  have hz : ∀ n : ℕ, 2 < W n → varphiN (Nat.floor (a n)) 0 x = 0 := by
    intro n hn
    apply varphiN_eq_zero_of_one_lt
    simp only [Nat.cast_zero, sub_zero]
    have h2 := lt_two_mul_pow_logN (Nat.floor (a n))
    rw [hW] at hn
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)]
    nlinarith [abs_nonneg x]
  -- the term bound
  have hterm : ∀ n : ℕ,
      ‖D (n + 1) - D n‖ ≤
        (if W (n + 1) ≤ 2 then 2 * ‖V (n + 1) - V n‖ + (W (n + 1) - W n) else 0)
          + (if W n ≤ 2 ∧ 2 < W (n + 1) then (2 : ℝ) else 0) := by
    intro n
    by_cases hA : 2 < W n
    · have hmono' : W n ≤ W (n + 1) := hWmono (Nat.le_succ n)
      have hzn : varphiN (Nat.floor (a n)) 0 x = 0 := hz n hA
      have hzn1 : varphiN (Nat.floor (a (n + 1))) 0 x = 0 := hz (n + 1) (by linarith)
      have hDn : D n = 0 := by rw [hD n, hVn n, hzn]; ring
      have hDn1 : D (n + 1) = 0 := by rw [hD (n + 1), hVn (n + 1), hzn1]; ring
      rw [hDn, hDn1, sub_zero, norm_zero, if_neg (by linarith),
        if_neg (by rintro ⟨h, -⟩; linarith)]
      norm_num
    · push_neg at hA
      by_cases hB : W (n + 1) ≤ 2
      · rw [if_pos hB, if_neg (by rintro ⟨-, h⟩; linarith)]
        have hNle : Nat.floor (a n) ≤ Nat.floor (a (n + 1)) := hNmono (Nat.le_succ n)
        have hdec : D (n + 1) - D n
            = ((G (n + 1) : ℝ) : ℂ) * (V (n + 1) - V n)
              + (((G (n + 1) : ℝ) : ℂ) - ((G n : ℝ) : ℂ)) * V n := by
          rw [hD (n + 1), hD n]
          ring
        rw [hdec]
        refine le_trans (norm_add_le _ _) ?_
        have h1 : ‖((G (n + 1) : ℝ) : ℂ) * (V (n + 1) - V n)‖ ≤ 2 * ‖V (n + 1) - V n‖ := by
          rw [norm_mul, aux_norm_ofReal, hGn (n + 1)]
          exact mul_le_mul_of_nonneg_right hB (norm_nonneg _)
        have h2 : ‖(((G (n + 1) : ℝ) : ℂ) - ((G n : ℝ) : ℂ)) * V n‖ ≤ W (n + 1) - W n := by
          rw [norm_mul]
          have hg : ‖((G (n + 1) : ℝ) : ℂ) - ((G n : ℝ) : ℂ)‖ = W (n + 1) - W n := by
            rw [← Complex.ofReal_sub, aux_norm_ofReal, hW]
            have h1' : (0 : ℝ) ≤ ((Nat.floor (a (n + 1)) : ℕ) : ℝ)
                - ((Nat.floor (a n) : ℕ) : ℝ) := by
              have := hNmono (Nat.le_succ n)
              exact sub_nonneg.mpr (by exact_mod_cast this)
            rw [hG, show ((Nat.floor (a (n + 1)) : ℕ) : ℝ) * x
                - ((Nat.floor (a n) : ℕ) : ℝ) * x
                = (((Nat.floor (a (n + 1)) : ℕ) : ℝ) - ((Nat.floor (a n) : ℕ) : ℝ)) * x by ring,
              abs_mul, abs_of_nonneg h1']
            ring
          rw [hg]
          have hVb : ‖V n‖ ≤ 1 := by
            rw [hVn n, norm_mul, norm_ee_eq_one, mul_one]
            exact varphiN_norm_le_one _ _ _
          exact mul_le_of_le_one_right (sub_nonneg.mpr (hWmono (Nat.le_succ n))) hVb
        linarith
      · push_neg at hB
        rw [if_neg (by linarith), if_pos ⟨hA, hB⟩]
        have hzn1 : varphiN (Nat.floor (a (n + 1))) 0 x = 0 := hz (n + 1) hB
        have hDn1 : D (n + 1) = 0 := by rw [hD (n + 1), hVn (n + 1), hzn1]; ring
        have hDn : ‖D n‖ ≤ 2 := by
          rw [hD n, hVn n, norm_mul, norm_mul, norm_ee_eq_one, mul_one, aux_norm_ofReal, hGn n]
          calc W n * ‖varphiN (Nat.floor (a n)) 0 x‖ ≤ 2 * 1 :=
                mul_le_mul hA (varphiN_norm_le_one _ _ _) (norm_nonneg _) (by norm_num)
            _ ≤ 2 := by norm_num
        rw [hDn1, zero_sub, norm_neg, zero_add]
        exact hDn
  -- the telescoping sums
  have hsumV : ∑ n ∈ Finset.range K, ‖V (n + 1) - V n‖ ≤ Cv₀ := by
    rw [hCv₀]
    refine le_trans (le_of_eq ?_) (varBound Lη hLη hLηb Λ hΛ a 0 t x K ha ha1 ht)
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [hVdef]
  have hsumW : ∑ n ∈ (Finset.range K).filter (fun n => W (n + 1) ≤ 2), (W (n + 1) - W n) ≤ 2 :=
    sum_diff_filter_le hWmono hW0 K (c := 2) (by norm_num)
  have hcross : (((Finset.range K).filter (fun n => W n ≤ 2 ∧ 2 < W (n + 1))).card : ℝ) ≤ 1 := by
    have := card_crossing_le_one hWmono K (c := 2)
    exact_mod_cast this
  have hstep1 : ∑ n ∈ Finset.range K, 2 * ‖V (n + 1) - V n‖ ≤ 2 * Cv₀ := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hsumV (by norm_num)
  have hstep2 : ∑ n ∈ Finset.range K,
      (if W (n + 1) ≤ 2 then W (n + 1) - W n else 0) ≤ 2 := by
    rw [← Finset.sum_filter]
    exact hsumW
  have hstep4 : ∑ n ∈ Finset.range K,
      (if W n ≤ 2 ∧ 2 < W (n + 1) then (2 : ℝ) else 0) ≤ 2 := by
    have h3 : ∑ n ∈ Finset.range K,
        (if W n ≤ 2 ∧ 2 < W (n + 1) then (1 : ℝ) else 0) ≤ 1 := by
      rw [sum_ite_one_zero]
      exact hcross
    have hmul : ∑ n ∈ Finset.range K,
        (if W n ≤ 2 ∧ 2 < W (n + 1) then (2 : ℝ) else 0)
        = 2 * ∑ n ∈ Finset.range K,
            (if W n ≤ 2 ∧ 2 < W (n + 1) then (1 : ℝ) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      by_cases h : W n ≤ 2 ∧ 2 < W (n + 1) <;> simp [h]
    rw [hmul]
    linarith
  have hmain : ∑ n ∈ Finset.range K,
      (if W (n + 1) ≤ 2 then 2 * ‖V (n + 1) - V n‖ + (W (n + 1) - W n) else 0)
      ≤ 2 * Cv₀ + 2 := by
    have hsplit : ∑ n ∈ Finset.range K,
        (if W (n + 1) ≤ 2 then 2 * ‖V (n + 1) - V n‖ + (W (n + 1) - W n) else 0)
        ≤ ∑ n ∈ Finset.range K, (2 * ‖V (n + 1) - V n‖)
          + ∑ n ∈ Finset.range K, (if W (n + 1) ≤ 2 then W (n + 1) - W n else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum (fun n _ => ?_)
      by_cases h : W (n + 1) ≤ 2
      · simp only [if_pos h]
        exact le_rfl
      · simp only [if_neg h]
        have hnn : (0 : ℝ) ≤ 2 * ‖V (n + 1) - V n‖ := by positivity
        linarith
    linarith [hsplit, hstep1, hstep2]
  calc ∑ n ∈ Finset.range K, ‖D (n + 1) - D n‖
      ≤ ∑ n ∈ Finset.range K,
          ((if W (n + 1) ≤ 2 then 2 * ‖V (n + 1) - V n‖ + (W (n + 1) - W n) else 0)
            + (if W n ≤ 2 ∧ 2 < W (n + 1) then (2 : ℝ) else 0)) :=
        Finset.sum_le_sum (fun n _ => hterm n)
    _ = (∑ n ∈ Finset.range K,
          (if W (n + 1) ≤ 2 then 2 * ‖V (n + 1) - V n‖ + (W (n + 1) - W n) else 0))
        + ∑ n ∈ Finset.range K, (if W n ≤ 2 ∧ 2 < W (n + 1) then (2 : ℝ) else 0) :=
        Finset.sum_add_distrib
    _ ≤ (2 * Cv₀ + 2) + 2 := add_le_add hmain hstep4
    _ = 2 * Cv₀ + 4 := by ring

/-! ## The per-`Λ` variation bound for all heights and twists -/

/-- **The total variation of the modified bump family is bounded by a constant depending only on
`Λ`**, for every height `k` and every twist `j ∈ {-1,0,1}` except the singular pair
`(k,j) = (0,-1)`.  This packages `lowModVarBoundHigh` (`k ≥ 1`), `lowModVarBoundZero` (`k = 0`,
`j = 1`) and the already-proved `varBound` (`j = 0`). -/
theorem lowModVarBoundAll (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ Cv : ℝ, 0 ≤ Cv ∧ ∀ (a : ℕ → NNReal) (k : ℕ) (j : ℤ) (t x : ℝ) (K : ℕ),
      PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) → t ∈ Set.Icc (1 / 2 : ℝ) 1 →
      j ∈ ({-1, 0, 1} : Finset ℤ) → ¬ (k = 0 ∧ j = -1) →
      ∑ n ∈ Finset.range K, ‖varphiNtj (Nat.floor (a (n + 1))) k j t x
        - varphiNtj (Nat.floor (a n)) k j t x‖ ≤ Cv := by
  obtain ⟨Lη, hLη, hLηb⟩ := kmtEta_lipschitz
  obtain ⟨Cv1, hCv1, hv1⟩ := lowModVarBoundHigh Λ hΛ
  obtain ⟨Cv2, hCv2, hv2⟩ := lowModVarBoundZero Λ hΛ
  refine ⟨max (max Cv1 Cv2)
    (3 * Lη + 2 + max (2 * (Real.log 40 / Real.log ((Λ : ℝ)) + 1)) (4 * Real.pi + 2)), ?_, ?_⟩
  · have h3 : 0 ≤ 3 * Lη + 2 + max (2 * (Real.log 40 / Real.log ((Λ : ℝ)) + 1))
        (4 * Real.pi + 2) := by
      have hlogΛ : 0 < Real.log ((Λ : ℝ)) := Real.log_pos (by exact_mod_cast hΛ)
      have h40 : 0 ≤ Real.log 40 := Real.log_nonneg (by norm_num)
      have hdiv : 0 ≤ Real.log 40 / Real.log ((Λ : ℝ)) := div_nonneg h40 hlogΛ.le
      have h2 : 0 ≤ 2 * (Real.log 40 / Real.log ((Λ : ℝ)) + 1) := by linarith
      have hm : 0 ≤ max (2 * (Real.log 40 / Real.log ((Λ : ℝ)) + 1)) (4 * Real.pi + 2) :=
        le_max_of_le_left h2
      linarith [hLη, hm]
    exact le_trans (le_trans hCv1 (le_max_left _ _)) (le_max_left _ _)
  · intro a k j t x K ha ha1 ht hj hne
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with h | h | h
      · exact absurd ⟨rfl, h⟩ hne
      · subst h
        have hb := varBound Lη hLη hLηb Λ hΛ a 0 t x K ha ha1 ht
        refine le_trans (le_of_eq ?_) (le_trans hb (le_max_right _ _))
        refine Finset.sum_congr rfl (fun n _ => ?_)
        simp only [varphiNtj_zero]
      · subst h
        exact le_trans (hv2 a t x K ha ha1 ht) (le_trans (le_max_right _ _) (le_max_left _ _))
    · exact le_trans (hv1 a k hkpos j hj t x K ha ha1 ht)
        (le_trans (le_max_left _ _) (le_max_left _ _))

/-! ## The pointwise bound of the randomised symbol of the clamped modified family -/

/-- **The randomised symbol of the clamped modified bump family is bounded by the variation bound
`Cv` of the unclamped family plus `16 = 2 * 8`.**  The eight is the uniform pointwise bound
`norm_varphiNtj_le_eight` of `lowModSymbFAux.lean`, and the factor `2` is the two jumps of the
order-convex clamping set (`randSymb_bounded_of_varBound_mod`). -/
theorem lowModSymbF_randSup (Λ : NNReal) (hΛ : 1 < Λ) (Cv : ℝ) (hCv : 0 ≤ Cv)
    (hvar : ∀ (a : ℕ → NNReal) (k : ℕ) (j : ℤ) (t x : ℝ) (K : ℕ),
      PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) → t ∈ Set.Icc (1 / 2 : ℝ) 1 →
      j ∈ ({-1, 0, 1} : Finset ℤ) → ¬ (k = 0 ∧ j = -1) →
      ∑ n ∈ Finset.range K, ‖varphiNtj (Nat.floor (a (n + 1))) k j t x
        - varphiNtj (Nat.floor (a n)) k j t x‖ ≤ Cv)
    (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ K : ℕ) (t : ℝ) (j : ℤ) (ε : ℕ → ℂ)
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
    (hε : ∀ n, ‖ε n‖ ≤ 1) (hj : j ∈ ({-1, 0, 1} : Finset ℤ))
    (hne : ¬ (k₁ = 0 ∧ j = -1)) (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) (x : ℝ) :
    ‖Work.KMTAreas.A7.randSymb (lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j t) ε K x‖ ≤ Cv + 16 := by
  have hΦb : ∀ n : ℕ, ‖varphiNtj (Nat.floor (a n)) k₁ j t x‖ ≤ 8 := by
    intro n
    have hN1 : 1 ≤ Nat.floor (a n) := Nat.le_floor (by exact_mod_cast ha1 n)
    have hk : k₁ ≠ 0 ∨ 0 ≤ j := by
      by_cases h0 : k₁ = 0
      · right
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with h | h | h
        · exact absurd ⟨h0, h⟩ hne
        · omega
        · omega
      · exact Or.inl h0
    exact norm_varphiNtj_le_eight (Nat.floor (a n)) k₁ j hj hk hN1 t x
  have hvar' : ∑ n ∈ Finset.range K,
      ‖varphiNtj (Nat.floor (a (n + 1))) k₁ j t x
        - varphiNtj (Nat.floor (a n)) k₁ j t x‖ ≤ Cv :=
    hvar a k₁ j t x K ha ha1 ht hj hne
  have hmain := randSymb_bounded_of_varBound_mod Λ hΛ C₀ 8 Cv (by norm_num)
    (fun n ξ => varphiNtj (Nat.floor (a n)) k₁ j t ξ) ρ a l₁ l₂ k₁ k₂ K t ε x
    ha ha1 hε hvar' hΦb
  have h16 : Cv + 2 * 8 = Cv + 16 := by norm_num
  rw [h16] at hmain
  show ‖Work.KMTAreas.A7.randSymb (fun n ξ => if n = 0 then 0
      else if lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n
        then varphiNtj (Nat.floor (a n)) k₁ j t ξ else 0) ε K x‖ ≤ Cv + 16
  exact hmain

/-! ## The target -/

/-- **The `ℓ²`-bound for the randomised `f`-side packets of Case B.**  See the module docstring. -/
theorem lowModRandL2F (P : Polynomial ℤ) (C₀ : ℕ) : Work.KMTPlan.A6.LowModRandL2F P C₀ := by
  classical
  obtain ⟨Cvf, hCvf⟩ : ∃ Cvf : NNReal → ℝ, ∀ (Λ : NNReal) (hΛ : 1 < Λ),
      (0 ≤ Cvf Λ ∧ ∀ (a : ℕ → NNReal) (k : ℕ) (j : ℤ) (t x : ℝ) (K : ℕ),
        PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) → t ∈ Set.Icc (1 / 2 : ℝ) 1 →
        j ∈ ({-1, 0, 1} : Finset ℤ) → ¬ (k = 0 ∧ j = -1) →
        ∑ n ∈ Finset.range K, ‖varphiNtj (Nat.floor (a (n + 1))) k j t x
          - varphiNtj (Nat.floor (a n)) k j t x‖ ≤ Cvf Λ) := by
    refine ⟨fun Λ => if h : 1 < Λ then Classical.choose (lowModVarBoundAll Λ h) else 0, ?_⟩
    intro Λ hΛ
    dsimp only
    rw [dif_pos hΛ]
    exact Classical.choose_spec (lowModVarBoundAll Λ hΛ)
  rcases Nat.eq_zero_or_pos C₀ with h0 | hpos
  · -- ## the degenerate case `C₀ = 0`
    subst h0
    refine ⟨1, one_pos, ?_⟩
    intro ρ hρ _
    refine ⟨0, fun Λ => Real.toNNReal (6 * (Cvf Λ + 16)), ?_⟩
    intro a Λ l₁ l₂ k₁ k₂ K t j ε f hΛ ha ha1 hε ht hj hne hBL hf
    set Φ : ℝ → ℂ := Work.KMTAreas.A7.randSymb (lowModSymbF ρ 0 a l₁ l₂ k₁ k₂ j t) ε K
      with hΦ
    have hsup : ∀ y : ℝ, ‖Φ y‖ ≤ Cvf Λ + 16 := by
      intro y
      rw [hΦ]
      exact lowModSymbF_randSup Λ hΛ (Cvf Λ) (hCvf Λ hΛ).1 (hCvf Λ hΛ).2
        ρ 0 a l₁ l₂ k₁ k₂ K t j ε ha ha1 hε hj hne ht y
    have hΦmeas : Measurable Φ := by
      rw [hΦ]
      unfold Work.KMTAreas.A7.randSymb
      refine Finset.measurable_sum _ (fun n _ => ?_)
      exact Measurable.const_mul (Measurable.sub
        (measurable_lowModSymbF ρ 0 a l₁ l₂ k₁ k₂ j t (n + 1))
        (measurable_lowModSymbF ρ 0 a l₁ l₂ k₁ k₂ j t n)) (ε n)
    have hsupp1 : ∀ y : ℝ, Φ y ≠ 0 → |y| ≤ 1 := by
      intro y hy
      rw [hΦ] at hy
      obtain ⟨n, _hnK, hn⟩ := exists_ne_zero_of_randSymb_ne_zero hy
      obtain ⟨-, hls, hne0⟩ := support_lowModSymbF hn
      obtain ⟨-, -, hk₁, -⟩ := inIndexSet_zero_eq (l₁ := l₁) (l₂ := l₂) (k₁ := k₁) (k₂ := k₂)
        (Nr := Nat.floor (a n)) hls.1
      subst hk₁
      have hV : varphiNt (Nat.floor (a n)) 0 t y ≠ 0 :=
        varphiNt_ne_zero_of_varphiNtj_ne_zero _ _ _ _ _ hne0
      have hs := varphiNt_support_le_all 0 (Nat.floor (a n)) t y hV
      have hL := Work.Analysis.EndVar.logN_nonneg (Nat.floor (a n))
      have h2 : (2 : ℝ) ^ (((0 : ℕ) : ℝ)
          - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)) ≤ 1 := by
        have hle : (((0 : ℕ) : ℝ)
            - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)) ≤ 0 := by
          have hnn : (0 : ℝ) ≤ ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ) := by
            exact_mod_cast hL
          have h0 : (((0 : ℕ) : ℝ)) = 0 := Nat.cast_zero
          rw [h0]
          linarith
        calc (2 : ℝ) ^ (((0 : ℕ) : ℝ)
              - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ))
            ≤ (2 : ℝ) ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
          _ = 1 := Real.rpow_zero 2
      linarith
    have hφ0 : ∀ y : ℝ, 1 < |y| → Φ y = 0 := by
      intro y hy
      by_contra hne1
      have hle := hsupp1 y hne1
      linarith
    have hsym : ∀ ξ : Circ, ‖iwSymbolSet (diffFreqs ρ l₁) (periodize Φ) ξ‖
        ≤ 6 * (Cvf Λ + 16) := by
      intro ξ
      by_cases hlc : lcL l₁ l₂ k₁ k₂ = 0
      · obtain ⟨hl₁, hl₂, hk₁, hk₂⟩ := lcL_eq_zero hlc
        subst hl₁; subst hl₂; subst hk₁; subst hk₂
        rw [diffFreqs_zero_eq]
        have hsingle : iwSymbolSet ({(0 : Circ)} : Finset Circ) (periodize Φ) ξ
            = periodize Φ ξ := by
          simp [iwSymbolSet]
        rw [hsingle]
        have hper := norm_periodize_le (phi := Φ) (R := 1) (C := Cvf Λ + 16) 1
          (by norm_num : (1 : ℝ) ≤ (1 : ℕ)) hφ0 (fun y => hsup y) ξ
        have h6 : (2 * ((1 : ℕ) : ℝ) + 4) = 6 := by norm_num
        rw [h6] at hper
        linarith [(hCvf Λ hΛ).1]
      · have hfam : lowModSymbF ρ 0 a l₁ l₂ k₁ k₂ j t = 0 := by
          funext n y
          simp only [lowModSymbF, Pi.zero_apply]
          by_cases hn : n = 0
          · rw [if_pos hn]
          · rw [if_neg hn]
            have hnot : ¬ lowSmallSet ρ 0 a l₁ l₂ k₁ k₂ n := by
              rintro ⟨hidx, -⟩
              obtain ⟨hl₁, hl₂, hk₁, hk₂⟩ := inIndexSet_zero_eq hidx
              rw [lcL, hl₁, hl₂, hk₁, hk₂] at hlc
              simp at hlc
            rw [if_neg hnot]
        have hΦ0 : Φ = 0 := by
          rw [hΦ, hfam]
          funext y
          simp [Work.KMTAreas.A7.randSymb]
        have hsymzero : iwSymbolSet (diffFreqs ρ l₁) (periodize Φ) ξ = 0 := by
          rw [hΦ0]
          have hper0 : periodize (0 : ℝ → ℂ) = 0 := by funext y; simp [periodize]
          rw [hper0]
          simp [iwSymbolSet]
        rw [hsymzero, norm_zero]
        linarith [(hCvf Λ hΛ).1]
    have hmem : MemLp (iwSymbolSet (diffFreqs ρ l₁) (periodize Φ)) ⊤ circleMeasure :=
      Work.Analysis.IWMultiplier.memLp_iwSymbolSet _
        (Work.Analysis.IonescuWainger.memLp_periodize hΦmeas (by norm_num : (0 : ℝ) ≤ 1) hφ0
          (fun y => hsup y))
    have hmain := eLpNorm_iwConv_two_le_of_symbol_bound (diffFreqs ρ l₁) (periodize Φ)
      (6 * (Cvf Λ + 16)) (by linarith [(hCvf Λ hΛ).1]) hsym hmem f hf
    change MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ l₁
        (Work.KMTAreas.A7.randSymb (lowModSymbF ρ 0 a l₁ l₂ k₁ k₂ j t) ε K) f)
        2 MeasureTheory.Measure.count
      ≤ ((Real.toNNReal (6 * (Cvf Λ + 16)) : NNReal) : ENNReal)
        * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
    exact hmain
  · -- ## the main case `C₀ ≥ 1`
    refine ⟨min (1 / 2) (1 / (8 * (C₀ : ℝ))), lt_min (by norm_num) (by positivity), ?_⟩
    intro ρ hρ hρle
    have hρC₀ : ρ * (C₀ : ℝ) ≤ 1 / 8 := by
      have h : ρ ≤ 1 / (8 * (C₀ : ℝ)) := le_trans hρle (min_le_right _ _)
      have h8 : (0 : ℝ) < 8 * (C₀ : ℝ) := by positivity
      have h9 := (le_div_iff₀ h8).mp h
      linarith
    obtain ⟨Bs, hBs⟩ := lowModSymbF_support ρ hρ C₀ hpos hρC₀
    obtain ⟨Bna, hBna⟩ := nonAliasing_diffFreqs ρ hρ
    refine ⟨max Bs Bna, fun Λ => Real.toNNReal (6 * (Cvf Λ + 16)), ?_⟩
    intro a Λ l₁ l₂ k₁ k₂ K t j ε f hΛ ha ha1 hε ht hj hne hBL hf
    set Φ : ℝ → ℂ := Work.KMTAreas.A7.randSymb (lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j t) ε K
      with hΦ
    have hsup : ∀ y : ℝ, ‖Φ y‖ ≤ Cvf Λ + 16 := by
      intro y
      rw [hΦ]
      exact lowModSymbF_randSup Λ hΛ (Cvf Λ) (hCvf Λ hΛ).1 (hCvf Λ hΛ).2
        ρ C₀ a l₁ l₂ k₁ k₂ K t j ε ha ha1 hε hj hne ht y
    have hΦmeas : Measurable Φ := by
      rw [hΦ]
      unfold Work.KMTAreas.A7.randSymb
      refine Finset.measurable_sum _ (fun n _ => ?_)
      exact Measurable.const_mul (Measurable.sub
        (measurable_lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j t (n + 1))
        (measurable_lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j t n)) (ε n)
    have harc : ∀ y : ℝ, Φ y ≠ 0 →
        y ∈ realArc (-(3 * (uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ))) := by
      intro y hy
      rw [hΦ] at hy
      have h := hBs a l₁ l₂ k₁ k₂ t j ε K (le_trans (le_max_left _ _) hBL) y hy
      rw [realArc, Set.mem_Icc]
      exact abs_le.mp h
    have hφ0 : ∀ y : ℝ, 1 < |y| → Φ y = 0 := by
      intro y hy
      by_contra hne1
      have h := harc y hne1
      rw [realArc, Set.mem_Icc] at h
      have hle : (2 : ℝ) ^ (-(3 * (uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ))) ≤ 1 := by
        have h3 : (-(3 * (uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ)) : ℤ) ≤ 0 := by omega
        calc (2 : ℝ) ^ (-(3 * (uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ)))
            ≤ (2 : ℝ) ^ (0 : ℤ) := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h3
          _ = 1 := by simp
      have habs : |y| ≤ (2 : ℝ) ^ (-(3 * (uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ))) := by
        rw [abs_le]
        exact ⟨h.1, h.2⟩
      linarith
    have hΦb_per : ∀ ξ : Circ, ‖periodize Φ ξ‖ ≤ 6 * (Cvf Λ + 16) := by
      intro ξ
      have hper := norm_periodize_le (phi := Φ) (R := 1) (C := Cvf Λ + 16) 1
        (by norm_num : (1 : ℝ) ≤ (1 : ℕ)) hφ0 (fun y => hsup y) ξ
      have h6 : (2 * ((1 : ℕ) : ℝ) + 4) = 6 := by norm_num
      rw [h6] at hper
      exact hper
    have hna : NonAliasing (-(3 * (uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ))) (diffFreqs ρ l₁) :=
      hBna (lcL l₁ l₂ k₁ k₂) l₁ (le_trans (le_max_right _ _) hBL)
        (by rw [lcL]; exact le_trans (le_max_left _ _) (le_max_left _ _))
    have hsym : ∀ ξ : Circ, ‖iwSymbolSet (diffFreqs ρ l₁) (periodize Φ) ξ‖
        ≤ 6 * (Cvf Λ + 16) :=
      fun ξ => iwSymbolSet_narrow_bound ρ l₁ (-(3 * (uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ)))
        (periodize Φ) (6 * (Cvf Λ + 16)) (by linarith [(hCvf Λ hΛ).1])
        (fun ξ' => hΦb_per ξ') (supportedInArc_periodize' harc) hna ξ
    have hmem : MemLp (iwSymbolSet (diffFreqs ρ l₁) (periodize Φ)) ⊤ circleMeasure :=
      Work.Analysis.IWMultiplier.memLp_iwSymbolSet _
        (Work.Analysis.IonescuWainger.memLp_periodize hΦmeas (by norm_num : (0 : ℝ) ≤ 1) hφ0
          (fun y => hsup y))
    have hmain := eLpNorm_iwConv_two_le_of_symbol_bound (diffFreqs ρ l₁) (periodize Φ)
      (6 * (Cvf Λ + 16)) (by linarith [(hCvf Λ hΛ).1]) hsym hmem f hf
    change MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ l₁
        (Work.KMTAreas.A7.randSymb (lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j t) ε K) f)
        2 MeasureTheory.Measure.count
      ≤ ((Real.toNNReal (6 * (Cvf Λ + 16)) : NNReal) : ENNReal)
        * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
    exact hmain

end

end Work.KMTPlan.A6
