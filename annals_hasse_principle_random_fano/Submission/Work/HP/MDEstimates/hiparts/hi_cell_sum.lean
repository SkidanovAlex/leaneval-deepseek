import Mathlib
import Submission.Work.HP.MDEstimates.hiparts.HiDefs
import Submission.Work.HP.MDEstimates.hiparts.HiCellDefs
import Submission.Work.HP.MDEstimates.hiparts.hi_dyadic_idx
import Submission.Work.HP.MDEstimates.hiparts.hi_dyadic_jdx
import Submission.Work.HP.MDEstimates.hiparts.hi_min_dyadic
import Submission.Work.HP.MDEstimates.hiparts.hi_fiber_card
import Submission.Work.HP.Sig2.le_mul_log_of_div_log_le
import Submission.Work.HP.Sig2.log_pow_le_rpow
import Submission.Work.HP.MDEstimates.dyadic_sum_le

set_option autoImplicit false

namespace Work.HP.MDEstimates.hiparts

open Finset
open scoped BigOperators

/-! Small facts about the dyadic cutoffs. -/

/-- For `x ≥ 1`: `⌈logb 2 x⌉₊ + 1 ≤ 2 log x + 2`. -/
private lemma hi_ceil_logb_le (x : ℝ) (hx : 1 ≤ x) :
    ((⌈Real.logb 2 x⌉₊ : ℝ) + 1) ≤ 2 * Real.log x + 2 := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2 : 1 ≤ 2 * Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogb : Real.logb 2 x ≤ 2 * Real.log x := by
    rw [Real.logb, div_le_iff₀ hlog2pos]
    nlinarith [hlogx, h2]
  have hceil : (⌈Real.logb 2 x⌉₊ : ℝ) < Real.logb 2 x + 1 :=
    Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num) hx)
  linarith

/-- **Cell count** (private copy, proved here directly): the number of dyadic cells
`(⌈logb 2 (48 B²/A^{21/20})⌉₊ + 1)(⌈logb 2 A⌉₊ + 1)` is at most `K · B^{1/1000}` for `B ≥ B₀`. -/
private theorem hi_cell_count_aux :
    ∃ K B₀ : ℝ, 0 < K ∧ ∀ A B : ℝ, B₀ ≤ B → B / Real.log B ≤ A → A ≤ B ^ 2 →
      ((⌈Real.logb 2 (48 * B ^ 2 / A ^ ((21 : ℝ) / 20))⌉₊ : ℝ) + 1) *
        ((⌈Real.logb 2 A⌉₊ : ℝ) + 1) ≤ K * B ^ ((1 : ℝ) / 1000) := by
  obtain ⟨A₀, hA₀, hlogpow⟩ := Work.HP.Sig2.log_pow_le_rpow 2 (1 / 1000 : ℝ) (by norm_num)
  refine ⟨(2 * Real.log 48 + 6) * 6, max 4 (max 2 A₀), ?_, ?_⟩
  · have h : 0 < Real.log 48 := Real.log_pos (by norm_num)
    positivity
  intro A B hB hAB hAB2
  set Λ : ℝ := 48 * B ^ 2 / A ^ ((21 : ℝ) / 20) with hΛ
  have hB4 : (4 : ℝ) ≤ B := le_trans (le_max_left 4 _) hB
  have hB2 : (2 : ℝ) ≤ B := le_trans (by norm_num) hB4
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB4
  have hlogBnn : 0 ≤ Real.log B := Real.log_nonneg (by linarith)
  have hlogBpos : 0 < Real.log B := Real.log_pos (by linarith)
  have hlog48 : 0 ≤ Real.log 48 := Real.log_nonneg (by norm_num)
  have hlogBleB : Real.log B ≤ B := by
    have h := Real.log_le_sub_one_of_pos hBpos
    linarith
  have hbl : 1 ≤ B / Real.log B := by
    rw [le_div_iff₀ hlogBpos]
    simpa using hlogBleB
  have hA1 : 1 ≤ A := le_trans hbl hAB
  have hApos : 0 < A := lt_of_lt_of_le one_pos hA1
  have hΛpos : 0 < Λ := by
    rw [hΛ]
    exact div_pos (by positivity) (Real.rpow_pos_of_pos hApos _)
  -- bound on the `𝔡₃`-index
  have hI : ((⌈Real.logb 2 Λ⌉₊ : ℝ) + 1) ≤ (2 * Real.log 48 + 6) * (Real.log B + 1) := by
    by_cases hΛ1 : 1 ≤ Λ
    · have hceil : (⌈Real.logb 2 Λ⌉₊ : ℝ) < Real.logb 2 Λ + 1 :=
        Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num) hΛ1)
      have hAexp : (1 : ℝ) ≤ A ^ ((21 : ℝ) / 20) := Real.one_le_rpow hA1 (by norm_num)
      have hΛle : Λ ≤ 48 * B ^ 2 := by
        rw [hΛ, div_le_iff₀ (Real.rpow_pos_of_pos hApos _)]
        nlinarith [hAexp, sq_nonneg B]
      have hmono : Real.logb 2 Λ ≤ Real.logb 2 (48 * B ^ 2) :=
        Real.logb_le_logb_of_le (by norm_num) hΛpos hΛle
      have hlog48B : Real.logb 2 (48 * B ^ 2) ≤ 2 * Real.log (48 * B ^ 2) := by
        rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
        have h1 : Real.log (48 * B ^ 2) ≥ 0 := by
          apply Real.log_nonneg
          nlinarith [sq_nonneg B]
        nlinarith [h1, Real.log_two_gt_d9]
      have hlogmul : Real.log (48 * B ^ 2) = Real.log 48 + 2 * Real.log B := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        push_cast
        ring
      nlinarith [hceil, hmono, hlog48B, hlogmul, hlog48, hlogBnn]
    · have hΛlt : Λ < 1 := lt_of_not_ge hΛ1
      have hlogb0 : Real.logb 2 Λ ≤ 0 := by
        have hlt : Real.logb 2 Λ < Real.logb 2 1 :=
          Real.logb_lt_logb (by norm_num : (1:ℝ) < 2) hΛpos (by simpa using hΛlt)
        simpa using le_of_lt hlt
      have hI0 : ⌈Real.logb 2 Λ⌉₊ = 0 := by
        have h : ⌈Real.logb 2 Λ⌉₊ ≤ 0 := Nat.ceil_le.mpr (by simpa using hlogb0)
        exact le_antisymm h (Nat.zero_le _)
      rw [hI0]
      push_cast
      nlinarith [hlog48, hlogBnn]
  -- bound on the `λ₁`-index
  have hJ : ((⌈Real.logb 2 A⌉₊ : ℝ) + 1) ≤ 6 * (Real.log B + 1) := by
    have hceil : (⌈Real.logb 2 A⌉₊ : ℝ) < Real.logb 2 A + 1 :=
      Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num) hA1)
    have hlogbA : Real.logb 2 A ≤ 2 * Real.log A := by
      rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
      have h1 : 0 ≤ Real.log A := Real.log_nonneg hA1
      nlinarith [h1, Real.log_two_gt_d9]
    have hlogA2 : Real.log A ≤ 2 * Real.log B := by
      have h := Real.log_le_log hApos hAB2
      rw [Real.log_pow] at h
      push_cast at h
      linarith
    nlinarith [hceil, hlogbA, hlogA2, hlogBnn]
  have hBpow : (Real.log B + 1) ^ 2 ≤ B ^ ((1 : ℝ) / 1000) := by
    have hB0 : B ≥ A₀ := le_trans (le_trans (le_max_right 2 A₀) (le_max_right 4 _)) hB
    exact hlogpow B hB0
  have hnonneg : (0 : ℝ) ≤ 2 * Real.log 48 + 6 := by linarith
  have hIJ : ((⌈Real.logb 2 Λ⌉₊ : ℝ) + 1) * ((⌈Real.logb 2 A⌉₊ : ℝ) + 1)
      ≤ ((2 * Real.log 48 + 6) * 6) * (Real.log B + 1) ^ 2 := by
    have h1 := mul_le_mul hI hJ (by positivity)
      (by nlinarith [hnonneg, hlogBnn])
    calc ((⌈Real.logb 2 Λ⌉₊ : ℝ) + 1) * ((⌈Real.logb 2 A⌉₊ : ℝ) + 1)
        ≤ ((2 * Real.log 48 + 6) * (Real.log B + 1)) * (6 * (Real.log B + 1)) := h1
      _ = ((2 * Real.log 48 + 6) * 6) * (Real.log B + 1) ^ 2 := by ring
  rw [hΛ] at hIJ
  rw [hΛ]
  calc ((⌈Real.logb 2 (48 * B ^ 2 / A ^ ((21 : ℝ) / 20))⌉₊ : ℝ) + 1)
        * ((⌈Real.logb 2 A⌉₊ : ℝ) + 1)
      ≤ ((2 * Real.log 48 + 6) * 6) * (Real.log B + 1) ^ 2 := hIJ
    _ ≤ ((2 * Real.log 48 + 6) * 6) * B ^ ((1 : ℝ) / 1000) :=
        mul_le_mul_of_nonneg_left hBpow (by linarith)


private lemma hiDelta_nonneg (A : ℝ) (hA : 0 ≤ A) (i : ℕ) : 0 ≤ hiDelta A i := by
  rw [hiDelta]
  exact mul_nonneg (Real.rpow_nonneg hA _) (pow_nonneg (by norm_num) _)

private lemma hiDelta_pos (A : ℝ) (hA : 0 < A) (i : ℕ) : 0 < hiDelta A i := by
  rw [hiDelta]
  exact mul_pos (Real.rpow_pos_of_pos hA _) (pow_pos (by norm_num) _)

private lemma one_le_two_pow (i : ℕ) : (1 : ℝ) ≤ (2:ℝ) ^ i := by
  have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (1:ℝ) ≤ 2) i
  simpa using h

private lemma le_hiDelta (A : ℝ) (hA : 0 ≤ A) (i : ℕ) : A ^ ((1 : ℝ) / 20) ≤ hiDelta A i := by
  rw [hiDelta]
  exact le_mul_of_one_le_right (Real.rpow_nonneg hA _) (one_le_two_pow i)

private lemma one_le_hiM (j : ℕ) : 1 ≤ hiM j := by
  rw [hiM]
  exact one_le_two_pow j

private lemma hiM_pos (j : ℕ) : 0 < hiM j := lt_of_lt_of_le one_pos (one_le_hiM j)

/-- **Dyadic cell-sum reduction for the `𝔡₃ > A^{1/20}` part of the case-`I` sum at `(4,4)`.**
Abstract counting lemma: `F` is a finite set of "items" (in the application: pairs `(x,y)`), `d p`
plays the role of `𝔡₃(x,y)` and `l p` that of `λ₁(Γ_{x,y})`.  Each item is assumed to satisfy
`A^{1/20} ≤ d p ≤ 48 B²/A` and `1 ≤ l p ≤ A`, and the number of items with `d p ≤ Δ` and `l p ≤ M`
is assumed to be at most `Kl * hiLZ B Δ M`
(`hiLZ B Δ M = B^{9/2}Δ²(B^{3/2}+Δ^{3/2})(log 2Δ)²min{Δ,M^{53}}`, the convenient `ℓ^{(1)}` bound).

The conclusion bounds the sum of `hiMin A B (d p) (l p) = min_{4 ≤ R0 ≤ 67}(A^{68-R0}B^{2R0-8}(d p)^{-R0} + (2A/l p)^{67-R0})`
by `K * Kl * C0 * A^{68-1/32} B²`, where the hypothesis `harith` supplies the per-cell estimate
`hiLZ B (2Δ) (2M) * hiMin A B Δ M ≤ C0 A^{68-1/32} B² B^{-1/1000}` for every cell.

Hints.  Decompose `F` dyadically: put `i p = ⌊logb 2 (d p / A^{1/20})⌋₊` and `j p = ⌊logb 2 (l p)⌋₊`,
so that with `Δ i = A^{1/20} 2^i` and `M j = 2^j` one has `Δ (i p) ≤ d p < 2 * Δ (i p)` and
`M (j p) ≤ l p < 2 * M (j p)` (`Work.HP.MDEstimates.dyadic_index_props`).  Then
`hiMin A B (d p) (l p) ≤ hiMin A B (Δ (i p)) (M (j p))` (`hiMin_anti`), and grouping `F` by the
map `p ↦ (i p, j p)` (`Finset.sum_fiberwise_of_maps_to`) bounds the sum by
`Σ_{(i,j) ∈ image} (card of fibre) * hiMin A B (Δ i) (M j)`.  The fibre lies in
`{p : d p ≤ 2Δ i ∧ l p ≤ 2M j}`, so its cardinality is at most `Kl * hiLZ B (2Δ i) (2M j)`, and
`harith` then bounds each cell by `C0 A^{68-1/32} B² B^{-1/1000}`.  Restrict `i` to
`i ≤ I := ⌊logb 2 (48 B²/A^{21/20})⌋₊` and `j` to `j ≤ J := ⌊logb 2 A⌋₊` (all items are covered),
so that there are at most `(I+1)(J+1) ≤ (log B)^3` cells; the margin `B^{-1/1000}` absorbs this
factor once `B₀` is chosen large (`(log B)^m ≤ B^ε` for large `B`,
`Work.HP.Sig2.log_pow_le_rpow`). -/
theorem hi_cell_sum :
    ∃ K B₀ : ℝ, 0 < K ∧ ∀ A B : ℝ, B₀ ≤ B → B / Real.log B ≤ A → A ≤ B ^ 2 →
    ∀ Kl C0 : ℝ, 0 < Kl → 0 < C0 →
      (∀ Δ M : ℝ, A ^ ((1 : ℝ) / 20) ≤ Δ → Δ ≤ 48 * B ^ 2 / A → 1 ≤ M → M ≤ A →
        hiLZ B (2 * Δ) (2 * M) * hiMin A B Δ M
          ≤ C0 * A ^ ((68 : ℝ) - 1 / 32) * B ^ 2 * B ^ (-(1 / 1000 : ℝ))) →
      ∀ {ι : Type*} (F : Finset ι) (d l : ι → ℝ),
        (∀ p ∈ F, A ^ ((1 : ℝ) / 20) ≤ d p) → (∀ p ∈ F, d p ≤ 48 * B ^ 2 / A) →
        (∀ p ∈ F, 1 ≤ l p) → (∀ p ∈ F, l p ≤ A) →
        (∀ Δ M : ℝ, 1 ≤ Δ → 1 ≤ M →
          ((F.filter (fun p => d p ≤ Δ ∧ l p ≤ M)).card : ℝ) ≤ Kl * hiLZ B Δ M) →
        (∑ p ∈ F, hiMin A B (d p) (l p)) ≤ K * Kl * C0 * A ^ ((68 : ℝ) - 1 / 32) * B ^ 2 := by
  obtain ⟨Kc, Bc, hKcpos, hcount_cells⟩ := hi_cell_count_aux
  refine ⟨Kc, max 4 Bc, hKcpos, ?_⟩
  intro A B hBB hAB hAB2 Kl C0 hKl hC0 harith ι F d l hd0 hd48 hl0 hlA hcount
  have hB4 : (4 : ℝ) ≤ B := le_trans (le_max_left 4 Bc) hBB
  have hBc : Bc ≤ B := le_trans (le_max_right 4 Bc) hBB
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB4
  have hB1 : 1 < B := lt_of_lt_of_le (by norm_num) hB4
  have hlogBpos : 0 < Real.log B := Real.log_pos hB1
  have hlogBleB : Real.log B ≤ B := by
    have h := Real.log_le_sub_one_of_pos hBpos
    linarith
  have hbl : 1 ≤ B / Real.log B := by
    rw [le_div_iff₀ hlogBpos]
    simpa using hlogBleB
  have hA1 : 1 ≤ A := le_trans hbl hAB
  have hApos : 0 < A := lt_of_lt_of_le one_pos hA1
  have hAnonneg : 0 ≤ A := le_of_lt hApos
  -- the cell indices lie in the ranges
  have hmap : ∀ p ∈ F, (hiIdx A (d p), hiJdx (l p)) ∈
      Finset.range (hiI A B + 1) ×ˢ Finset.range (hiJ A + 1) := by
    intro p hp
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (hi_dyadic_idx A B (d p) hApos (hd0 p hp) (hd48 p hp)).2.2,
      Nat.lt_succ_of_le (hi_dyadic_jdx A (l p) hA1 (hl0 p hp) (hlA p hp)).2.2⟩
  have hpoint : ∀ p ∈ F, hiMin A B (d p) (l p)
      ≤ hiMin A B (hiDelta A (hiIdx A (d p))) (hiM (hiJdx (l p))) :=
    fun p hp => hi_min_dyadic A B (d p) (l p) hApos hBpos (hd0 p hp) (hl0 p hp)
  have hfiber := Finset.sum_fiberwise_of_maps_to hmap
    (fun p => hiMin A B (hiDelta A (hiIdx A (d p))) (hiM (hiJdx (l p))))
  -- per cell bound
  have hcell : ∀ c : ℕ × ℕ,
      (∑ p ∈ F.filter (fun p => (hiIdx A (d p), hiJdx (l p)) = c),
          hiMin A B (hiDelta A c.1) (hiM c.2))
        ≤ Kl * (C0 * A ^ ((68 : ℝ) - 1 / 32) * B ^ 2 * B ^ (-(1 / 1000 : ℝ))) := by
    intro c
    by_cases hne : (F.filter (fun p => (hiIdx A (d p), hiJdx (l p)) = c)).Nonempty
    · obtain ⟨p, hp⟩ := hne
      rw [Finset.mem_filter] at hp
      obtain ⟨hpF, hpc⟩ := hp
      have hpi : hiIdx A (d p) = c.1 := congrArg Prod.fst hpc
      have hpj : hiJdx (l p) = c.2 := congrArg Prod.snd hpc
      have hfilt : F.filter (fun p => (hiIdx A (d p), hiJdx (l p)) = c)
          = F.filter (fun p => hiIdx A (d p) = c.1 ∧ hiJdx (l p) = c.2) := by
        apply Finset.filter_congr
        intro p hp
        exact ⟨fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩, fun h => Prod.ext h.1 h.2⟩
      have hcard := hi_fiber_card F d l A B Kl hApos hA1 hKl.le hd0 hl0 hcount c.1 c.2
      have hcard' : ((F.filter (fun p => (hiIdx A (d p), hiJdx (l p)) = c)).card : ℝ)
          ≤ Kl * hiLZ B (2 * hiDelta A c.1) (2 * hiM c.2) := by
        rw [hfilt]
        exact hcard
      have hΔlo : A ^ ((1 : ℝ) / 20) ≤ hiDelta A c.1 := le_hiDelta A hAnonneg c.1
      have hΔhi : hiDelta A c.1 ≤ 48 * B ^ 2 / A := by
        have h1 := (hi_dyadic_idx A B (d p) hApos (hd0 p hpF) (hd48 p hpF)).1
        rw [hpi] at h1
        exact le_trans h1 (hd48 p hpF)
      have hMlo : 1 ≤ hiM c.2 := one_le_hiM c.2
      have hMhi : hiM c.2 ≤ A := by
        have h1 := (hi_dyadic_jdx A (l p) hA1 (hl0 p hpF) (hlA p hpF)).1
        rw [hpj] at h1
        exact le_trans h1 (hlA p hpF)
      have har := harith (hiDelta A c.1) (hiM c.2) hΔlo hΔhi hMlo hMhi
      have hGnn : 0 ≤ hiMin A B (hiDelta A c.1) (hiM c.2) :=
        hiMin_nonneg A B (hiDelta A c.1) (hiM c.2) hAnonneg hBpos.le
          (le_of_lt (hiDelta_pos A hApos c.1)) (hiM_pos c.2)
      have hsum_eq : (∑ p ∈ F.filter (fun p => (hiIdx A (d p), hiJdx (l p)) = c),
            hiMin A B (hiDelta A c.1) (hiM c.2))
          = ((F.filter (fun p => (hiIdx A (d p), hiJdx (l p)) = c)).card : ℝ)
            * hiMin A B (hiDelta A c.1) (hiM c.2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      rw [hsum_eq]
      calc ((F.filter (fun p => (hiIdx A (d p), hiJdx (l p)) = c)).card : ℝ)
              * hiMin A B (hiDelta A c.1) (hiM c.2)
          ≤ (Kl * hiLZ B (2 * hiDelta A c.1) (2 * hiM c.2)) * hiMin A B (hiDelta A c.1) (hiM c.2) :=
            mul_le_mul_of_nonneg_right hcard' hGnn
        _ = Kl * (hiLZ B (2 * hiDelta A c.1) (2 * hiM c.2)
              * hiMin A B (hiDelta A c.1) (hiM c.2)) := by ring
        _ ≤ Kl * (C0 * A ^ ((68 : ℝ) - 1 / 32) * B ^ 2 * B ^ (-(1 / 1000 : ℝ))) :=
            mul_le_mul_of_nonneg_left har hKl.le
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
      exact mul_nonneg hKl.le (mul_nonneg (mul_nonneg (mul_nonneg hC0.le
        (Real.rpow_nonneg hAnonneg _)) (sq_nonneg B)) (Real.rpow_nonneg hBpos.le _))
  have hcellsum : (∑ c ∈ Finset.range (hiI A B + 1) ×ˢ Finset.range (hiJ A + 1),
        ∑ p ∈ F.filter (fun p => (hiIdx A (d p), hiJdx (l p)) = c),
          hiMin A B (hiDelta A c.1) (hiM c.2))
      ≤ ∑ c ∈ Finset.range (hiI A B + 1) ×ˢ Finset.range (hiJ A + 1),
          Kl * (C0 * A ^ ((68 : ℝ) - 1 / 32) * B ^ 2 * B ^ (-(1 / 1000 : ℝ))) :=
    Finset.sum_le_sum (fun c _ => hcell c)
  have hstep5 : (∑ c ∈ Finset.range (hiI A B + 1) ×ˢ Finset.range (hiJ A + 1),
          Kl * (C0 * A ^ ((68 : ℝ) - 1 / 32) * B ^ 2 * B ^ (-(1 / 1000 : ℝ))))
      = ((hiI A B : ℝ) + 1) * ((hiJ A : ℝ) + 1)
          * (Kl * (C0 * A ^ ((68 : ℝ) - 1 / 32) * B ^ 2 * B ^ (-(1 / 1000 : ℝ)))) := by
    rw [Finset.sum_const, Finset.card_product, Finset.card_range, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  have hcells : ((hiI A B : ℝ) + 1) * ((hiJ A : ℝ) + 1) ≤ Kc * B ^ ((1 : ℝ) / 1000) := by
    simpa [hiI, hiJ] using hcount_cells A B hBc hAB hAB2
  have hZnn : 0 ≤ Kl * (C0 * A ^ ((68 : ℝ) - 1 / 32) * B ^ 2 * B ^ (-(1 / 1000 : ℝ))) :=
    mul_nonneg hKl.le (mul_nonneg (mul_nonneg (mul_nonneg hC0.le
      (Real.rpow_nonneg hAnonneg _)) (sq_nonneg B)) (Real.rpow_nonneg hBpos.le _))
  have hB1rpow : B ^ ((1 : ℝ) / 1000) * B ^ (-(1 / 1000 : ℝ)) = 1 := by
    rw [← Real.rpow_add hBpos]
    norm_num
  have hkey : (Kc * B ^ ((1 : ℝ) / 1000))
        * (Kl * (C0 * A ^ ((68 : ℝ) - 1 / 32) * B ^ 2 * B ^ (-(1 / 1000 : ℝ))))
      = Kc * Kl * C0 * A ^ ((68 : ℝ) - 1 / 32) * B ^ 2 := by
    rw [show (Kc * B ^ ((1 : ℝ) / 1000))
          * (Kl * (C0 * A ^ ((68 : ℝ) - 1 / 32) * B ^ 2 * B ^ (-(1 / 1000 : ℝ))))
        = Kc * Kl * C0 * A ^ ((68 : ℝ) - 1 / 32) * B ^ 2
          * (B ^ ((1 : ℝ) / 1000) * B ^ (-(1 / 1000 : ℝ))) from by ring]
    rw [hB1rpow, mul_one]
  calc (∑ p ∈ F, hiMin A B (d p) (l p))
      ≤ ∑ p ∈ F, hiMin A B (hiDelta A (hiIdx A (d p))) (hiM (hiJdx (l p))) :=
        Finset.sum_le_sum hpoint
    _ = ∑ c ∈ Finset.range (hiI A B + 1) ×ˢ Finset.range (hiJ A + 1),
          ∑ p ∈ F.filter (fun p => (hiIdx A (d p), hiJdx (l p)) = c),
            hiMin A B (hiDelta A (hiIdx A (d p))) (hiM (hiJdx (l p))) := hfiber.symm
    _ = ∑ c ∈ Finset.range (hiI A B + 1) ×ˢ Finset.range (hiJ A + 1),
          ∑ p ∈ F.filter (fun p => (hiIdx A (d p), hiJdx (l p)) = c),
            hiMin A B (hiDelta A c.1) (hiM c.2) := by
        refine Finset.sum_congr rfl (fun c hc => ?_)
        refine Finset.sum_congr rfl (fun p hp => ?_)
        have hp' : (hiIdx A (d p), hiJdx (l p)) = c := (Finset.mem_filter.mp hp).2
        have hpi : hiIdx A (d p) = c.1 := congrArg Prod.fst hp'
        have hpj : hiJdx (l p) = c.2 := congrArg Prod.snd hp'
        rw [hpi, hpj]
    _ ≤ ∑ c ∈ Finset.range (hiI A B + 1) ×ˢ Finset.range (hiJ A + 1),
          Kl * (C0 * A ^ ((68 : ℝ) - 1 / 32) * B ^ 2 * B ^ (-(1 / 1000 : ℝ))) := hcellsum
    _ = ((hiI A B : ℝ) + 1) * ((hiJ A : ℝ) + 1)
          * (Kl * (C0 * A ^ ((68 : ℝ) - 1 / 32) * B ^ 2 * B ^ (-(1 / 1000 : ℝ)))) := hstep5
    _ ≤ (Kc * B ^ ((1 : ℝ) / 1000))
          * (Kl * (C0 * A ^ ((68 : ℝ) - 1 / 32) * B ^ 2 * B ^ (-(1 / 1000 : ℝ)))) :=
        mul_le_mul_of_nonneg_right hcells hZnn
    _ = Kc * Kl * C0 * A ^ ((68 : ℝ) - 1 / 32) * B ^ 2 := hkey

end Work.HP.MDEstimates.hiparts
