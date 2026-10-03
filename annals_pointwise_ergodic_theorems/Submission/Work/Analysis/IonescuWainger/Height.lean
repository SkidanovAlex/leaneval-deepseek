/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Submission.Work.Analysis.IonescuWainger.iwPconcrete_contains_range

/-!
# The Ionescu–Wainger height: monotonicity, the naive comparison, and the level sets

Continuing Appendix A of Krause–Mirek–Tao.  The main results here are

* `iwP_mono` — the admissible denominator sets `P_{≤l}` are non-decreasing in `l`;
* `iwArithFreqs_eq` / `iwHeight_le_iff` — `(ℚ/ℤ)_{≤l}` is exactly the level set
  `{α : Height_ρ(α) ≤ 2^l}` of the IW height;
* `iwHeight_le_naiveHeight` — `Height_ρ(α) ≤ Height_naive(α)`, i.e. `mag-lem`(i);
* `iwArithFreqs_mono` — `(ℚ/ℤ)_{≤l}` is non-decreasing in `l`.

The definitional facts about `naiveHeight` are collected in
`Submission.Work.Analysis.IonescuWainger.NaiveHeight`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Analysis.IonescuWainger

open MeasureTheory

theorem iwP_succ {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l : ℕ) : iwP ρ l ⊆ iwP ρ (l + 1) := by
  intro q hq
  rw [mem_iwP] at hq ⊢
  rcases hq with ⟨hl, h1, h2⟩ | ⟨hl, hq⟩
  · by_cases h : l + 1 ≤ iwC0 ρ
    · refine Or.inl ⟨h, h1, ?_⟩
      have : (2 : ℕ) ^ l ≤ 2 ^ (l + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ l)
      omega
    · refine Or.inr ⟨not_le.mp h, ?_⟩
      refine iwPconcrete_contains_range hρ hρ1 (l := l + 1) (q := q) (by omega) h1 ?_
      have : (2 : ℕ) ^ l ≤ 2 ^ (l + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ l)
      omega
  · refine Or.inr ⟨by omega, iwPconcrete_mono (Nat.le_succ l) hq⟩

/-- The Ionescu–Wainger denominator sets are non-decreasing in the height parameter `l`. -/
theorem iwP_mono {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) : Monotone (iwP ρ) :=
  monotone_nat_of_le_succ (iwP_succ hρ hρ1)

theorem iwArithFreqs_mono {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) : Monotone (iwArithFreqs ρ) := by
  intro l l' hll' α hα
  rw [mem_iwArithFreqs] at hα ⊢
  obtain ⟨q, hq, hqα⟩ := hα
  exact ⟨q, iwP_mono hρ hρ1 hll' hq, hqα⟩

/-- The denominator `q = addOrderOf α` of a torsion frequency belongs to `P_{≤⌈log₂ q⌉}`:
this is the inclusion `[2^l] ⊆ P_{≤l}` of Appendix A. -/
theorem addOrderOf_mem_iwP {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {α : Circle}
    (hα : IsOfFinAddOrder α) : addOrderOf α ∈ iwP ρ (Nat.clog 2 (addOrderOf α)) := by
  have ho0 : 0 < addOrderOf α := addOrderOf_pos_iff.mpr hα
  rw [mem_iwP]
  by_cases hc : Nat.clog 2 (addOrderOf α) ≤ iwC0 ρ
  · exact Or.inl ⟨hc, ho0, Nat.le_pow_clog (by norm_num) _⟩
  · exact Or.inr ⟨not_le.mp hc,
      iwPconcrete_contains_range hρ hρ1 (le_of_lt (not_le.mp hc)) ho0
        (Nat.le_pow_clog (by norm_num) _)⟩

/-- For a torsion frequency there is some `l` with `α ∈ (ℚ/ℤ)_{≤l}`: the nonemptiness statement
underlying the well-definedness of the IW height. -/
theorem exists_mem_iwArithFreqs {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {α : Circle}
    (hα : IsOfFinAddOrder α) : ∃ l : ℕ, α ∈ iwArithFreqs ρ l := by
  refine ⟨max (iwC0 ρ) (Nat.clog 2 (addOrderOf α)), ?_⟩
  rw [mem_iwArithFreqs]
  exact ⟨addOrderOf α, iwP_mono hρ hρ1 (le_max_right _ _) (addOrderOf_mem_iwP hρ hρ1 hα),
    addOrderOf_nsmul_eq_zero α⟩

/-- **`mag-lem`(i) and (ii) combined**: for a torsion frequency, `Height_ρ(α) ≤ 2^l` if and only
if `α ∈ (ℚ/ℤ)_{≤l}`. -/
theorem iwHeight_le_iff {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {α : Circle}
    (hα : IsOfFinAddOrder α) {l : ℕ} :
    iwHeight ρ α ≤ 2 ^ l ↔ α ∈ iwArithFreqs ρ l := by
  have hne : ({l : ℕ | ∃ q ∈ iwP ρ l, q • α = 0}).Nonempty := by
    obtain ⟨l, hl⟩ := exists_mem_iwArithFreqs hρ hρ1 hα
    exact ⟨l, mem_iwArithFreqs.mp hl⟩
  rw [iwHeight, Nat.pow_le_pow_iff_right (by norm_num : 1 < 2), iwHeightIndex,
    mem_iwArithFreqs]
  constructor
  · intro h
    obtain ⟨q, hq, hqα⟩ := Nat.sInf_mem hne
    exact ⟨q, iwP_mono hρ hρ1 h hq, hqα⟩
  · rintro ⟨q, hq, hqα⟩
    exact Nat.sInf_le ⟨q, hq, hqα⟩

/-- `Height_ρ(α)` is the smallest dyadic number `2^l` with `α ∈ (ℚ/ℤ)_{≤l}`. -/
theorem iwHeight_mem {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {α : Circle}
    (hα : IsOfFinAddOrder α) : α ∈ iwArithFreqs ρ (iwHeightIndex ρ α) := by
  have hne : ({l : ℕ | ∃ q ∈ iwP ρ l, q • α = 0}).Nonempty := by
    obtain ⟨l, hl⟩ := exists_mem_iwArithFreqs hρ hρ1 hα
    exact ⟨l, mem_iwArithFreqs.mp hl⟩
  rw [mem_iwArithFreqs]
  exact Nat.sInf_mem hne

end Work.Analysis.IonescuWainger
