import Mathlib
import Submission.Ell2Greedy

open Submission.L2Norm

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

/-!
# Prop ell-2 update: counting-form assembly (`ell2_update_counting`)

Tikhomirov 2020, Section 3, `Prop ell-2 update` (paper lines ~1013–1120).
This file assembles the deterministic greedy-interval machinery of
`Submission.Ell2Greedy` (shell threshold choice, good-block covering,
per-block aux-averaging count, union/Markov count) and the ℓ₂-drop lemma
(`Submission.L2Norm.l2_drop_shift`) into the counting form of the proposition:

for `Y` uniform on an integer interval `J` of cardinality at least `N`, all but
`1024μ·|J|` shifts `y` satisfy the ℓ₂-drop inequality
`‖(1−p)g₁ + p·g₂(·+y)‖₂² ≤ (1−p)‖g₁‖₂² + p‖g₂‖₂² − p(1−p)μ⁶R²N/2`.

Hypotheses mirror the paper: `g₁` nonnegative with `ratioLip (μ⁴)`,
`Σ_{Ĩ} g₁ ≤ 2RN` (`Ĩ` = the doubled interval), and at least `μN` spikes of
`g₁ ≥ 8R` on `I₀ = [lo, lo+N−1]`; `g₁,g₂` in ℓ₂.
-/

namespace Submission.Ell2Greedy

attribute [local instance] Classical.propDecidable

open scoped BigOperators

/-- For a shift `y`, the set of "bad" points of the doubled interval `Ĩ`:
`|g₁ t − g₂(t+y)| ≥ κ/2`. -/
def ItBad (g1 g2 : ℤ → ℝ) (κ : ℝ) (lo : ℤ) (N : ℕ) (y : ℤ) : Finset ℤ :=
  (It lo N).filter (fun t : ℤ => κ / 2 ≤ |g1 t - g2 (t + y)|)

/-- A block's bad points (inside its interval). -/
def blockBad (g1 g2 : ℤ → ℝ) (κ : ℝ) (y : ℤ) (b : ℤ × ℤ) : Finset ℤ :=
  (Finset.Icc b.1 b.2).filter (fun t : ℤ => κ / 2 ≤ |g1 t - g2 (t + y)|)

/-- membership in `ItBad`. -/
lemma mem_ItBad_iff {g1 g2 : ℤ → ℝ} {κ : ℝ} {lo : ℤ} {N : ℕ} {y t : ℤ} :
    t ∈ ItBad g1 g2 κ lo N y ↔
      t ∈ It lo N ∧ κ / 2 ≤ |g1 t - g2 (t + y)| := by
  simp [ItBad]

/-- membership in `blockBad`. -/
lemma mem_blockBad_iff {g1 g2 : ℤ → ℝ} {κ : ℝ} {y : ℤ} {b : ℤ × ℤ} {t : ℤ} :
    t ∈ blockBad g1 g2 κ y b ↔
      t ∈ Finset.Icc b.1 b.2 ∧ κ / 2 ≤ |g1 t - g2 (t + y)| := by
  simp [blockBad]

/-- The bad points of a block are exactly `blockBad`, so its cardinality is
`badInBlock`. -/
lemma blockBad_card (g1 g2 : ℤ → ℝ) (κ : ℝ) (y : ℤ) (b : ℤ × ℤ) :
    (blockBad g1 g2 κ y b).card = badInBlock g1 g2 κ y b := by
  rfl


/-- All bad points of the good blocks lie inside the doubled interval's bad set
(blocks are subintervals of `Ĩ`). -/
theorem bad_points_in_It {g1 : ℤ → ℝ} {a R μ : ℝ} {lo : ℤ} {N : ℕ}
    (hμ0 : 0 < μ) (hμ1 : μ ≤ 1 / 64) (hR0 : 0 < R) (ha0 : 0 < a) (ha4R : 4 * R ≤ a)
    (hN1 : 1 ≤ N) (hg10 : ∀ t : ℤ, 0 ≤ g1 t)
    (hlip : Ell2Update.ratioLip (μ ^ 4) g1)
    (hmass : (∑ t ∈ It lo N, g1 t) ≤ 2 * R * (N : ℝ))
    (Bfin : Finset (ℤ × ℤ)) (hB : ∀ b ∈ Bfin,
      b ∈ coverBlocks g1 a μ lo N (largeSorted g1 a μ lo N)) :
    ∀ (g2 : ℤ → ℝ) (κ : ℝ) (y : ℤ),
      Bfin.biUnion (fun b : ℤ × ℤ => blockBad g1 g2 κ y b) ⊆ ItBad g1 g2 κ lo N y := by
  intro g2 κ y t ht
  rw [Finset.mem_biUnion] at ht
  rcases ht with ⟨b, hb, htb⟩
  have hsub := block_subset_It_of_mem (g := g1) (a := a) (R := R) (μ := μ) (lo := lo) (N := N)
    hμ0 hμ1 hR0 ha0 ha4R hN1 hg10 hlip hmass (hB b hb)
  rw [mem_ItBad_iff]
  rw [mem_blockBad_iff] at htb
  exact ⟨hsub htb.1, htb.2⟩

/-- The per-block bad sets of a disjoint block family are pairwise disjoint. -/
theorem blockBad_disjoint {g1 : ℤ → ℝ} {a μ : ℝ} {lo : ℤ} {N : ℕ}
    (Bfin : Finset (ℤ × ℤ))
    (hB : ∀ b ∈ Bfin, b ∈ coverBlocks g1 a μ lo N (largeSorted g1 a μ lo N)) :
    ∀ (g2 : ℤ → ℝ) (κ : ℝ) (y : ℤ),
      (↑Bfin : Set (ℤ × ℤ)).PairwiseDisjoint
        (fun b : ℤ × ℤ => blockBad g1 g2 κ y b) := by
  intro g2 κ y b1 hb1 b2 hb2 hne
  have hsep := coverBlocks_pairwise_sep (g := g1) (a := a) (μ := μ) (lo := lo) (N := N)
    (largeSorted g1 a μ lo N)
  have hI := block_intervals_disjoint_of_mem hsep (hB b1 hb1) (hB b2 hb2) hne
  exact Finset.disjoint_filter_filter (p := fun t : ℤ => κ / 2 ≤ |g1 t - g2 (t + y)|)
    (q := fun t : ℤ => κ / 2 ≤ |g1 t - g2 (t + y)|) hI

/-- total bad points over `Ĩ` are at least the sum over the good blocks. -/
theorem sum_blockBad_le_ItBad {g1 : ℤ → ℝ} {a R μ : ℝ} {lo : ℤ} {N : ℕ}
    (hμ0 : 0 < μ) (hμ1 : μ ≤ 1 / 64) (hR0 : 0 < R) (ha0 : 0 < a) (ha4R : 4 * R ≤ a)
    (hN1 : 1 ≤ N) (hg10 : ∀ t : ℤ, 0 ≤ g1 t)
    (hlip : Ell2Update.ratioLip (μ ^ 4) g1)
    (hmass : (∑ t ∈ It lo N, g1 t) ≤ 2 * R * (N : ℝ))
    (Bfin : Finset (ℤ × ℤ)) (hB : ∀ b ∈ Bfin,
      b ∈ coverBlocks g1 a μ lo N (largeSorted g1 a μ lo N)) :
    ∀ (g2 : ℤ → ℝ) (κ : ℝ) (y : ℤ),
      (∑ b ∈ Bfin, ((badInBlock g1 g2 κ y b : ℕ) : ℝ)) ≤
        ((ItBad g1 g2 κ lo N y).card : ℝ) := by
  classical
  intro g2 κ y
  have hdisj := blockBad_disjoint (a := a) (μ := μ) (lo := lo) (N := N)
    (Bfin := Bfin) hB g2 κ y
  have hcard := Finset.card_biUnion (s := Bfin)
    (t := fun b : ℤ × ℤ => blockBad g1 g2 κ y b) hdisj
  have hsub := bad_points_in_It (g1 := g1) (a := a) (R := R) (μ := μ) (lo := lo) (N := N)
    hμ0 hμ1 hR0 ha0 ha4R hN1 hg10 hlip hmass (Bfin := Bfin) hB g2 κ y
  have hleU : (Bfin.biUnion (fun b : ℤ × ℤ => blockBad g1 g2 κ y b)).card ≤
      (ItBad g1 g2 κ lo N y).card := Finset.card_le_card hsub
  have hcardEq : (∑ b ∈ Bfin, (blockBad g1 g2 κ y b).card) ≤
      (ItBad g1 g2 κ lo N y).card := by
    calc
      (∑ b ∈ Bfin, (blockBad g1 g2 κ y b).card)
          = (Bfin.biUnion (fun b : ℤ × ℤ => blockBad g1 g2 κ y b)).card := hcard.symm
      _ ≤ (ItBad g1 g2 κ lo N y).card := hleU
  rw [show (∑ b ∈ Bfin, ((badInBlock g1 g2 κ y b : ℕ) : ℝ)) =
      (∑ b ∈ Bfin, ((blockBad g1 g2 κ y b).card : ℝ)) by
        apply Finset.sum_congr rfl
        intro b hb
        rw [blockBad_card]]
  exact_mod_cast hcardEq

/-- (drop lower-bound implication) from `manyBad` the total number of bad
points of `Ĩ` is at least `μ²N/2`. -/theorem bad_points_ge_of_manyBad {g1 g2 : ℤ → ℝ} {a R μ : ℝ} {lo : ℤ} {N : ℕ} {y : ℤ}
    (hμ0 : 0 < μ) (hμ1 : μ ≤ 1 / 64) (hR0 : 0 < R) (ha0 : 0 < a) (ha4R : 4 * R ≤ a)
    (hN1 : 1 ≤ N) (hg10 : ∀ t : ℤ, 0 ≤ g1 t)
    (hlip : Ell2Update.ratioLip (μ ^ 4) g1)
    (hmass : (∑ t ∈ It lo N, g1 t) ≤ 2 * R * (N : ℝ))
    (Bfin : Finset (ℤ × ℤ)) (hB : ∀ b ∈ Bfin,
      b ∈ coverBlocks g1 a μ lo N (largeSorted g1 a μ lo N))
    (hmany : manyBad g1 g2 μ (kappa μ R) N Bfin y) :
    μ ^ 2 * (N : ℝ) / 2 ≤ ((ItBad g1 g2 (kappa μ R) lo N y).card : ℝ) := by
  classical
  let κ : ℝ := kappa μ R
  let cond : ℤ × ℤ → Prop := fun b =>
    (8 * μ) * ((Finset.Icc b.1 b.2).card : ℝ) / 4 ≤ (badInBlock g1 g2 κ y b : ℝ)
  let S : ℝ := ∑ b ∈ Bfin, (ilen b.1 b.2 : ℝ) * (if cond b then 1 else 0)
  have hS : μ * (N : ℝ) / 4 ≤ S := by
    dsimp [S, κ, cond]
    exact hmany
  have hEsum : (∑ b ∈ Bfin, ((badInBlock g1 g2 κ y b : ℕ) : ℝ)) ≤
      ((ItBad g1 g2 κ lo N y).card : ℝ) := by
    simpa using (sum_blockBad_le_ItBad (g1 := g1) (a := a) (R := R) (μ := μ) (lo := lo)
      (N := N) hμ0 hμ1 hR0 ha0 ha4R hN1 hg10 hlip hmass (Bfin := Bfin) hB g2 κ y)
  have hterm : ∀ b ∈ Bfin,
      (if cond b then (2 * μ) * (ilen b.1 b.2 : ℝ) else 0) ≤ (badInBlock g1 g2 κ y b : ℝ) := by
    intro b hb
    by_cases hc : cond b
    · have hc' : (8 * μ) * (ilen b.1 b.2 : ℝ) / 4 ≤ (badInBlock g1 g2 κ y b : ℝ) := by
        exact hc
      have hdiv : (8 * μ) * (ilen b.1 b.2 : ℝ) / 4 = (2 * μ) * (ilen b.1 b.2 : ℝ) := by ring_nf
      have hle : (2 * μ) * (ilen b.1 b.2 : ℝ) ≤ (badInBlock g1 g2 κ y b : ℝ) := by
        rwa [hdiv] at hc'
      rw [if_pos hc]
      exact hle
    · rw [if_neg hc]
      exact_mod_cast Nat.zero_le _
  have hLHS : (∑ b ∈ Bfin, (if cond b then (2 * μ) * (ilen b.1 b.2 : ℝ) else 0)) = (2 * μ) * S := by
    calc
      (∑ b ∈ Bfin, (if cond b then (2 * μ) * (ilen b.1 b.2 : ℝ) else 0))
          = (∑ b ∈ Bfin, (2 * μ) * ((ilen b.1 b.2 : ℝ) * (if cond b then 1 else 0))) := by
            apply Finset.sum_congr rfl
            intro b hb
            by_cases hc : cond b
            · simp [hc]
            · simp [hc]
      _ = (2 * μ) * (∑ b ∈ Bfin, (ilen b.1 b.2 : ℝ) * (if cond b then 1 else 0)) := by
            rw [Finset.mul_sum]
      _ = (2 * μ) * S := by
            rfl
  have hsumle := Finset.sum_le_sum (s := Bfin) hterm
  have hSge : (2 * μ) * S ≤ ∑ b ∈ Bfin, (badInBlock g1 g2 κ y b : ℝ) := by
    rw [← hLHS]
    exact hsumle
  have hchain1 : (2 * μ) * (μ * (N : ℝ) / 4) ≤ (2 * μ) * S := by
    exact mul_le_mul_of_nonneg_left hS (by positivity)
  have hred : (2 * μ) * (μ * (N : ℝ) / 4) = μ ^ 2 * (N : ℝ) / 2 := by ring_nf
  have hres : μ ^ 2 * (N : ℝ) / 2 ≤ ((ItBad g1 g2 κ lo N y).card : ℝ) := by
    calc
      μ ^ 2 * (N : ℝ) / 2 = (2 * μ) * (μ * (N : ℝ) / 4) := by rw [hred]
      _ ≤ (2 * μ) * S := hchain1
      _ ≤ ∑ b ∈ Bfin, (badInBlock g1 g2 κ y b : ℝ) := hSge
      _ ≤ (ItBad g1 g2 κ lo N y).card := hEsum
  simpa [κ] using hres

theorem drop_of_manyBad {g1 g2 : ℤ → ℝ} {R μ p : ℝ} {lo : ℤ} {N : ℕ} {y : ℤ}
    (hμ0 : 0 < μ) (hμ1 : μ ≤ 1 / 64) (hR0 : 0 < R) (hN1 : 1 ≤ N)
    (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hg1sq : Summable (fun t : ℤ => (g1 t) ^ 2)) (hg2sq : Summable (fun t : ℤ => (g2 t) ^ 2))
    (hEbig : μ ^ 2 * (N : ℝ) / 2 ≤
      (((It lo N).filter (fun t : ℤ => kappa μ R / 2 ≤ |g1 t - g2 (t + y)|)).card : ℝ)) :
    norm₂sq (fun t : ℤ => (1 - p) * g1 t + p * g2 (t + y)) ≤
      (1 - p) * norm₂sq g1 + p * norm₂sq g2 -
        (1 / 2) * p * (1 - p) * μ ^ 6 * R ^ 2 * (N : ℝ) := by
  classical
  let E : Finset ℤ := (It lo N).filter (fun t : ℤ => kappa μ R / 2 ≤ |g1 t - g2 (t + y)|)
  have hκ0 : 0 ≤ kappa μ R / 2 := by
    have hpos := kappa_pos hμ0 hR0
    positivity
  have hdrop := l2_drop_shift (p := p) (le_of_lt hp0) hp1 hg1sq hg2sq y E (k := E.card) (le_rfl)
    (κ := kappa μ R / 2) hκ0 (by
      intro t ht
      exact (Finset.mem_filter.mp ht).2)
  have hκhalf : μ ^ 2 * R ≤ kappa μ R / 2 := by
    have hκ : 2 * μ ^ 2 * R ≤ kappa μ R := by
      dsimp [kappa]
      have hμ2 : μ ^ 2 ≤ (1 : ℝ) := by
        have h1 : μ ^ 2 ≤ (1 / 64 : ℝ) ^ 2 := by
          exact pow_le_pow_left₀ (by positivity : 0 ≤ μ) hμ1 2
        norm_num at h1
        linarith
      have htwo : μ ^ 2 / 2 ≤ (2 : ℝ) ^ (μ ^ 2) - 1 :=
        Ell2Update.two_pow_sub_one_ge_half (μ ^ 2) (sq_nonneg μ) hμ2
      have h4 : 0 ≤ 4 * R := by positivity
      have hm := mul_le_mul_of_nonneg_right htwo h4
      have hred : μ ^ 2 / 2 * (4 * R) = 2 * μ ^ 2 * R := by ring_nf
      rwa [hred] at hm
    nlinarith
  have hκsq : μ ^ 4 * R ^ 2 ≤ (kappa μ R / 2) ^ 2 := by
    have hprod : (μ ^ 2 * R) * (μ ^ 2 * R) ≤ (kappa μ R / 2) * (kappa μ R / 2) := by
      exact mul_self_le_mul_self (by positivity : 0 ≤ μ ^ 2 * R) hκhalf
    nlinarith [hprod]
  have hE0 : 0 ≤ (E.card : ℝ) := by exact_mod_cast Nat.zero_le _
  have hEbig' : μ ^ 2 * (N : ℝ) / 2 ≤ (E.card : ℝ) := by
    simpa [E] using hEbig
  have hpp : 0 ≤ p * (1 - p) := by
    have hp1' : 0 ≤ 1 - p := by linarith
    exact mul_nonneg (le_of_lt hp0) hp1'
  have hμ4pos : 0 ≤ μ ^ 4 * R ^ 2 := by positivity
  have hc1 : 0 ≤ p * (1 - p) * (μ ^ 4 * R ^ 2) := by
    exact mul_nonneg hpp hμ4pos
  have hc2 : 0 ≤ p * (1 - p) * (E.card : ℝ) := by
    exact mul_nonneg hpp hE0
  have hstep1 : (1 / 2) * p * (1 - p) * μ ^ 6 * R ^ 2 * (N : ℝ) ≤
      p * (1 - p) * (μ ^ 4 * R ^ 2) * (E.card : ℝ) := by
    calc
      (1 / 2) * p * (1 - p) * μ ^ 6 * R ^ 2 * (N : ℝ)
          = p * (1 - p) * (μ ^ 4 * R ^ 2) * (μ ^ 2 * (N : ℝ) / 2) := by ring_nf
      _ ≤ p * (1 - p) * (μ ^ 4 * R ^ 2) * (E.card : ℝ) := by
            exact mul_le_mul_of_nonneg_left hEbig' hc1
  have hstep2 : p * (1 - p) * (μ ^ 4 * R ^ 2) * (E.card : ℝ) ≤
      p * (1 - p) * (kappa μ R / 2) ^ 2 * (E.card : ℝ) := by
    calc
      p * (1 - p) * (μ ^ 4 * R ^ 2) * (E.card : ℝ)
          = p * (1 - p) * (E.card : ℝ) * (μ ^ 4 * R ^ 2) := by ring
      _ ≤ p * (1 - p) * (E.card : ℝ) * (kappa μ R / 2) ^ 2 := by
            exact mul_le_mul_of_nonneg_left hκsq hc2
      _ = p * (1 - p) * (kappa μ R / 2) ^ 2 * (E.card : ℝ) := by ring
  have hAmt : p * (1 - p) * (kappa μ R / 2) ^ 2 * (E.card : ℝ) ≥
      (1 / 2) * p * (1 - p) * μ ^ 6 * R ^ 2 * (N : ℝ) := by
    exact le_trans hstep1 hstep2
  nlinarith [hdrop, hAmt]

/-- (counting-form main theorem) `Prop ell-2 update`, counting form:
all but `1024μ·|J|` of the shifts `y ∈ J = Icc c d` satisfy the ℓ₂-drop. -/
theorem ell2_update_counting {g1 g2 : ℤ → ℝ} {R μ p : ℝ} {lo c d : ℤ} {N : ℕ}
    (hμ0 : 0 < μ) (hμ1 : μ ≤ 1 / 64) (hR0 : 0 < R) (hN1 : 1 ≤ N)
    (hp0 : 0 < p) (hp1 : p ≤ 1) (hg10 : ∀ t : ℤ, 0 ≤ g1 t)
    (hg1sq : Summable (fun t : ℤ => (g1 t) ^ 2)) (hg2sq : Summable (fun t : ℤ => (g2 t) ^ 2))
    (hlip : Ell2Update.ratioLip (μ ^ 4) g1)
    (hmass : (∑ t ∈ It lo N, g1 t) ≤ 2 * R * (N : ℝ))
    (hsp : μ * (N : ℝ) ≤
      (((Finset.Icc lo (lo + (N : ℤ) - 1)).filter (fun t : ℤ => 8 * R ≤ g1 t)).card : ℝ))
    (hJlen : (N : ℝ) ≤ ((Finset.Icc c d).card : ℝ)) :
    (((Finset.Icc c d).filter (fun y : ℤ =>
      ¬ (norm₂sq (fun t : ℤ => (1 - p) * g1 t + p * g2 (t + y)) ≤
          (1 - p) * norm₂sq g1 + p * norm₂sq g2 -
            (1 / 2) * p * (1 - p) * μ ^ 6 * R ^ 2 * (N : ℝ)))).card : ℝ)
      ≤ 1024 * μ * ((Finset.Icc c d).card : ℝ) := by
  classical
  let J : Finset ℤ := Finset.Icc c d
  rcases exists_shell_data (g := g1) (R := R) (μ := μ) (lo := lo) (N := N)
    hμ0 hμ1 hR0 hN1 hsp with ⟨a, ha0, ha4R, htop, hmed, hL⟩
  let B : List (ℤ × ℤ) := coverBlocks g1 a μ lo N (largeSorted g1 a μ lo N)
  let good : ℤ × ℤ → Prop := fun b =>
    ((mediumBlock g1 a μ b).card : ℝ) ≤ (8 * μ) * (ilen b.1 b.2 : ℝ)
  let B₀ : Finset (ℤ × ℤ) := B.toFinset.filter good
  let κ : ℝ := kappa μ R
  have hBlist : ∀ b ∈ B.toFinset, b ∈ coverBlocks g1 a μ lo N (largeSorted g1 a μ lo N) := by
    intro b hb
    simpa [B] using (List.mem_toFinset.mp hb)
  have hB₀ : ∀ b ∈ B₀, b ∈ coverBlocks g1 a μ lo N (largeSorted g1 a μ lo N) := by
    intro b hb
    exact hBlist b (Finset.mem_filter.mp hb).1
  -- (1) total length of good blocks ≥ μN/2
  have hgoodsum : μ * (N : ℝ) / 2 ≤ ∑ b ∈ B.toFinset,
      if ((mediumBlock g1 a μ b).card : ℝ) ≤ (8 * μ) * (ilen b.1 b.2 : ℝ)
        then (ilen b.1 b.2 : ℝ) else 0 := by
    simpa [B] using (good_index_bound (g := g1) (a := a) (R := R) (μ := μ) (lo := lo) (N := N)
      hμ0 hμ1 hR0 ha0 ha4R hN1 hg10 hlip hmass hL hmed)
  have hLtot : μ * (N : ℝ) / 2 ≤ ∑ b ∈ B₀, (ilen b.1 b.2 : ℝ) := by
    dsimp [B₀, good]
    rw [Finset.sum_filter]
    exact hgoodsum
  -- (2) per-good-block aux-averaging count
  have hbnd : ∀ b ∈ B₀,
      (((J.filter (fun y : ℤ =>
        ((badInBlock g1 g2 κ y b : ℝ)) <
          (8 * μ) * ((Finset.Icc b.1 b.2).card : ℝ) / 4)).card : ℝ))
        ≤ 64 * (8 * μ) * (J.card : ℝ) := by
    intro b hb
    have hbToF : b ∈ B.toFinset := (Finset.mem_filter.mp hb).1
    have hgoodb : good b := (Finset.mem_filter.mp hb).2
    have hbL : b ∈ coverBlocks g1 a μ lo N (largeSorted g1 a μ lo N) := by
      simpa [B] using (List.mem_toFinset.mp hbToF)
    have hcore := coverBlocks_block_core (g := g1) (a := a) (R := R) (μ := μ) (lo := lo) (N := N)
      (L := largeSorted g1 a μ lo N) hμ0 hμ1 hR0 ha0 ha4R hN1 hg10 hlip hmass
      (fun x hx => mem_largeSorted.mp hx) b hbL
    dsimp at hcore
    rcases hcore with ⟨hlx, hrlt, hsc1, hsc2, hlen, hlenq⟩
    have hIle : ((Finset.Icc b.1 b.2).card : ℝ) ≤ (N : ℝ) := by
      simpa [ilen] using hlen
    have hJ : ((Finset.Icc b.1 b.2).card : ℝ) ≤ ((Finset.Icc c d).card : ℝ) := by
      linarith
    have hbac := block_aux_count (g1 := g1) (g2 := g2) (a := a) (R := R) (μ := μ) (lo := lo)
      (N := N) (c := c) (d := d) (b := b)
      hμ0 hμ1 hR0 ha0 ha4R hN1 hg10 hlip hmass hbL hgoodb hJ
    simpa [J, κ, badInBlock] using hbac
  -- (3) union/Markov count over good blocks
  have hN : 0 < N := by omega
  have hunion : (((J.filter (fun y : ℤ => ¬ manyBad g1 g2 μ κ N B₀ y)).card : ℝ)
      ≤ 128 * (8 * μ) * (J.card : ℝ)) :=
    union_good_y_count (g1 := g1) (g2 := g2) (μ := μ) (κ := κ) (N := N) (J := J) (B₀ := B₀)
      hμ0 (by simpa [κ] using kappa_pos hμ0 hR0) hN hLtot hbnd
  -- (4) manyBad forces the drop
  let drop : ℤ → Prop := fun y : ℤ =>
    norm₂sq (fun t : ℤ => (1 - p) * g1 t + p * g2 (t + y)) ≤
      (1 - p) * norm₂sq g1 + p * norm₂sq g2 -
        (1 / 2) * p * (1 - p) * μ ^ 6 * R ^ 2 * (N : ℝ)
  have hEbig : ∀ y : ℤ, manyBad g1 g2 μ κ N B₀ y →
      μ ^ 2 * (N : ℝ) / 2 ≤ ((ItBad g1 g2 κ lo N y).card : ℝ) := by
    intro y hmy
    have hb := bad_points_ge_of_manyBad (a := a) (R := R) (μ := μ) (lo := lo) (N := N)
      hμ0 hμ1 hR0 ha0 ha4R hN1 hg10 hlip hmass (Bfin := B₀) hB₀
      (by simpa [κ] using hmy)
    simpa [κ] using hb
  have hmd : ∀ y : ℤ, manyBad g1 g2 μ κ N B₀ y → drop y := by
    intro y hmy
    have hb := hEbig y hmy
    have hb' : μ ^ 2 * (N : ℝ) / 2 ≤
        (((It lo N).filter (fun t : ℤ => kappa μ R / 2 ≤ |g1 t - g2 (t + y)|)).card : ℝ) := by
      simpa [κ, ItBad] using hb
    have hd := drop_of_manyBad (g1 := g1) (g2 := g2) (R := R) (μ := μ) (lo := lo) (N := N)
      hμ0 hμ1 hR0 hN1 hp0 hp1 hg1sq hg2sq hb'
    simpa [drop] using hd
  -- (5) assemble the count
  have hnot : ∀ y ∈ J, ¬ drop y → ¬ manyBad g1 g2 μ κ N B₀ y := by
    intro y hy hnd hm
    exact hnd (hmd y hm)
  have hsubF : J.filter (fun y => ¬ drop y) ⊆ J.filter (fun y => ¬ manyBad g1 g2 μ κ N B₀ y) := by
    intro y hy
    rw [Finset.mem_filter] at hy ⊢
    exact ⟨hy.1, hnot y hy.1 hy.2⟩
  have hcnt : (((J.filter (fun y => ¬ drop y)).card : ℝ) ≤ 128 * (8 * μ) * (J.card : ℝ)) := by
    calc
      ((J.filter (fun y => ¬ drop y)).card : ℝ) ≤
          ((J.filter (fun y => ¬ manyBad g1 g2 μ κ N B₀ y)).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsubF
      _ ≤ 128 * (8 * μ) * (J.card : ℝ) := hunion
  have hcnt' : (((Finset.Icc c d).filter (fun y : ℤ =>
      ¬ (norm₂sq (fun t : ℤ => (1 - p) * g1 t + p * g2 (t + y)) ≤
          (1 - p) * norm₂sq g1 + p * norm₂sq g2 -
            (1 / 2) * p * (1 - p) * μ ^ 6 * R ^ 2 * (N : ℝ)))).card : ℝ)
      ≤ 128 * (8 * μ) * ((Finset.Icc c d).card : ℝ) := by
    simpa [J, drop] using hcnt
  have hring : 128 * (8 * μ) * ((Finset.Icc c d).card : ℝ) =
      1024 * μ * ((Finset.Icc c d).card : ℝ) := by ring
  rwa [hring] at hcnt'

end Submission.Ell2Greedy
