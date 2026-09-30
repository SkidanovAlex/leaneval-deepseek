import Mathlib
import Submission.Work.BMF.SD.tk_bad_defs
import Submission.Work.BMF.SD.markov_inv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.BMF.SD.tkw_bad_per_y`

Fix a left endpoint `y`, a shift `H > 0`, a map `f : ℕ → ℂ` and a phase polynomial `φ`.
The "bad" set of primes at `y` (see `tkw_bad`) consists of the primes that are either small
(`p < 64/c₀`) or for which the discrepancy `tkw_disc f φ p y H` is large
(`(c₀/4)^2 H^2 < p^2 ‖tkw_disc f φ p y H‖^2`).

Given the second-moment input `Σ_{p ∈ S} p ‖tkw_disc …‖^2 ≤ 200 H^2`, this file bounds the
reciprocal-prime weight of the bad set:

`Σ_{p ∈ S, bad} 1/p ≤ 3200/c₀^2 + 64/c₀ + 8`.

The two contributions are handled separately:

* the "small primes" contribute at most `64/c₀ + 8` (at most `⌈64/c₀⌉` prime values, each
  weighted by at most `1`), and
* the "large discrepancy" primes contribute at most `3200/c₀^2` by the Markov-type inequality
  `Work.BMF.SD.markov_inv` with `c = 200`, `δ = c₀/4`.
-/

namespace Work.BMF.SD

open Classical Polynomial Finset Real Complex
open Work.BMF
open Work.BMF.SD

/-- The reciprocal weight of the "small primes" `< 64/c₀` in a finite set is at most
`64/c₀ + 8`. There are at most `⌈64/c₀⌉` natural numbers below `64/c₀`, and each contributes
`1/p ≤ 1`. -/
lemma tkw_small_primes_weight (c₀ : ℝ) (hc₀ : 0 < c₀) (S : Finset ℕ) :
    ∑ p ∈ S.filter (fun p : ℕ => ((p : ℕ) : ℝ) < 64 / c₀), 1 / ((p : ℕ) : ℝ) ≤
      64 / c₀ + 8 := by
  have hsubset : S.filter (fun p : ℕ => ((p : ℕ) : ℝ) < 64 / c₀) ⊆
      Finset.range ⌈(64 : ℝ) / c₀⌉₊ := by
    intro p hp
    simp only [Finset.mem_range]
    have hp' : ((p : ℕ) : ℝ) < 64 / c₀ := (Finset.mem_filter.mp hp).2
    have hle : (64 : ℝ) / c₀ ≤ (⌈(64 : ℝ) / c₀⌉₊ : ℝ) := Nat.le_ceil _
    have hlt : ((p : ℕ) : ℝ) < (⌈(64 : ℝ) / c₀⌉₊ : ℝ) := lt_of_lt_of_le hp' hle
    exact_mod_cast hlt
  have hcard : (S.filter (fun p : ℕ => ((p : ℕ) : ℝ) < 64 / c₀)).card ≤ ⌈(64 : ℝ) / c₀⌉₊ := by
    have := Finset.card_le_card hsubset
    rwa [Finset.card_range] at this
  calc ∑ p ∈ S.filter (fun p : ℕ => ((p : ℕ) : ℝ) < 64 / c₀), 1 / ((p : ℕ) : ℝ)
      ≤ ∑ _p ∈ S.filter (fun p : ℕ => ((p : ℕ) : ℝ) < 64 / c₀), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro p _
        rcases Nat.eq_zero_or_pos p with h | h
        · simp [h]
        · have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast h
          rw [div_le_one (by positivity)]
          exact hp1
    _ = ((S.filter (fun p : ℕ => ((p : ℕ) : ℝ) < 64 / c₀)).card : ℝ) := by simp
    _ ≤ (⌈(64 : ℝ) / c₀⌉₊ : ℝ) := by exact_mod_cast hcard
    _ ≤ 64 / c₀ + 1 := le_of_lt (Nat.ceil_lt_add_one (by positivity))
    _ ≤ 64 / c₀ + 8 := by norm_num

theorem tkw_bad_per_y (c₀ H : ℝ) (hc₀ : 0 < c₀) (hH : 0 < H)
    (f : ℕ → ℂ) (φ : Polynomial ℝ) (S : Finset ℕ) (y : ℝ)
    (hTK : ∑ p ∈ S, (p : ℝ) * ‖tkw_disc f φ p y H‖ ^ 2 ≤ 200 * H ^ 2) :
    ∑ p ∈ S.filter (fun p => tkw_bad c₀ H f φ y p), 1 / (p : ℝ) ≤
      3200 / c₀ ^ 2 + 64 / c₀ + 8 := by
  -- Split the bad set into the "small primes" and "large discrepancy" parts.
  rw [tkw_bad_filter c₀ H f φ y S]
  -- The union bound for sums of nonnegative terms.
  have hg : ∀ x ∈ S.filter (fun p : ℕ =>
      (c₀ / 4) ^ 2 * H ^ 2 < ((p : ℕ) : ℝ) ^ 2 * ‖tkw_disc f φ p y H‖ ^ 2),
      0 ≤ 1 / ((x : ℕ) : ℝ) := by
    intro x _
    positivity
  -- Small primes contribute `≤ 64/c₀ + 8`.
  have hsmall := tkw_small_primes_weight c₀ hc₀ S
  -- Large-discrepancy primes contribute `≤ 3200/c₀^2` by the Markov inequality.
  have hmarkov := markov_inv S (fun p => ‖tkw_disc f φ p y H‖ ^ 2) 200 (c₀ / 4) H
      (fun p _ => sq_nonneg _) (by positivity) hH (by norm_num) hTK
  have hmarkov' : ∑ p ∈ S.filter (fun p : ℕ =>
        (c₀ / 4) ^ 2 * H ^ 2 < ((p : ℕ) : ℝ) ^ 2 * ‖tkw_disc f φ p y H‖ ^ 2),
      1 / ((p : ℕ) : ℝ) ≤ 3200 / c₀ ^ 2 := by
    refine hmarkov.trans (le_of_eq ?_)
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  refine (tkw_sum_union_le
      (S.filter (fun p : ℕ => ((p : ℕ) : ℝ) < 64 / c₀))
      (S.filter (fun p : ℕ =>
        (c₀ / 4) ^ 2 * H ^ 2 < ((p : ℕ) : ℝ) ^ 2 * ‖tkw_disc f φ p y H‖ ^ 2))
      (fun x => 1 / ((x : ℕ) : ℝ)) hg).trans ?_
  refine (add_le_add hsmall hmarkov').trans ?_
  rw [show (64 / c₀ + 8) + 3200 / c₀ ^ 2 = 3200 / c₀ ^ 2 + 64 / c₀ + 8 from by ring]

end Work.BMF.SD
