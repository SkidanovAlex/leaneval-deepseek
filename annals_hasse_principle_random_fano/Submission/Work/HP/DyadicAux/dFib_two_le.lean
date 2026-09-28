import Mathlib
import Submission.Work.HP.DyadicR2Defs

/-!
# The fibre sum of powers of two over `dFib`

`dFib s X Y` is the set of `a ≤ s - a` with `2 ^ a ≤ 2 * X` and `2 ^ (s - a) ≤ 2 * Y`.
Its defining conditions are *downward closed in `a`* (up to the irrelevant `Y`-condition),
so the whole fibre is a subset of `{a : 2 ^ a ≤ 2 * X}`, which is an initial segment of the
naturals.  Summing `2 ^ a` over any subset of an initial segment `{0, …, A}` of the powers of
two gives at most `2 ^ (A + 1) - 1 ≤ 2 · 2 ^ A ≤ 4 X`.

The key elementary input is `∑_{a < n} 2 ^ a ≤ 2 ^ n`, proved by induction.
-/

namespace Work.HP.DyadicAux

/-- The partial geometric sum of powers of two is bounded by the next power of two:
`∑_{a < n} 2 ^ a ≤ 2 ^ n`.  (In fact equality holds for `n ≥ 1`, but the inequality is
all we need and is immediate by induction.) -/
lemma sum_range_pow_two_le (n : ℕ) :
    ∑ a ∈ Finset.range n, (2 : ℝ) ^ a ≤ (2 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    linarith

theorem dFib_two_le (s : ℕ) (X Y : ℝ) (hX : 0 ≤ X) :
    ∑ a ∈ dFib s X Y, (2 : ℝ) ^ a ≤ 4 * X := by
  rcases Finset.eq_empty_or_nonempty (dFib s X Y) with h | h
  · -- the fibre is empty: the sum vanishes and `4 * X ≥ 0`
    rw [h, Finset.sum_empty]
    linarith
  · -- otherwise take `A` the largest element of the fibre
    set A := (dFib s X Y).max' h with hAdef
    have hAmem : A ∈ dFib s X Y := Finset.max'_mem _ h
    have hAle : ∀ a ∈ dFib s X Y, a ≤ A := fun a ha => Finset.le_max' _ _ ha
    -- the fibre is contained in `range (A + 1)`
    have hsub : dFib s X Y ⊆ Finset.range (A + 1) := fun a ha =>
      Finset.mem_range.mpr (Nat.lt_succ_of_le (hAle a ha))
    have h1 : ∑ a ∈ dFib s X Y, (2 : ℝ) ^ a ≤ ∑ a ∈ Finset.range (A + 1), (2 : ℝ) ^ a :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => by positivity)
    have h2 : ∑ a ∈ Finset.range (A + 1), (2 : ℝ) ^ a ≤ (2 : ℝ) ^ (A + 1) :=
      sum_range_pow_two_le (A + 1)
    -- `2 ^ A ≤ 2 * X` by membership of `A` in the fibre
    have hAcond := (Finset.mem_filter.mp hAmem).2
    have h3 : (2 : ℝ) ^ A ≤ 2 * X := hAcond.2.1
    have h4 : (2 : ℝ) ^ (A + 1) ≤ 4 * X := by
      rw [pow_succ]; linarith
    linarith

end Work.HP.DyadicAux
