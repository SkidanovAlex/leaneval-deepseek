import Mathlib
import Submission.Work.BW.ulcm_le_three_pow

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Finset

private lemma syl_pos' (i : ℕ) : 0 < syl i := by
  have := syl_two_le i; omega

/-- The Egyptian-fraction identity for the Sylvester sequence, over `ℝ`. -/
private lemma syl_sum_inv_real' (m : ℕ) :
    (∑ i ∈ Finset.range m, (1 : ℝ) / (syl i : ℝ)) = 1 - 1 / ((syl m : ℝ) - 1) := by
  induction m with
  | zero => norm_num [syl_zero]
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      have h2 : 2 ≤ syl m := syl_two_le m
      have hcast : ((syl (m + 1) : ℕ) : ℝ) - 1 = (syl m : ℝ) * ((syl m : ℝ) - 1) := by
        rw [syl_succ]
        push_cast [Nat.cast_sub (show 1 ≤ syl m by omega)]
        ring
      have hne : (syl m : ℝ) - 1 ≠ 0 := by
        have h3 : (2 : ℝ) ≤ (syl m : ℝ) := by exact_mod_cast h2
        intro h; linarith
      rw [hcast]
      field_simp
      ring

/-- **Floor-sum lower bound (Hanson's key floor estimate).**  For `n ≥ 1`, with `syl` Sylvester's
sequence (`syl 0 = 2`, `syl (i+1) = syl i * (syl i - 1) + 1`, defined in
`Submission/Work/BW/ulcm_le_three_pow.lean`),
`n ≤ ∑_{i ≤ n} ⌊n / syl i⌋ + K + 1`, where `K = #{i ≤ n : syl i ≤ n}` counts the Sylvester numbers
at most `n`.  (Equivalently `(n:ℝ) - 1 - K ≤ ∑_{i ≤ n} ((n / syl i : ℕ) : ℝ)`; this is the `r ≤ K + 1`
input of the entropy bound for `n!/sylBlocks n`, where `r = n - ∑_{i≤n} ⌊n/syl i⌋`.)

Route.  `S = {i ≤ n : syl i ≤ n}` is downward closed (`syl` strictly increasing:
`Work.BW.syl_lt_of_lt`, `Work.BW.syl_mono`; `Work.BW.Kset_downclosed` answers this directly) and
`S ⊆ range (n+1)`, so `S = range K` (each `i ∈ S` has `{0,…,i} ⊆ S`, so `i < K`; conversely any
`i < K` must lie in `S` since otherwise `S ⊆ range i` gives `K ≤ i`; cf. `Work.BW.Kset_eq_range_aux`).
Hence `∑_{i∈S} 1/syl i = ∑_{i<K} 1/syl i = 1 - 1/(syl K - 1)` (`Work.BW.syl_sum_inv`, stated over
`ℚ`; cast it to `ℝ` or redo the same induction in `ℝ`, cf. `Work.BW.syl_sum_inv_real_aux`), and
`syl K > n` (if `K ≤ n` then `K ∈ range (n+1)` and `K ∉ S`, so `syl K > n`; if `K > n` then
`Work.BW.syl_ge` gives `syl K ≥ K + 2 > n`).  So `syl K - 1 ≥ n` and
`∑_{i∈S} n/(syl i) = n·(1 - 1/(syl K - 1)) ≥ n - 1`.  Finally for `i ∈ S` one has
`⌊n/syl i⌋ ≥ n/syl i - 1` in `ℝ` (from `n = syl i * (n / syl i) + n % syl i`, `Nat.div_add_mod`,
`Nat.mod_lt` and `syl i > 0`), hence
`∑_{i≤n} ⌊n/syl i⌋ ≥ ∑_{i∈S} ⌊n/syl i⌋ ≥ ∑_{i∈S} n/syl i - K ≥ n - 1 - K`.

Use only sorry-free helpers (`syl_sum_inv`, `syl_prod`, `syl_mono`, `syl_lt_of_lt`, `syl_ge`,
`syl_two_le`); do NOT use anything whose proof contains `sorry`. -/
theorem syl_floor_sum_lb (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) ≤ (∑ i ∈ Finset.range (n + 1), ((n / syl i : ℕ) : ℝ))
      + (((Finset.range (n + 1)).filter (fun i => syl i ≤ n)).card : ℝ) + 1 := by
  classical
  set B : Finset ℕ := (Finset.range (n + 1)).filter (fun i => syl i ≤ n) with hB
  set k : ℕ := B.card with hk
  have hmem : ∀ i, i ∈ B ↔ i ≤ n ∧ syl i ≤ n := by
    intro i
    rw [hB]
    simp [Nat.lt_succ_iff]
  -- `B` is an initial segment of `ℕ`.
  have hBrange : B = Finset.range k := by
    have hsub : B ⊆ Finset.range k := by
      intro i hi
      have hi' : i ≤ n ∧ syl i ≤ n := (hmem i).mp hi
      rw [Finset.mem_range]
      by_contra hcon
      push_neg at hcon
      have h1 : Finset.range (i + 1) ⊆ B := by
        intro j hj
        rw [Finset.mem_range] at hj
        rw [hmem]
        exact ⟨by omega, le_trans (syl_mono (by omega)) hi'.2⟩
      have h2 := Finset.card_le_card h1
      rw [Finset.card_range] at h2
      omega
    exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_range])
  -- The full sum over `range (n+1)` collapses onto `B`.
  have hsum_swap : (∑ i ∈ Finset.range (n + 1), ((n / syl i : ℕ) : ℝ))
      = ∑ i ∈ B, ((n / syl i : ℕ) : ℝ) := by
    refine (Finset.sum_subset (s₁ := B) (s₂ := Finset.range (n + 1)) ?_ ?_).symm
    · intro x hx
      rw [hB] at hx
      exact (Finset.mem_filter.mp hx).1
    · intro x hx hxnB
      have hsyl : n < syl x := by
        by_contra hcon
        push_neg at hcon
        exact hxnB (by rw [hB]; exact Finset.mem_filter.mpr ⟨hx, hcon⟩)
      rw [Nat.div_eq_of_lt hsyl]
      norm_num
  -- `k = (Kset n).card` does not exceed `n`.
  have hk_le_n : k ≤ n := by
    have h1 : k ≤ n + 1 := by
      rw [hk]
      calc B.card = ((Finset.range (n + 1)).filter (fun i => syl i ≤ n)).card := by rw [hB]
        _ ≤ (Finset.range (n + 1)).card := Finset.card_le_card (Finset.filter_subset _ _)
        _ = n + 1 := Finset.card_range _
    rcases lt_or_ge k (n + 1) with h | h
    · omega
    · have hk' : k = n + 1 := le_antisymm h1 h
      have hmem_n : n ∈ B := by
        rw [hBrange, hk']
        exact Finset.mem_range.mpr (Nat.lt_succ_self n)
      have h1' := (hmem n).mp hmem_n
      have h2' := syl_ge n
      omega
  -- `syl k > n`.
  have hnsyl : n + 1 ≤ syl k := by
    have hk_notin : k ∉ B := by
      rw [hBrange]
      exact Finset.notMem_range_self
    have hnot : ¬ (syl k ≤ n) := fun h => hk_notin ((hmem k).mpr ⟨hk_le_n, h⟩)
    omega
  -- Termwise floor bound.
  have hfloor : ∀ i ∈ B, (n : ℝ) / (syl i : ℝ) - 1 ≤ ((n / syl i : ℕ) : ℝ) := by
    intro i _
    have hs : 0 < syl i := syl_pos' i
    have hsi : (0 : ℝ) < (syl i : ℝ) := by exact_mod_cast hs
    have hmod : n % syl i < syl i := Nat.mod_lt n hs
    have hdecomp : (n : ℝ) = (syl i : ℝ) * ((n / syl i : ℕ) : ℝ) + ((n % syl i : ℕ) : ℝ) := by
      have h := Nat.div_add_mod n (syl i)
      have h' : (n : ℝ) = ((syl i * (n / syl i) + n % syl i : ℕ) : ℝ) := by rw [h]
      push_cast at h'
      exact h'
    have hlt : ((n % syl i : ℕ) : ℝ) < (syl i : ℝ) := by exact_mod_cast hmod
    have hle : (n : ℝ) / (syl i : ℝ) ≤ ((n / syl i : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ hsi]
      nlinarith [hdecomp, hlt]
    linarith
  have hstep1 : ∑ i ∈ B, ((n : ℝ) / (syl i : ℝ) - 1)
      ≤ ∑ i ∈ B, ((n / syl i : ℕ) : ℝ) := Finset.sum_le_sum hfloor
  -- Evaluate the reciprocal sum.
  have hsum_inv : (∑ i ∈ B, (1 : ℝ) / (syl i : ℝ)) = 1 - 1 / ((syl k : ℝ) - 1) := by
    rw [hBrange]
    exact syl_sum_inv_real' k
  have hconst : (∑ _i ∈ B, (1 : ℝ)) = (k : ℝ) := by
    rw [Finset.sum_const, ← hk]
    simp
  have hsplit : (∑ i ∈ B, ((n : ℝ) / (syl i : ℝ) - 1))
      = (n : ℝ) * (1 - 1 / ((syl k : ℝ) - 1)) - (k : ℝ) := by
    rw [Finset.sum_sub_distrib, ← hsum_inv, ← hconst, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [div_eq_mul_one_div]
  have hdenpos : (0 : ℝ) < (syl k : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ (syl k : ℝ) := by exact_mod_cast syl_two_le k
    linarith
  have hdiv1 : (n : ℝ) / ((syl k : ℝ) - 1) ≤ 1 := by
    rw [div_le_one hdenpos]
    have h3 : (n : ℝ) + 1 ≤ (syl k : ℝ) := by exact_mod_cast hnsyl
    linarith
  have hmain : (n : ℝ) - (1 + (k : ℝ)) ≤ ∑ i ∈ B, ((n / syl i : ℕ) : ℝ) := by
    have h1 := hstep1
    rw [hsplit] at h1
    have heq : (n : ℝ) * (1 - 1 / ((syl k : ℝ) - 1)) - (k : ℝ)
        = (n : ℝ) - (n : ℝ) / ((syl k : ℝ) - 1) - (k : ℝ) := by
      field_simp
    linarith [h1, hdiv1]
  rw [hsum_swap]
  linarith [hmain]

end Work.BW
