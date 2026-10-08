import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.BCountSum
import Submission.Work.CORE3.SumMulBCount
import Submission.Work.CORE3.Case1bEightNine

namespace Work.CORE3

namespace Work.CORE3

open Work.GW2

/-! ## The two finite-sum reductions used by `Case1bIndex`

The only non-elementary input of `Work.CORE3.Case1bIndex` is the reduction of the two sums
`∑_{n ≤ |Ĥ|} b_n` and `∑_{n ≤ |Ĥ|} (n - 3) b_n` to the five terms `n = 0, …, 4`, using Bender
1981 (6) (`b_n = 0` for `n ≥ 5`).  Both are instances of: *a sum over `range (N+1)` of a
function that vanishes at every `n ≥ 5` is the sum over the five values `0, …, 4`.* -/

/-- A sum over `range (N + 1)` of a function vanishing at all `n ≥ 5` is the sum of its first
five values. -/
theorem sum_range_eq_of_vanishes_above {M : Type*} [AddCommMonoid M] {N : ℕ} (hN : 5 ≤ N)
    {b : ℕ → M} (hb : ∀ n, 5 ≤ n → b n = 0) :
    ∑ n ∈ Finset.range (N + 1), b n = b 0 + b 1 + b 2 + b 3 + b 4 := by
  have hsub : Finset.range 5 ⊆ Finset.range (N + 1) :=
    Finset.range_subset_range.mpr (by omega)
  have hzero : ∀ x ∈ Finset.range (N + 1), x ∉ Finset.range 5 → b x = 0 := by
    intro x _ hx5
    simp only [Finset.mem_range, not_lt] at hx5
    exact hb x hx5
  rw [← Finset.sum_subset hsub hzero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]

/-- The weighted sum `∑ (n - 3) b_n` over `range (N + 1)` of a function vanishing at all
`n ≥ 5` equals `-3 b_0 - 2 b_1 - b_2 + b_4`. -/
theorem sum_range_shift_eq_of_vanishes_above {N : ℕ} (hN : 5 ≤ N) {b : ℕ → ℕ}
    (hb : ∀ n, 5 ≤ n → b n = 0) :
    ∑ n ∈ Finset.range (N + 1), ((n : ℤ) - 3) * (b n : ℤ)
      = -3 * (b 0 : ℤ) - 2 * (b 1 : ℤ) - (b 2 : ℤ) + (b 4 : ℤ) := by
  have hsub : Finset.range 5 ⊆ Finset.range (N + 1) :=
    Finset.range_subset_range.mpr (by omega)
  have hzero : ∀ x ∈ Finset.range (N + 1), x ∉ Finset.range 5 →
      ((x : ℤ) - 3) * (b x : ℤ) = 0 := by
    intro x _ hx5
    simp only [Finset.mem_range, not_lt] at hx5
    rw [hb x hx5, Nat.cast_zero, mul_zero]
  rw [← Finset.sum_subset hsub hzero]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num
  ring

/-- Bender 1981 §3, p. 224, end of §3.  Deliverable `Work.GW2.Case1bIndexProp`.

Together with `hCount : Case1bCountProp` ((1)–(4)), `h89 : Case1bEightNineProp` ((6)–(9)) and
`hNum : Case1bNumericsProp` (`12 ∣ b₄`, `b₁ = 0`, `b₃ = 0`, `|Ĥ| = 72`), the arithmetic of the
`b_n` gives the paper's conclusion:

* `b₄ ≠ 0` (else (4) and (8) give `k ≤ 1`, contradicting `K ≠ ⊥`), so `|U| = k = 3`;
* `3b₄ + b₂ = 6k² = 54` with `12 ∣ b₄` gives `b₄ = 12`, `b₂ = 18`;
* (4) with `b₁ = b₃ = 0` gives `3b₀ + 2b₁ = 18 + b₄ − b₂ = 12`, so `b₀ = 4`;
* `|G:Ĥ| = 1 + Σ b_n = 1 + 4 + 0 + 18 + 0 + 12 = 35`;
* `|G| = |Ĥ| · 35 = 72 · 35 = 2520`. -/
theorem Case1bIndex (I : Case1Inputs) (hCount : Case1bCountProp) (h89 : Case1bEightNineProp)
    (hNum : Case1bNumericsProp) : Case1bIndexProp := by
  -- the toolkit `I` is not needed for this counting argument
  have _hToolkit := I.h22
  intro G instG instFin hFT hBC B hCase D
  obtain ⟨_, _, _, hCount4, hCount5⟩ := hCount G hFT hBC B hCase D
  obtain ⟨h89a, h89b, h89c⟩ := h89 G hFT hBC B hCase D
  obtain ⟨hNum1, hNum2, hNum3, hNum4⟩ := hNum G hFT hBC B hCase D
  -- (6) reduces both sums to the five values `n = 0, …, 4`
  have hsum_b : ∑ n ∈ Finset.range (Nat.card B.Hhat + 1), bCount B.Hhat n =
      bCount B.Hhat 0 + bCount B.Hhat 1 + bCount B.Hhat 2 + bCount B.Hhat 3
        + bCount B.Hhat 4 := by
    rw [hNum4]
    exact sum_range_eq_of_vanishes_above (show 5 ≤ 72 by norm_num) h89a
  have hsum_i : ∑ n ∈ Finset.range (Nat.card B.Hhat + 1),
        ((n : ℤ) - 3) * (bCount B.Hhat n : ℤ)
      = -3 * (bCount B.Hhat 0 : ℤ) - 2 * (bCount B.Hhat 1 : ℤ) - (bCount B.Hhat 2 : ℤ)
        + (bCount B.Hhat 4 : ℤ) := by
    rw [hNum4]
    exact sum_range_shift_eq_of_vanishes_above (show 5 ≤ 72 by norm_num) h89a
  -- Bender's (4), in the form `6k + (-3b₀ - 2b₁ - b₂ + b₄) = 0`
  have h4z : (6 : ℤ) * (Nat.card D.K : ℤ) + (-3 * (bCount B.Hhat 0 : ℤ)
      - 2 * (bCount B.Hhat 1 : ℤ) - (bCount B.Hhat 2 : ℤ) + (bCount B.Hhat 4 : ℤ)) = 0 := by
    rw [← hsum_i]
    exact hCount4
  -- `b₄ ≠ 0`
  have hb4ne : bCount B.Hhat 4 ≠ 0 := by
    intro hb4
    have hb2 : bCount B.Hhat 2 = 6 * (Nat.card D.K) ^ 2 := by
      have h := h89b
      rw [hb4, mul_zero, zero_add] at h
      exact h
    have hb2z : (bCount B.Hhat 2 : ℤ) = 6 * (Nat.card D.K : ℤ) ^ 2 := by
      rw [hb2]; push_cast; ring
    have hb4z : (bCount B.Hhat 4 : ℤ) = 0 := by rw [hb4]; norm_num
    have hb0z : (0 : ℤ) ≤ (bCount B.Hhat 0 : ℤ) := by exact_mod_cast Nat.zero_le _
    have hb1z : (0 : ℤ) ≤ (bCount B.Hhat 1 : ℤ) := by exact_mod_cast Nat.zero_le _
    -- (4) and (8) give `6k² ≤ 6k`
    have hle : 6 * (Nat.card D.K : ℤ) ^ 2 ≤ 6 * (Nat.card D.K : ℤ) := by
      nlinarith [h4z, hb2z, hb4z, hb0z, hb1z]
    have hleN : 6 * (Nat.card D.K) ^ 2 ≤ 6 * Nat.card D.K := by exact_mod_cast hle
    have hkk : Nat.card D.K * Nat.card D.K ≤ Nat.card D.K := by
      have h2 : 6 * (Nat.card D.K * Nat.card D.K) ≤ 6 * Nat.card D.K := by
        simpa [pow_two] using hleN
      exact Nat.le_of_mul_le_mul_left (a := Nat.card D.K * Nat.card D.K) (b := Nat.card D.K)
        (c := 6) h2 (by norm_num)
    -- hence `k ≤ 1`, i.e. `K = ⊥`
    have hk1 : Nat.card D.K ≤ 1 := by
      by_contra hk
      have hk2 : 2 ≤ Nat.card D.K := by omega
      have h2 : 2 * Nat.card D.K ≤ Nat.card D.K * Nat.card D.K := Nat.mul_le_mul_right _ hk2
      omega
    have hk1' : Nat.card D.K = 1 := by
      have : 0 < Nat.card D.K := Nat.card_pos
      omega
    exact D.ne ((Subgroup.card_eq_one).mp hk1')
  -- (7): `b₄ ≠ 0` forces `k = 3`
  have hk3 : Nat.card D.K = 3 := (h89c hb4ne).2
  -- (8) with `12 ∣ b₄` gives `b₄ = 12` and `b₂ = 18`
  obtain ⟨m, hm⟩ := hNum1
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    exact hb4ne hm
  have h8 : 3 * bCount B.Hhat 4 + bCount B.Hhat 2 = 54 := by
    have h := h89b
    rw [hk3] at h
    norm_num at h
    exact h
  have hb4_12 : bCount B.Hhat 4 = 12 := by omega
  have hb2_18 : bCount B.Hhat 2 = 18 := by omega
  -- (4) with `b₁ = b₃ = 0` gives `b₀ = 4`
  have hb0_4 : bCount B.Hhat 0 = 4 := by
    have hz : (bCount B.Hhat 0 : ℤ) = 4 := by omega
    omega
  -- (3) gives `|G : Ĥ| = 1 + Σ b_n = 35`
  have hidx : B.Hhat.index = 35 := by
    have h := hCount5
    rw [hsum_b] at h
    omega
  refine ⟨hidx, ?_⟩
  -- `|G| = |Ĥ| · |G : Ĥ| = 72 · 35 = 2520`
  rw [← Subgroup.card_mul_index B.Hhat, hNum4, hidx]

end Work.CORE3

open Work.GW2

/-- The same statement, exposed under the name `Work.CORE3.Case1bIndex` requested by the lead
(the module's main declaration sits in the doubly nested namespace `Work.CORE3.Work.CORE3`). -/
theorem Case1bIndex (I : Case1Inputs) (hCount : Case1bCountProp) (h89 : Case1bEightNineProp)
    (hNum : Case1bNumericsProp) : Work.GW2.Case1bIndexProp :=
  _root_.Work.CORE3.Work.CORE3.Case1bIndex I hCount h89 hNum

end Work.CORE3
