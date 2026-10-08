import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.inf_U_S_eq_bot
import Submission.Work.CORE3.BCountSum
import Submission.Work.CORE3.SumMulBCount
import Submission.Work.CORE3.H_eq_U_sup_S
import Submission.Work.CORE3.NormalizerPcoreEqHhat
import Submission.Work.BSW.Cases.K4.CardSup

set_option linter.dupNamespace false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.CORE3

namespace Work.CORE3

open Work.GW2

/-! ## Two `Finset` reductions

The only non-elementary step of the arithmetic below is the reduction of the two sums
`∑_{n ≤ N} bₙ` and `∑_{n ≤ N} (n - 3) bₙ` (with `N = |Ĥ|`) to the five terms `n = 0, …, 4`,
using Bender 1981 §3 (6): `bₙ = 0` for `n ≥ 5`.  *A sum over `range (N + 1)` of a function that
vanishes at every `n ≥ 5` is the sum of its first five values.* -/

private theorem sum_range_eq_of_vanishes_above {M : Type*} [AddCommMonoid M] {N : ℕ} (hN : 5 ≤ N)
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

/-- The weighted sum `∑ (n - 3) bₙ` over `range (N + 1)` of a function vanishing at all `n ≥ 5`
equals `-3 b₀ - 2 b₁ - b₂ + b₄`. -/
private theorem sum_range_shift_eq_of_vanishes_above {N : ℕ} (hN : 5 ≤ N) {b : ℕ → ℕ}
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

/-- The bundle of numerical facts of Bender 1981 §3, p. 224 used by `Work.CORE3.Case1bIndex`:
`12 ∣ b₄` (`hDiv`, the fixed-point-free action of `KV`), `b₁ = 0` (from `8 ∣ b₁` (`hOne`)
together with `3b₀ + 2b₁ = 12`), `b₃ = 0` (`hThree`), and `|Ĥ| = 72` (`O(Ĥ) = K` of order 3 with
`Ĥ/V·K ≅ D₃`, from `hSetup`'s `|S| = 8` and `|U| = k = 3`).

`b₄ = 12`: `b₄ ≠ 0` (else `hCount`(4) and `h89` give `k ≤ 1`, against `K ≠ ⊥`), so `|U| = k = 3`
by `h89` and `3b₄ + b₂ = 6k² = 54`; with `12 ∣ b₄` this gives `b₄ = 12` and `b₂ = 18`. -/
theorem Case1bNumerics (I : Case1Inputs) (hSetup : Case1bSetupProp) (hCount : Case1bCountProp)
    (h89 : Case1bEightNineProp) (hThree : Case1bThreeProp) (hOne : Case1bOneProp)
    (hDiv : Case1bDivProp) : Case1bNumericsProp := by
  intro G instG instFin hFT hBC B hCase D
  -- Bender (1)–(4) and (6)–(9)
  obtain ⟨-, -, hIdx, hWsum, -⟩ := hCount G hFT hBC B hCase D
  obtain ⟨hvan, h89b, h89c⟩ := h89 G hFT hBC B hCase D
  have h4 : IsFourGroup (pCoreIn 2 B.Hhat) := D.four
  -- ## `[Ĥ : H] = 3` and `5 ≤ |Ĥ|`
  have hHle : B.H ≤ B.Hhat := B.H_le_Hhat
  have hrel : B.H.relIndex B.Hhat = 3 := by
    have h := Subgroup.relIndex_mul_index hHle
    rw [hIdx] at h
    exact Nat.mul_right_cancel (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := B.Hhat)))
      h
  have hcardHhat : Nat.card B.Hhat = 3 * Nat.card B.H := by
    have h := Subgroup.relIndex_mul_card B.H B.Hhat
    rw [inf_eq_left.mpr hHle] at h
    rw [hrel] at h
    exact h.symm
  have hSH : Nat.card (B.S : Subgroup G) ≤ Nat.card B.H :=
    Nat.card_le_card_of_injective
      (fun s : ↥(B.S : Subgroup G) => (⟨(s : G), Work.CORE2A.bSetup_S_le_H B s.2⟩ : ↥B.H))
      (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab))
  have h5 : 5 ≤ Nat.card B.Hhat := by
    rw [D.S8] at hSH
    rw [hcardHhat]
    omega
  -- ## The reduced form of Bender's (4)
  have hsum_i : ∑ n ∈ Finset.range (Nat.card B.Hhat + 1),
        ((n : ℤ) - 3) * (bCount B.Hhat n : ℤ)
      = -3 * (bCount B.Hhat 0 : ℤ) - 2 * (bCount B.Hhat 1 : ℤ) - (bCount B.Hhat 2 : ℤ)
        + (bCount B.Hhat 4 : ℤ) :=
    sum_range_shift_eq_of_vanishes_above h5 hvan
  have hEqz : (6 : ℤ) * (Nat.card D.K : ℤ) + (-3 * (bCount B.Hhat 0 : ℤ)
      - 2 * (bCount B.Hhat 1 : ℤ) - (bCount B.Hhat 2 : ℤ) + (bCount B.Hhat 4 : ℤ)) = 0 := by
    rw [← hsum_i]; exact hWsum
  -- ## `b₄ ≠ 0`
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
      nlinarith [hEqz, hb2z, hb4z, hb0z, hb1z]
    have hleN : 6 * (Nat.card D.K) ^ 2 ≤ 6 * Nat.card D.K := by exact_mod_cast hle
    have hkk : Nat.card D.K * Nat.card D.K ≤ Nat.card D.K := by
      have h2 : 6 * (Nat.card D.K * Nat.card D.K) ≤ 6 * Nat.card D.K := by
        simpa [pow_two] using hleN
      exact Nat.le_of_mul_le_mul_left h2 (by norm_num)
    -- hence `k ≤ 1`, i.e. `K = ⊥`, contradicting `D.ne`
    have hk1 : Nat.card D.K ≤ 1 := by
      by_contra hk
      have hk2 : 2 ≤ Nat.card D.K := by omega
      have h2 : 2 * Nat.card D.K ≤ Nat.card D.K * Nat.card D.K := Nat.mul_le_mul_right _ hk2
      omega
    have hk1' : Nat.card D.K = 1 := by
      have : 0 < Nat.card D.K := Nat.card_pos
      omega
    exact D.ne ((Subgroup.card_eq_one).mp hk1')
  -- ## `k = 3` and `|U| = 3` (Bender (9) with `b₄ ≠ 0`)
  have hk3 : Nat.card D.K = 3 := (h89c hb4ne).2
  have hU3 : Nat.card B.U = 3 := (h89c hb4ne).1
  -- ## `b₄ = 12`, `b₂ = 18`
  have h8 : 3 * bCount B.Hhat 4 + bCount B.Hhat 2 = 54 := by
    have h := h89b
    rw [hk3] at h
    norm_num at h
    exact h
  have hb4_12 : bCount B.Hhat 4 = 12 := by
    obtain ⟨m, hm⟩ := hDiv G hFT hBC B hCase h4
    have hm1 : m = 1 := by omega
    rw [hm, hm1, mul_one]
  have hb2_18 : bCount B.Hhat 2 = 18 := by omega
  -- ## `b₁ = 0`: (4) reads `3b₀ + 2b₁ = 12`, and `8 ∣ b₁`
  have hb1 : bCount B.Hhat 1 = 0 := by
    have hone : 8 ∣ bCount B.Hhat 1 := hOne G hFT hBC B hCase h4
    have hlin : 3 * bCount B.Hhat 0 + 2 * bCount B.Hhat 1 = 12 := by
      have h := hEqz
      rw [hk3, hb4_12, hb2_18] at h
      norm_num at h
      omega
    obtain ⟨t, ht⟩ := hone
    omega
  have hb3 : bCount B.Hhat 3 = 0 := hThree G hFT hBC B hCase h4
  -- ## `|Ĥ| = 72`: `|H| = |U ⊔ S| = |U| · |S| = 3 · 8 = 24` and `|Ĥ| = 3 |H|`
  have hSNU : (B.S : Subgroup G) ≤ Subgroup.normalizer (B.U : Set G) :=
    le_trans (Work.CORE2A.bSetup_S_le_H B)
      (Work.CORE3.le_normalizer_map_subtype B.H (Work.GW2.oddCore ↥B.H))
  have hcardH : Nat.card B.H = 24 := by
    rw [← _root_.Work.CORE3.H_eq_U_sup_S G I.T hBC B,
      Work.BSW.Cases.K4.card_sup_of_le_normalizer_of_inf_eq_bot hSNU
        (Work.CORE2A.inf_U_S_eq_bot B), hU3, D.S8]
  have hcard72 : Nat.card B.Hhat = 72 := by
    rw [hcardHhat, hcardH]
  exact ⟨hDiv G hFT hBC B hCase h4, hb1, hb3, hcard72⟩

end Work.CORE3

open Work.GW2

/-- The same statement, exposed under the name `Work.CORE3.Case1bNumerics` requested by the lead
(the module's main declaration sits in the doubly nested namespace `Work.CORE3.Work.CORE3`). -/
theorem Case1bNumerics (I : Case1Inputs) (hSetup : Case1bSetupProp) (hCount : Case1bCountProp)
    (h89 : Case1bEightNineProp) (hThree : Case1bThreeProp) (hOne : Case1bOneProp)
    (hDiv : Case1bDivProp) : Case1bNumericsProp :=
  _root_.Work.CORE3.Work.CORE3.Case1bNumerics I hSetup hCount h89 hThree hOne hDiv

end Work.CORE3
