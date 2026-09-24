import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.BLodDefs

open Finset
open scoped BigOperators

namespace Work.NumberTheory.Chen.BTermCount

attribute [local instance] Classical.propDecidable

/-!
# The dyadic-block decomposition of the plain `a`-coefficient

The window `[M, Y)` is partitioned into the dyadic blocks `[M * 2^j, 2 * M * 2^j)`,
`j = 0, …, blockCount M Y - 1`.  Consequently the plain (unblocked) `a`-coefficient
`aCoeff0 M Y u` — the indicator of the primes of `[M, Y)`, cut down by coprimality to
a modulus `d` — is the *sum* of the blocked coefficients `aCoeffC M Y j d u` over the
blocks:

  `aCoeff0C M Y d u = ∑ j ∈ Finset.range (blockCount M Y), aCoeffC M Y j d u`.

This is the elementary identity that allows a bilinear character sum against the plain
`a`-coefficient to be evaluated block by block.
-/

/-- `aCoeff` factors as the plain coefficient `aCoeff0` times the indicator of the
dyadic block condition. -/
theorem aCoeff_eq_aCoeff0_mul (M Y j u : ℕ) :
    aCoeff M Y j u = aCoeff0 M Y u *
      (if blockStart M j ≤ u ∧ u < 2 * blockStart M j then (1 : ℂ) else 0) := by
  unfold aCoeff aCoeff0
  by_cases h : u.Prime ∧ M ≤ u ∧ u < Y
  · have hiff : (u.Prime ∧ M ≤ u ∧ u < Y ∧ blockStart M j ≤ u ∧ u < 2 * blockStart M j)
        ↔ (blockStart M j ≤ u ∧ u < 2 * blockStart M j) := by
      constructor
      · intro hh; exact ⟨hh.2.2.2.1, hh.2.2.2.2⟩
      · intro hh; exact ⟨h.1, h.2.1, h.2.2, hh.1, hh.2⟩
    rw [if_congr hiff rfl rfl, if_pos h, one_mul]
  · have hnot : ¬(u.Prime ∧ M ≤ u ∧ u < Y ∧ blockStart M j ≤ u ∧ u < 2 * blockStart M j) :=
      fun hh => h ⟨hh.1, hh.2.1, hh.2.2.1⟩
    rw [if_neg hnot, if_neg h, zero_mul]

/-- The coprimality-cut coefficient `aCoeffC` factors in the same way. -/
theorem aCoeffC_eq_aCoeff0C_mul (M Y j d u : ℕ) :
    aCoeffC M Y j d u = aCoeff0C M Y d u *
      (if blockStart M j ≤ u ∧ u < 2 * blockStart M j then (1 : ℂ) else 0) := by
  rw [aCoeffC_eq, aCoeff0C_eq, aCoeff_eq_aCoeff0_mul]
  ring

/-- For a prime `u ∈ [M, Y)` with `M ≥ 1` there is exactly one dyadic block containing
`u`, namely the block `j = Nat.log 2 (u / M)`.  Hence the block indicators sum to `1`. -/
theorem blockIndicator_sum_eq_one (M Y u : ℕ) (hM : 1 ≤ M)
    (hu : u.Prime ∧ M ≤ u ∧ u < Y) :
    ∑ j ∈ Finset.range (blockCount M Y),
      (if blockStart M j ≤ u ∧ u < 2 * blockStart M j then (1 : ℂ) else 0) = 1 := by
  have hMpos : 0 < M := hM
  obtain ⟨hup, hMle, huY⟩ := hu
  have hne : u / M ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.div_pos hMle hMpos)
  have hkey : ∀ j : ℕ,
      (blockStart M j ≤ u ∧ u < 2 * blockStart M j) ↔ j = Nat.log 2 (u / M) := by
    intro j
    have h1 : blockStart M j ≤ u ↔ 2 ^ j ≤ u / M := by
      rw [blockStart, Nat.mul_comm M (2^j), Nat.le_div_iff_mul_le hMpos]
    have h2 : u < 2 * blockStart M j ↔ u / M < 2 ^ (j+1) := by
      have hpow : 2 * blockStart M j = M * 2 ^ (j+1) := by
        rw [blockStart, pow_succ]; ring
      rw [hpow, Nat.div_lt_iff_lt_mul hMpos, Nat.mul_comm M (2^(j+1))]
    rw [h1, h2]
    constructor
    · intro ⟨hlo, hhi⟩
      have hle : j ≤ Nat.log 2 (u / M) := by
        by_contra h
        rw [not_le] at h
        have hpl : Nat.log 2 (u / M) + 1 ≤ j := by omega
        have hp : 2 ^ (Nat.log 2 (u / M) + 1) ≤ 2 ^ j :=
          Nat.pow_le_pow_right (n := 2) (by norm_num) hpl
        have hl := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (u / M)
        simp only [Nat.succ_eq_add_one] at hl
        omega
      have hge : Nat.log 2 (u / M) ≤ j := by
        by_contra h
        rw [not_le] at h
        have hpl : j + 1 ≤ Nat.log 2 (u / M) := by omega
        have hp : 2 ^ (j + 1) ≤ 2 ^ Nat.log 2 (u / M) :=
          Nat.pow_le_pow_right (n := 2) (by norm_num) hpl
        have hlog := Nat.pow_log_le_self 2 hne
        omega
      exact le_antisymm hle hge
    · intro h
      rw [h]
      refine ⟨Nat.pow_log_le_self 2 hne, ?_⟩
      have hl := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (u / M)
      simpa [Nat.succ_eq_add_one] using hl
  have hle : u / M ≤ Y / M + 1 := by
    have h1 : u / M ≤ (Y-1) / M := Nat.div_le_div_right (by omega)
    have h2 : (Y-1) / M ≤ Y / M := Nat.div_le_div_right (by omega)
    omega
  have hj0mem : Nat.log 2 (u / M) ∈ Finset.range (blockCount M Y) := by
    rw [Finset.mem_range, blockCount]
    have := Nat.log_mono_right (b := 2) hle
    omega
  have hmain := Finset.sum_eq_single (s := Finset.range (blockCount M Y))
      (f := fun j => (if blockStart M j ≤ u ∧ u < 2 * blockStart M j then (1:ℂ) else 0))
      (Nat.log 2 (u / M))
      (fun b _ hne' => by rw [if_neg]; intro hc; exact hne' ((hkey b).mp hc))
      (fun hnot => absurd hj0mem hnot)
  rw [hmain]
  rw [if_pos ((hkey _).mpr rfl)]

/-- **The dyadic-block split of the plain `a`-coefficient.**  The plain coefficient equals
the sum of the blocked coefficients over the dyadic blocks of the window. -/
theorem BLodBlockSplit (M Y d u : ℕ) (hM : 1 ≤ M) :
    aCoeff0C M Y d u = ∑ j ∈ Finset.range (blockCount M Y), aCoeffC M Y j d u := by
  by_cases hu : u.Prime ∧ M ≤ u ∧ u < Y
  · calc aCoeff0C M Y d u
        = aCoeff0C M Y d u * 1 := by ring
      _ = aCoeff0C M Y d u * (∑ j ∈ Finset.range (blockCount M Y),
            (if blockStart M j ≤ u ∧ u < 2 * blockStart M j then (1:ℂ) else 0)) := by
            rw [blockIndicator_sum_eq_one M Y u hM hu]
      _ = ∑ j ∈ Finset.range (blockCount M Y), aCoeff0C M Y d u *
            (if blockStart M j ≤ u ∧ u < 2 * blockStart M j then (1:ℂ) else 0) := by
            rw [Finset.mul_sum]
      _ = ∑ j ∈ Finset.range (blockCount M Y), aCoeffC M Y j d u := by
            refine Finset.sum_congr rfl (fun j _ => ?_)
            rw [aCoeffC_eq_aCoeff0C_mul]
  · have h0 : aCoeff0C M Y d u = 0 := by
      unfold aCoeff0C aCoeff0
      rw [if_neg hu, zero_mul]
    rw [h0]
    symm
    refine Finset.sum_eq_zero (fun j _ => ?_)
    unfold aCoeffC aCoeff
    rw [if_neg ?_, zero_mul]
    intro hh
    exact hu ⟨hh.1, hh.2.1, hh.2.2.1⟩

end Work.NumberTheory.Chen.BTermCount
