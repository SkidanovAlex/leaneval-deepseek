import Mathlib

namespace Work.HP.LatRecurse

/-- The integers `a` with `|(a : ℝ) + c| ≤ M` form the integer interval
`[⌈-M - c⌉, ⌊M - c⌋]`, whose cardinality is thus at most `⌊2M⌋ + 1`. -/
theorem ncard_int_interval {c M : ℝ} (hM : 0 ≤ M) :
    {a : ℤ | |(a : ℝ) + c| ≤ M}.ncard ≤ Nat.floor (2 * M) + 1 := by
  -- Identify the set with an integer interval `Icc ⌈-M - c⌉ ⌊M - c⌋`.
  have hset : {a : ℤ | |(a : ℝ) + c| ≤ M} = Set.Icc ⌈-M - c⌉ ⌊M - c⌋ := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_Icc, abs_le, Int.ceil_le, Int.le_floor]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by linarith, by linarith⟩
  rw [hset, Set.ncard_Icc, Int.card_Icc]
  -- `⌊2M⌋₊` cast to `ℤ` is `⌊2M⌋`, since `2M ≥ 0`.
  have hM2 : (0 : ℝ) ≤ 2 * M := by linarith
  have hfloor : (Nat.floor (2 * M) : ℤ) = ⌊(2 * M : ℝ)⌋ := by
    rw [eq_comm, Int.floor_eq_iff]
    constructor
    · push_cast
      exact Nat.floor_le hM2
    · push_cast
      exact Nat.lt_floor_add_one (2 * M)
  -- The endpoints bound the length of the interval by `2M`.
  have hceil : (-M - c : ℝ) ≤ (⌈-M - c⌉ : ℤ) := Int.le_ceil _
  have hfl : ((⌊M - c⌋ : ℤ) : ℝ) ≤ M - c := Int.floor_le _
  have hvu : ⌊M - c⌋ - ⌈-M - c⌉ ≤ ⌊(2 * M : ℝ)⌋ := by
    rw [Int.le_floor]
    push_cast
    linarith
  rw [Int.toNat_le]
  push_cast
  rw [hfloor]
  linarith

end Work.HP.LatRecurse
