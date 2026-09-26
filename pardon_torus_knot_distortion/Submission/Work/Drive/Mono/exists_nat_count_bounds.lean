import Mathlib

namespace Work.Drive.Mono

/-- The extended floor of a (nonnegative) `ENNReal.ofReal` is the natural floor.  This is the
bridge between an `ENNReal`-valued upper bound via `ENNReal.ofReal` and a bound by a *natural*
number in `ℕ∞` (the value type of `Set.encard`). -/
lemma ENat_floor_ofReal_eq (x : ℝ) (hx : 0 ≤ x) :
    ENat.floor (ENNReal.ofReal x) = (⌊x⌋₊ : ℕ∞) := by
  apply le_antisymm
  · -- `⌊ofReal x⌋ₑ ≤ ⌊x⌋₊`: since `ofReal x < ⌊x⌋₊ + 1`.
    rw [ENat.floor_le (by simp : (⌊x⌋₊ : ℕ∞) ≠ ⊤)]
    rw [ENat.toENNReal_coe]
    rw [show ((⌊x⌋₊ : ENNReal) + 1) = ((⌊x⌋₊ + 1 : ℕ) : ENNReal) by push_cast; rfl]
    rw [ENNReal.ofReal_lt_natCast (by omega : ⌊x⌋₊ + 1 ≠ 0)]
    simpa using Nat.lt_floor_add_one x
  · -- `⌊x⌋₊ ≤ ⌊ofReal x⌋ₑ`: since `⌊x⌋₊ ≤ x`.
    rw [ENat.le_floor]
    rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (Nat.floor_le hx)

/-- **Two `ENNReal` counting bounds give natural bounds.**  If a set `S` has extended cardinality
at most `75 * d` and a set `U` at most `75/2 * d` in the `ENNReal` sense, and `150 * d < N`, then
there are naturals `A`, `B` with `A + 2 * B < N` and `encard S ≤ A`, `encard U ≤ B`; namely
`A := ⌊75 * d⌋` and `B := ⌊75/2 * d⌋`.

This is pure arithmetic (`⌊·⌋`, `ENNReal.ofReal`, `ENat.toENNReal`, `ENNReal.toReal`); it is the
bridge between the `ENNReal`-valued counting hypotheses of the crux and the *natural* bounds
consumed by the level-count results of the workspace (`150 = countConst`, `75 = 10*(1+eps)/eps` and
`75/2 = 5*(1+eps)/eps` for `eps = 2/13`, which the caller rewrites). -/
theorem exists_nat_count_bounds (N : ℕ) (d : ℝ) (hd : 0 ≤ d)
    (hsmall : 150 * d < (N : ℝ))
    {S U : Set ℝ}
    (hS : (↑(Set.encard S) : ENNReal) ≤ ENNReal.ofReal (75 * d))
    (hU : (↑(Set.encard U) : ENNReal) ≤ ENNReal.ofReal (75 / 2 * d)) :
    ∃ A B : ℕ, A + 2 * B < N ∧ Set.encard S ≤ A ∧ Set.encard U ≤ B := by
  -- `encard S` (resp. `encard U`) is at most the integer part of `75 * d` (resp. `75/2 * d`).
  have hS' : Set.encard S ≤ (⌊75 * d⌋₊ : ℕ∞) := by
    rw [← ENat_floor_ofReal_eq (75 * d) (by positivity)]
    exact ENat.le_floor.mpr hS
  have hU' : Set.encard U ≤ (⌊75 / 2 * d⌋₊ : ℕ∞) := by
    rw [← ENat_floor_ofReal_eq (75 / 2 * d) (by positivity)]
    exact ENat.le_floor.mpr hU
  refine ⟨⌊75 * d⌋₊, ⌊75 / 2 * d⌋₊, ?_, hS', hU'⟩
  -- `⌊75 d⌋ + 2 ⌊75 d / 2⌋ ≤ 75 d + 75 d = 150 d < N`.
  have hA : ((⌊75 * d⌋₊ : ℕ) : ℝ) ≤ 75 * d := Nat.floor_le (by positivity)
  have hB : ((⌊75 / 2 * d⌋₊ : ℕ) : ℝ) ≤ 75 / 2 * d := Nat.floor_le (by positivity)
  have : ((⌊75 * d⌋₊ + 2 * ⌊75 / 2 * d⌋₊ : ℕ) : ℝ) < (N : ℝ) := by
    push_cast
    nlinarith [hA, hB, hsmall]
  exact_mod_cast this

end Work.Drive.Mono
