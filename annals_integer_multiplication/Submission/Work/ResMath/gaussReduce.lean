import Mathlib

/-!
# Reducing the centre of a Gaussian lattice sum to `[-1/2, 1/2]`

`Work.ResMath.gaussReduce`: for `a > 0` and every `z : ℝ` there is `η ∈ [-1/2, 1/2]` with

`∑' n : ℤ, exp (-a * (z + n)²) = ∑' n : ℤ, exp (-a * (η + n)²)`.

The Gaussian lattice sum is `1`-periodic in its centre, so it suffices to translate the
centre by an integer: take `η = z - ⌊z + 1/2⌋`, which lies in `[-1/2, 1/2]`, and reindex the
sum along the bijection `n ↦ ⌊z + 1/2⌋ + n` of `ℤ`.
-/

set_option linter.unusedVariables false

namespace Work.ResMath

theorem gaussReduce (a : ℝ) (ha : 0 < a) (z : ℝ) : ∃ η : ℝ, η ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2) ∧ (∑' n : ℤ, Real.exp (-a * (z + (n : ℝ)) ^ 2)) = (∑' n : ℤ, Real.exp (-a * (η + (n : ℝ)) ^ 2)) := by
  refine ⟨z - (⌊z + 1 / 2⌋ : ℤ), ?_, ?_⟩
  · -- `η = z - ⌊z + 1/2⌋` lies in `[-1/2, 1/2]`.
    constructor
    · have h := Int.floor_le (z + 1 / 2)
      linarith
    · have h := Int.lt_floor_add_one (z + 1 / 2)
      linarith
  · -- The summand is periodic in the centre, so reindex by the integer shift.
    have hkey : ∀ n : ℤ,
        z + (n : ℝ) = (z - (⌊z + 1 / 2⌋ : ℤ)) + ((⌊z + 1 / 2⌋ + n : ℤ) : ℝ) := by
      intro n
      push_cast
      ring
    calc ∑' n : ℤ, Real.exp (-a * (z + (n : ℝ)) ^ 2)
        = ∑' n : ℤ, Real.exp (-a * ((z - (⌊z + 1 / 2⌋ : ℤ)) + ((⌊z + 1 / 2⌋ + n : ℤ) : ℝ)) ^ 2) :=
          tsum_congr (fun n => by rw [hkey n])
      _ = ∑' k : ℤ, Real.exp (-a * ((z - (⌊z + 1 / 2⌋ : ℤ)) + (k : ℝ)) ^ 2) :=
          Equiv.tsum_eq (Equiv.addLeft (⌊z + 1 / 2⌋ : ℤ))
            (fun k : ℤ => Real.exp (-a * ((z - (⌊z + 1 / 2⌋ : ℤ)) + (k : ℝ)) ^ 2))

end Work.ResMath
