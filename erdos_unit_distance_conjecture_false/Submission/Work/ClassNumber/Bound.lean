import Mathlib
import Submission.Work.ClassNumber.IdealCount
import Submission.Work.ClassNumber.MinkowskiBound
import Submission.Work.ClassNumber.ClassNumberInjection

namespace Work.ClassNumber

/-- **Minkowski's bound** (paper Proposition 3.7): the class number of a number field is at most
exponential in the degree, with a base depending only on the root discriminant. -/
theorem Bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type*) [Field K] [NumberField K] (A : ℝ), 1 ≤ A →
      NumberField.rootDiscr K ≤ A →
      (NumberField.classNumber K : ℝ) ≤ (C * A * (1 + Real.log A)) ^ (Module.finrank ℚ K) := by
  classical
  refine ⟨8, by norm_num, ?_⟩
  intro K _ _ A hA hroot
  -- The Minkowski bound of `K`, and its rounded-down value.
  set M : ℝ := (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
      ((Module.finrank ℚ K).factorial / (Module.finrank ℚ K) ^ (Module.finrank ℚ K) *
        Real.sqrt |((NumberField.discr K : ℤ) : ℝ)|) with hM
  have hMnonneg : 0 ≤ M := by rw [hM]; positivity
  -- Minkowski: the Minkowski bound is at most `(2 √A)^{[K:ℚ]}`.
  have hMin : M ≤ (2 * Real.sqrt A) ^ (Module.finrank ℚ K) := by
    rw [hM]; exact MinkowskiBound K hA hroot
  -- Every ideal class contains an integral ideal of norm at most `M`.
  have h1 : (NumberField.classNumber K : ℝ) ≤
      (Nat.card {I : Ideal (NumberField.RingOfIntegers K) // I ≠ ⊥ ∧
        Ideal.absNorm I ≤ ⌊M⌋₊} : ℝ) :=
    ClassNumberInjection K M hM.ge
  -- The number of integral ideals of norm at most `⌊M⌋₊` is at most `⌊M⌋₊² · 2^{[K:ℚ]}`.
  have h2 : (Nat.card {I : Ideal (NumberField.RingOfIntegers K) // I ≠ ⊥ ∧
        Ideal.absNorm I ≤ ⌊M⌋₊} : ℝ) ≤ (⌊M⌋₊ : ℝ) ^ 2 * (2 : ℝ) ^ Module.finrank ℚ K := by
    have h := IdealCount K ⌊M⌋₊
    exact_mod_cast h
  have h3 : (⌊M⌋₊ : ℝ) ≤ (2 * Real.sqrt A) ^ (Module.finrank ℚ K) :=
    (Nat.floor_le hMnonneg).trans hMin
  -- Collect the constants: `⌊M⌋₊² · 2^{[K:ℚ]} ≤ (8A)^{[K:ℚ]}`.
  have h4 : (⌊M⌋₊ : ℝ) ^ 2 * (2 : ℝ) ^ Module.finrank ℚ K ≤
      (8 * A) ^ (Module.finrank ℚ K) := by
    have hsq : (⌊M⌋₊ : ℝ) ^ 2 ≤ ((2 * Real.sqrt A) ^ (Module.finrank ℚ K)) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) h3 2
    calc (⌊M⌋₊ : ℝ) ^ 2 * (2 : ℝ) ^ Module.finrank ℚ K
        ≤ ((2 * Real.sqrt A) ^ (Module.finrank ℚ K)) ^ 2 * (2 : ℝ) ^ Module.finrank ℚ K :=
          mul_le_mul_of_nonneg_right hsq (by positivity)
      _ = (8 * A) ^ (Module.finrank ℚ K) := by
          rw [← pow_mul, mul_comm (Module.finrank ℚ K) 2, pow_mul, ← mul_pow]
          congr 1
          rw [mul_pow, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ A)]
          ring
  have h5 : (8 * A) ^ (Module.finrank ℚ K) ≤
      (8 * A * (1 + Real.log A)) ^ (Module.finrank ℚ K) := by
    refine pow_le_pow_left₀ (by positivity) ?_ _
    nlinarith [Real.log_nonneg hA]
  calc (NumberField.classNumber K : ℝ)
      ≤ (Nat.card {I : Ideal (NumberField.RingOfIntegers K) // I ≠ ⊥ ∧
          Ideal.absNorm I ≤ ⌊M⌋₊} : ℝ) := h1
    _ ≤ (⌊M⌋₊ : ℝ) ^ 2 * (2 : ℝ) ^ Module.finrank ℚ K := h2
    _ ≤ (8 * A) ^ (Module.finrank ℚ K) := h4
    _ ≤ (8 * A * (1 + Real.log A)) ^ (Module.finrank ℚ K) := h5

end Work.ClassNumber
