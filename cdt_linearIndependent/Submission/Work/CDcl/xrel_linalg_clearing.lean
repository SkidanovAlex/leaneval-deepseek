import Mathlib

namespace Work.CDcl

/-- Clearing denominators for a finite family of rational functions: given
`c : Fin 5 → RatFunc ℚ` and `D : RatFunc ℚ`, there is a nonzero `A : RatFunc ℚ`
such that `A * c k` and `A * D` all lie in the image of `Polynomial ℚ`. -/
theorem xrel_linalg_clearing (c : Fin 5 → RatFunc ℚ) (hc : c ≠ 0) (D : RatFunc ℚ) :
    ∃ (A : RatFunc ℚ) (Q : Fin 5 → Polynomial ℚ) (r : Polynomial ℚ),
      A ≠ 0 ∧ (∀ k, algebraMap (Polynomial ℚ) (RatFunc ℚ) (Q k) = A * c k) ∧
      algebraMap (Polynomial ℚ) (RatFunc ℚ) r = A * D := by
  classical
  -- A common denominator for the finite set of rational functions `c k`, `D`:
  -- `b ∈ nonZeroDivisors ℚ[X]` clears denominators of all of them at once.
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors (Polynomial ℚ)) (Finset.univ.image c ∪ {D})
  have hbk : ∀ k, ∃ q : Polynomial ℚ,
      algebraMap (Polynomial ℚ) (RatFunc ℚ) q =
        algebraMap (Polynomial ℚ) (RatFunc ℚ) (b : Polynomial ℚ) * c k := by
    intro k
    have h := hb (c k) (by simp)
    rw [IsLocalization.IsInteger, RingHom.mem_rangeS] at h
    obtain ⟨q, hq⟩ := h
    exact ⟨q, by rw [hq, Algebra.smul_def]⟩
  have hbD : ∃ q : Polynomial ℚ,
      algebraMap (Polynomial ℚ) (RatFunc ℚ) q =
        algebraMap (Polynomial ℚ) (RatFunc ℚ) (b : Polynomial ℚ) * D := by
    have h := hb D (by simp)
    rw [IsLocalization.IsInteger, RingHom.mem_rangeS] at h
    obtain ⟨q, hq⟩ := h
    exact ⟨q, by rw [hq, Algebra.smul_def]⟩
  choose Q hQ using hbk
  obtain ⟨r, hr⟩ := hbD
  refine ⟨algebraMap (Polynomial ℚ) (RatFunc ℚ) (b : Polynomial ℚ), Q, r, ?_, hQ, hr⟩
  -- `A ≠ 0` because `b ≠ 0` and `algebraMap` into the fraction field is injective.
  intro hzero
  exact nonZeroDivisors.ne_zero b.property
    (IsFractionRing.injective (Polynomial ℚ) (RatFunc ℚ) (by simpa using hzero))

end Work.CDcl
