import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.CrossProduct

open scoped Matrix

namespace Commons.Analysis.CrossProduct

/-- The cross product of two vectors in `F³` (for a field `F`) vanishes
exactly when they are linearly dependent over `F`: one of them is the zero
vector, or the second is a scalar multiple of the first.

This is the function-space version of `cross3_eq_zero_iff_smul`, phrased on
`Fin 3 → F` where Mathlib's `⨯₃` cross product lives.  The forward direction
uses Mathlib's rank criterion
`crossProduct_ne_zero_iff_linearIndependent` together with the pair
independence lemma `LinearIndependent.pair_iff'`: over a field, two vectors
fail to be independent precisely when the second lies in the span of the
first (here made explicit as `∃ t, B = t • A` when `A ≠ 0`). -/
lemma cross3_eq_zero_iff_smul_field {F : Type*} [Field F] (A B : Fin 3 → F) :
    A ⨯₃ B = 0 ↔ A = 0 ∨ ∃ t : F, B = t • A := by
  by_cases hA : A = 0
  · rw [hA]
    simp
  constructor
  · intro h
    right
    -- `crossProduct A B = 0` contradicts the linear-independence criterion,
    -- so `A` and `B` are linearly dependent.
    have hnotLI : ¬ LinearIndependent F ![A, B] := by
      intro hLI
      exact ((crossProduct_ne_zero_iff_linearIndependent (F := F) (v := A) (w := B)).mpr hLI) h
    -- With `A ≠ 0`, `LinearIndependent.pair_iff'` says dependence means some
    -- scalar multiple of `A` equals `B`.
    have hnotall : ¬ ∀ t : F, t • A ≠ B := by
      intro hall
      exact hnotLI ((LinearIndependent.pair_iff' (x := A) (y := B) hA).mpr hall)
    rw [not_forall] at hnotall
    rcases hnotall with ⟨t, ht⟩
    have htAB : t • A = B := by simpa using ht
    exact ⟨t, htAB.symm⟩
  · intro h
    rcases h with hA0 | ⟨t, hB⟩
    · exact False.elim (hA hA0)
    · rw [hB]
      simp

/-- The cross product of two vectors in `EuclideanSpace ℝ (Fin 3)` (i.e. in
`ℝ³`, equipped with its Euclidean norm via the `WithLp` transportation) is
zero exactly when the vectors are linearly dependent over `ℝ`: either the
first is zero, or the second is a real scalar multiple of the first. -/
theorem cross3_eq_zero_iff_smul (u v : EuclideanSpace ℝ (Fin 3)) :
    WithLp.toLp 2 (WithLp.ofLp u ⨯₃ WithLp.ofLp v) = 0 ↔ u = 0 ∨ ∃ t : ℝ, v = t • u := by
  calc
    (WithLp.toLp 2 (WithLp.ofLp u ⨯₃ WithLp.ofLp v) = 0)
        ↔ WithLp.ofLp u ⨯₃ WithLp.ofLp v = 0 := by
          -- `WithLp.toLp` / `WithLp.ofLp` form a bijection (definitionally),
          -- so a transported vector is zero iff its underlying function is.
          constructor
          · intro h
            simpa using congrArg (WithLp.ofLp (p := 2) (V := Fin 3 → ℝ)) h
          · intro h
            simp [h]
    _ ↔ WithLp.ofLp u = 0 ∨ ∃ t : ℝ, WithLp.ofLp v = t • WithLp.ofLp u := by
          exact cross3_eq_zero_iff_smul_field (F := ℝ) (WithLp.ofLp u) (WithLp.ofLp v)
    _ ↔ u = 0 ∨ ∃ t : ℝ, v = t • u := by
          -- `WithLp.ofLp` is injective and ℝ-linear, so equality and scalar
          -- multiples transport back and forth through the `WithLp` wrapper.
          constructor
          · rintro (h | ⟨t, h⟩)
            · exact Or.inl ((WithLp.ofLp_eq_zero (p := 2) (V := Fin 3 → ℝ)).mp h)
            · exact Or.inr ⟨t, by
                simpa using congrArg (WithLp.toLp (p := 2) (V := Fin 3 → ℝ)) h⟩
          · rintro (h | ⟨t, h⟩)
            · exact Or.inl (by
                simpa using congrArg (WithLp.ofLp (p := 2) (V := Fin 3 → ℝ)) h)
            · exact Or.inr ⟨t, by
                simpa using congrArg (WithLp.ofLp (p := 2) (V := Fin 3 → ℝ)) h⟩

end Commons.Analysis.CrossProduct
