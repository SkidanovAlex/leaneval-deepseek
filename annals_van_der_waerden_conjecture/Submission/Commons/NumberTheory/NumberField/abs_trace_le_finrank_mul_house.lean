import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.NumberField.House
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.NumberTheory.NumberField

/-- The trace of an algebraic integer is bounded by the degree times its house: this is the
elementary estimate `|Tr(a)| ≤ n · house(a)` obtained by writing the trace as the sum of the
conjugates of `a` and bounding each conjugate by the house. -/
theorem abs_trace_le_finrank_mul_house {K : Type*} [Field K] [NumberField K]
    (a : NumberField.RingOfIntegers K) :
    |((Algebra.trace ℚ K ((a : NumberField.RingOfIntegers K) : K) : ℚ) : ℝ)| ≤
      (Module.finrank ℚ K : ℝ) * NumberField.house (((a : NumberField.RingOfIntegers K) : K)) := by
  set x : K := ((a : NumberField.RingOfIntegers K) : K) with hx
  -- The trace is the sum of the conjugates, i.e. of the values of the `ℚ`-embeddings into `ℂ`.
  have htr : algebraMap ℚ ℂ (Algebra.trace ℚ K x) = ∑ σ : K →ₐ[ℚ] ℂ, σ x :=
    trace_eq_sum_embeddings ℂ
  -- There are exactly `finrank ℚ K` such embeddings.
  have hcard : Fintype.card (K →ₐ[ℚ] ℂ) = Module.finrank ℚ K := AlgHom.card ℚ K ℂ
  have hbound : ‖algebraMap ℚ ℂ (Algebra.trace ℚ K x)‖ ≤
      (Module.finrank ℚ K : ℝ) * NumberField.house x := by
    rw [htr]
    calc ‖∑ σ : K →ₐ[ℚ] ℂ, σ x‖ ≤ ∑ σ : K →ₐ[ℚ] ℂ, ‖σ x‖ := norm_sum_le _ _
      _ ≤ ∑ _σ : K →ₐ[ℚ] ℂ, NumberField.house x := by
            apply Finset.sum_le_sum; intro σ _
            rw [← AlgHom.coe_toRingHom]
            exact NumberField.norm_embedding_le_house x σ.toRingHom
      _ = (Module.finrank ℚ K : ℝ) * NumberField.house x := by
            rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
  -- Identify `‖algebraMap ℚ ℂ q‖` with the absolute value of `q : ℝ`.
  rw [show algebraMap ℚ ℂ (Algebra.trace ℚ K x) = ((Algebra.trace ℚ K x : ℚ) : ℂ) from by simp,
    Complex.norm_ratCast] at hbound
  exact hbound

end Commons.NumberTheory.NumberField