import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.NumberField.House

namespace Commons.NumberTheory.NumberField

/-- For an imaginary quadratic number field `K` (degree `2` over `ℚ` with no real places),
the house of any `x : K` equals `‖σ x‖` for *any* complex embedding `σ : K →+* ℂ`.

Indeed, `K` has exactly one infinite place: `nrRealPlaces K + 2 * nrComplexPlaces K = 2`
and `nrRealPlaces K = 0` force `nrComplexPlaces K = 1`, hence
`Fintype.card (InfinitePlace K) = nrRealPlaces K + nrComplexPlaces K = 1`.
Any two complex embeddings therefore define the same place, so by
`InfinitePlace.mk_eq_iff` an arbitrary embedding `φ` is either `σ` itself or the
complex conjugate of `σ`; in both cases `‖φ x‖ = ‖σ x‖`. -/
theorem house_eq_norm_embedding_of_finrank_two {K : Type*} [Field K] [NumberField K]
    (h2 : Module.finrank ℚ K = 2) (h0 : NumberField.InfinitePlace.nrRealPlaces K = 0)
    (σ : K →+* ℂ) (x : K) : NumberField.house x = ‖σ x‖ := by
  have hrank := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [h0] at hrank
  have hnc : NumberField.InfinitePlace.nrComplexPlaces K = 1 := by omega
  have hcard : Fintype.card (NumberField.InfinitePlace K) = 1 := by
    rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K, h0, hnc]
  have hplace_unique : ∀ a b : NumberField.InfinitePlace K, a = b :=
    Fintype.card_le_one_iff.mp (le_of_eq hcard)
  -- Every complex embedding `φ` has the same value of `‖· x‖` as `σ`.
  have hnorm : ∀ φ : K →+* ℂ, ‖φ x‖₊ = ‖σ x‖₊ := by
    intro φ
    have hplace : NumberField.InfinitePlace.mk φ = NumberField.InfinitePlace.mk σ :=
      hplace_unique _ _
    rcases NumberField.InfinitePlace.mk_eq_iff.mp hplace with h | h
    · rw [h]
    · have hφ : φ = NumberField.ComplexEmbedding.conjugate σ := by
        have hc := congrArg NumberField.ComplexEmbedding.conjugate h
        rwa [NumberField.ComplexEmbedding.involutive_conjugate K φ] at hc
      rw [hφ, NumberField.ComplexEmbedding.conjugate_coe_eq]
      simp
  rw [NumberField.house_eq_sup']
  have hsup : Finset.univ.sup' Finset.univ_nonempty (fun φ : K →+* ℂ => ‖φ x‖₊) = ‖σ x‖₊ := by
    apply le_antisymm
    · apply Finset.sup'_le Finset.univ_nonempty
      intro φ _
      rw [hnorm φ]
    · exact Finset.le_sup' (fun φ : K →+* ℂ => ‖φ x‖₊) (Finset.mem_univ σ)
  rw [hsup]
  rfl

end Commons.NumberTheory.NumberField