import Mathlib
import Submission.Work.BW.mixedCoordAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A per-place bound from a bound on the `stdBasis` coordinates

If every `mixedEmbedding.stdBasis` coordinate of a point `z` of the mixed space is bounded in
absolute value by `ρ`, then the norm of `z` at any infinite place `v` is bounded by `ρ` if `v` is
real and by `√2 · ρ` if `v` is complex (the real and imaginary parts of a complex coordinate are
each bounded by `ρ`).
-/

noncomputable section

open NumberField

namespace Work.BW

lemma normAtPlace_le_of_repr_le {F : Type*} [Field F] [NumberField F]
    (z : NumberField.mixedEmbedding.mixedSpace F) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : ∀ k : NumberField.mixedEmbedding.index F,
      |(NumberField.mixedEmbedding.stdBasis F).repr z k| ≤ ρ) :
    ∀ v : NumberField.InfinitePlace F,
      NumberField.mixedEmbedding.normAtPlace v z ≤ Work.BW.placeBound ρ v := by
  intro v
  rcases NumberField.InfinitePlace.isReal_or_isComplex v with hv | hv
  · -- real place: the coordinate of `z` is itself one of the `stdBasis` coordinates
    rw [NumberField.mixedEmbedding.normAtPlace_apply_of_isReal hv, Work.BW.placeBound_of_isReal hv]
    have h1 := h (Sum.inl ⟨v, hv⟩)
    rw [NumberField.mixedEmbedding.stdBasis_apply_isReal] at h1
    simpa using h1
  · -- complex place: both parts are `stdBasis` coordinates, and `‖a‖ ≤ √2 · ρ`
    rw [NumberField.mixedEmbedding.normAtPlace_apply_of_isComplex hv,
      Work.BW.placeBound_of_isComplex hv]
    have hre : |(z.2 ⟨v, hv⟩).re| ≤ ρ := by
      have := h (Sum.inr (⟨v, hv⟩, 0))
      rwa [NumberField.mixedEmbedding.stdBasis_apply_isComplex_fst] at this
    have him : |(z.2 ⟨v, hv⟩).im| ≤ ρ := by
      have := h (Sum.inr (⟨v, hv⟩, 1))
      rwa [NumberField.mixedEmbedding.stdBasis_apply_isComplex_snd] at this
    have h1 : (z.2 ⟨v, hv⟩).re ^ 2 ≤ ρ ^ 2 := by
      nlinarith [abs_le.mp hre]
    have h2 : (z.2 ⟨v, hv⟩).im ^ 2 ≤ ρ ^ 2 := by
      nlinarith [abs_le.mp him]
    have hsq : ‖z.2 ⟨v, hv⟩‖ ^ 2 ≤ (Real.sqrt 2 * ρ) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      nlinarith
    calc ‖z.2 ⟨v, hv⟩‖ = Real.sqrt (‖z.2 ⟨v, hv⟩‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt ((Real.sqrt 2 * ρ) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt 2 * ρ := Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg 2) hρ)

end Work.BW
