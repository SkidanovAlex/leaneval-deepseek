import Mathlib.LinearAlgebra.Matrix.Rank

namespace Commons.LinearAlgebra.Matrix


/-- Pre-composing with an injective linear map preserves the dimension of the range. -/
lemma finrank_range_comp_of_ker_eq_bot {K : Type*} [Field K]
    {U V W : Type*} [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) (hf : LinearMap.ker f = ⊥) (X : U →ₗ[K] V) :
    Module.finrank K (LinearMap.range (f.comp X)) = Module.finrank K (LinearMap.range X) := by
  rw [LinearMap.range_comp]
  exact (Submodule.equivMapOfInjective f (LinearMap.ker_eq_bot.mp hf) _).finrank_eq.symm

/-- Post-composing with a surjective linear map preserves the dimension of the range. -/
lemma finrank_range_comp_of_range_eq_top {K : Type*} [Field K]
    {U V W : Type*} [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (g : U →ₗ[K] V) (hg : LinearMap.range g = ⊤) (X : V →ₗ[K] W) :
    Module.finrank K (LinearMap.range (X.comp g)) = Module.finrank K (LinearMap.range X) := by
  rw [LinearMap.range_comp_of_range_eq_top X hg]

/-- Multiplying a matrix by an injective matrix on the left and a surjective matrix on the
right does not change its rank. -/
lemma rank_mul_mul {m n P Q : ℕ} {K : Type*} [Field K]
    (M₁ : Matrix (Fin m) (Fin P) K) (M₂ : Matrix (Fin Q) (Fin n) K)
    (X : Matrix (Fin P) (Fin Q) K)
    (h₁ : LinearMap.ker M₁.mulVecLin = ⊥) (h₂ : LinearMap.range M₂.mulVecLin = ⊤) :
    (M₁ * X * M₂).rank = X.rank := by
  simp only [Matrix.rank]
  rw [Matrix.mulVecLin_mul, Matrix.mulVecLin_mul, LinearMap.comp_assoc]
  rw [finrank_range_comp_of_ker_eq_bot M₁.mulVecLin h₁ (X.mulVecLin.comp M₂.mulVecLin),
    finrank_range_comp_of_range_eq_top M₂.mulVecLin h₂ X.mulVecLin]

/-- Conjugating the rank-poset relation `B.rank = A.rank + (B - A).rank` by an injective `M₁`
and a surjective `M₂` does not change it. -/
theorem plLE_mul_mul_iff {m n P Q : ℕ} {K : Type*} [Field K]
    (M₁ : Matrix (Fin m) (Fin P) K) (M₂ : Matrix (Fin Q) (Fin n) K)
    (A B : Matrix (Fin P) (Fin Q) K)
    (h₁ : LinearMap.ker M₁.mulVecLin = ⊥) (h₂ : LinearMap.range M₂.mulVecLin = ⊤) :
    ((M₁ * B * M₂).rank = (M₁ * A * M₂).rank + (M₁ * B * M₂ - M₁ * A * M₂).rank)
      ↔ B.rank = A.rank + (B - A).rank := by
  have hsub : M₁ * B * M₂ - M₁ * A * M₂ = M₁ * (B - A) * M₂ := by
    rw [← Matrix.sub_mul, ← Matrix.mul_sub]
  rw [hsub, rank_mul_mul M₁ M₂ B h₁ h₂, rank_mul_mul M₁ M₂ A h₁ h₂,
    rank_mul_mul M₁ M₂ (B - A) h₁ h₂]

end Commons.LinearAlgebra.Matrix