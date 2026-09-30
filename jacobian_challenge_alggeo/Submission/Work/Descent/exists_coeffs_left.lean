import Mathlib
import Submission.Work.Descent.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


universe u

namespace Work.Descent

/-- For a `k`-basis `c` of `k'` indexed by the Galois group there are, for each `σ₀` in the group,
coefficients `l` with `∑ τ, l τ * σ (c τ)` equal to `1` at `σ = σ₀` and `0` elsewhere. -/
theorem exists_coeffs_left {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] [IsGalois k k'] (c : Module.Basis (Work.Descent.Gal k k') k k')
    (σ₀ : Work.Descent.Gal k k') : ∃ l : Work.Descent.Gal k k' → k',
      (∑ τ, l τ * σ₀ (c τ)) = 1 ∧
        ∀ σ : Work.Descent.Gal k k', σ ≠ σ₀ → ∑ τ, l τ * σ (c τ) = 0 := by
  classical
  -- The Galois automorphisms, viewed as `k`-linear endomorphisms of `k'`, are `k'`-linearly
  -- independent (Dedekind's independence of characters).
  have hli : LinearIndependent k' (fun τ : Gal k k' => (τ : k' →ₐ[k] k').toLinearMap) :=
    (linearIndependent_algHom_toLinearMap k k' k').comp
      (fun τ : Gal k k' => (τ : k' →ₐ[k] k')) AlgEquiv.coe_toAlgHom_injective
  -- The "Galois matrix" `A υ τ = τ (c υ)`.
  set A : Matrix (Gal k k') (Gal k k') k' := Matrix.of (fun υ τ => τ (c υ)) with hA
  -- The matrix `A` is invertible: its kernel is trivial.
  have key : ∀ l : Gal k k' → k', A.mulVec l = 0 → l = 0 := by
    intro l hl
    have hψ : (∑ τ : Gal k k', l τ • ((τ : k' →ₐ[k] k').toLinearMap)) = 0 := by
      apply Module.Basis.ext c
      intro υ
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply,
        smul_eq_mul, LinearMap.zero_apply]
      have h := congr_fun hl υ
      simp only [Matrix.mulVec_apply_eq_sum, hA, Matrix.of_apply, Pi.zero_apply] at h
      rw [← h]
      apply Finset.sum_congr rfl
      intro τ _
      simp only [AlgEquiv.toAlgHom_apply, mul_comm]
    exact funext (Fintype.linearIndependent_iff.mp hli l hψ)
  have hAinj : Function.Injective A.mulVec := by
    intro x y hxy
    exact sub_eq_zero.mp (key (x - y) (by rw [Matrix.mulVec_sub, hxy, sub_self]))
  have hAunit : IsUnit A := Matrix.mulVec_injective_iff_isUnit.mp hAinj
  -- Hence the transpose `Aᵀ` (which is the "Galois matrix" `σ (c τ)`) is invertible,
  -- so its matrix-vector multiplication is surjective.
  have hsurj : Function.Surjective A.transpose.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr ((Matrix.isUnit_transpose A).mpr hAunit)
  obtain ⟨l, hl⟩ := hsurj (Pi.single σ₀ 1)
  refine ⟨l, ?_, ?_⟩
  · have h := congr_fun hl σ₀
    simp only [Matrix.mulVec_apply_eq_sum, Matrix.transpose_apply, hA, Matrix.of_apply,
      Pi.single_eq_same] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro τ _
    rw [mul_comm]
  · intro σ hσ
    have h := congr_fun hl σ
    simp only [Matrix.mulVec_apply_eq_sum, Matrix.transpose_apply, hA, Matrix.of_apply,
      Pi.single_eq_of_ne hσ] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro τ _
    rw [mul_comm]

end Work.Descent
