import Mathlib
import Submission.Work.Descent.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Descent

universe u

open CategoryTheory Limits AlgebraicGeometry

open scoped TensorProduct

/-- The Galois trace element: if `∑ σ, σ c = 1` in `k'`, then `1 = ∑ σ, 1 ⊗ σ c` in `A ⊗_k k'`. -/
lemma sum_tmul_one_eq_one {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] [IsGalois k k']
    {A : Type u} [CommRing A] [Algebra k A] {c : k'}
    (h : ∑ σ : Gal k k', σ c = 1) :
    (∑ σ : Gal k k', (1 : A) ⊗ₜ[k] (σ c)) = 1 := by
  rw [← TensorProduct.tmul_sum, h]
  exact Algebra.TensorProduct.one_def.symm

/-- The sum of the Galois conjugates `∑ σ, σ x` of any element `x` of `A ⊗_k k'` lies in the image
of `A`: it is the composition of `id_A ⊗ Tr` with `includeLeft`. -/
lemma sum_baseChangeAlgEquiv_mem_range {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] [IsGalois k k'] {A : Type u} [CommRing A] [Algebra k A]
    (x : TensorProduct k A k') :
    (∑ σ : Gal k k', baseChangeAlgEquiv A σ x) ∈
      (Algebra.TensorProduct.includeLeft : A →ₐ[k] TensorProduct k A k').range := by
  induction x using TensorProduct.inductionOn with
  | tmul a c =>
      rw [AlgHom.mem_range]
      refine ⟨Algebra.trace k k' c • a, ?_⟩
      rw [show (∑ σ : Gal k k', baseChangeAlgEquiv A σ (a ⊗ₜ[k] c))
          = ∑ σ : Gal k k', a ⊗ₜ[k] (σ c) from
            Finset.sum_congr rfl (fun σ _ => baseChangeAlgEquiv_tmul A σ a c)]
      rw [← TensorProduct.tmul_sum, ← trace_eq_sum_automorphisms (K := k) (L := k') c,
        Algebra.TensorProduct.includeLeft_apply, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul]
  | add x y hx hy =>
      rw [AlgHom.mem_range] at hx hy ⊢
      obtain ⟨ax, hax⟩ := hx
      obtain ⟨ay, hay⟩ := hy
      refine ⟨ax + ay, ?_⟩
      rw [show (∑ σ : Gal k k', baseChangeAlgEquiv A σ (x + y))
          = ∑ σ : Gal k k', (baseChangeAlgEquiv A σ x + baseChangeAlgEquiv A σ y) from
            Finset.sum_congr rfl (fun σ _ => map_add (baseChangeAlgEquiv A σ) x y)]
      rw [Finset.sum_add_distrib, ← hax, ← hay, map_add]

/-- The fixed points of the Galois action on `A ⊗_k k'` (acting on the second tensor factor) are
exactly the image of `A`. -/
theorem baseChange_fixed_iff {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] [IsGalois k k'] {A : Type u} [CommRing A] [Algebra k A]
    (x : TensorProduct k A k') :
    (∀ σ : Gal k k', baseChangeAlgEquiv A σ x = x) ↔
      x ∈ (Algebra.TensorProduct.includeLeft : A →ₐ[k] TensorProduct k A k').range := by
  constructor
  · intro hx
    -- Choose `c` with Galois trace `1`, so that `1 = ∑ σ, 1 ⊗ σ c` in `A ⊗_k k'`.
    obtain ⟨c, hc⟩ := Algebra.trace_surjective k k' 1
    have hc1 : ∑ σ : Gal k k', σ c = 1 := by
      rw [← trace_eq_sum_automorphisms (K := k) (L := k') c, hc, map_one]
    -- For fixed `x` we have `x = ∑ σ, σ ((1 ⊗ c) * x)`, and the right hand side lies in `A`.
    have key : (∑ σ : Gal k k', baseChangeAlgEquiv A σ (((1 : A) ⊗ₜ[k] c) * x)) = x := by
      calc ∑ σ : Gal k k', baseChangeAlgEquiv A σ (((1 : A) ⊗ₜ[k] c) * x)
          = ∑ σ : Gal k k', ((1 : A) ⊗ₜ[k] (σ c)) * x := by
              refine Finset.sum_congr rfl (fun σ _ => ?_)
              rw [map_mul, hx σ, baseChangeAlgEquiv_tmul]
        _ = (∑ σ : Gal k k', ((1 : A) ⊗ₜ[k] (σ c))) * x := (Finset.sum_mul _ _ _).symm
        _ = 1 * x := by rw [sum_tmul_one_eq_one hc1]
        _ = x := one_mul x
    rw [← key]
    exact sum_baseChangeAlgEquiv_mem_range (((1 : A) ⊗ₜ[k] c) * x)
  · intro hx σ
    obtain ⟨a, ha⟩ := hx
    rw [← ha]
    simp [Algebra.TensorProduct.includeLeft_apply]

end Work.Descent
