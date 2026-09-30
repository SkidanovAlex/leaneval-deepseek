import Mathlib
import Submission.Work.Descent.Basic
import Submission.Work.Descent.baseChange_fixed_iff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Descent

universe u

open CategoryTheory Limits AlgebraicGeometry

/-- Affine case of the descent of invariant maps: a `k`-algebra map `C →ₐ[k] A ⊗_k k'` whose
image is fixed by the Galois action (acting on the second tensor factor) factors uniquely through
`A → A ⊗_k k'`. -/
theorem affine_desc {k k' : Type u} [Field k] [Field k'] [Algebra k k'] [FiniteDimensional k k']
    [IsGalois k k'] {A C : Type u} [CommRing A] [Algebra k A] [CommRing C] [Algebra k C]
    (f : C →ₐ[k] TensorProduct k A k')
    (hf : ∀ σ : Gal k k', (baseChangeAlgEquiv A σ).toAlgHom.comp f = f) :
    ∃! g : C →ₐ[k] A,
      (Algebra.TensorProduct.includeLeft : A →ₐ[k] TensorProduct k A k').comp g = f := by
  -- Write `F` for the structure map `A →ₐ[k] A ⊗_k k'`, `a ↦ a ⊗ 1`.
  let F : A →ₐ[k] TensorProduct k A k' := Algebra.TensorProduct.includeLeft
  -- `F` is injective because `k` is a field (so `A` is flat) and `k → k'` is injective.
  have hF : Function.Injective F :=
    Algebra.TensorProduct.includeLeft_injective (R := k) (S := k) (A := A) (B := k')
      (algebraMap k k').injective
  -- Every value of `f` is fixed by the Galois action.
  have hfix : ∀ (σ : Gal k k') (c : C), baseChangeAlgEquiv A σ (f c) = f c := fun σ c =>
    congrArg (fun (h : C →ₐ[k] TensorProduct k A k') => h c) (hf σ)
  -- Hence by the fixed-point theorem every value of `f` lies in the image of `F`.
  have hmem : ∀ c : C, f c ∈ F.range := fun c =>
    (baseChange_fixed_iff (f c)).mp (fun σ => hfix σ c)
  -- `F` identifies `A` with its range; the inverse of this identification lets us pull `f` back.
  have hsymm : ∀ y : F.range,
      F ((AlgEquiv.ofInjective F hF).symm y) = (y : TensorProduct k A k') := by
    intro y
    have h := AlgEquiv.ofInjective_apply F hF ((AlgEquiv.ofInjective F hF).symm y)
    rw [AlgEquiv.apply_symm_apply] at h
    exact h.symm
  -- The descended map.
  let g : C →ₐ[k] A :=
    ((AlgEquiv.ofInjective F hF).symm : F.range →ₐ[k] A).comp (f.codRestrict F.range hmem)
  have hg : F.comp g = f := by
    ext c
    show F ((AlgEquiv.ofInjective F hF).symm ((f.codRestrict F.range hmem) c)) = f c
    rw [hsymm]
    rfl
  refine ⟨g, ?_, ?_⟩
  · simpa only [F] using hg
  · intro y hy
    ext c
    apply hF
    have h1 : F (y c) = f c :=
      congrArg (fun (h : C →ₐ[k] TensorProduct k A k') => h c) hy
    have h2 : F (g c) = f c :=
      congrArg (fun (h : C →ₐ[k] TensorProduct k A k') => h c) hg
    rw [h1, h2]

end Work.Descent
