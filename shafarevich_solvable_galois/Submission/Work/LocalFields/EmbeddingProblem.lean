/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Embedding problems and their solutions

Shafarevich's theorem is proved by induction on the order of the solvable group `G`, using the
*solvability of embedding problems with abelian kernel*: given a finite Galois extension `l/k`
with `Gal(l/k) ≅ G/A` for an abelian normal `A ◁ G`, one must find a finite Galois extension
`m/k` containing `l` with `Gal(m/k) ≅ G`.

This file sets up that vocabulary in unbundled form (all instances are parameters):

* `Work.LocalFields.IsEmbeddingProblem l E π` : `π : E ↠ Gal(l/k)` is a finite embedding problem
  over `k` (with kernel `π.ker`);
* `Work.LocalFields.IsSolution l E π m F e_F e` : a finite Galois extension `m/k` with a
  subextension `F ≅ l` and an isomorphism `Gal(m/k) ≃* E` carrying the subgroup fixing `F` onto
  `ker π`;
* `Work.LocalFields.Solvable l E π` : `∃` a solution;
* `Work.LocalFields.HasEmbeddingPropertyWithAbelianKernel k` and
  `Work.LocalFields.LocalEmbeddingProblemInput k` : the named global and local inputs.

## Main results

* `Work.LocalFields.solvable_of_bijective` : the trivial embedding problem is solvable.
-/
import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocalFields

universe u

variable {k : Type*} [Field k]

/-- **The embedding problem** over `k` given by a finite Galois extension `l/k`, a finite group
`E` and a surjection `π : E ↠ Gal(l/k)`.  The problem has *abelian kernel* if `↥π.ker` is
abelian. -/
def IsEmbeddingProblem (l : Type*) [Field l] [Algebra k l] [FiniteDimensional k l]
    [IsGalois k l] (E : Type*) [Group E] [Finite E] (π : E →* (l ≃ₐ[k] l)) : Prop :=
  Function.Surjective π

/-- **A solution** of the embedding problem `(l/k, E, π)`: a finite Galois extension `m/k`, a
subextension `F` isomorphic to `l` over `k`, and an isomorphism `Gal(m/k) ≃* E` carrying the
subgroup fixing `F` (i.e. `Gal(m/F)`) onto `ker π`.  Equivalently, under the identification
`Gal(F/k) ≅ Gal(l/k) = E ⧸ ker π`, the restriction map `Gal(m/k) →* Gal(F/k)` is `π`. -/
def IsSolution (l : Type*) [Field l] [Algebra k l] [FiniteDimensional k l] [IsGalois k l]
    (E : Type*) [Group E] [Finite E] (π : E →* (l ≃ₐ[k] l))
    (m : Type*) [Field m] [Algebra k m] [FiniteDimensional k m] [IsGalois k m]
    (F : IntermediateField k m) (e_F : F ≃ₐ[k] l) (e : (m ≃ₐ[k] m) ≃* E) : Prop :=
  Subgroup.map e (IntermediateField.fixingSubgroup F) = π.ker

/-- The embedding problem `(l/k, E, π)` is **solvable** if it has a solution. -/
def Solvable (l : Type u) [Field l] [Algebra k l] [FiniteDimensional k l] [IsGalois k l]
    (E : Type*) [Group E] [Finite E] (π : E →* (l ≃ₐ[k] l)) : Prop :=
  ∃ (m : Type u) (_ : Field m) (_ : Algebra k m) (_ : FiniteDimensional k m) (_ : IsGalois k m)
    (F : IntermediateField k m) (e_F : F ≃ₐ[k] l) (e : (m ≃ₐ[k] m) ≃* E),
    IsSolution l E π m F e_F e

/-- The trivial embedding problem (`π` bijective, i.e. `E ≅ Gal(l/k)`) is solvable: take
`m = l` and `F = ⊤`. -/
theorem solvable_of_bijective (l : Type u) [Field l] [Algebra k l] [FiniteDimensional k l]
    [IsGalois k l] (E : Type*) [Group E] [Finite E] (π : E →* (l ≃ₐ[k] l))
    (h : Function.Bijective π) : Solvable l E π := by
  refine ⟨l, inferInstance, inferInstance, inferInstance, inferInstance, ⊤,
    IntermediateField.topEquiv, (MulEquiv.ofBijective π h).symm, ?_⟩
  unfold IsSolution
  rw [IntermediateField.fixingSubgroup_top, Subgroup.map_bot]
  exact ((MonoidHom.ker_eq_bot_iff π).mpr h.injective).symm

/-- **The property that every finite embedding problem with abelian kernel over `k` is
solvable.**  (This holds for local fields only after an enlargement step; see
`Work.LocalFields.LocalEmbeddingProblemInput`.) -/
def HasEmbeddingPropertyWithAbelianKernel (k : Type*) [Field k] : Prop :=
  ∀ (l : Type*) [Field l] [Algebra k l] [FiniteDimensional k l] [IsGalois k l]
    (E : Type*) [Group E] [Finite E] (π : E →* (l ≃ₐ[k] l)),
    IsEmbeddingProblem l E π → IsMulCommutative ↥π.ker → Solvable l E π

/-- **The local embedding-problem input (named statement).**

The classical local theorem (Shafarevich; see also Neukirch–Schmidt–Wingberg, *Cohomology of
Number Fields*, Ch. 9, and Schmidt–Wingberg, arXiv:math/9809211) is:

> for a non-archimedean local field `k`, every finite embedding problem with abelian kernel
> becomes solvable after replacing the given Galois extension `l/k` by a finite *unramified*
> extension of `l`.

The formal content recorded here is the part that is expressible without a theory of base change
of embedding problems: there is a finite Galois extension `l'/k` containing `l` as a
`k`-subextension, a finite group `E'` with abelian kernel `π' : E' ↠ Gal(l'/k)`, and a surjection
`ψ : E' ↠ E` compatible with the restriction `Gal(l'/k) ↠ Gal(l/k)`, such that the problem
`(l'/k, E', π')` is solvable.

This is a *named statement*, not proved here: together with
`Work.LocalFields.HasEmbeddingPropertyWithAbelianKernel` it is the local arithmetic input of
Shafarevich's theorem.  Note that the un-enlarged form
`HasEmbeddingPropertyWithAbelianKernel k` is *false* in general (take `k = ℚ_p`, `l = k`, and
`E = (ℤ/ℓ)³`: the maximal pro-`ℓ` quotient of the absolute Galois group of `ℚ_p` is generated by
two elements, so `(ℤ/ℓ)³` is not realizable). -/
def LocalEmbeddingProblemInput (k : Type*) [Field k] : Prop :=
  ∀ (l : Type*) [Field l] [Algebra k l] [FiniteDimensional k l] [IsGalois k l]
    (E : Type*) [Group E] [Finite E] (π : E →* (l ≃ₐ[k] l)),
    IsEmbeddingProblem l E π → IsMulCommutative ↥π.ker →
      ∃ (l' : Type) (_ : Field l') (_ : Algebra k l') (_ : FiniteDimensional k l')
        (_ : IsGalois k l') (_ : Algebra l l') (_ : IsScalarTower k l l')
        (E' : Type) (_ : Group E') (_ : Finite E') (π' : E' →* (l' ≃ₐ[k] l')),
        IsEmbeddingProblem l' E' π' ∧ IsMulCommutative ↥π'.ker ∧ Solvable l' E' π'

end Work.LocalFields
