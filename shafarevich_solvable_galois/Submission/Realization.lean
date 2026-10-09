/-
Copyright (c) 2025. All rights reserved.

# Galois realizability of finite groups

This file sets up the basic API for the inverse Galois problem: a group `G` is
*realizable over a field `k`* if there is a finite Galois extension `K/k` with
`Gal(K/k) ≃* G`.

The main results here are:

* `RealizableOver.of_surjective`: a quotient of a realizable group is realizable
  (via the Galois correspondence: take the fixed field of the kernel).
* the reduction of Shafarevich's theorem to the *embedding step* for abelian
  kernels (see `Submission/Shafarevich.lean`).
-/
import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Submission

open scoped Classical

/-- `RealizableOver k G` means: there is a finite Galois extension `K/k` whose Galois
group is isomorphic to `G`. -/
def RealizableOver (k : Type*) [Field k] (G : Type*) [Group G] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Algebra k K) (_ : FiniteDimensional k K) (_ : IsGalois k K),
    Nonempty (G ≃* (K ≃ₐ[k] K))

/-- Realizability is invariant under group isomorphism. -/
theorem RealizableOver.of_mulEquiv {k : Type*} [Field k] {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (h : RealizableOver k G) : RealizableOver k H := by
  obtain ⟨K, hF, hA, hFD, hG, ⟨f⟩⟩ := h
  exact ⟨K, hF, hA, hFD, hG, ⟨e.symm.trans f⟩⟩

/-- A quotient of a realizable group is realizable. -/
theorem RealizableOver.of_surjective {k : Type*} [Field k] {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (h : RealizableOver k G) :
    RealizableOver k H := by
  obtain ⟨K, hKf, hKa, hKfd, hKg, ⟨e⟩⟩ := h
  letI : Field K := hKf
  letI : Algebra k K := hKa
  letI : FiniteDimensional k K := hKfd
  letI : IsGalois k K := hKg
  -- the kernel of `f`, transported to `Gal(K/k)`
  let N : Subgroup (K ≃ₐ[k] K) := f.ker.map e.toMonoidHom
  haveI hN : N.Normal := f.normal_ker.map e.toMonoidHom e.surjective
  let K' : IntermediateField k K := IntermediateField.fixedField N
  haveI : FiniteDimensional k ↥K' := IntermediateField.finiteDimensional_left K'
  haveI : IsGalois k ↥K' := IsGalois.of_fixedField_normal_subgroup N
  refine ⟨↥K', inferInstance, inferInstance, inferInstance, inferInstance, ⟨?iso⟩⟩
  have h1 : H ≃* G ⧸ f.ker := (QuotientGroup.quotientKerEquivOfSurjective f hf).symm
  have h2 : G ⧸ f.ker ≃* (K ≃ₐ[k] K) ⧸ N :=
    QuotientGroup.congr f.ker N e (by simp [N])
  have h3 : (K ≃ₐ[k] K) ⧸ N ≃* (↥K' ≃ₐ[k] ↥K') :=
    IsGalois.normalAutEquivQuotient N
  exact h1.trans (h2.trans h3)

end Submission
