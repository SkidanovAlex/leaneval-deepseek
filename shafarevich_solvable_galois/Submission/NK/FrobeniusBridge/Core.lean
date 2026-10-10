import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.NK.FrobeniusBridge.Tame
import Submission.NK.FrobeniusBridge.isTrivialOnResidueAtLevel_mul_inv_of_frobAt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Frobenius bridge: the core of the local–global dictionary

The named input `NK.FrobeniusBridge.PlaceLevelBridge` has two halves: the *residue-field
normalisation* ("a local Frobenius lift restricts to a Frobenius element at every finite level")
and the statement that a Frobenius element at a *single* level agrees there with a local Frobenius
lift.  This file shows that the second half is *not* an independent input: it follows from

* the residue-field normalisation at the level (`level_of_local`),
* the existence of **one** local Frobenius lift at the place, and
* the fact that the level inertia subgroups are contained in the image of the local inertia
  subgroup (`inertia_surjective`).

Indeed, if `g` is a Frobenius element at the level `L` and `u` is a local Frobenius lift, then
`g * u⁻¹` acts trivially on the residue field of `L` (it is the quotient of two Frobenius elements
at the same prime, `NK.FrobeniusBridge.isTrivialOnResidueAtLevel_mul_inv_of_frobAt`); the
inertia surjectivity lifts `g * u⁻¹` (or rather its restriction to `L`, which is all that matters)
to an element `h` of the local inertia subgroup, and then `h * u` is a local Frobenius lift (the
Frobenius lifts form a coset of the inertia subgroup,
`NK.LocalTame.IsFrobeniusFor.mul_mem_inertia`) agreeing with `g` on `L`.

This is exactly the classical route: the Frobenius coset of `D_A` is determined by its
residue-field action at a single level together with the identification of the level inertia
subgroup with the image of the local inertia subgroup.
-/

namespace NK.FrobeniusBridge

open scoped Classical Pointwise

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

universe u

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The local data at a place**: the residue characteristic `p`, the residue field cardinality
`q` of the completion `κ = K_𝔭`, and the local structure inputs
(`NK.LocalTame.TameData`, `NK.LocalTame.Zl2ResidueChar`) for `κ` and its separable closure. -/
structure PlaceLevelData (A : FinitePlaceOf K K') where
  /-- the residue characteristic -/
  p : ℕ
  /-- the residue field cardinality -/
  q : ℕ
  /-- the local structure inputs -/
  hT : NK.LocalTame.TameData p q (localField A) (localClosure A)
  /-- Shimizu's `ℤ_ℓ²` characterisation of the residue characteristic -/
  hZ : NK.LocalTame.Zl2ResidueChar p (localField A) (localClosure A)

/-- **The core of the local–global dictionary at a place**: the residue-field normalisation at the
level, the existence of a local Frobenius lift, and the fact that every element acting trivially on
the residue field of a level agrees on that level with an element of the local inertia subgroup.

These three statements are what the classical proof of the local Frobenius correspondence
(NSW (12.1.8); Shimizu Lemma 2.1) actually uses; the full dictionary
`NK.FrobeniusBridge.PlaceLevelBridge` is *derived* from them in
`NK.FrobeniusBridge.PlaceLevelBridge.of_core`. -/
structure PlaceLevelBridgeCore (A : FinitePlaceOf K K') (D : PlaceLevelData A) : Prop where
  /-- **the residue-field normalisation**: a local Frobenius lift restricts to a Frobenius element
  at every finite level -/
  level_of_local : ∀ (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L]
      [NumberField ↥L] (g : Gal(K'/K)), localFrobAt A g → frobAtLevel A L g
  /-- **the existence of a local Frobenius lift** at the place -/
  exists_frob : ∃ (u : Gal(K'/K))
      (hu : u ∈ Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') A.1),
    NK.LocalAnabelian.IsFrobeniusFor D.p D.q (localGaloisEquiv A ⟨u, hu⟩)
  /-- **the local inertia subgroup surjects onto the level inertia subgroups**: every element
  acting trivially on the residue field of a finite level agrees on that level with an element of
  the decomposition group whose local image is in the local inertia subgroup -/
  inertia_surjective : ∀ (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L]
      [NumberField ↥L] (g : Gal(K'/K)), IsTrivialOnResidueAtLevel A L g →
    ∃ (h : Gal(K'/K))
        (hh : h ∈ Submission.NeukirchUchida.decompositionGroup (K₁ := K) (K₁' := K') A.1),
      localGaloisEquiv A ⟨h, hh⟩ ∈
          NK.LocalAnabelian.inertiaSubgroup (κ := localField A) (K' := localClosure A) D.p ∧
        AlgEquiv.restrictNormalHom L h = AlgEquiv.restrictNormalHom L g

section Core

variable {A : FinitePlaceOf K K'} {D : PlaceLevelData A}

/-- **The "up" half of the local–global dictionary follows from the core**: a Frobenius element at
a single level agrees there with a local Frobenius lift. -/
theorem PlaceLevelBridgeCore.local_of_level (hC : PlaceLevelBridgeCore A D)
    (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L] [NumberField ↥L]
    (g : Gal(K'/K)) (hg : frobAtLevel A L g) :
    ∃ g₀ : Gal(K'/K), AlgEquiv.restrictNormalHom L g₀ = AlgEquiv.restrictNormalHom L g ∧
      localFrobAt A g₀ := by
  obtain ⟨u, hu, hF_u⟩ := hC.exists_frob
  -- `u` is a local Frobenius lift, hence a Frobenius element at the level `L`
  have hloc_u : localFrobAt A u := ⟨hu, D.p, D.q, D.hT, D.hZ, hF_u⟩
  have huFrob : frobAtLevel A L u := hC.level_of_local L u hloc_u
  -- the quotient of two Frobenius elements at the level acts trivially on the residue field
  have htriv : IsTrivialOnResidueAtLevel A L (g * u⁻¹) :=
    isTrivialOnResidueAtLevel_mul_inv_of_frobAt A L hg huFrob
  -- which lifts to an element of the local inertia subgroup
  obtain ⟨h, hh, hhI, hhrestrict⟩ := hC.inertia_surjective L (g * u⁻¹) htriv
  refine ⟨h * u, ?_, ⟨Subgroup.mul_mem _ hh hu, D.p, D.q, D.hT, D.hZ, ?_⟩⟩
  · -- the restriction of `h * u` to `L` is that of `g`
    rw [map_mul, hhrestrict, ← map_mul]
    rw [show (g * u⁻¹) * u = g from by group]
  · -- and `h * u` is a local Frobenius lift
    have hsub : (⟨h * u, Subgroup.mul_mem _ hh hu⟩ : Submission.NeukirchUchida.decompositionGroup
        (K₁ := K) (K₁' := K') A.1) = ⟨h, hh⟩ * ⟨u, hu⟩ :=
      Subtype.ext (by simp only [Subgroup.coe_mul])
    simpa only [hsub, map_mul] using
      NK.LocalTame.IsFrobeniusFor.mul_mem_inertia D.hT hF_u hhI

/-- **The local–global dictionary from its core.** -/
theorem PlaceLevelBridgeCore.toPlaceLevelBridge (hC : PlaceLevelBridgeCore A D) :
    PlaceLevelBridge A where
  level_of_local := hC.level_of_local
  local_of_level := fun L _ _ _ g hg => hC.local_of_level L g hg

/-- The local data at a place can be chosen when the local structure theory is available. -/
theorem PlaceLevelData.nonempty (h : TameDataAtPlaces K K') : Nonempty (PlaceLevelData A) := by
  obtain ⟨p, q, hT, hZ⟩ := h A
  exact ⟨⟨p, q, hT, hZ⟩⟩

end Core

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The Frobenius bridge from the core of the local–global dictionary**: the finite-level,
σ-free Frobenius correspondence — input (b) of the Neukirch–Uchida endgame — follows from the core
inputs of `NK.FrobeniusBridge.PlaceLevelBridgeCore` at the places of the two fields and the
place-level Frobenius correspondence for `ϕ`. -/
theorem frobeniusCorrespondencePlace_of_core (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (hϕ : IsHomeomorph ϕ) (a : NK.Reconstruct.LocalCorrespondence ϕ)
    (D₁ : ∀ A : FinitePlaceOf K₁ K₁', PlaceLevelData A)
    (D₂ : ∀ B : FinitePlaceOf K₂ K₂', PlaceLevelData B)
    (hC₁ : ∀ A : FinitePlaceOf K₁ K₁', PlaceLevelBridgeCore A (D₁ A))
    (hC₂ : ∀ B : FinitePlaceOf K₂ K₂', PlaceLevelBridgeCore B (D₂ B))
    (hB : LocalFrobCorrespondencePlace ϕ hϕ a) :
    NK.Reconstruct.FrobeniusCorrespondencePlace ϕ hϕ a :=
  frobeniusCorrespondencePlace_of_bridge ϕ hϕ a
    (fun A => (hC₁ A).toPlaceLevelBridge) (fun B => (hC₂ B).toPlaceLevelBridge) hB

end NK.FrobeniusBridge
