import Mathlib.Topology.Constructions
import Mathlib.GroupTheory.Abelianization.Finite
import Mathlib.NumberTheory.NumberField.Basic
import Submission.NK.LocalInputs.Defs
import Submission.NK.Reconstruct.exists_splitIsFrobElementAt_notMem_iUnion_closedSubgroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.Reconstruct

open scoped Pointwise

set_option linter.unusedSectionVars false

/-!
# Density of the images of the Frobenius elements at completely split primes away from `ℓ`

This file proves `NK.Reconstruct.dense_image_galToGamma_splitFrobenius_awayFromL`: the images under
`galToGamma ℓ` of the Frobenius elements at primes which are **completely split over `ℚ`** and lie
**away from `ℓ`** are dense in `Γ_L`.

The mathematical content is the same as that of
`NK.Reconstruct.dense_image_galToGamma_splitFrobenius` (Shimizu, arXiv:2009.10431, §4): the basic
open subsets of the projective limit `Γ_L` are finite cylinders, and a Frobenius element at a
completely split prime with prescribed restriction to any single finite normal level over `L` can be
produced.  Here the existence of such an element — with the additional requirement that the rational
prime below `𝔭` be different from `ℓ` — is not derived from Čebotarev but *assumed*, as the
hypothesis `hD` (it is the conclusion of the prime-avoidance argument at the split primes).

## Contents

* `dense_image_galToGamma_of_levelwise` — the general form: if a set `S ⊆ Gal(Ω/L)` meets every
  "level condition" `{σ | σ|_T = τ}` (`T` a finite normal level over `L`) then the image of `S`
  under `galToGamma ℓ` is dense in `Γ_L`;
* `dense_image_galToGamma_splitFrobenius_awayFromL` — the target statement, obtained from `hD`.
-/

/-! ## Density from levelwise density -/

section Levelwise

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]

/-- **Density of the image of a levelwise dense set.**  Let `Ω/ℚ` be Galois, `L` a finite normal
level of `Ω/ℚ` with `Ω` a separable closure of `L`, and let `S ⊆ Gal(Ω/L)` be a set of
automorphisms which is *levelwise as large as possible*: for every finite normal level `T` of `Ω`
over `L` and every `τ ∈ Gal(T/L)` there is `σ ∈ S` with `σ|_T = τ`.  Then the image of `S` under
`galToGamma ℓ` is dense in `Γ_L`.

Indeed the topology of `Γ_L` is induced from the product of the finite discrete level groups, so a
basic open set is a finite cylinder, i.e. a finite set `I` of levels together with values `u a` at
them; taking an upper bound `T` of `I`, an element `τ ∈ Gal(T/L)` whose ℓ-primary component is the
`T`-component of the given point (`exists_levelComponent_eq`) and then `σ ∈ S` with `σ|_T = τ`, the
coherence of the projective system (`Gamma.proj_compatible`) makes `galToGamma ℓ σ` agree with the
given point at every `a ∈ I`. -/
theorem dense_image_galToGamma_of_levelwise (L : FrobLevel ℚ Ω) [IsSepClosure ↥L.L Ω] (ℓ : ℕ)
    (S : Set Gal(Ω/↥L.L))
    (hS : ∀ (T : IntermediateField ↥L.L Ω) [FiniteDimensional ↥L.L T] [Normal ↥L.L T]
      [NumberField ↥T] (τ : Gal(↥T/↥L.L)), ∃ σ ∈ S,
        AlgEquiv.restrictNormalHom (F := ↥L.L) (K₁ := Ω) T σ = τ) :
    Dense ((galToGamma (K := ↥L.L) (K' := Ω) ℓ) '' S) := by
  classical
  rw [dense_iff_inter_open]
  rintro U hU ⟨f, hfU⟩
  rw [isOpen_induced_iff] at hU
  obtain ⟨Ũ, hŨ, rfl⟩ := hU
  obtain ⟨I, u, hu, hIU⟩ :=
    isOpen_pi_iff.mp hŨ (f : ∀ a : FrobLevel ↥L.L Ω, LevelEllPart a.L ℓ) hfU
  have key : ∃ σ ∈ S, ∀ a ∈ I,
      Gamma.proj a (galToGamma (K := ↥L.L) (K' := Ω) ℓ σ) ∈ u a := by
    by_cases hI : I.Nonempty
    · obtain ⟨L₀, hL₀⟩ := hI
      obtain ⟨T, hT, -⟩ := projSurj_finset_exists_upper_bound (K := ↥L.L) (K' := Ω) L₀ I
      obtain ⟨τ, hτ⟩ :=
        exists_levelComponent_eq (K := ↥L.L) (K' := Ω) ℓ T (Gamma.proj T f)
      obtain ⟨σ, hσS, hσT⟩ := hS T.L τ
      refine ⟨σ, hσS, fun a ha => ?_⟩
      have hle : a.L ≤ T.L := hT a ha
      have h1 : Gamma.proj a (galToGamma (K := ↥L.L) (K' := Ω) ℓ σ) = Gamma.proj a f := by
        rw [← Gamma.proj_compatible a T hle (galToGamma (K := ↥L.L) (K' := Ω) ℓ σ),
          galToGamma_proj, levelComponent, hσT, hτ, Gamma.proj_compatible a T hle f]
      rw [h1]
      exact (hu a ha).2
    · obtain ⟨σ, hσS, -⟩ := hS (frobLevelBot L).L 1
      refine ⟨σ, hσS, fun a ha => ?_⟩
      rw [Finset.not_nonempty_iff_eq_empty.mp hI] at ha
      exact absurd ha (Finset.notMem_empty a)
  obtain ⟨σ, hσS, hσ⟩ := key
  exact ⟨galToGamma (K := ↥L.L) (K' := Ω) ℓ σ, hIU (by rw [Set.mem_pi]; exact hσ),
    ⟨σ, hσS, rfl⟩⟩

end Levelwise

/-! ## The target statement -/

theorem dense_image_galToGamma_splitFrobenius_awayFromL {Ω : Type*} [Field Ω] [Algebra ℚ Ω]
    [IsGalois ℚ Ω] (L : NK.Reconstruct.FrobLevel ℚ Ω) [IsSepClosure ↥L.L Ω] (ℓ : ℕ)
    (hD : ∀ (T : IntermediateField ↥L.L Ω) [FiniteDimensional ↥L.L T] [Normal ↥L.L T]
      [NumberField ↥T] (τ : Gal(↥T/↥L.L)),
      ∃ (𝔭 : NK.Chebotarev.PrimeIdeal ↥L.L) (σ : Gal(Ω/↥L.L)),
        NK.Reconstruct.SplitsCompletelyOverRat 𝔭 ∧ NK.Reconstruct.IsFrobElementAt 𝔭 σ ∧
        NK.LocalInputs.primeBelowNat ↥L.L 𝔭 ≠ ℓ ∧
        AlgEquiv.restrictNormalHom (F := ↥L.L) (K₁ := Ω) T σ = τ) :
    Dense ((NK.Reconstruct.galToGamma (K := ↥L.L) (K' := Ω) ℓ) ''
      {σ : Gal(Ω/↥L.L) | ∃ 𝔭 : NK.Chebotarev.PrimeIdeal ↥L.L,
        NK.Reconstruct.SplitsCompletelyOverRat 𝔭 ∧ NK.Reconstruct.IsFrobElementAt 𝔭 σ ∧
        NK.LocalInputs.primeBelowNat ↥L.L 𝔭 ≠ ℓ}) := by
  refine dense_image_galToGamma_of_levelwise (Ω := Ω) L ℓ _ (fun T _ _ _ τ => ?_)
  obtain ⟨𝔭, σ, hsplit, hfrob, hnot, hres⟩ := hD T τ
  exact ⟨σ, ⟨𝔭, hsplit, hfrob, hnot⟩, hres⟩

end NK.Reconstruct
