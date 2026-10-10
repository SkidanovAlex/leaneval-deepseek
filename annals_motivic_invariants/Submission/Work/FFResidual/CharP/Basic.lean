/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: Work.FFResidual
-/
import Submission.Work.FFResidual.Ord
import Submission.Work.TorsorExistence.ArtinSchreier.Irreducible
import Submission.Work.TorsorExistence.ArtinSchreier.SplittingField
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The Artin–Schreier extension of a function field at a place (characteristic five)

Let `P : FunctionFieldPlace 𝔽 𝕜` be a place of a function field of characteristic `5` over its
field of constants, with uniformizer `π`.  In characteristic `5` there is no primitive fifth root
of unity, and the cyclic quintic extension of the classes (b), (c), (d) is the **Artin–Schreier**
extension of the place at *infinity*: with `t := π⁻¹` (the element with a simple pole at the place),
the extension is `AsTop P = 𝕜(s)` with `s ^ 5 - s = t` (irreducible since `t ∉ ℘(𝕜)`, see
`FunctionFieldPlace.not_exists_artinSchreier_inv_uniformizer`), with generator the Artin–Schreier
automorphism `σ : s ↦ s + 1`.

The Eisenstein element of the local model is `w := s⁻¹`, satisfying `w ^ 5 + π w ^ 4 - π = 0`
(`asRecip_pow`); the model itself is `R[w]/(X ^ 5 + π X ^ 4 - π)`
(`Submission/Work/FFResidual/CharP/Order.lean`).

## Main definitions and results

* `FunctionFieldPlace.asElement`, `asPoly`, `AsTop`, `asRoot`, `asRoot_equation`.
* `FunctionFieldPlace.asRecip`, `asRecip_pow` — the Eisenstein element `w = s⁻¹`.
* `FunctionFieldPlace.asEquiv` — the automorphism `s ↦ s + 1`, and `asCyclicExtension` — `AsTop P`
  as a `CyclicExtension 𝕜 5` with that generator.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.FFResidual

noncomputable section

open Polynomial

namespace FunctionFieldPlace

variable {𝔽 : Type} [Field 𝔽] {𝕜 : Type} [Field 𝕜] [Algebra 𝔽 𝕜]

/-! ## 1. The Artin–Schreier extension `𝕜(s)`, `s ^ 5 - s = π⁻¹` -/

/-- The Artin–Schreier element of the place: `1 / π`, an element with a simple pole there. -/
abbrev asElement (P : FunctionFieldPlace 𝔽 𝕜) : 𝕜 := (algebraMap P.R 𝕜 P.π)⁻¹

/-- The Artin–Schreier polynomial `X ^ 5 - X - 1 / π`. -/
abbrev asPoly (P : FunctionFieldPlace 𝔽 𝕜) : 𝕜[X] := X ^ 5 - X - C P.asElement

theorem asElement_ne_zero (P : FunctionFieldPlace 𝔽 𝕜) : P.asElement ≠ 0 :=
  inv_ne_zero fun h => P.pi_ne_zero (IsFractionRing.injective P.R 𝕜 (by simpa using h))

theorem asPoly_irreducible (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] :
    Irreducible P.asPoly :=
  Work.TorsorExistence.ArtinSchreier.irreducible_X_pow_five_sub_X_sub_C P.asElement
    P.not_exists_artinSchreier_inv_uniformizer

instance asPoly_fact (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] : Fact (Irreducible P.asPoly) :=
  ⟨P.asPoly_irreducible⟩

/-- **The Artin–Schreier top field** `𝕜(s)`, `s ^ 5 - s = 1 / π`. -/
abbrev AsTop (P : FunctionFieldPlace 𝔽 𝕜) : Type := AdjoinRoot P.asPoly

/-- The Artin–Schreier root `s`. -/
abbrev asRoot (P : FunctionFieldPlace 𝔽 𝕜) : P.AsTop := AdjoinRoot.root P.asPoly

theorem asRoot_equation (P : FunctionFieldPlace 𝔽 𝕜) :
    P.asRoot ^ 5 - P.asRoot = algebraMap 𝕜 P.AsTop P.asElement := by
  have h := AdjoinRoot.eval₂_root P.asPoly
  simp only [asPoly, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h
  rw [sub_eq_zero] at h
  rw [h, AdjoinRoot.algebraMap_eq]

theorem asPoly_natDegree (P : FunctionFieldPlace 𝔽 𝕜) : P.asPoly.natDegree = 5 := by
  have h : P.asPoly = (X ^ 5 - C P.asElement) - X := by rw [asPoly]; ring
  rw [h, natDegree_sub_eq_left_of_natDegree_lt]
  · exact natDegree_X_pow_sub_C
  · rw [natDegree_X, natDegree_X_pow_sub_C]
    norm_num

theorem asPoly_ne_zero (P : FunctionFieldPlace 𝔽 𝕜) : P.asPoly ≠ 0 := by
  intro h
  have := P.asPoly_natDegree
  rw [h] at this
  simp at this

theorem asRoot_ne_zero (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] : P.asRoot ≠ 0 := by
  intro h
  have h5 := P.asRoot_equation
  rw [h, zero_pow (by norm_num : (5 : ℕ) ≠ 0), zero_sub] at h5
  have h6 : algebraMap 𝕜 P.AsTop P.asElement = 0 := by
    rw [← h5, neg_eq_zero]
  exact P.asElement_ne_zero ((algebraMap 𝕜 P.AsTop).injective (by simpa using h6))

/-- The `𝔽`-algebra structure on the Artin–Schreier top field, through the constants. -/
noncomputable instance (P : FunctionFieldPlace 𝔽 𝕜) : Algebra 𝔽 P.AsTop :=
  ((algebraMap 𝕜 P.AsTop).comp (algebraMap 𝔽 𝕜)).toAlgebra

/-- The `R`-algebra structure on the Artin–Schreier top field along the place. -/
noncomputable instance (P : FunctionFieldPlace 𝔽 𝕜) : Algebra P.R P.AsTop :=
  ((algebraMap 𝕜 P.AsTop).comp (algebraMap P.R 𝕜)).toAlgebra

theorem algebraMap_R_AsTop (P : FunctionFieldPlace 𝔽 𝕜) (r : P.R) :
    algebraMap P.R P.AsTop r = algebraMap 𝕜 P.AsTop (algebraMap P.R 𝕜 r) := rfl

/-- **The Artin–Schreier element `w = s⁻¹`**: the uniformizer of the place of `AsTop P` above the
place `P`. -/
abbrev asRecip (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] : P.AsTop := P.asRoot⁻¹

/-- **The Eisenstein equation of `w = s⁻¹`**: `w ^ 5 + π w ^ 4 - π = 0`. -/
theorem asRecip_pow (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] :
    P.asRecip ^ 5 + algebraMap P.R P.AsTop P.π * P.asRecip ^ 4
      - algebraMap P.R P.AsTop P.π = 0 := by
  have hs : P.asRoot ≠ 0 := P.asRoot_ne_zero
  have hR : algebraMap P.R 𝕜 P.π ≠ 0 := fun h =>
    P.pi_ne_zero (IsFractionRing.injective P.R 𝕜 (by simpa using h))
  have hu_ne : algebraMap P.R P.AsTop P.π ≠ 0 := by
    rw [algebraMap_R_AsTop]
    exact fun h => hR ((algebraMap 𝕜 P.AsTop).injective (by simpa using h))
  have h' : P.asRoot ^ 5 - P.asRoot = (algebraMap P.R P.AsTop P.π)⁻¹ := by
    rw [P.asRoot_equation, asElement, map_inv₀]
    rfl
  have hu : algebraMap P.R P.AsTop P.π = (P.asRoot ^ 5 - P.asRoot)⁻¹ := by
    rw [h', inv_inv]
  have h3 : algebraMap P.R P.AsTop P.π * (P.asRoot ^ 5 - P.asRoot) = 1 := by
    rw [h', mul_inv_cancel₀ hu_ne]
  have hden : P.asRoot ^ 5 - P.asRoot ≠ 0 := fun h0 => hu_ne (by rw [hu, h0, inv_zero])
  have key : (P.asRoot⁻¹) ^ 5 + algebraMap P.R P.AsTop P.π * (P.asRoot⁻¹) ^ 4
      - algebraMap P.R P.AsTop P.π = 0 := by
    field_simp [hs]
    linear_combination (norm := first | refl_ring1 | ring1) (-1) * h3
  rwa [asRecip]


/-! ## 2. The Artin–Schreier automorphism `s ↦ s + 1` -/

theorem charP_asTop (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] : CharP P.AsTop 5 :=
  charP_of_injective_algebraMap (algebraMap 𝕜 P.AsTop).injective 5

theorem asPoly_eval_root_add_one (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] :
    eval₂ (algebraMap 𝕜 P.AsTop) (P.asRoot + 1) P.asPoly = 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI hchar : CharP P.AsTop 5 :=
    charP_of_injective_algebraMap (algebraMap 𝕜 P.AsTop).injective 5
  simp only [asPoly, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  rw [add_pow_char, one_pow, ← P.asRoot_equation]
  first | refl_ring1 | ring

/-- **The Artin–Schreier endomorphism** `s ↦ s + 1` of the top field. -/
noncomputable def asHom (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] :
    P.AsTop →ₐ[𝕜] P.AsTop :=
  AdjoinRoot.liftAlgHom P.asPoly (Algebra.ofId 𝕜 P.AsTop) (P.asRoot + 1)
    P.asPoly_eval_root_add_one

theorem asHom_root (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] :
    P.asHom P.asRoot = P.asRoot + 1 :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

theorem asHom_algebraMap (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] (c : 𝕜) :
    P.asHom (algebraMap 𝕜 P.AsTop c) = algebraMap 𝕜 P.AsTop c := by
  rw [AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.liftAlgHom_of _ _ _ _ c

theorem asHom_injective (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] :
    Function.Injective P.asHom := by
  intro x y hxy
  have h : P.asHom (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  by_contra hne
  have hx : x - y ≠ 0 := sub_ne_zero.mpr hne
  have hinv := congrArg P.asHom (inv_mul_cancel₀ hx)
  rw [map_mul, map_one] at hinv
  rw [h, mul_zero] at hinv
  exact one_ne_zero hinv.symm

theorem isSplittingField_asPoly (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] :
    IsSplittingField 𝕜 P.AsTop P.asPoly :=
  Work.TorsorExistence.ArtinSchreier.isSplittingField_adjoin_of_pow_five_sub_self P.asElement
    P.asRoot_equation AdjoinRoot.adjoinRoot_eq_top

theorem finiteDimensional_asTop (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] :
    FiniteDimensional 𝕜 P.AsTop := by
  haveI := P.isSplittingField_asPoly
  exact IsSplittingField.finiteDimensional (L := P.AsTop) P.asPoly

theorem asHom_surjective (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] :
    Function.Surjective P.asHom := by
  haveI := P.finiteDimensional_asTop
  exact (LinearMap.injective_iff_surjective (f := P.asHom.toLinearMap)).mp
    (P.asHom_injective)

/-- **The Artin–Schreier automorphism** `s ↦ s + 1` of the top field. -/
noncomputable def asEquiv (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] :
    P.AsTop ≃ₐ[𝕜] P.AsTop :=
  AlgEquiv.ofBijective _ ⟨P.asHom_injective, P.asHom_surjective⟩

theorem asEquiv_root (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] :
    P.asEquiv P.asRoot = P.asRoot + 1 := P.asHom_root

theorem asEquiv_pow_apply_root (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] (n : ℕ) :
    (P.asEquiv ^ n) P.asRoot = P.asRoot + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, map_add, asEquiv_root, map_natCast]
    push_cast
    ring_nf

theorem asEquiv_pow_five (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] : P.asEquiv ^ 5 = 1 := by
  haveI := P.charP_asTop
  refine AlgEquiv.coe_toAlgHom_injective ?_
  refine AdjoinRoot.algHom_ext ?_
  rw [AlgEquiv.coe_toAlgHom, P.asEquiv_pow_apply_root 5]
  have h5 : (5 : P.AsTop) = 0 := CharP.cast_eq_zero P.AsTop 5
  change P.asRoot + (5 : P.AsTop) = (1 : P.AsTop →ₐ[𝕜] P.AsTop) P.asRoot
  rw [h5, add_zero]
  rfl

theorem asEquiv_ne_one (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] : P.asEquiv ≠ 1 := by
  intro h
  have h1 := congrArg (fun f : P.AsTop ≃ₐ[𝕜] P.AsTop => f P.asRoot) h
  rw [AlgEquiv.one_apply, asEquiv_root] at h1
  exact one_ne_zero (add_left_cancel (show P.asRoot + 1 = P.asRoot + 0 by simpa using h1))

theorem orderOf_asEquiv (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] :
    orderOf P.asEquiv = 5 :=
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  orderOf_eq_prime (P.asEquiv_pow_five) (P.asEquiv_ne_one)

theorem isGalois_asTop (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] : IsGalois 𝕜 P.AsTop := by
  haveI hsplit := P.isSplittingField_asPoly
  have hsep : P.asPoly.Separable := by
    rw [separable_def]
    refine ⟨0, -1, ?_⟩
    have hd : derivative P.asPoly = -1 := by
      rw [asPoly, derivative_sub, derivative_sub, derivative_X, derivative_C, derivative_X_pow,
        C_eq_algebraMap, map_natCast (algebraMap 𝕜 𝕜[X]) 5, CharP.cast_eq_zero 𝕜[X] 5, zero_mul]
      first | refl_ring1 | ring
    rw [hd]
    first | refl_ring1 | ring
  exact IsGalois.of_separable_splitting_field hsep

theorem finrank_asTop (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] : Module.finrank 𝕜 P.AsTop = 5 := by
  change Module.finrank 𝕜 (AdjoinRoot P.asPoly) = 5
  rw [PowerBasis.finrank (AdjoinRoot.powerBasis (f := P.asPoly) P.asPoly_ne_zero),
    AdjoinRoot.powerBasis_dim (f := P.asPoly) P.asPoly_ne_zero, P.asPoly_natDegree]

/-- **The Artin–Schreier top field as a cyclic quintic extension of `𝕜`**, with generator the
automorphism `s ↦ s + 1`. -/
noncomputable def asCyclicExtension (P : FunctionFieldPlace 𝔽 𝕜) [CharP 𝕜 5] :
    Work.TorsorExistence.CyclicExtension 𝕜 5 := by
  haveI := P.finiteDimensional_asTop
  haveI hgal := P.isGalois_asTop
  haveI : Fintype (P.AsTop ≃ₐ[𝕜] P.AsTop) := AlgEquiv.fintype 𝕜 P.AsTop
  have htop : Subgroup.zpowers P.asEquiv = ⊤ := by
    refine Subgroup.eq_top_of_card_eq _ ?_
    rw [Nat.card_zpowers, P.orderOf_asEquiv,
      IsGalois.card_aut_eq_finrank 𝕜 P.AsTop, P.finrank_asTop]
  refine { L := P.AsTop
           finrank_eq := P.finrank_asTop
           gen := P.asEquiv
           orderOf_gen := P.orderOf_asEquiv
           gen_generator := ?_ }
  intro g
  have hmem : g ∈ Submonoid.powers P.asEquiv :=
    (isOfFinOrder_of_finite P.asEquiv).mem_powers_iff_mem_zpowers.mpr (htop ▸ Subgroup.mem_top g)
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff g _).mp hmem
  exact ⟨k, hk.symm⟩

end FunctionFieldPlace

end

end Work.FFResidual
