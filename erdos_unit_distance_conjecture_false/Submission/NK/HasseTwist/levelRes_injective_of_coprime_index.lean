/-
# Injectivity of the level-wise restriction for an index prime to `p`

For an inclusion `V ≤ U` of subgroups of `Gal(K'/K)` and a finite Galois level `L`, the restriction
of the level cohomology

`NK.HasseTwist.levelRes p h L : H²(U/(U ⊓ Gal(K'/L)), μ_p(L)) ⟶ H²(V/(V ⊓ Gal(K'/L)), μ_p(L))`

is injective whenever the index of the image of the level inclusion
`NK.BrauerHasse.levelInclHom h L : V/(V ⊓ Gal(K'/L)) →* U/(U ⊓ Gal(K'/L))` is prime to `p`.

This is the transfer (corestriction) argument `cor ∘ res = [U : V]` with cyclotomic (`μ_p`)
coefficients: the group `H²(U, μ_p(L))` is a `p`-torsion group (the coefficient module `μ_p(L)` is
`p`-torsion), and multiplication by an integer coprime to `p` is injective on a `p`-torsion group,
so restriction has trivial kernel.

The group-theoretic input is `NK.GCTransfer.map_injective_of_coprime_index`, proved from the
cochain-level transfer identities `NK.GCTransfer.cor1_d12` and `NK.GCTransfer.cor2_cocycles`.
-/
import Mathlib
import Submission.NK.HasseTwist.Restrict
import Submission.NK.HassePrinciple.finite_levelGroup
import Submission.NK.HassePrinciple.levelInclHom_injective
import Submission.NK.GCTransfer.Basic

open CategoryTheory Representation Rep
open scoped Pointwise

set_option autoImplicit false
set_option maxHeartbeats 1600000

universe u

namespace NK.HasseTwist

open NK.BrauerTwist

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-! ## The coefficient morphism of the restriction is an isomorphism -/

/-- The inverse of the coefficient morphism `NK.HasseTwist.levelResCoeff p h L`: the two
representations have the same underlying module `μ_p(L)` and the same action, so the inverse is
again given by the identity of `μ_p(L)`. -/
noncomputable def levelResCoeffInv (p : ℕ) {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (L : FiniteGaloisIntermediateField K K') :
    NK.BrauerTwist.levelRep p V L ⟶
      Rep.res (NK.BrauerHasse.levelInclHom h L) (NK.BrauerTwist.levelRep p U L) :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap
    (ρ := (NK.BrauerTwist.levelRep p V L).ρ)
    (σ := (Rep.res (NK.BrauerHasse.levelInclHom h L)
      (NK.BrauerTwist.levelRep p U L)).ρ)
    (f := muInclLinearMap (le_refl L))
    (fun q x => by
      induction q using QuotientGroup.induction_on with
      | H v =>
        simp only [NK.BrauerHasse.levelInclHom, NK.BrauerTwist.levelGroupHom,
          QuotientGroup.map_mk, MonoidHom.id_apply, Subgroup.coe_inclusion,
          Rep.coe_res_obj_ρ', NK.BrauerTwist.levelRep_ρ_apply,
          NK.BrauerTwist.muInclLinearMap_apply]
        rfl))

@[simp]
lemma levelResCoeffInv_apply (p : ℕ) {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (L : FiniteGaloisIntermediateField K K')
    (x : (NK.BrauerTwist.levelRep p V L)) :
    (levelResCoeffInv p h L).hom.toLinearMap x = muInclLinearMap (le_refl L) x := rfl

/-- The coefficient morphism of the level restriction is an isomorphism. -/
theorem levelResCoeff_isIso (p : ℕ) {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (L : FiniteGaloisIntermediateField K K') :
    IsIso (NK.HasseTwist.levelResCoeff p h L) := by
  refine ⟨levelResCoeffInv p h L, ?_, ?_⟩
  · apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    simp only [Rep.hom_comp, Rep.hom_id, Representation.IntertwiningMap.comp_toLinearMap,
      LinearMap.comp_apply, levelResCoeff_apply, levelResCoeffInv_apply]
    exact Subtype.ext rfl
  · apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    simp only [Rep.hom_comp, Rep.hom_id, Representation.IntertwiningMap.comp_toLinearMap,
      LinearMap.comp_apply, levelResCoeff_apply, levelResCoeffInv_apply]
    exact Subtype.ext rfl

/-! ## The coefficient module is `p`-torsion -/

/-- Every element of the level module `μ_p(L)` is annihilated by `p`. -/
theorem levelRep_p_nsmul_eq_zero (p : ℕ) (U : Subgroup Gal(K'/K))
    (L : FiniteGaloisIntermediateField K K') :
    ∀ m : Additive ↥(NK.BrauerTwist.muLevel p L), p • m = 0 := by
  intro m
  rw [← toMul_eq_one, toMul_nsmul]
  have h : (((Additive.toMul m : ↥(NK.BrauerTwist.muLevel p L)) : (K')ˣ) ^ p = 1) :=
    (mem_rootsOfUnity (M := K') p _).mp
      (((Additive.toMul m : ↥(NK.BrauerTwist.muLevel p L)) : rootsOfUnity p K').2)
  have h2 : ((Additive.toMul m : ↥(NK.BrauerTwist.muLevel p L)) : rootsOfUnity p K') ^ p = 1 :=
    Subtype.ext h
  exact Subtype.ext h2

/-! ## Injectivity of the level restriction -/

theorem levelRes_injective_of_coprime_index (p : ℕ) {K K' : Type u} [Field K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] {U V : Subgroup Gal(K'/K)} (h : V ≤ U)
    (L : FiniteGaloisIntermediateField K K')
    (hcop : Nat.Coprime (Subgroup.index (MonoidHom.range (NK.BrauerHasse.levelInclHom h L))) p) :
    Function.Injective (fun a : NK.BrauerTwist.LevelH2 p U L => (NK.HasseTwist.levelRes p h L) a) := by
  haveI : Fintype (NK.BrauerHasse.LevelGroup U L) := Fintype.ofFinite _
  haveI : IsIso (NK.HasseTwist.levelResCoeff p h L) :=
    levelResCoeff_isIso (K := K) (K' := K') p h L
  have hmain := NK.GCTransfer.map_injective_of_coprime_index
    (k := NK.BrauerTwist.CoeffInt) (Γ := NK.BrauerHasse.LevelGroup U L)
    (Δ := NK.BrauerHasse.LevelGroup V L) p (NK.BrauerHasse.levelInclHom h L)
    (NK.HassePrinciple.levelInclHom_injective h L)
    (NK.BrauerTwist.levelRep p U L) (NK.BrauerTwist.levelRep p V L)
    (NK.HasseTwist.levelResCoeff p h L) hcop (levelRep_p_nsmul_eq_zero p U L)
  simpa only [NK.HasseTwist.levelRes, NK.BrauerTwist.LevelH2] using hmain

end NK.HasseTwist
