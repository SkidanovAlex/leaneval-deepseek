import Mathlib
import Submission.NK.GlobalCFTdeep.AbstractH0
import Submission.NK.GlobalCFT.GlobalCFT
import Submission.NK.GlobalCFT.H0Computation

namespace NK.GlobalCFTdeep.SecondInequality

/-!
# The `H⁰`-computation in multiplicative form

The goal of this file is to identify the index `[C_K : N_{L/K} C_L]` of the norm class subgroup
with the cardinality of the degree-zero Tate cohomology group `Ĥ⁰(Gal(L/K), C_L)`, in the
*multiplicative* model `NK.GlobalCFTdeep.H0 G M = M^G ⧸ N_G M` of
`Submission.NK.GlobalCFTdeep.AbstractH0`.

The bridge is provided by the following general observation,
`natCard_H0_eq_natCard_invariants_quotient`: for a finite group `G` acting on a commutative group
`M` (multiplicatively), the map `x ↦ Additive.ofMul x` identifies the fixed points
`M^G = NK.GlobalCFTdeep.fixedSubgroup G M` with the invariants of the associated `ℤ`-linear
representation `ρ = Representation.ofMulDistribMulAction G M`, and the norm `∏_{g} g • x` with
`ρ.norm`.  Consequently the multiplicative quotient `M^G ⧸ N_G M` and the additive quotient
`ρ.invariants ⧸ ρ.norm(ρ.V)` have the same cardinality (`Quotient.congr`).

Combining this with

* the workspace's `NK.GlobalCFT.globalCFT_H0Computation` and
  `NK.GlobalCFT.H0Computation.index_eq_natCard`, which identify the norm index with
  `Nat.card (tateCohomology (IdeleClassGroup.rep K L) 0)`, and
* the commons' `Commons.RepresentationTheory.TateCohomology.tateCohomology_zero_iso`, which
  identifies `tateCohomology (Rep.of ρ) 0` with the additive quotient of the invariants by the
  range of the norm,

yields the announced statement.
-/

open scoped BigOperators
open CategoryTheory

/-- **The multiplicative `Ĥ⁰` versus the additive `Ĥ⁰`.**  For a finite group `G` acting on a
commutative group `M`, the cardinality of the multiplicative model
`NK.GlobalCFTdeep.H0 G M = M^G ⧸ N_G M` equals the cardinality of the quotient of the
invariants of the associated `ℤ`-linear representation `Representation.ofMulDistribMulAction G M`
by the range of its norm. -/
theorem natCard_H0_eq_natCard_invariants_quotient {G M : Type} [Group G] [Fintype G]
    [CommGroup M] [MulDistribMulAction G M] :
    Nat.card (NK.GlobalCFTdeep.H0 G M) =
      Nat.card (↥(Representation.ofMulDistribMulAction G M).invariants ⧸
        Submodule.comap (Representation.ofMulDistribMulAction G M).invariants.subtype
          (LinearMap.range (Representation.ofMulDistribMulAction G M).norm)) := by
  classical
  -- The norm of the representation is the product of the conjugates (the group-theoretic norm).
  have key : ∀ v : Additive M,
      (∃ w : Additive M, (Representation.ofMulDistribMulAction G M).norm w = v) ↔
        ∃ u : M, NK.GlobalCFTdeep.normHom G M u = Additive.toMul v := by
    intro v
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨Additive.toMul w, by
        rw [NK.GlobalCFTdeep.normHom_apply,
          ← Representation.norm_ofMulDistribMulAction_eq w, hw]⟩
    · rintro ⟨u, hu⟩
      refine ⟨Additive.ofMul u, ?_⟩
      apply Additive.toMul.injective
      rw [Representation.norm_ofMulDistribMulAction_eq, toMul_ofMul,
        ← NK.GlobalCFTdeep.normHom_apply, hu]
  -- The fixed points of `M` are the invariants of the representation.
  let e : ↥(NK.GlobalCFTdeep.fixedSubgroup G M) ≃
      ↥((Representation.ofMulDistribMulAction G M).invariants) :=
    { toFun := fun x => ⟨Additive.ofMul (x : M), by
        rw [Representation.mem_invariants]
        intro g
        simp only [Representation.ofMulDistribMulAction_apply_apply, toMul_ofMul]
        exact congrArg Additive.ofMul (x.2 g)⟩
      invFun := fun y => ⟨Additive.toMul (y : Additive M), by
        intro g
        have hy : Additive.ofMul (g • Additive.toMul (y : Additive M)) = (y : Additive M) := by
          have h := (Representation.mem_invariants (Representation.ofMulDistribMulAction G M)
            (y : Additive M)).mp y.2 g
          rwa [Representation.ofMulDistribMulAction_apply_apply] at h
        exact Additive.ofMul.injective (hy.trans (ofMul_toMul (y : Additive M)).symm)⟩
      left_inv := fun x => Subtype.ext (toMul_ofMul (x : M))
      right_inv := fun y => Subtype.ext (ofMul_toMul (y : Additive M)) }
  -- `e` carries the norm subgroup onto the range of the norm of the representation.
  have heq : ∀ a b : ↥(NK.GlobalCFTdeep.fixedSubgroup G M),
      (QuotientGroup.leftRel ((NK.GlobalCFTdeep.normHom G M).range.subgroupOf
          (NK.GlobalCFTdeep.fixedSubgroup G M))) a b ↔
      (QuotientAddGroup.leftRel (Submodule.comap
          (Representation.ofMulDistribMulAction G M).invariants.subtype
          (LinearMap.range (Representation.ofMulDistribMulAction G M).norm)).toAddSubgroup)
        (e a) (e b) := by
    intro a b
    rw [QuotientGroup.leftRel_apply, QuotientAddGroup.leftRel_apply]
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_range]
    rw [Submodule.mem_toAddSubgroup, Submodule.mem_comap, LinearMap.mem_range,
      Submodule.subtype_apply]
    have hval : ((- e a + e b : ↥((Representation.ofMulDistribMulAction G M).invariants)) :
        Additive M) = Additive.ofMul ((a : M)⁻¹ * (b : M)) := by
      change - Additive.ofMul (a : M) + Additive.ofMul (b : M) =
        Additive.ofMul ((a : M)⁻¹ * (b : M))
      rw [← ofMul_inv, ← ofMul_mul]
    rw [hval, key, toMul_ofMul]
    constructor <;> rintro ⟨u, hu⟩ <;> exact ⟨u, by simpa using hu⟩
  exact Nat.card_congr (Quotient.congr e heq)

/-- The `H⁰`-computation of global class field theory in multiplicative form: for a finite Galois extension `L / K` of number fields, the index of the norm class subgroup equals the cardinality of `H0 (Gal(L/K)) C_L = (C_L)^G ⧸ N_G C_L`.

Note the fields live in `Type` (universe `0`): the workspace's `H0Computation`/`globalCFT_H0Computation` are stated for `{K L : Type}`, so the proof should either use them (via the additive model `tateCohomology (IdeleClassGroup.rep K L) 0` and `NK.GlobalCFT.H0Computation.index_eq_natCard`, bridging the additive quotient to `NK.GlobalCFTdeep.H0` using `Commons.RepresentationTheory.TateCohomology.tateCohomology_zero_iso`, `Representation.mem_invariants` and `Representation.norm_ofMulDistribMulAction_eq`) or run the inclusion argument directly: take `ψ : C[K] →* C[L]` from `NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_exists`, which is injective (`..._inclusion_injective`), has range exactly the `Gal(L/K)`-fixed points (`..._invariants_ideleClassGroup`) and satisfies `ψ (IdeleClassGroup.normClassHom K L q) = ∏ σ : L ≃ₐ[K] L, σ • q` (`NK.GlobalCFT.globalCFT_normClassHom_eq_prod_smul`, obtained from the `φ`/`hφ` data produced by `NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_exists`, exactly as in `NK.GlobalCFT.globalCFT_H0Computation`). These produce a `MulEquiv` `C[K] ≃* ↥(NK.GlobalCFTdeep.fixedSubgroup (L ≃ₐ[K] L) (C[L]))` carrying `Idele.normClassSubgroup K L = (IdeleClassGroup.normClassHom K L).range` onto `(NK.GlobalCFTdeep.normHom (L ≃ₐ[K] L) (C[L])).range`, hence an isomorphism of quotients; conclude with `Subgroup.index_eq_card` (`NK.GlobalCFT.Idele.normClassSubgroup_eq_range` rewrites the left side). -/
theorem normClassSubgroup_index_eq_natCard_H0 {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    (NK.GlobalCFT.Idele.normClassSubgroup K L).index =
      Nat.card (NK.GlobalCFTdeep.H0 (L ≃ₐ[K] L) (NK.GlobalCFT.IdeleClassGroup L)) := by
  rw [NK.GlobalCFT.H0Computation.index_eq_natCard
      (NK.GlobalCFT.globalCFT_H0Computation (K := K) (L := L))]
  obtain ⟨e⟩ := Commons.RepresentationTheory.TateCohomology.tateCohomology_zero_iso
    ((NK.GlobalCFT.IdeleClassGroup.rep K L).ρ)
  rw [show Rep.of ((NK.GlobalCFT.IdeleClassGroup.rep K L).ρ) =
      NK.GlobalCFT.IdeleClassGroup.rep K L from rfl] at e
  exact (Nat.card_congr e.toEquiv).trans
    (natCard_H0_eq_natCard_invariants_quotient (G := L ≃ₐ[K] L)
      (M := NK.GlobalCFT.IdeleClassGroup L)).symm

end NK.GlobalCFTdeep.SecondInequality
