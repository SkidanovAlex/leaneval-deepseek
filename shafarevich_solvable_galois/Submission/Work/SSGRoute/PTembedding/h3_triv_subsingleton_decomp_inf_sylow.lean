import Mathlib
import Submission.Work.AbsoluteKummer.All
import Submission.Work.SSGRoute.sha2_defs
import Submission.Work.SSGRoute.kummerBase_euler_h3_absKummer
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.EulerSymm.h3triv_fixingSubgroup
import Submission.Work.SSGRoute.pgroup_fixes_primitiveRoot
import Submission.Work.SSGRoute.HS.Setup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `H³(D_A ∩ P⁻¹, 𝔽_p) = 0` for a `p`-Sylow preimage inside the decomposition group

For a number field `k`, an algebraic closure `Ω`, a finite place `A` of `Ω` and a prime `p`, let
`K/k` be a finite Galois subextension of `Ω` containing a primitive `p`-th root of unity `ζ`, and
let `P ≤ Gal(K/k)` be a `p`-Sylow subgroup.  Writing `D_A = decomp k A ≤ G_k`, the goal is

`Subsingleton (H³(D_A ⊓ res⁻¹(P), 𝔽_p))`.

## The mathematics

Let `L = K^P` be the fixed field of `P` inside `K`, viewed as an intermediate field of `Ω/k`.
Since `K/k` is finite Galois, `Gal(K/L) = P`, so
`res⁻¹(P) = Gal(Ω/L) = L.fixingSubgroup`.  Since `P` is a `p`-group and the action of
`Gal(K/k)` on the `p`-th roots of unity in `K` factors through the cyclotomic character into
`(ℤ/p)^×` (of order `p - 1`, coprime to `p`), every Sylow `P` fixes `ζ`
(`Work.SSGRoute.pgroup_fixes_primitiveRoot`); hence `ζ ∈ L`.

Therefore `D_A ⊓ res⁻¹(P) = D_A ⊓ Gal(Ω/L) = Gal(Ω/L) ∩ D_A` is the decomposition group of `A`
over the base field `L`, and the local vanishing `H³(Gal(Ω/L) ∩ D_A, 𝔽_p) = 0` of
`Work.SSGRoute.EulerSymm.h3triv_subsingleton_fixingSubgroup` — which is
`h3_triv_subsingleton_decomp` at the base field `L`, using `ζ ∈ L` to identify `μ_p ≅ 𝔽_p` —
applies.

The only formal gap between the two statements is that `D_A ⊓ L.fixingSubgroup` is a subgroup of
`G_k` whereas the vanishing statement is phrased for `(L.fixingSubgroup).subgroupOf D_A`, a
subgroup of `↥D_A`; the two are canonically isomorphic as topological groups (both compact
subsets of `G_k`), which is the auxiliary lemma `subsingleton_H3_inf_of_subgroupOf` below.
-/

set_option linter.style.haveILetI false
open scoped Pointwise

namespace Work.SSGRoute.PTembedding

/-- **Transfer of `H³`-vanishing between `H.subgroupOf D` and `D ⊓ H`.**

For subgroups `H, D` of a Hausdorff topological group with `D` compact and `H` closed, the
canonical group isomorphism `↥(H.subgroupOf D) ≃* ↥(D ⊓ H)` (both are the set `H ∩ D` with the
subspace topology inherited from `G`) is a homeomorphism, so `H³(-, 𝔽_p)` vanishes for one if and
only if it vanishes for the other. -/
theorem subsingleton_H3_inf_of_subgroupOf (p : ℕ) {G : Type*} [Group G] [TopologicalSpace G]
    [T2Space G] (H D : Subgroup G) [CompactSpace ↥D] (hH : IsClosed (H : Set G))
    (h : Subsingleton (Work.SSGRoute.H3 (M := Work.SSGRoute.Triv p) ↥(H.subgroupOf D))) :
    Subsingleton (Work.SSGRoute.H3 (M := Work.SSGRoute.Triv p) ↥(D ⊓ H)) := by
  -- `H.subgroupOf D` is closed in the compact group `↥D`, hence compact
  haveI : CompactSpace ↥(H.subgroupOf D) := by
    have hcl : IsClosed ((H.subgroupOf D : Subgroup ↥D) : Set ↥D) := by
      rw [Subgroup.coe_subgroupOf]
      exact hH.preimage continuous_subtype_val
    exact isCompact_iff_compactSpace.mp hcl.isCompact
  -- the canonical identification `↥(H.subgroupOf D) ≃* ↥(D ⊓ H)`
  let Φ : ↥(H.subgroupOf D) ≃* ↥(D ⊓ H) :=
    { toFun := fun u => ⟨((u : ↥D) : G), (u : ↥D).2, u.2⟩
      invFun := fun v => ⟨⟨(v : G), v.2.1⟩, v.2.2⟩
      left_inv := fun u => Subtype.ext rfl
      right_inv := fun v => Subtype.ext rfl
      map_mul' := fun u w => Subtype.ext rfl }
  have hcont : Continuous (Φ : ↥(H.subgroupOf D) → ↥(D ⊓ H)) :=
    Continuous.subtype_mk
      (f := fun u : ↥(H.subgroupOf D) => ((u : ↥D) : G))
      (continuous_subtype_val.comp continuous_subtype_val)
      (fun u => ⟨(u : ↥D).2, u.2⟩)
  -- a continuous bijection from a compact to a Hausdorff space is a homeomorphism
  have hΦ : IsHomeomorph (Φ : ↥(H.subgroupOf D) → ↥(D ⊓ H)) :=
    (isHomeomorph_iff_continuous_bijective).mpr ⟨hcont, Φ.bijective⟩
  have hΨ : ∀ (g' : ↥(H.subgroupOf D)) (m' : Work.SSGRoute.Triv p),
      (AddEquiv.refl (Work.SSGRoute.Triv p)) (g' • m') =
        Φ g' • (AddEquiv.refl (Work.SSGRoute.Triv p)) m' := fun _ _ => rfl
  refine ⟨fun a b => ?_⟩
  have h2 : (Work.SSGRoute.PT.h3Transfer Φ hΦ (AddEquiv.refl (Work.SSGRoute.Triv p))
        hΨ).symm a
      = (Work.SSGRoute.PT.h3Transfer Φ hΦ (AddEquiv.refl (Work.SSGRoute.Triv p)) hΨ).symm b :=
    h.elim _ _
  simpa using congrArg (fun x => (Work.SSGRoute.PT.h3Transfer Φ hΦ
    (AddEquiv.refl (Work.SSGRoute.Triv p)) hΨ) x) h2

theorem h3_triv_subsingleton_decomp_inf_sylow (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)] (ζ : Ω)
    (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (P : Sylow p (K ≃ₐ[k] K))
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    Subsingleton (Work.SSGRoute.H3 (M := Work.SSGRoute.Triv p)
      ↥(SSGRoute.decomp k A ⊓ Subgroup.comap (SSGRoute.res k K) (P : Subgroup (K ≃ₐ[k] K)))) := by
  classical
  -- the fixed field `L = K^P` of the Sylow, viewed inside `Ω`
  set L : IntermediateField k Ω :=
    IntermediateField.map K.val (IntermediateField.fixedField (P : Subgroup (K ≃ₐ[k] K))) with hLdef
  haveI hLfin : FiniteDimensional k ↥L := by
    rw [hLdef]
    haveI : FiniteDimensional k ↥(IntermediateField.fixedField (P : Subgroup (K ≃ₐ[k] K))) :=
      IntermediateField.finiteDimensional_left _
    exact LinearEquiv.finiteDimensional
      (IntermediateField.equivMap (IntermediateField.fixedField (P : Subgroup (K ≃ₐ[k] K)))
        K.val).toLinearEquiv
  -- `P` fixes `ζ`, so `ζ ∈ L`
  have hζL : ζ ∈ L := by
    haveI : NumberField ↥K := NumberField.of_module_finite k ↥K
    let z : ↥K := ⟨ζ, hζK⟩
    have hz : IsPrimitiveRoot z p :=
      hζ.of_map_of_injective (f := IntermediateField.val K) (fun a b h => Subtype.ext h)
    have hfix : ∀ σ ∈ (P : Subgroup (K ≃ₐ[k] K)), σ z = z :=
      Work.SSGRoute.pgroup_fixes_primitiveRoot p k ↥K z hz (P : Subgroup (K ≃ₐ[k] K)) P.isPGroup'
    rw [hLdef, IntermediateField.mem_map]
    exact ⟨z, (IntermediateField.mem_fixedField_iff _ z).mpr hfix, rfl⟩
  -- `res⁻¹(P) = Gal(Ω/L)`
  have hS : Subgroup.comap (SSGRoute.res k K) (P : Subgroup (K ≃ₐ[k] K)) = L.fixingSubgroup := by
    ext x
    rw [Subgroup.mem_comap, IntermediateField.mem_fixingSubgroup_iff]
    have hQ : (SSGRoute.res k K x) ∈ (P : Subgroup (K ≃ₐ[k] K)) ↔
        (SSGRoute.res k K x) ∈
          (IntermediateField.fixedField (P : Subgroup (K ≃ₐ[k] K))).fixingSubgroup := by
      rw [IntermediateField.fixingSubgroup_fixedField (P : Subgroup (K ≃ₐ[k] K))]
    rw [hQ, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h z hz
      rw [hLdef] at hz
      rw [IntermediateField.mem_map] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      show x ↑y = ↑y
      rw [← AlgEquiv.restrictNormalHom_apply K x y]
      exact congrArg Subtype.val (h y hy)
    · intro h y hy
      have hz : K.val y ∈ L := by
        rw [hLdef, IntermediateField.mem_map]; exact ⟨y, hy, rfl⟩
      apply Subtype.ext
      rw [AlgEquiv.restrictNormalHom_apply K x y]
      exact h (K.val y) hz
  -- the base case: `H³(Gal(Ω/L) ∩ D_A, 𝔽_p) = 0`
  have hbase : Subsingleton (Work.SSGRoute.H3 (M := Work.SSGRoute.Triv p)
      ↥((L.fixingSubgroup).subgroupOf (SSGRoute.decomp k A))) :=
    Work.SSGRoute.EulerSymm.h3triv_subsingleton_fixingSubgroup p k Ω L ζ hζ hζL A hA
  -- topologies: `G_k` is Hausdorff, `D_A` is closed hence compact
  haveI hInt : Algebra.IsIntegral k Ω :=
    Algebra.isAlgebraic_iff_isIntegral.mp (Algebra.IsSeparable.isAlgebraic k Ω)
  haveI hT2 : T2Space (Ω ≃ₐ[k] Ω) := krullTopology_t2
  haveI : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  haveI hCompD : CompactSpace ↥(SSGRoute.decomp k A) :=
    isCompact_iff_compactSpace.mp (Work.SSGRoute.HS.isClosed_decomp (k := k) (Ω := Ω) A).isCompact
  have hHclosed : IsClosed (L.fixingSubgroup : Set (Ω ≃ₐ[k] Ω)) :=
    IntermediateField.fixingSubgroup_isClosed L
  rw [hS]
  exact subsingleton_H3_inf_of_subgroupOf p L.fixingSubgroup (SSGRoute.decomp k A) hHclosed hbase

end Work.SSGRoute.PTembedding
