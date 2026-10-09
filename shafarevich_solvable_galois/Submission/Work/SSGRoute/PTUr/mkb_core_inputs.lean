/-
# The inputs of the coprime-index case of local Tate duality in degrees `0`/`2`

`Submission/Work/SSGRoute/PT/mkb_ld02_core_of_h3.lean` assembles Milne's `α²`-dévissage
(`ADT`, Thm I.1.8 at `r = 2`) as `mkb_alphaTwo_bijective_of_inputs`, whose remaining hypotheses are

* `hc` — the corestriction `cor : H²(U,Ωˣ) → H²(D_A,Ωˣ)` is bijective on the `p`-torsion
  (Milne (1.1b)); available for `p ∤ [D_A : U]` (`corH2_ptorsion_bijective_of_coprime_index`);
* `hbase` — the trivial-action base case `α²(U, N)`;
* `hbase₁` — the base case `α²(U, N₁)` for the cokernel `N₁ = Coind_U^{D_A} N ⧸ N`;
* `hDN`, `hDco`, `hDm1` — discreteness of the three `Hom_ℤ(-,Ωˣ)`-modules occurring in the dual
  coefficient sequence;
* `hhtop` — `H³(D_A, Hom_ℤ(N₁,Ωˣ)) = 0` (the arithmetic input `cd_p ≤ 2` for the finite module
  `N₁`; the remaining arithmetic piece).

This file supplies the *formal* inputs (`hbase`, `hbase₁`, `hDN`, `hDco`, `hDm1`) for an arbitrary
`U ≤ D_A`, and, for `U = levelFixSub k Ω A K`, also `hc` (the coprime-index corestriction).  The
mathematical content is that `Coind_U^{D_A} M` and its cokernel are *finite* (a `Coind`-element is
determined by its values on a finite set of coset representatives), that a normal `U` acting
trivially on `M` acts trivially on `Coind_U^{D_A} M` and on its cokernel, and that `α²(U,-)` is
bijective for finite trivial-action coefficients (Kummer + Hilbert 90 at the open subgroup).
-/
import Mathlib
import Submission.Work.SSGRoute.PT.DevissageSESFinal
import Submission.Work.SSGRoute.PT.devissageLinear
import Submission.Work.SSGRoute.PT.isDiscreteModule_conjHom
import Submission.Work.SSGRoute.PT.isDiscreteModule_coind
import Submission.Work.SSGRoute.PT.alphaTwo_trivAction_of_trivMod
import Submission.Work.SSGRoute.PT.AlphaTwoTrivModSurj
import Submission.Work.SSGRoute.PT.kummerSES
import Submission.Work.SSGRoute.PT.KrullCorrespondence
import Submission.Work.SSGRoute.PT.br_pTorsion_openSubgroup
import Submission.Work.SSGRoute.PT.brOpenSubgroupDefs
import Submission.Work.SSGRoute.PT.corH2_ptorsion_bijective_of_coprime_index
import Submission.Work.SSGRoute.PTembedding.kummer_ses_decomp
import Submission.Work.SSGRoute.PTUr.hdiv_addUnits
import Submission.Work.SSGRoute.PTUr.subgroupAction_discrete
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1000000

open Classical
open scoped TensorProduct

namespace Work.SSGRoute.PTUr

open Work.SSGRoute.PT

universe u v

/-! ## The `G`-equivariance of `ConjHom.precomp` -/

theorem ptu_isEquivariant_conjHom_precomp {G : Type u} [Group G]
    {N₁ : Type u} [AddCommGroup N₁] [DistribMulAction G N₁]
    {N₂ : Type u} [AddCommGroup N₂] [DistribMulAction G N₂]
    {C : Type v} [AddCommGroup C] [DistribMulAction G C]
    (φ : N₁ →+ N₂) (hφ : Work.GroupCohomology.IsEquivariant G φ) :
    Work.GroupCohomology.IsEquivariant G (ConjHom.precomp (C := C) φ) := by
  intro g f
  refine ConjHom.ext_apply (fun n => ?_)
  rw [ConjHom.precomp_apply, ConjHom.smul_apply, ConjHom.smul_apply, ConjHom.precomp_apply,
    hφ g⁻¹ n]

/-! ## Triviality of a normal subgroup on `Coind` and on its cokernel -/

section CoindGeneral

variable {G : Type u} [Group G] {M : Type u} [AddCommGroup M] [DistribMulAction G M]

/-- **`U` acts trivially on `Coind_U^G M`** when `U` is normal in `G` and acts trivially on `M`. -/
theorem ptu_coind_sub_smul_eq (U : Subgroup G) [U.Normal]
    (hUt : ∀ (u : U) (m : M), u • m = m) (u : U) (f : Coind G U M) : (u : G) • f = f := by
  have key : ∀ x : G, x⁻¹ * (u : G)⁻¹ * x ∈ U := by
    intro x
    have h := (inferInstance : U.Normal).conj_mem ((u : G)⁻¹) (U.inv_mem u.2) x⁻¹
    simpa using h
  refine Subtype.ext (funext fun x => ?_)
  rw [Coind.smul_apply]
  have hx : (u : G)⁻¹ * x = x * ((⟨x⁻¹ * (u : G)⁻¹ * x, key x⟩ : U) : G) := by group
  rw [hx, Coind.coe_mul, hUt]

end CoindGeneral

section CoindFinite

variable {G : Type u} [Group G] {M : Type u} [AddCommGroup M] [DistribMulAction G M] [Finite M]

/-- **`Coind_U^G M` is finite** for `U` of finite index (`M` finite): a `Coind`-element is
determined by its values on a finite set of coset representatives. -/
theorem ptu_finite_coind (U : Subgroup G) [U.FiniteIndex] : Finite (Coind G U M) := by
  classical
  letI : Fintype (G ⧸ U) := Subgroup.fintypeQuotientOfFiniteIndex
  let S : Finset G := Finset.univ.image (fun q : G ⧸ U => Quotient.out q)
  have hcov : ∀ x : G, ∃ s ∈ S, ∃ u : U, x = s * (u : G) := by
    intro x
    refine ⟨Quotient.out (⟦x⟧ : G ⧸ U), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨⟦x⟧, Finset.mem_univ _, rfl⟩
    · have h : (QuotientGroup.leftRel U) (Quotient.out (⟦x⟧ : G ⧸ U)) x := by
        apply Quotient.exact
        exact Quotient.out_eq ⟦x⟧
      rw [QuotientGroup.leftRel_apply] at h
      exact ⟨⟨(Quotient.out (⟦x⟧ : G ⧸ U))⁻¹ * x, h⟩, by group⟩
  haveI : Fintype M := Fintype.ofFinite M
  haveI : Fintype ↥S := S.fintypeCoeSort
  haveI : Fintype (↥S → M) := inferInstance
  refine Finite.of_injective (fun f : Coind G U M => fun s : ↥S => f (s : G))
    fun f f' hff' => ?_
  refine Subtype.ext (funext fun x => ?_)
  obtain ⟨s, hs, u, rfl⟩ := hcov x
  have hs_eq : f s = f' s := by
    have := congrFun hff' ⟨s, hs⟩
    simpa using this
  rw [Coind.coe_mul, Coind.coe_mul, hs_eq]

/-- **The cokernel `M₁ = Coind_U^G M ⧸ M` is finite.** -/
theorem ptu_finite_devissageM1 (U : Subgroup G) [U.FiniteIndex] :
    Finite (devissageM1 (M := M) U) := by
  haveI : Finite (Coind G U M) := ptu_finite_coind (M := M) U
  exact Finite.of_surjective (devissagePi (M := M) U) (QuotientAddGroup.mk'_surjective _)

end CoindFinite

section CoindTriv

variable {G : Type u} [Group G] (U : Subgroup G) [U.Normal]
  {M : Type u} [AddCommGroup M] [DistribMulAction G M]

/-- **`U` acts trivially on the cokernel `M₁ = Coind_U^G M ⧸ M`** when it acts trivially on `M`. -/
theorem ptu_devissageM1_sub_smul_eq (hUt : ∀ (u : U) (m : M), u • m = m) (u : U)
    (q : devissageM1 (M := M) U) : (u : G) • q = q := by
  refine QuotientAddGroup.induction_on q (fun f => ?_)
  show QuotientAddGroup.mk' (devissageIota (M := M) U).range ((u : G) • f)
    = QuotientAddGroup.mk' (devissageIota (M := M) U).range f
  rw [ptu_coind_sub_smul_eq U hUt u f]

end CoindTriv

/-! ## Hilbert 90 at an open subgroup of a decomposition group -/

/-- **Hilbert 90 at an open subgroup `U ≤ D_A` of a decomposition group**: `H¹(U,Ωˣ) = 0`. -/
theorem ptu_hilbert90_openSubgroup
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (U : Subgroup ↥(SSGRoute.decomp k A)) (hUo : IsOpen (U : Set ↥(SSGRoute.decomp k A))) :
    Subsingleton (Work.AbsoluteKummer.H1 ↥U (Additive (Units Ω))) := by
  haveI hGal : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  haveI hCZ : CharZero k := inferInstance
  have hDcl : IsClosed ((SSGRoute.decomp k A : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) :=
    Work.SSGRoute.PTembedding.isClosed_decomp' k Ω A
  have hUcl : IsClosed (U : Set ↥(SSGRoute.decomp k A)) := Subgroup.isClosed_of_isOpen U hUo
  have hHcl : IsClosed ((U.map (Subgroup.subtype (SSGRoute.decomp k A)) :
      Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) :=
    Work.SSGRoute.PT.bropenIsClosedMapSubtype (SSGRoute.decomp k A) hDcl U hUcl
  have h90 : Subsingleton (Work.AbsoluteKummer.H1
      ↥(U.map (Subgroup.subtype (SSGRoute.decomp k A))) (Additive (Units Ω))) :=
    Work.SSGRoute.PT.bropenHilbert90ClosedSubgroup (k := k) (Ω := Ω) _ hHcl
  have hΦ : IsHomeomorph (((Work.SSGRoute.PT.bropenSubgroupMapValEquiv (SSGRoute.decomp k A) U) :
      ↥U → ↥(U.map (Subgroup.subtype (SSGRoute.decomp k A))))) :=
    Work.SSGRoute.PT.bropenIsHomeomorphSubgroupMapValEquiv (SSGRoute.decomp k A) hDcl U hUcl
  have h := Work.SSGRoute.PT.h1Transfer
    (G := ↥(U.map (Subgroup.subtype (SSGRoute.decomp k A)))) (G' := ↥U)
    (M := Additive (Units Ω)) (M' := Additive (Units Ω))
    (Work.SSGRoute.PT.bropenSubgroupMapValEquiv (SSGRoute.decomp k A) U) hΦ
    (AddEquiv.refl (Additive (Units Ω))) (fun _ _ => rfl)
  exact ⟨fun a b => h.injective (Subsingleton.elim _ _)⟩

/-! ## The trivial-action base case of `α²` -/

/-- **The trivial-action base case `α²(U, N)`**: for a finite `𝔽_p[U]`-module `N` on which `U`
acts trivially, `α²(U, N)` is bijective — Kummer plus Hilbert 90 at `U`. -/
theorem ptu_alphaTwo_base_of_trivAction
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (A : ValuationSubring Ω) (_hA : SSGRoute.IsFinPlace k A)
    (U : Subgroup ↥(SSGRoute.decomp k A)) (hUo : IsOpen (U : Set ↥(SSGRoute.decomp k A)))
    (N : Type) [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction ↥U N] [Finite N]
    (htriv : ∀ (u : ↥U) (n : N), u • n = n) :
    Function.Bijective (Work.SSGRoute.PT.alphaTwo (G := ↥U) (N := N)
      (C := Additive (Units Ω))) := by
  haveI : IsTopologicalGroup ↥U := inferInstance
  have hdiv : ∀ c : Additive (Units Ω), ∃ c' : Additive (Units Ω), p • c' = c :=
    hdiv_addUnits (k := k) (Ω := Ω) p (Fact.out : p.Prime).ne_zero
  have hdisc : Work.AbsoluteKummer.IsDiscreteModule ↥U (Additive (Units Ω)) := by
    have hD := Work.SSGRoute.PTembedding.MupCard.isDiscreteModule_decomp_addUnits
      (k := k) (Ω := Ω) A
    intro c
    show IsOpen (MulAction.stabilizer ↥U c : Set ↥U)
    have hset : (MulAction.stabilizer ↥U c : Set ↥U)
        = Subtype.val ⁻¹' ((MulAction.stabilizer ↥(SSGRoute.decomp k A) c) :
            Set ↥(SSGRoute.decomp k A)) := by
      ext u
      show (u : ↥U) • c = c ↔ (u : ↥(SSGRoute.decomp k A)) • c = c
      exact Iff.rfl
    rw [hset]
    exact (hD c).preimage continuous_subtype_val
  have h1 : Subsingleton (Work.AbsoluteKummer.H1 ↥U (Additive (Units Ω))) :=
    ptu_hilbert90_openSubgroup k Ω A _hA U hUo
  obtain ⟨S, hSι, hSπ⟩ := Work.SSGRoute.PT.kummerSES (G := ↥U) p hdiv hdisc
  have htrivMod : Function.Bijective (Work.SSGRoute.PT.alphaTwo (G := ↥U)
      (N := Work.SSGRoute.PT.TrivMod ↥U p) (C := Additive (Units Ω))) :=
    Work.SSGRoute.PT.alphaTwo_trivMod_bijective (G := ↥U) p S hSι hSπ h1
  exact Work.SSGRoute.PT.alphaTwo_trivAction_of_trivMod (G := ↥U) p htriv htrivMod

/-! ## Discreteness of the dual coefficient modules -/

/-- **Discreteness of `Hom_ℤ(Coind_U^G M, Ωˣ)`** (`M` finite and discrete over `U`, `U` open of
finite index). -/
theorem ptu_isDiscreteModule_conjHom_coind
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G)
    (hUo : IsOpen (U : Set G)) [U.FiniteIndex]
    {M : Type u} [AddCommGroup M] [DistribMulAction G M] [Finite M]
    (hMdisc : Work.AbsoluteKummer.IsDiscreteModule ↥U M)
    {C : Type v} [AddCommGroup C] [DistribMulAction G C]
    (hCdisc : Work.AbsoluteKummer.IsDiscreteModule G C) :
    Work.AbsoluteKummer.IsDiscreteModule G (ConjHom (Coind G U M) C) := by
  haveI : Finite (Coind G U M) := ptu_finite_coind (M := M) U
  exact Work.SSGRoute.PT.isDiscreteModule_conjHom
    (Work.SSGRoute.PT.isDiscreteModule_coind U hUo hMdisc) hCdisc

/-- **Discreteness of `Hom_ℤ(M₁, Ωˣ)`** for the cokernel `M₁ = Coind_U^G M ⧸ M`. -/
theorem ptu_isDiscreteModule_conjHom_m1
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G)
    [U.FiniteIndex] {M : Type u} [AddCommGroup M] [DistribMulAction G M] [Finite M]
    (hMdisc : Work.AbsoluteKummer.IsDiscreteModule G (devissageM1 (M := M) U))
    {C : Type v} [AddCommGroup C] [DistribMulAction G C]
    (hCdisc : Work.AbsoluteKummer.IsDiscreteModule G C) :
    Work.AbsoluteKummer.IsDiscreteModule G (ConjHom (devissageM1 (M := M) U) C) := by
  haveI : Finite (devissageM1 (M := M) U) := ptu_finite_devissageM1 (M := M) U
  exact Work.SSGRoute.PT.isDiscreteModule_conjHom (N := devissageM1 (M := M) U) hMdisc hCdisc

/-! ## The level-`K` subgroup is open -/

/-- The level-`K` subgroup `levelFixSub k Ω A K ≤ D_A` is open. -/
theorem ptu_levelFixSub_isOpen (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (A : ValuationSubring Ω) (K : IntermediateField k Ω) [FiniteDimensional k K] :
    IsOpen (levelFixSub k Ω A K : Set ↥(SSGRoute.decomp k A)) := by
  have h : (levelFixSub k Ω A K : Set ↥(SSGRoute.decomp k A))
      = (fun x : ↥(SSGRoute.decomp k A) => (x : Ω ≃ₐ[k] Ω)) ⁻¹'
        ((K.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) := by
    ext x
    simp only [SetLike.mem_coe, levelFixSub, Subgroup.mem_subgroupOf, Set.mem_preimage]
  rw [h]
  exact (IntermediateField.fixingSubgroup_isOpen K).preimage continuous_subtype_val

/-! ## The coprime-index corestriction input at the level-`K` subgroup -/

/-- **The corestriction `cor : H²(U,Ωˣ) → H²(D_A,Ωˣ)` is bijective on the `p`-torsion** for
`U = levelFixSub k Ω A K` of index coprime to `p`. -/
theorem ptu_cor_ptorsion_bijective_levelFixSub
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    [hfi : (levelFixSub k Ω A K).FiniteIndex]
    [hft : Fintype (↥(SSGRoute.decomp k A) ⧸ levelFixSub k Ω A K)]
    (hcop : (Nat.card (↥(SSGRoute.decomp k A) ⧸ levelFixSub k Ω A K)).Coprime p) :
    Function.Bijective (fun x : {x : Work.AbsoluteKummer.H2 ↥(levelFixSub k Ω A K)
        (Additive (Units Ω)) // p • x = 0} =>
      (⟨Work.SSGRoute.PT.corH2 (levelFixSub k Ω A K)
          (ptu_levelFixSub_isOpen k Ω A K) (Additive (Units Ω)) x.1,
        by rw [← map_nsmul, x.2, map_zero]⟩ :
        {y : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)) //
          p • y = 0})) :=
  Work.SSGRoute.PT.corH2_ptorsion_bijective_of_coprime_index p k Ω A hA
    (levelFixSub k Ω A K) (ptu_levelFixSub_isOpen k Ω A K) hcop

end Work.SSGRoute.PTUr
