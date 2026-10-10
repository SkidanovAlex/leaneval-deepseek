import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.CharP.IntermediateField
import Submission.Work.SSGRoute.equivariant_flowQuotient_surjection
import Submission.Work.SSGRoute.exists_normal_sup_rootsOfUnity
import Submission.Work.SSGRoute.splitEmbeddingSolvable_of_surjective_lift
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/SSGRoute/DESIGN.md first (orchestrator design; your lemma is one node of its DAG). Shared vocabulary: Submission/Work/SSGRoute/Interfaces.lean (namespace SSGRoute; do NOT edit — put any new shared definition in your own file). The proved class-field-theory library is available as NK.* (Chebotarev: NK.NUV2.chebotarev_all0 with hFC := NK.CFTLib.fundamentalClassElement; local reciprocity NK.NUV2.kernelCondition_all; existence NK.CFTLib.Existence.classField_exists_primeIndex (unramified only); Hasse–Brauer–Noether NK.GlobalCFTdeep.hbnUnits; NK.KC.localBaseChangeInput_of_kc; NK.HR2.transferStepOnePlace), all axiom-clean. NEVER use Work.HilbertSymbol.GrunwaldWang (false as written). Siblings run in parallel; import them when they land.

# Guidance: descent from Theorem 15 (flow groups, K ⊇ μ) to `GenericKernelSolvable`

The hypothesis `h` is what `theorem15_scholz` gives (drop the Scholz conditions). Target:
`Work.GenericKernelReduction.GenericKernelSolvable`, an arbitrary finite Galois L ⊆ ℚ̄ with an arbitrary
descended action on `Work.ProP.FreePQuotient p n ν`.

**Sketch.**
1. Take K := L ⊔ ℚ(μ_{p^{ν+2}}) (normal, finite) and i := ν+1, j := 1. `HasRootsOfUnity p K (ν+1)` holds.
   Then F^{(ν+1,1)} = pSeries (ν+1) = `pCentralSeries ν`, so flowQuotient n' (ν+1) 1 = F(n')/P_{ν+1}.
2. Let G' = Gal(K/ℚ) act on P := FreePQuotient p n ν through Gal(K/ℚ) ↠ Gal(L/ℚ) and Φ. Build the
   G'-equivariant surjection FreeGroup(Fin n' × G') → P, x_{a,g} ↦ g·(generator a), with n' = max n 1.
   It kills `pCentralSeries ν` (image of the p-central series lies in the p-central series of P, which is
   trivial at ν). It therefore descends to flowQuotient ↠ P, equivariantly.
3. The surjection flowGroup ↠ P ⋊[Φ] Gal(L/ℚ) (`SemidirectProduct.map` + restriction), composed with φ from
   `h`, gives a continuous surjection G_ℚ ↠ P ⋊ Gal(L/ℚ) over res_L. Its fixed field solves the problem:
   use `Work.GenericKernelReduction.inClosure_of_surjective` (or pass through
   `Work.AbsoluteGalois.isSolvable_iff_hasSurjectiveLift`) and
   `Work.GenericKernelReduction.splitEmbeddingSolvable_of_inClosure`.

**Assets.**
- `Work.GenericKernelReduction.exists_equivariant_surjection_freeGroup`,
  `…exists_equivariant_quotient_freePQuotient`, `…IsDescendedAction`, `…inClosure_of_surjective`;
- `Work.ProP.freePQuotientMk`;
- `Work.CohomologicalShrinking.flowGroup`, `flowQuot`, `flowAction`;
- `Work.AbsoluteGalois.realizableOver_iff_exists_continuous_surjective` (for the continuity ↔ fixed field
  dictionary).

**Imports.** `Submission.Work.SSGRoute.Interfaces` (which imports GenericKernelReduction.All).

**Pitfalls.** The `IsGalois ℚ ↥L` vs `Normal ℚ ↥K` instance diamonds: see `Submission/NOTES.md`, "Known trap".
Produce `Normal ℚ K` from `IsGalois` by term, not by instance search.
-/

namespace Work.SSGRoute

open SSGRoute

open Work.CohomologicalShrinking

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-! ## Restriction maps between intermediate fields -/

/-- For `L ≤ K`, both normal over `ℚ`, the restriction `Gal(K/ℚ) →* Gal(L/ℚ)`: the unique
homomorphism whose composite with the restriction `G_ℚ →* Gal(K/ℚ)` is the restriction
`G_ℚ →* Gal(L/ℚ)` (which exists by the universal property of the restriction `G_ℚ ↠ Gal(K/ℚ)`). -/
noncomputable def restrictNormalHomOfLe {L K : IntermediateField ℚ SSGRoute.QBar}
    [Normal ℚ L] [Normal ℚ K] (hLK : L ≤ K) : (K ≃ₐ[ℚ] K) →* (L ≃ₐ[ℚ] L) :=
  (MonoidHom.liftOfSurjective (Work.AbsoluteGalois.restrictHom K)
    (Work.AbsoluteGalois.restrictHom_surjective K)
    ⟨Work.AbsoluteGalois.restrictHom L, by
      rw [Work.AbsoluteGalois.restrictHom_ker K, Work.AbsoluteGalois.restrictHom_ker L]
      exact IntermediateField.fixingSubgroup_le hLK⟩)

/-- The defining property of `restrictNormalHomOfLe`: it is compatible with the restrictions from
`G_ℚ`. -/
theorem restrictNormalHomOfLe_apply {L K : IntermediateField ℚ SSGRoute.QBar} [Normal ℚ L]
    [Normal ℚ K] (hLK : L ≤ K) (σ : SSGRoute.GalQ) :
    restrictNormalHomOfLe hLK (Work.AbsoluteGalois.restrictHom K σ)
      = Work.AbsoluteGalois.restrictHom L σ := by
  have hker : (Work.AbsoluteGalois.restrictHom K).ker
      ≤ (Work.AbsoluteGalois.restrictHom L).ker := by
    rw [Work.AbsoluteGalois.restrictHom_ker K, Work.AbsoluteGalois.restrictHom_ker L]
    exact IntermediateField.fixingSubgroup_le hLK
  have h1 : ((MonoidHom.liftOfSurjective (Work.AbsoluteGalois.restrictHom K)
      (Work.AbsoluteGalois.restrictHom_surjective K))
        ⟨Work.AbsoluteGalois.restrictHom L, hker⟩).comp (Work.AbsoluteGalois.restrictHom K)
      = Work.AbsoluteGalois.restrictHom L :=
    congrArg Subtype.val (Equiv.left_inv (MonoidHom.liftOfSurjective
      (Work.AbsoluteGalois.restrictHom K) (Work.AbsoluteGalois.restrictHom_surjective K))
      ⟨Work.AbsoluteGalois.restrictHom L, hker⟩)
  exact congrFun (congrArg DFunLike.coe h1) σ

/-- `restrictNormalHomOfLe` is surjective (it is a restriction map in Galois theory). -/
theorem restrictNormalHomOfLe_surjective {L K : IntermediateField ℚ SSGRoute.QBar} [Normal ℚ L]
    [Normal ℚ K] (hLK : L ≤ K) : Function.Surjective (restrictNormalHomOfLe hLK) := by
  intro u
  obtain ⟨σ, hσ⟩ := Work.AbsoluteGalois.restrictHom_surjective L u
  exact ⟨Work.AbsoluteGalois.restrictHom K σ, by
    rw [restrictNormalHomOfLe_apply hLK σ]; exact hσ⟩

/-- **Descent from the flow solutions of Theorem 15 to the generic-kernel statement.**

Given, for every prime `p`, every finite normal `K ⊆ ℚ̄` containing `μ_{p^{i+1}}` and all `n ≥ 1`, a
*proper* solution `φ : G_ℚ ↠ F(n)/F(n)^{(i,j)} ⋊ Gal(K/ℚ)` of the split generic embedding problem
(`SSGRoute.IsFlowSolution`, i.e. Theorem 15 of Schmidt–Wingberg with its Scholz conditions
dropped), every split embedding problem over `ℚ` with kernel the generic kernel
`F^(n)/F^(n)(ν)` has a proper solution (`Work.GenericKernelReduction.GenericKernelSolvable`).

Proof.  Fix `L`, `p`, `n`, `ν` and an action `Φ` of `Gal(L/ℚ)` on `P := F^(n)/F^(n)(ν)`.
Choose a finite normal `K ⊇ L` with `μ_{p^{ν+2}} ⊆ K`
(`Work.SSGRoute.exists_normal_sup_rootsOfUnity`), so that `F^(ν+1,1) = P_{ν+1}` and
`flowQuotient p Gal(K) m (ν+1) 1 = F(m)/P_{ν+1}`.  Apply the hypothesis at `(i,j) = (ν+1,1)` and
rank `m := max n 1` to obtain `φ`.  The map `x_{a,g} ↦ Φ(g)(x_a)` on the free `Gal(K/ℚ)`-operator
group descends to a surjective `Gal(K/ℚ)`-equivariant homomorphism
`f : F(m)/P_{ν+1} ↠ P` (`Work.SSGRoute.equivariant_flowQuotient_surjection`); regarding the
actions of `Gal(L/ℚ)` on `P` and of `Gal(K/ℚ)` on the flow quotient, `f` together with the
restriction `res : Gal(K/ℚ) →* Gal(L/ℚ)` (`restrictNormalHomOfLe`) yields, through
`SemidirectProduct.map`, a surjection `ψ : F(m)/P_{ν+1} ⋊ Gal(K/ℚ) ↠ P ⋊[Φ] Gal(L/ℚ)` over
`Gal(L/ℚ)`.  Composing with `φ` gives an open-kernel surjection `G_ℚ ↠ P ⋊[Φ] Gal(L/ℚ)` whose
composite with `SemidirectProduct.rightHom` is the restriction to `L`, i.e. a solution of the split
embedding problem (`Work.SSGRoute.splitEmbeddingSolvable_of_surjective_lift`, the fixed field of
the kernel of the surjection).  Note that the descended action hypothesis `hdesc` is not needed:
the construction works for an arbitrary action `Φ`. -/
theorem genericKernelSolvable_of_flowSolutions
    (h : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K]
      [Normal ℚ K] (i j : ℕ), 1 ≤ j → j ≤ i → SSGRoute.HasRootsOfUnity p K i →
      ∀ n : ℕ, 1 ≤ n →
        ∃ φ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n i j,
          SSGRoute.IsFlowSolution p K n i j φ) :
    Work.GenericKernelReduction.GenericKernelSolvable := by
  intro L hLfd hLgal p hp n ν ρ Φ hdesc
  haveI : Fact p.Prime := hp
  haveI : FiniteDimensional ℚ L := hLfd
  haveI : IsGalois ℚ L := hLgal
  haveI hLnrm : Normal ℚ L := hLgal.to_normal
  -- Step 1: a finite normal `K ⊇ L` containing a primitive `p^(ν+2)`-th root of unity.
  obtain ⟨K, hKfd, hKnrm, hLK, hμ⟩ :=
    exists_normal_sup_rootsOfUnity L (p := p) (i := ν + 1) hp.out.pos
  haveI : FiniteDimensional ℚ K := hKfd
  haveI hKnrm' : Normal ℚ K := hKnrm
  -- Step 2: a flow solution at the level `(ν+1, 1)` and rank `max n 1`.
  obtain ⟨φ, hφsurj, hφopen, hφproj⟩ :=
    h p K (ν + 1) 1 le_rfl (by omega) hμ (max n 1) (le_max_right n 1)
  haveI : Finite (Work.ProP.FreePQuotient p n ν) := Work.ProP.finite_freePQuotient (p := p) n ν
  -- Step 3: the `Gal(K/ℚ)`-equivariant surjection `F(m)/F(m)^{(ν+1,1)} ↠ F^(n)/F^(n)(ν)`.
  let res : (K ≃ₐ[ℚ] K) →* (L ≃ₐ[ℚ] L) := restrictNormalHomOfLe hLK
  obtain ⟨f, hfsurj, hfeq⟩ :=
    equivariant_flowQuotient_surjection (G := K ≃ₐ[ℚ] K) (Φ.comp res)
  have hressurj : Function.Surjective res := restrictNormalHomOfLe_surjective hLK
  -- Step 4: the induced surjection of the flow groups `F(m)/F(m)^{(ν+1,1)} ⋊ Gal(K/ℚ) ↠ P ⋊ Gal(L/ℚ)`.
  have hcond : ∀ g : K ≃ₐ[ℚ] K,
      f.comp (flowAction p (K ≃ₐ[ℚ] K) (max n 1) (ν + 1) 1 g).toMonoidHom
        = ((Φ (res g)).toMonoidHom).comp f := by
    intro g
    refine MonoidHom.ext fun y => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [hfeq g y, MonoidHom.comp_apply]
  let ψ : flowGroup p (K ≃ₐ[ℚ] K) (max n 1) (ν + 1) 1 →*
      (Work.ProP.FreePQuotient p n ν ⋊[Φ] (L ≃ₐ[ℚ] L)) :=
    SemidirectProduct.map f res hcond
  have hψsurj : Function.Surjective ψ := by
    intro z
    obtain ⟨a, ha⟩ := hfsurj z.left
    obtain ⟨u, hu⟩ := hressurj z.right
    refine ⟨⟨a, u⟩, ?_⟩
    refine SemidirectProduct.ext ?_ ?_
    · rw [SemidirectProduct.map_left]; exact ha
    · rw [SemidirectProduct.map_right]; exact hu
  have hψproj : ∀ x : flowGroup p (K ≃ₐ[ℚ] K) (max n 1) (ν + 1) 1,
      SemidirectProduct.rightHom (ψ x)
        = res (flowQuot p (K ≃ₐ[ℚ] K) (max n 1) (ν + 1) 1 x) :=
    fun x => congrFun (congrArg DFunLike.coe (show SemidirectProduct.rightHom.comp ψ
        = res.comp (flowQuot p (K ≃ₐ[ℚ] K) (max n 1) (ν + 1) 1) from
      SemidirectProduct.rightHom_comp_map f res hcond)) x
  -- Step 5: compose with the flow solution and solve the split embedding problem.
  let F : SSGRoute.GalQ →* (Work.ProP.FreePQuotient p n ν ⋊[Φ] (L ≃ₐ[ℚ] L)) := ψ.comp φ
  have hFsurj : Function.Surjective F := hψsurj.comp hφsurj
  have hFopen : IsOpen (F.ker : Set SSGRoute.GalQ) := by
    refine Subgroup.isOpen_mono ?_ hφopen
    intro σ hσ
    rw [MonoidHom.mem_ker] at hσ ⊢
    show ψ (φ σ) = 1
    rw [hσ, map_one]
  have hFproj : ∀ σ : SSGRoute.GalQ,
      SemidirectProduct.rightHom (F σ) = AlgEquiv.restrictNormalHom L σ := by
    intro σ
    show SemidirectProduct.rightHom (ψ (φ σ)) = AlgEquiv.restrictNormalHom L σ
    have hσ : (flowQuot p (K ≃ₐ[ℚ] K) (max n 1) (ν + 1) 1) (φ σ)
        = Work.AbsoluteGalois.restrictHom K σ := by
      rw [hφproj σ]
      rfl
    rw [hψproj (φ σ), hσ, restrictNormalHomOfLe_apply hLK σ]
    rfl
  exact splitEmbeddingSolvable_of_surjective_lift L F hFsurj hFopen hFproj

end Work.SSGRoute
