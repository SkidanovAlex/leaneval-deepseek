import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ProperStageDefs
import Submission.Work.SSGRoute.local_tame_lifting
import Submission.Work.SSGRoute.flowLift_ramified
import Submission.Work.SSGRoute.localZhatHom_ker
import Submission.Work.SSGRoute.flowLift_ramified_continuous
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open Work.CohomologicalShrinking
open _root_.SSGRoute

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# Local liftability with open kernel at the finite places outside `T¹`

This file proves `Work.SSGRoute.exists_localLift_outside_T1`, the "continuous" form of
`Work.SSGRoute.stage_local_solvable` in which the local lift additionally has an **open kernel**.

It is a *standalone* module: it does **not** import `Submission.Work.SSGRoute.stage_local_solvable`
(nor `stage_local_solvable_continuous`), whose `flowQuotientProj` / `flowGroupProj` clash with the
canonical ones of `Submission.Work.SSGRoute.ProperStageDefs`.  Instead, the canonical projections
of `ProperStageDefs` are used throughout, together with the local liftability statements

* `Work.SSGRoute.flowLift_ramified_continuous` (the ramified case, `φ` non-trivial on inertia);
* `Work.SSGRoute.exists_hom_at_frob` / `eq_of_apply_frob_eq` (`SSGRoute.local_tame_lifting`, part
  (a)) for the unramified case, where `φ` kills the inertia subgroup and the lift is produced by the
  universal property of a Frobenius generator of `D_A/I_A ≅ Ẑ`.

The only auxiliary facts proved here are the canonical counterparts of the elementary projection
lemmas of `stage_local_solvable` (surjectivity of the level projection, and `LiftsFlowAt` from
equality of projections) and finiteness of the flow groups.
-/

/-! ## The canonical level projection: elementary facts -/

/-- The level projection of the left factors `F(m)/F(m)^{(τ+1)} →* F(m)/F(m)^{(τ)}` is surjective. -/
theorem flowQuotientProj_surjective_canon (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    Function.Surjective (flowQuotientProj p G m i j) := by
  intro z
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
    ((flowTerm p G m i j).subgroupOf (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))) z
  exact ⟨QuotientGroup.mk' _ y, by rw [flowQuotientProj_mk]; rfl⟩

/-- The level projection `Γ^{(τ+1)} →* Γ^{(τ)}` of the flow groups is surjective. -/
theorem flowGroupProj_surjective_canon (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    Function.Surjective (flowGroupProj p G m i j) := by
  intro γ
  obtain ⟨y, hy⟩ := flowQuotientProj_surjective_canon p G m i j γ.left
  refine ⟨SemidirectProduct.mk y γ.right, ?_⟩
  rw [flowGroupProj_mk, hy]

/-- If the level projection of `y` is `x`, then `y` lifts `x` in the sense of `LiftsFlowAt`. -/
theorem liftsFlowAt_of_flowGroupProj_eq_canon (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar)
    {m : ℕ} (i j : ℕ)
    (y : flowGroup p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2)
    (x : flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (h : flowGroupProj p (K ≃ₐ[ℚ] K) m i j y = x) : LiftsFlowAt y x := by
  refine ⟨?_, ?_⟩
  · rw [← h, flowGroupProj, SemidirectProduct.map_right, MonoidHom.id_apply]
  · obtain ⟨z, hz⟩ := QuotientGroup.mk'_surjective
      ((flowTerm p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2).subgroupOf
        (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup (K ≃ₐ[ℚ] K) m))) y.left
    refine ⟨z, hz.symm, ?_⟩
    rw [← h]
    show (flowGroupProj p (K ≃ₐ[ℚ] K) m i j y).left =
      (QuotientGroup.mk z : flowQuotient p (K ≃ₐ[ℚ] K) m i j)
    rw [flowGroupProj, SemidirectProduct.map_left, ← hz, flowQuotientProj_mk]
    rfl

/-! ## Finiteness of the flow groups -/

/-- The quotient `F(m)/F(m)^{(i,j)}` is finite for a finite `G`. -/
theorem finite_flowQuotient_canon (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
    (m i j : ℕ) : Finite (flowQuotient p G m i j) := by
  haveI : Fintype (Fin m × G) := inferInstance
  have hmap : Subgroup.map (Subgroup.topEquiv (G := Work.Shrinking.freeOperatorGroup G m)).toMonoidHom
      ((flowTerm p G m i j).subgroupOf ⊤) = flowTerm p G m i j := by
    change Subgroup.map (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m)).subtype
      ((flowTerm p G m i j).subgroupOf ⊤) = flowTerm p G m i j
    rw [Subgroup.subgroupOf_map_subtype, inf_top_eq]
  haveI : (flowTerm p G m i j).Normal := inferInstance
  haveI : Finite (Work.Shrinking.freeOperatorGroup G m ⧸ flowTerm p G m i j) := by
    have hle : Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G m) i
        ≤ flowTerm p G m i j := by
      rw [flowTerm, refinedTerm]; exact le_sup_right
    have hfin : Finite (Work.Shrinking.freeOperatorGroup G m ⧸
        Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G m) i) :=
      Work.Shrinking.finite_freeGroup_quotient_pCentralSeries p (Fin m × G) i
    have hsurj : Function.Surjective (QuotientGroup.map
        (Work.Shrinking.pCentralSeries p (Work.Shrinking.freeOperatorGroup G m) i)
        (flowTerm p G m i j) (MonoidHom.id _) (by simpa using hle)) := fun y => by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (flowTerm p G m i j) y
      exact ⟨QuotientGroup.mk' _ x, by rw [QuotientGroup.map_mk']; rfl⟩
    exact hfin.of_surjective _ hsurj
  exact Finite.of_equiv _
    (QuotientGroup.congr ((flowTerm p G m i j).subgroupOf ⊤) (flowTerm p G m i j)
      (Subgroup.topEquiv (G := Work.Shrinking.freeOperatorGroup G m)) hmap).symm.toEquiv

/-- The flow group `F(m)/F(m)^{(i,j)} ⋊ G` is finite for a finite `G`. -/
theorem finite_flowGroup_canon (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
    (m i j : ℕ) : Finite (flowGroup p G m i j) := by
  haveI : Finite (flowQuotient p G m i j) := finite_flowQuotient_canon p G m i j
  haveI : Finite (flowQuotient p G m i j × G) := inferInstance
  exact Finite.of_equiv _ (SemidirectProduct.equivProd.symm)

/-! ## The unramified case, with open kernel -/

/-- **Local lift with open kernel when `φ` kills the inertia of `A`.**

The lift is produced by the universal property of a Frobenius generator of `D_A/I_A ≅ Ẑ`
(`SSGRoute.exists_hom_at_frob`): starting from an arbitrary preimage `x₀` of `φ(F)` in
`Γ^{(τ+1)}` we obtain a homomorphism `f : D_A →* Γ^{(τ+1)}` with open kernel, killing the
inertia and with `f F = x₀`; by the uniqueness statement `SSGRoute.eq_of_apply_frob_eq` the
composite `π ∘ f` equals `φ|D_A`, whence `f` lifts `φ|D_A` and its kernel is open. -/
theorem exists_continuous_lift_of_killsInertia_canon (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K]
    (i j m : ℕ)
    (φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (A : ValuationSubring SSGRoute.QBar) (hfin : SSGRoute.IsFinPlace ℚ A)
    (hopen : IsOpen (φ.ker : Set SSGRoute.GalQ))
    (hkill : ∀ σ : ↥(SSGRoute.decomp ℚ A),
      SSGRoute.IsInertia ℚ A (σ : SSGRoute.GalQ) → φ (σ : SSGRoute.GalQ) = 1) :
    ∃ l : ↥(SSGRoute.decomp ℚ A) →* flowGroup p (K ≃ₐ[ℚ] K) m
          (tauSucc i j).1 (tauSucc i j).2,
      IsOpen (l.ker : Set ↥(SSGRoute.decomp ℚ A)) ∧
      (∀ σ : ↥(SSGRoute.decomp ℚ A), LiftsFlowAt (l σ) (φ (σ : SSGRoute.GalQ))) := by
  classical
  haveI : Fintype (K ≃ₐ[ℚ] K) := AlgEquiv.fintype ℚ ↥K
  haveI : Finite (flowGroup p (K ≃ₐ[ℚ] K) m i j) := finite_flowGroup_canon p _ m i j
  haveI : Finite (flowGroup p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2) :=
    finite_flowGroup_canon p _ m _ _
  set A' : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar := ⟨A, hfin⟩ with hA'
  set φD : ↥(SSGRoute.decomp ℚ A) →* flowGroup p (K ≃ₐ[ℚ] K) m i j :=
    φ.comp (Subgroup.subtype (SSGRoute.decomp ℚ A)) with hφD
  obtain ⟨x₀, hx₀⟩ :=
    flowGroupProj_surjective_canon p (K ≃ₐ[ℚ] K) m i j (φD (SSGRoute.localFrobElem A'))
  obtain ⟨f, hfopen, hfiner, hfF⟩ := SSGRoute.exists_hom_at_frob A hfin
    (flowGroup p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2) x₀
  have hprojopen : IsOpen (((flowGroupProj p (K ≃ₐ[ℚ] K) m i j).comp f).ker :
      Set ↥(SSGRoute.decomp ℚ A)) :=
    isOpen_subgroup_of_le_isOpen _
      (U := (f.ker : Set ↥(SSGRoute.decomp ℚ A))) hfopen (Subgroup.one_mem _)
      (fun x hx => by
        show ((flowGroupProj p (K ≃ₐ[ℚ] K) m i j).comp f) x = 1
        rw [MonoidHom.comp_apply, MonoidHom.mem_ker.mp hx, map_one])
  have hprojiner : ∀ σ : ↥(SSGRoute.decomp ℚ A),
      SSGRoute.IsInertia ℚ A (σ : SSGRoute.GalQ) →
      ((flowGroupProj p (K ≃ₐ[ℚ] K) m i j).comp f) σ = 1 := by
    intro σ hσ
    rw [MonoidHom.comp_apply, hfiner σ hσ, map_one]
  have hφDopen : IsOpen (φD.ker : Set ↥(SSGRoute.decomp ℚ A)) := by
    rw [hφD]; exact isOpen_ker_comp_subtype φ A hopen
  have hφDiner : ∀ σ : ↥(SSGRoute.decomp ℚ A),
      SSGRoute.IsInertia ℚ A (σ : SSGRoute.GalQ) → φD σ = 1 := by
    intro σ hσ; rw [hφD]; exact hkill σ hσ
  have hF : ((flowGroupProj p (K ≃ₐ[ℚ] K) m i j).comp f) (SSGRoute.localFrobElem A')
      = φD (SSGRoute.localFrobElem A') := by
    rw [MonoidHom.comp_apply, hfF, hx₀]
  have heq : (flowGroupProj p (K ≃ₐ[ℚ] K) m i j).comp f = φD :=
    SSGRoute.eq_of_apply_frob_eq A hfin (flowGroup p (K ≃ₐ[ℚ] K) m i j) _ φD
      hprojopen hφDopen hprojiner hφDiner hF
  refine ⟨f, hfopen, fun σ => ?_⟩
  have hcomp : flowGroupProj p (K ≃ₐ[ℚ] K) m i j (f σ) = φ (σ : SSGRoute.GalQ) := by
    have := MonoidHom.ext_iff.mp heq σ
    rw [MonoidHom.comp_apply] at this
    rw [this]; rfl
  exact liftsFlowAt_of_flowGroupProj_eq_canon p K i j (f σ) (φ (σ : SSGRoute.GalQ)) hcomp

/-! ## The main lemma -/

/-- Local liftability with **open kernel** at the finite places outside `T¹` (SW Step 1b/1c).

IMPORTANT for the prover: write the file as a *standalone* module (namespace `Work.SSGRoute`),
and do NOT import `Submission.Work.SSGRoute.stage_local_solvable` (nor
`stage_local_solvable_continuous`): that file declares its own `flowQuotientProj` /`flowGroupProj`,
which **name-clash** with `Submission.Work.SSGRoute.ProperStageDefs` as soon as both are imported,
and the consumer `solvableStage_of_scholz` needs both.  Use the canonical
`Submission.Work.SSGRoute.ProperStageDefs.flowQuotientProj` / `flowGroupProj` (already imported
here) instead: they are the same construction.  The proof is the case analysis of
`stage_local_solvable.lean` (readable, do not import): if `φ` kills the inertia of `A` then
`D_A/I_A ≅ Ẑ` is generated by a Frobenius and the lift is built from `localZhatHom` (its kernel is
the inertia, `localZhatHom_ker`), a preimage of `φ F` in `Γ^{τ+1}`, and
`localZhatHom⁻¹(powSubgroup (orderOf x₀))` being open; if `φ` is non-trivial on inertia then
condition (ii) of `IsScholzSolution` makes `φ|_{D_A}` a totally ramified character and
`flowLift_ramified` supplies a lift with open kernel.  See also the sorry-free modules
`Submission.Work.SSGRoute.exists_continuous_lift_of_killsInertia` (case 1) and
`Submission.Work.SSGRoute.flowLift_ramified_continuous` (case 2). -/
theorem exists_localLift_outside_T1 (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K]
    (i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i) (hμ : SSGRoute.HasRootsOfUnity p K i) (m : ℕ)
    (φ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (hφ : SSGRoute.IsScholzSolution p K m i j φ) :
    ∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ A →
      ¬ SSGRoute.IsT1Place p K A →
      ∃ l : ↥(SSGRoute.decomp ℚ A) →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m
            (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2,
        (∀ σ : ↥(SSGRoute.decomp ℚ A), SSGRoute.LiftsFlowAt (l σ) (φ σ)) ∧
        IsOpen (l.ker : Set ↥(SSGRoute.decomp ℚ A)) := by
  intro A hfin hnT1
  by_cases hkill : ∀ σ : ↥(SSGRoute.decomp ℚ A),
      SSGRoute.IsInertia ℚ A (σ : SSGRoute.GalQ) → φ (σ : SSGRoute.GalQ) = 1
  · obtain ⟨l, hlopen, hl⟩ :=
      exists_continuous_lift_of_killsInertia_canon p K i j m φ A hfin hφ.1.2.1 hkill
    exact ⟨l, hl, hlopen⟩
  · push_neg at hkill
    obtain ⟨σ, hσI, hσne⟩ := hkill
    exact flowLift_ramified_continuous p K i j hj hji hμ m φ hφ A hfin hnT1 ⟨σ, hσI, hσne⟩

end Work.SSGRoute
