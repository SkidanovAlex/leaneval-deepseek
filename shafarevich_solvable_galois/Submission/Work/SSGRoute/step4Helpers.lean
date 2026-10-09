import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ProperStageDefs
import Submission.Work.SSGRoute.inertia_map_eq_of_isCyclic
import Submission.Work.SSGRoute.t0Generation_cyclic
import Submission.Work.SSGRoute.twistLayer
import Submission.Work.SSGRoute.stage3Defs
import Submission.Work.SSGRoute.isProperStageData_pushdown
import Submission.Work.SSGRoute.step4CokerSideDefs
import Submission.Work.SSGRoute.step4_bundle_assembly
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! # The Step-4 bookkeeping: the helpers that the Step-4 *arithmetic* modules need

These declarations used to live in `Submission/Work/SSGRoute/scholz_succ_of_properStage.lean` (the
node file).  They are *not* arithmetic: they are the twist algebra's consequences
(`isFlowSolution_flowTwistEHom`, `isScholzSolution_flowTwistEHom`), the finiteness of the flow
groups, the Chebotarev `T⁰` (`exists_T0_cyclic_of_surjective`), the node's input predicate
`Step4Input` and its assembly `scholz_succ_of_step4Input`, the section of `restrictNormalHom`, and the
formal-corestriction bookkeeping (`cocycle_conj_eq_zero`, `smul_inv_sec_ne_self`,
`corestriction_eq_self_on_decomp`, `corestriction_eq_zero_on_decomp_of_eq_zero`).

They are pulled out **because of the import cycle**: the arithmetic modules
(`step4_y_exists`, `step4_x_exists`, `step4_x_old_ramification`, `step4_local_clauses`) need them,
but they may not import the node file (the node file is *downstream* of them, via
`step4CokerSide_holds`); importing a common, upstream module is the fix (see
`Submission/Work/SSGRoute/H9_STATUS.md` §10.2). -/

open scoped Pointwise

namespace Work.SSGRoute

open SSGRoute
open _root_.SSGRoute
open Work.CohomologicalShrinking

variable {p : ℕ}

/-! ### The twist of a solution: the flow-solution clauses, and the assembly of Step 4

The following two lemmas contain everything of Step 4 of the paper that is *not* arithmetic:

* `isFlowSolution_flowTwistEHom`: the twist of a flow solution by an `E(n,τ)`-valued cocycle is a
  flow solution as soon as it is surjective (properness is the `T⁰` input, see the paper);
* `isScholzSolution_flowTwistEHom`: with the stage-3 clauses for `ψ` and the local conditions on
  the cocycle `x` (the arithmetic input), the twist satisfies the Scholz conditions at `τ + 1`.

The hypotheses of the second lemma are exactly the data that the arithmetic produces: `x` is a
`1`-cocycle for the `G(K/ℚ)`-action which is locally constant and vanishes on `G_K`
(`hxmul`, `hxloc`, `hx0`; these come from
`SSGRoute.shafarevich_theorem13` applied with `y` from `SSGRoute.coker_obstruction`), its new
ramification is at places completely decomposed in `N_τ/ℚ` (`hnew`), at those places the local
group of the twist is cyclic and equal to the image of the inertia (`hNewLocal`; this is the local
verification at the places of new ramification, whose "totally ramified" half follows from
`Work.SSGRoute.inertia_map_eq_of_isCyclic`), and the twist is proper (`hsurj`, from the `T⁰`
generation of `ker (flowGroupProj)`). -/




/-- The twist of a flow solution is a flow solution (given that it is surjective). -/
theorem isFlowSolution_flowTwistEHom (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K]
    (n i j : ℕ) (x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (hψ : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (ψ σ) = restrict K σ)
    (hxmul : ∀ σ τ : SSGRoute.GalQ, x (σ * τ) = x σ + (restrict K σ) • x τ)
    (hopen : IsOpen (ψ.ker : Set SSGRoute.GalQ))
    (hxloc : SSGRoute.IsLocConstOn ⊤ x)
    (hsurj : Function.Surjective (flowTwistEHom p K n i j x ψ hψ hxmul)) :
    SSGRoute.IsFlowSolution p K n (tauSucc i j).1 (tauSucc i j).2
      (flowTwistEHom p K n i j x ψ hψ hxmul) := by
  refine ⟨hsurj, ?_, ?_⟩
  · have hxmul' : ∀ σ τ : SSGRoute.GalQ,
        (fun θ => Additive.toMul (x θ)) (σ * τ) =
          (fun θ => Additive.toMul (x θ)) σ * (restrict K σ) • (fun θ => Additive.toMul (x θ)) τ :=
      fun σ τ => by
        show Additive.toMul (x (σ * τ)) =
          Additive.toMul (x σ) * (restrict K σ) • Additive.toMul (x τ)
        rw [hxmul σ τ]
        rfl
    have hxloc' : SSGRoute.IsLocConstOn ⊤ (fun θ => Additive.toMul (x θ)) := by
      obtain ⟨U, hU, hU'⟩ := hxloc
      exact ⟨U, hU, fun g hg u hu huH => by
        have := hU' g hg u hu huH
        show Additive.toMul (x (g * u)) = Additive.toMul (x g)
        rw [this]⟩
    have h := flowTwist_isOpen_ker p K n i j (fun σ => Additive.toMul (x σ)) ψ hψ hxmul'
      hopen hxloc'
    simpa [flowTwistHom, flowTwistEHom] using h
  · intro σ
    rw [flowTwistEHom_apply, flowQuot_flowTwistE]
    exact hψ σ



/-- **Assembly of Step 4 of Theorem 15.** -/
theorem isScholzSolution_flowTwistEHom (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K]
    (n i j : ℕ)
    (φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (hφsurj : Function.Surjective φ)
    (hφquot : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n i j (φ σ) = restrict K σ)
    (hψquot : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (ψ σ) = restrict K σ)
    (hψT1 : ∀ A : ValuationSubring SSGRoute.QBar, IsT1Place p K A →
      ∀ σ ∈ decomp ℚ A, σ ∈ K.fixingSubgroup → ψ σ = 1)
    (hψinv : ∀ c : SSGRoute.GalQ, c ^ 2 = 1 → c ∈ K.fixingSubgroup → ψ c = 1)
    (hψprop : ∀ A : ValuationSubring SSGRoute.QBar, IsFinPlace ℚ A →
      (∃ σ, IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ ψ σ ≠ 1) →
      (∀ σ ∈ decomp ℚ A, σ ∈ K.fixingSubgroup) ∧
      ((∀ σ ∈ decomp ℚ A, φ σ = 1) ∨
        (IsCyclic ((decomp ℚ A).map ψ) ∧ ∀ σ ∈ decomp ℚ A, ∃ τ, IsInertia ℚ A τ ∧ ψ τ = ψ σ)))
    (hxmul : ∀ σ τ : SSGRoute.GalQ, x (σ * τ) = x σ + (restrict K σ) • x τ)
    (hxloc : SSGRoute.IsLocConstOn ⊤ x)
    (hx0T1 : ∀ A : ValuationSubring SSGRoute.QBar, IsT1Place p K A →
      SSGRoute.IsCoboundaryOn (restrict K) (decomp ℚ A) x)
    (hx0inv : ∀ c : SSGRoute.GalQ, c ^ 2 = 1 →
      SSGRoute.IsCoboundaryOn (restrict K) (Subgroup.zpowers c) x)
    (hnew : ∀ A : ValuationSubring SSGRoute.QBar, IsFinPlace ℚ A →
      (∃ σ, IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ x σ ≠ 0) →
      (∀ σ ∈ decomp ℚ A, φ σ = 1))
    (hpropBranch : ∀ A : ValuationSubring SSGRoute.QBar, IsFinPlace ℚ A →
      (∃ σ, IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ ψ σ ≠ 1) →
      (∃ σ, IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧
        (flowTwistEHom p K n i j x ψ hψquot hxmul) σ ≠ 1) →
      (IsCyclic ((decomp ℚ A).map ψ) ∧
        ∀ σ ∈ decomp ℚ A, ∃ τ, IsInertia ℚ A τ ∧ ψ τ = ψ σ) →
      IsCyclic ((decomp ℚ A).map (flowTwistEHom p K n i j x ψ hψquot hxmul)) ∧
        ∀ σ ∈ decomp ℚ A, ∃ τ, IsInertia ℚ A τ ∧
          (flowTwistEHom p K n i j x ψ hψquot hxmul) τ =
          (flowTwistEHom p K n i j x ψ hψquot hxmul) σ)
    (hLift : ∀ σ, SSGRoute.LiftsFlowAt (ψ σ) (φ σ))
    (hNewLocal : ∀ A : ValuationSubring SSGRoute.QBar, IsFinPlace ℚ A →
      (∃ σ, IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧
        (flowTwistEHom p K n i j x ψ hψquot hxmul) σ ≠ 1) →
      (∀ σ ∈ decomp ℚ A, φ σ = 1) →
      IsCyclic ((decomp ℚ A).map (flowTwistEHom p K n i j x ψ hψquot hxmul)))
    (hopen : IsOpen (ψ.ker : Set SSGRoute.GalQ))
    (T0 : Finset (ValuationSubring SSGRoute.QBar))
    (hT0gen : (⨆ A ∈ T0, (decomp ℚ A).map ψ) = flowEKer p (K ≃ₐ[ℚ] K) n i j)
    (hT0x : ∀ A ∈ T0, ∀ σ ∈ decomp ℚ A, x σ = 0) :
    SSGRoute.IsScholzSolution p K n (tauSucc i j).1 (tauSucc i j).2
      (flowTwistEHom p K n i j x ψ hψquot hxmul) := by
  have hsurj : Function.Surjective (flowTwistEHom p K n i j x ψ hψquot hxmul) := by
    refine surjective_flowTwistEHom_of_iSup p K n i j x ψ φ hφsurj hψquot hxmul hLift
      (fun A : {A : ValuationSubring SSGRoute.QBar // A ∈ T0} => decomp ℚ A.1) ?_ ?_
    · have hconv : (⨆ A : {A : ValuationSubring SSGRoute.QBar // A ∈ T0},
            (decomp ℚ A.1).map ψ) = ⨆ A ∈ T0, (decomp ℚ A).map ψ :=
        le_antisymm
          (iSup_le fun A => le_iSup_of_le A.1 (le_iSup_of_le A.2 le_rfl))
          (iSup_le fun A => iSup_le fun hA => le_iSup_of_le ⟨A, hA⟩ le_rfl)
      rw [hconv, hT0gen]
    · intro A σ hσ
      exact hT0x A.1 A.2 σ hσ
  refine ⟨?_, ?_⟩
  · exact isFlowSolution_flowTwistEHom p K n i j x ψ hψquot hxmul hopen hxloc hsurj
  · refine scholzConditions_of_stageData p K n i j φ
      (flowTwistEHom p K n i j x ψ hψquot hxmul) ?_ ?_ ?_ ?_
    · intro A hA σ hσ hfix
      have hxσ : x σ = 0 := eq_zero_of_isCoboundaryOn p K n i j (hx0T1 A hA) σ hσ hfix
      rw [flowTwistEHom_apply, flowTwistE, flowTwist, hxσ, hψT1 A hA σ hσ hfix]
      simp
    · intro c hc1 hcK
      have hxc : x c = 0 :=
        eq_zero_of_isCoboundaryOn p K n i j (hx0inv c hc1) c (Subgroup.mem_zpowers c) hcK
      rw [flowTwistEHom_apply, flowTwistE, flowTwist, hxc, hψinv c hc1 hcK]
      simp
    · intro A hA hhyp
      by_cases hψram : ∃ σ, IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ ψ σ ≠ 1
      · obtain ⟨hDfix, hcase⟩ := hψprop A hA hψram
        refine ⟨hDfix, ?_⟩
        rcases hcase with h1 | h2
        · exact Or.inl h1
        · exact Or.inr (hpropBranch A hA hψram hhyp h2)
      · obtain ⟨σ₀, hσ₀I, hσ₀K, hσ₀ne⟩ := hhyp
        have hψσ₀ : ψ σ₀ = 1 := by
          by_contra h
          exact hψram ⟨σ₀, hσ₀I, hσ₀K, h⟩
        have hxσ₀ : x σ₀ ≠ 0 := by
          intro hx
          apply hσ₀ne
          rw [flowTwistEHom_apply, flowTwistE, flowTwist, hx, hψσ₀]
          simp
        have hφtriv : ∀ σ ∈ decomp ℚ A, φ σ = 1 := hnew A hA ⟨σ₀, hσ₀I, hσ₀K, hxσ₀⟩
        refine ⟨fun σ hσ => ?_, Or.inl hφtriv⟩
        exact mem_fixingSubgroup_of_restrict_eq_one K
          (by rw [← hφquot σ, hφtriv σ hσ]; rfl)
    · intro A hA hhyp hphi
      have hcyc : IsCyclic ((decomp ℚ A).map (flowTwistEHom p K n i j x ψ hψquot hxmul)) :=
        hNewLocal A hA hhyp hphi
      refine ⟨hcyc, ?_⟩
      exact inertia_map_eq_flowTwistEHom p K n i j x ψ φ hψquot hxmul hLift A hphi hcyc
        ⟨hhyp.choose, hhyp.choose_spec.1, hhyp.choose_spec.2.2⟩



/-! ## The finite set `T⁰` of Step 4 (proved, not arithmetic)

The paper's `T⁰` is a finite set of primes over which the level-`τ` field is completely decomposed,
whose decomposition groups generate the copy `flowEKer = E(n,τ)` of the graded piece inside
`Γ_{τ+1}` and whose local groups are cyclic.  The last two properties are a theorem about
decomposition groups (Chebotarev), not arithmetic: they are
`Work.SSGRoute.t0Generation_cyclic`.  What is left to the arithmetic about `T⁰` is only that the
twisting cocycle `x` can be chosen to vanish on its decomposition groups (the paper's "`x_p = 0` for
`p ∈ …∪ T⁰`"), which is a condition on `x` alone. -/

/-- The quotient `F(n)/F(n)^{(i,j)}` of the free operator group by a term of the refinement is
finite for a finite `G`; hence so is the flow group `Γ_n^{(i,j)}`.  (This is the finiteness
`t0Generation_cyclic` needs.) -/
theorem finite_flowQuotient_of_fintype (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
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

/-- The flow group `F(n)/F(n)^{(i,j)} ⋊ G` is finite for a finite `G`. -/
instance instFiniteFlowGroup (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
    (m i j : ℕ) : Finite (flowGroup p G m i j) := by
  haveI : Finite (flowQuotient p G m i j) := finite_flowQuotient_of_fintype p G m i j
  haveI : Finite (flowQuotient p G m i j × G) := inferInstance
  exact Finite.of_equiv _ (SemidirectProduct.equivProd.symm)

/-- **The finite set `T⁰` of Step 4 of Theorem 15.**  For a surjective level-`τ+1` solution `ψ` with
open kernel there is a finite set of places whose `ψ`-images generate the copy `flowEKer` of the
graded piece `E(n,τ)` and are cyclic; in particular every place of `T⁰` is completely decomposed in
the level-`τ` field, and the local group of `ψ` (hence of any twist of `ψ` by a cocycle vanishing
there) at such a place is cyclic of order dividing `p`. -/
theorem exists_T0_cyclic_of_surjective (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K] (n i j : ℕ)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (hopen : IsOpen (ψ.ker : Set SSGRoute.GalQ)) (hsurj : Function.Surjective ψ) :
    ∃ T0 : Finset (ValuationSubring SSGRoute.QBar),
      (⨆ A ∈ T0, (decomp ℚ A).map ψ) = flowEKer p (K ≃ₐ[ℚ] K) n i j ∧
      (∀ A ∈ T0, IsCyclic ((decomp ℚ A).map ψ)) :=
  t0Generation_cyclic (flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2) ψ hopen hsurj
    (flowEKer p (K ≃ₐ[ℚ] K) n i j)


/-! ## The target: Step 4 of Theorem 15 -/

/-- **The output of the Step-4 shrinking** (SW pp. 30–31).  The level-`n` solutions `φ` (at `τ`) and
`ψ` (at `τ+1`) with their stage-3 clauses, a finite set `T⁰` of primes whose decomposition groups
generate `flowEKer` under `ψ`, and a class `x ∈ H¹(k_S|K, E(n,τ))` which is a `1`-cocycle for the
`G(K/ℚ)`-action, locally constant, vanishing on `T⁰`, such that the twist of `ψ` by `x` has cyclic
(hence cyclic and totally ramified) local groups at the places of new ramification.

This is (definitionally) the conclusion of the sibling node `Work.SSGRoute.step4_shrunk_input`; the
parameters `hj`, `hji`, `hμ` and the hypothesis `hP` are needed only to *produce* the data, not to
state it, which is why they are not part of the predicate. -/
def Step4Input (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K] (n i j : ℕ) : Prop :=
  ∃ (φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (hψquot : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (ψ σ) =
      Work.SSGRoute.restrict K σ)
    (T0 : Finset (ValuationSubring SSGRoute.QBar))
    (x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (hxmul : ∀ σ τ : SSGRoute.GalQ, x (σ * τ) = x σ + (Work.SSGRoute.restrict K σ) • x τ),
      SSGRoute.IsScholzSolution p K n i j φ ∧ SSGRoute.LiftsFlow ψ φ ∧
      IsOpen (ψ.ker : Set SSGRoute.GalQ) ∧
      (∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsT1Place p K A →
        ∀ σ ∈ SSGRoute.decomp ℚ A, σ ∈ K.fixingSubgroup → ψ σ = 1) ∧
      (∀ c : SSGRoute.GalQ, c ^ 2 = 1 → c ∈ K.fixingSubgroup → ψ c = 1) ∧
      (∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ A →
        (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ ψ σ ≠ 1) →
        (∀ σ ∈ SSGRoute.decomp ℚ A, σ ∈ K.fixingSubgroup) ∧
        ((∀ σ ∈ SSGRoute.decomp ℚ A, φ σ = 1) ∨
          (IsCyclic ((SSGRoute.decomp ℚ A).map ψ) ∧
            ∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧ ψ τ = ψ σ))) ∧
      SSGRoute.IsLocConstOn ⊤ x ∧
      (∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsT1Place p K A →
        SSGRoute.IsCoboundaryOn (Work.SSGRoute.restrict K) (SSGRoute.decomp ℚ A) x) ∧
      (∀ c : SSGRoute.GalQ, c ^ 2 = 1 →
        SSGRoute.IsCoboundaryOn (Work.SSGRoute.restrict K) (Subgroup.zpowers c) x) ∧
      (∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ A →
        (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ x σ ≠ 0) →
        (∀ σ ∈ SSGRoute.decomp ℚ A, φ σ = 1)) ∧
      (∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ A → A ∉ T0 →
        (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧
          (Work.SSGRoute.flowTwistEHom p K n i j x ψ hψquot hxmul) σ ≠ 1) →
        (∀ σ ∈ SSGRoute.decomp ℚ A, φ σ = 1) →
        IsCyclic ((SSGRoute.decomp ℚ A).map
          (Work.SSGRoute.flowTwistEHom p K n i j x ψ hψquot hxmul))) ∧
      (∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ A →
        (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ ψ σ ≠ 1) →
        (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧
          (Work.SSGRoute.flowTwistEHom p K n i j x ψ hψquot hxmul) σ ≠ 1) →
        (IsCyclic ((SSGRoute.decomp ℚ A).map ψ) ∧
          ∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧ ψ τ = ψ σ) →
        IsCyclic ((SSGRoute.decomp ℚ A).map
            (Work.SSGRoute.flowTwistEHom p K n i j x ψ hψquot hxmul)) ∧
          ∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧
            (Work.SSGRoute.flowTwistEHom p K n i j x ψ hψquot hxmul) τ =
            (Work.SSGRoute.flowTwistEHom p K n i j x ψ hψquot hxmul) σ) ∧
      (⨆ A ∈ T0, (SSGRoute.decomp ℚ A).map ψ) = Work.SSGRoute.flowEKer p (K ≃ₐ[ℚ] K) n i j ∧
      (∀ A ∈ T0, ∀ σ ∈ SSGRoute.decomp ℚ A, x σ = 0) ∧
      (∀ A ∈ T0, IsCyclic ((SSGRoute.decomp ℚ A).map ψ))

/-- **Step 4 of Theorem 15 from the arithmetic input.**  Everything except the arithmetic: the twist
of `ψ` by `x` is a Scholz solution at `τ + 1`. -/
theorem scholz_succ_of_step4Input (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)
    (hμ : SSGRoute.HasRootsOfUnity p K i)
    (hP : ∀ m : ℕ, 1 ≤ m → SSGRoute.IsProperStage p K m i j)
    (n : ℕ) (hn : 1 ≤ n) (harith : Step4Input p K n i j) :
    ∃ ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2,
      SSGRoute.IsScholzSolution p K n (tauSucc i j).1 (tauSucc i j).2 ψ := by
  obtain ⟨φ, ψ, hψquot, T0, x, hxmul, hφ, hLift, hopen, hT1, hInv, hProp, hxloc,
    hx0T1, hx0inv, hnew, hNewLocal, hpropBranch, hT0gen, hT0x, hT0cyc⟩ := harith
  -- at the primes of `T⁰` the cocycle `x` vanishes, so the twist has the local group of `ψ` there,
  -- which is cyclic; the paper uses these primes for *properness* and not for the local conditions.
  have hNewLocalFull : ∀ A : ValuationSubring SSGRoute.QBar, IsFinPlace ℚ A →
      (∃ σ, IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧
        (flowTwistEHom p K n i j x ψ hψquot hxmul) σ ≠ 1) →
      (∀ σ ∈ decomp ℚ A, φ σ = 1) →
      IsCyclic ((decomp ℚ A).map (flowTwistEHom p K n i j x ψ hψquot hxmul)) := by
    intro A hA hram hφ1
    by_cases hAT : A ∈ T0
    · exact isCyclic_map_flowTwistEHom_of_x_eq_zero p K n i j x ψ hψquot hxmul
        (hT0x A hAT) (hT0cyc A hAT)
    · exact hNewLocal A hA hAT hram hφ1
  exact ⟨flowTwistEHom p K n i j x ψ hψquot hxmul,
    isScholzSolution_flowTwistEHom p K n i j φ ψ x hφ.1.1 hφ.1.2.2 hψquot hT1 hInv hProp
      hxmul hxloc hx0T1 hx0inv hnew hpropBranch hLift hNewLocalFull hopen T0 hT0gen hT0x⟩

/-- **The first block of the coker side is free**: from `hP` (a proper stage at every level `m`) one
gets the level `m`, the operator map `Φ : F(m) ↠ F(n)` and the level-`m` stage-3 data with no
arithmetic at all.  (In particular the level in `Step4CokerSide` may be taken to be `n` itself with
`Φ := OperatorMap.ofLe _ le_rfl`; the shrinking of `SSGRoute.coker_obstruction` may however need a
larger `m`.) -/
theorem exists_stage3_data_at_level (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (i j : ℕ)
    (hP : ∀ m : ℕ, 1 ≤ m → SSGRoute.IsProperStage p K m i j) (n : ℕ) (hn : 1 ≤ n) :
    ∃ (m : ℕ) (_ : 1 ≤ m) (_ : n ≤ m)
      (Φ : OperatorMap (K ≃ₐ[ℚ] K) m n)
      (φm : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m i j)
      (ψm : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2),
      SSGRoute.IsProperStageData p K m i j φm ψm := by
  obtain ⟨φm, ψm, hdata⟩ := exists_data_of_isProperStage p K n i j (hP n hn)
  exact ⟨n, hn, le_rfl, OperatorMap.ofLe (K ≃ₐ[ℚ] K) le_rfl, φm, ψm, hdata⟩

/-! ## An ingredient of the arithmetic: a section of `restrictNormalHom`

Both arithmetic inputs (`SSGRoute.coker_obstruction` in its naturality clause and
`SSGRoute.shafarevich_theorem13`) require a *section* `sec` of the restriction map
`AlgEquiv.restrictNormalHom K : G_ℚ → Gal(K/ℚ)`.  It exists by `Normal ℚ K` (and `Normal ℚ ℚ̄`);
this is the only place where the `IsAlgClosure` instance on `ℚ̄` has to be produced by hand
(Mathlib's instance is registered behind a transparency option, see
`Submission/Work/SSGRoute/flowKernel_fixedField.lean`). -/

set_option linter.style.haveILetI false in
theorem exists_section_restrict (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K]
    [Normal ℚ K] :
    ∃ sec : (K ≃ₐ[ℚ] K) → SSGRoute.GalQ, ∀ s, AlgEquiv.restrictNormalHom K (sec s) = s := by
  have : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ
  have : Normal ℚ SSGRoute.QBar := inferInstance
  have hsurj : Function.Surjective (AlgEquiv.restrictNormalHom K) :=
    AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := K) (E := SSGRoute.QBar)
  exact ⟨fun s => Classical.choose (hsurj s), fun s => Classical.choose_spec (hsurj s)⟩

/-- A section of `restrictNormalHom K` that is normalised by `sec 1 = 1` (multiply a given one by
`(sec 1)⁻¹`; this is the normalisation used in the paper so that the `s = 1` term of the formal
corestriction sum is `y δ` itself). -/
theorem exists_section_restrict_one (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K]
    [Normal ℚ K] :
    ∃ sec : (K ≃ₐ[ℚ] K) → SSGRoute.GalQ,
      (∀ s, AlgEquiv.restrictNormalHom K (sec s) = s) ∧ sec 1 = 1 := by
  obtain ⟨sec, hsec⟩ := exists_section_restrict K
  refine ⟨fun s => sec s * (sec 1)⁻¹, ?_, ?_⟩
  · intro s
    show AlgEquiv.restrictNormalHom K (sec s * (sec 1)⁻¹) = s
    rw [map_mul, map_inv, hsec s, hsec 1, inv_one, mul_one]
  · show sec 1 * (sec 1)⁻¹ = (1 : SSGRoute.GalQ)
    rw [mul_inv_cancel]

/-! ## An ingredient of the arithmetic: the formal corestriction is the identity on `D_A`

The clauses `hxsplit`, `hreal` and `hyT0` of `Work.SSGRoute.Step4CokerSide` all evaluate the formal
corestriction `∑_s s • y(sec(s)⁻¹ δ sec(s))` at a place `A ∈ S` that splits in `K`, where
`D_A ≤ G_K` acts trivially.  Since `S` consists of pairwise non-conjugate places and `sec` can be
normalised by `sec 1 = 1`, the `s ≠ 1` terms live at the *conjugate* places `(sec s)⁻¹ • A`, which
are not in `S`; when `y` vanishes there the sum collapses to its `s = 1` term and equals `y δ`.  The
three lemmas below are this collapse, the propagation of a vanishing to conjugates (which produces
the hypothesis of the collapse from `y = 0` on `D_A`), and the resulting `T⁰` clause `hyT0`. -/

/-- A `1`-cocycle for the `Gal(K/ℚ)`-action which vanishes on a subgroup `H ≤ G_K` vanishes on
every `G_ℚ`-conjugate of `H`. -/
theorem cocycle_conj_eq_zero (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K]
    (n i j : ℕ) (y : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (hy : ∀ σ τ : SSGRoute.GalQ, y (σ * τ) = y σ + (Work.SSGRoute.restrict K σ) • y τ)
    (H : Subgroup SSGRoute.GalQ) (hH : H ≤ K.fixingSubgroup) (h0 : ∀ δ ∈ H, y δ = 0) :
    ∀ τ : SSGRoute.GalQ, ∀ δ ∈ H, y (τ * δ * τ⁻¹) = 0 := by
  intro τ δ hδ
  have h1 : y 1 = 0 := by
    have h := hy 1 1
    rw [mul_one, map_one, one_smul] at h
    have h' : y 1 + y 1 = y 1 + 0 := by rw [add_zero, ← h]
    exact add_left_cancel h'
  have hτ : (Work.SSGRoute.restrict K τ) • y τ⁻¹ = - y τ := by
    have h := hy τ τ⁻¹
    rw [mul_inv_cancel, h1] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  have hδ1 : Work.SSGRoute.restrict K δ = 1 :=
    (Work.SSGRoute.step4_restrict_eq_one_iff K δ).mpr (hH hδ)
  calc y (τ * δ * τ⁻¹)
      = y (τ * δ) + (Work.SSGRoute.restrict K (τ * δ)) • y τ⁻¹ := hy (τ * δ) τ⁻¹
    _ = (y τ + (Work.SSGRoute.restrict K τ) • y δ)
          + (Work.SSGRoute.restrict K (τ * δ)) • y τ⁻¹ := by rw [hy τ δ]
    _ = (y τ + 0) + (Work.SSGRoute.restrict K τ) • y τ⁻¹ := by
        rw [h0 δ hδ, smul_zero, map_mul, hδ1, mul_one]
    _ = y τ + (Work.SSGRoute.restrict K τ) • y τ⁻¹ := by rw [add_zero]
    _ = y τ + (- y τ) := by rw [hτ]
    _ = 0 := add_neg_cancel _

/-- At a place `A` that splits in `K` the translate `(sec s)⁻¹ • A` is `A` only for `s = 1`. -/
theorem smul_inv_sec_ne_self (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K]
    (A : ValuationSubring SSGRoute.QBar) (hsplit : SSGRoute.IsSplitIn ℚ K A)
    (sec : (K ≃ₐ[ℚ] K) → SSGRoute.GalQ)
    (hsec : ∀ s, Work.SSGRoute.restrict K (sec s) = s) :
    ∀ s : K ≃ₐ[ℚ] K, s ≠ 1 → (sec s)⁻¹ • A ≠ A := by
  intro s hs h
  have hmem : (sec s)⁻¹ ∈ SSGRoute.decomp ℚ A := by
    show (sec s)⁻¹ ∈ MulAction.stabilizer SSGRoute.GalQ A
    exact MulAction.mem_stabilizer_iff.mpr h
  have hK : (sec s)⁻¹ ∈ K.fixingSubgroup := hsplit hmem
  have h1 : Work.SSGRoute.restrict K (sec s)⁻¹ = 1 :=
    (Work.SSGRoute.step4_restrict_eq_one_iff K _).mpr hK
  rw [map_inv, hsec s, inv_eq_one] at h1
  exact hs h1

/-- **The formal corestriction is the identity on `D_A`** at a place `A` whose `s ≠ 1` conjugates
carry the vanishing datum. -/
theorem corestriction_eq_self_on_decomp (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K]
    (n i j : ℕ) (A : ValuationSubring SSGRoute.QBar)
    (sec : (K ≃ₐ[ℚ] K) → SSGRoute.GalQ) (hsec1 : sec 1 = 1)
    (y : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (hy : ∀ s : K ≃ₐ[ℚ] K, s ≠ 1 →
      ∀ τ ∈ SSGRoute.decomp ℚ ((sec s)⁻¹ • A), y τ = 0)
    (δ : SSGRoute.GalQ) (hδ : δ ∈ SSGRoute.decomp ℚ A) :
    (∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹ * δ * sec s)) = y δ := by
  have hsum : (∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹ * δ * sec s)) =
      (1 : K ≃ₐ[ℚ] K) • y ((sec 1)⁻¹ * δ * sec 1) :=
    Finset.sum_eq_single 1 (fun s _ hs => by
      have hmem : (sec s)⁻¹ * δ * sec s ∈ SSGRoute.decomp ℚ ((sec s)⁻¹ • A) := by
        rw [Work.SSGRoute.decomp_conj A (sec s)⁻¹]
        exact Subgroup.mem_map.mpr ⟨δ, hδ, by simp⟩
      rw [hy s hs _ hmem, smul_zero]) (fun h1 => absurd (Finset.mem_univ _) h1)
  rw [hsum, hsec1, inv_one, one_mul, mul_one, one_smul]

/-- **The `T⁰` clause `hyT0` of the coker side**: if `y` is a cocycle for the `Gal(K/ℚ)`-action and
vanishes on `D_A` at a place `A` that splits in `K`, then the formal corestriction vanishes on
`D_A`. -/
theorem corestriction_eq_zero_on_decomp_of_eq_zero (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K]
    (n i j : ℕ) (A : ValuationSubring SSGRoute.QBar) (hsplit : SSGRoute.IsSplitIn ℚ K A)
    (sec : (K ≃ₐ[ℚ] K) → SSGRoute.GalQ) (hsec1 : sec 1 = 1)
    (y : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (hy : ∀ σ τ : SSGRoute.GalQ, y (σ * τ) = y σ + (Work.SSGRoute.restrict K σ) • y τ)
    (h0 : ∀ δ ∈ SSGRoute.decomp ℚ A, y δ = 0)
    (σ : SSGRoute.GalQ) (hσ : σ ∈ SSGRoute.decomp ℚ A) :
    (∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹ * σ * sec s)) = 0 := by
  have hconj : ∀ τ : SSGRoute.GalQ, ∀ δ ∈ SSGRoute.decomp ℚ A, y (τ * δ * τ⁻¹) = 0 :=
    cocycle_conj_eq_zero p K n i j y hy (SSGRoute.decomp ℚ A) hsplit h0
  have hvan : ∀ s : K ≃ₐ[ℚ] K, s ≠ 1 →
      ∀ τ ∈ SSGRoute.decomp ℚ ((sec s)⁻¹ • A), y τ = 0 := by
    intro s hs τ hτ
    rw [Work.SSGRoute.decomp_conj A (sec s)⁻¹] at hτ
    obtain ⟨δ, hδ, hδτ⟩ := Subgroup.mem_map.mp hτ
    rw [← hδτ]
    exact hconj (sec s)⁻¹ δ hδ
  rw [corestriction_eq_self_on_decomp p K n i j A sec hsec1 y hvan σ hσ, h0 σ hσ]

end Work.SSGRoute
