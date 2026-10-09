import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ProperStageDefs
import Submission.Work.SSGRoute.properStageAssemblyData
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/SSGRoute/DESIGN.md first (orchestrator design; your lemma is one node of its DAG). Shared vocabulary: Submission/Work/SSGRoute/Interfaces.lean (namespace SSGRoute; do NOT edit — put any new shared definition in your own file). The proved class-field-theory library is available as NK.* (Chebotarev: NK.NUV2.chebotarev_all0 with hFC := NK.CFTLib.fundamentalClassElement; local reciprocity NK.NUV2.kernelCondition_all; existence NK.CFTLib.Existence.classField_exists_primeIndex (unramified only); Hasse–Brauer–Noether NK.GlobalCFTdeep.hbnUnits; NK.KC.localBaseChangeInput_of_kc; NK.HR2.transferStepOnePlace), all axiom-clean. NEVER use Work.HilbertSymbol.GrunwaldWang (false as written). Siblings run in parallel; import them when they land.

# Guidance: Step 3 of the proof of Theorem 15 — a proper lift satisfying (i), ramification controlled

From level-m data of `IsSolvableStage` (φ_m Scholz, ψ_m lift, split over T¹), produce level-n data
`IsProperStage`: ψ̃ = ε · (flowGroupMap⁺ Φ ∘ ψ_m) with ε a global E_n-valued cocycle.

**Sketch** (paper pp. 26–30).
1. Solutions of the τ+1 problem form a torsor under Z¹(G_ℚ, E). Use `Work.Properness.exists_unique_smulLift`
   and `liftClass_eq_iff`. Properness: `Work.Properness.isProper_of_closure_iUnion_map_eq`, which is
   Frattini for τ ≥ (2,1).
2. Local targets at level m:
   - T⁰ (split in N_m): unramified maps generating E_m, from `local_tame_lifting`.1.
   - T¹: the class making ψ split, which exists because the local extension splits (`IsSolvableStage`).
   - T² = Ram(N_m/K): subtract the unramified part (D_N·I = D since totally ramified).
   - T³ = new ramification of ψ_m: kill it (H¹(D) → H¹(I)^D onto, from D/I ≅ Ẑ).
   - ∞: anything, e.g. 0.
3. Apply `SSGRoute.coker_obstruction` with k = ℚ, N = N_m (the fixed field of ker φ_m;
   Gal(N_m/ℚ) ≅ Γ_m via φ_m), E = E_m, T = μ_p^∨, S = one place per prime of T.
   - Transport x ∈ H₁(Gal(N_m/ℚ), E_m ⊗ T) to `groupHomology.H1 (flowRep p G m i j T)`.
   - Kill it with `exists_shrinking_H1_semidirect_paper` (i ≥ 2), or with `exists_shrinking_Hm2_tate` +
     `exists_bridge` at i = 1, where Γ = G.
   - Then feed N₂ = N_n, q = flowGroupMap, F = `flowRepMap`. `flowZMap` is `(groupHomology.map … 1).hom`,
     the same shape as in the statement.
4. Twist, and check the `IsProperStage` clauses. The new ramification lies only in cs(N_n) ⊆ cs(K)
   (first disjunct). At T² the local extension is cyclic totally ramified (second disjunct). SW's remark
   "one easily verifies" is exactly this check.

**Imports.** Interfaces, `SSGRoute.coker_obstruction`, `SSGRoute.local_tame_lifting`,
`SSGRoute.prop5Data_exists`, `Submission.Work.Properness.All`, `Submission.Work.AbsoluteGalois.All`.

Delegate: the torsor/twist lemma, the four local choices, the transport of Gal(N_m/ℚ) to flowGroup (with the
Rep identification), and the final clause check.

---

## What this file does

The level-`n` construction of Step 3 (the four local choices at `T⁰, T¹, T², T³`, the global
realisation of the local data by `SSGRoute.coker_obstruction` together with the shrinking of
`Work.CohomologicalShrinking.exists_shrinking_H1_semidirect_paper`, the twist, and the check of the
clauses) is isolated as the sibling lemma `Work.SSGRoute.properStageAssemblyData`, which delivers a
level-`n` solution `ψ` lifting `(flowGroupMap Φ) ∘ φm`, with `IsOpen ψ.ker`, the local conditions
(i), (ii) of Theorem 15, and the `T⁰`-generation of the kernel copy `flowEKer p G n i j` of
`E p G n i j` inside `Γ'_n`.

This file performs the remaining, purely group-theoretic steps:

* `flowGroupProj_comp_of_LiftsFlow`: a lift `ψ` of `φ` factors through the level projection
  `flowGroupProj : Γ'_n →* Γ_n` constructed in `ProperStageDefs`;
* `Work.SSGRoute.surjective_of_iSup_map_eq_flowEKer` (from `ProperStageDefs`) then gives the
  properness of `ψ` from the `T⁰`-generation;
* `scholz_pushdown` (below) gives that the pushed-down level-`n` solution
  `(flowGroupMap Φ) ∘ φm` is again a Scholz solution.
-/

namespace Work.SSGRoute

open SSGRoute
open Work.CohomologicalShrinking

open scoped TensorProduct

set_option maxHeartbeats 800000

variable {p₀ : ℕ} {G₀ : Type*} [Group G₀]

/-- The image of a cyclic subgroup under a homomorphism is cyclic. -/
theorem isCyclic_map_of_isCyclic {N P : Type*} [Group N] [Group P] (f : N →* P) (H : Subgroup N)
    (h : IsCyclic ↥H) : IsCyclic ↥(Subgroup.map f H) := by
  let F : ↥H →* ↥(Subgroup.map f H) :=
    { toFun := fun x => ⟨f x.1, Subgroup.mem_map_of_mem f x.2⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun a b => Subtype.ext (map_mul f a.1 b.1) }
  have hsurj : Function.Surjective F := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, rfl⟩
  exact isCyclic_of_surjective F hsurj

/-- `flowQuotMap` is surjective (it is induced by a surjective operator map). -/
theorem flowQuotMap_surjective_p {m n : ℕ} (i j : ℕ) (Φ : OperatorMap G₀ m n) :
    Function.Surjective (flowQuotMap p₀ G₀ i j Φ) := by
  intro y
  induction y using QuotientGroup.induction_on with
  | H x =>
    obtain ⟨z, hz⟩ := Φ.surjective x.1
    refine ⟨QuotientGroup.mk' _ ⟨z, Subgroup.mem_top z⟩, ?_⟩
    rw [flowQuotMap_mk]
    exact congrArg (QuotientGroup.mk' _) (Subtype.ext hz)

/-- `flowGroupMap` is surjective. -/
theorem flowGroupMap_surjective_p {m n : ℕ} (i j : ℕ) (Φ : OperatorMap G₀ m n) :
    Function.Surjective (flowGroupMap p₀ G₀ i j Φ) := by
  intro γ
  obtain ⟨x, hx⟩ := flowQuotMap_surjective_p (p₀ := p₀) i j Φ γ.left
  have key : flowGroupMap p₀ G₀ i j Φ (SemidirectProduct.mk x γ.right)
      = SemidirectProduct.mk ((flowQuotMap p₀ G₀ i j Φ) x) γ.right := by
    rw [flowGroupMap]
    refine SemidirectProduct.ext ?_ ?_
    · rw [SemidirectProduct.map_left]
    · rw [SemidirectProduct.map_right]; rfl
  exact ⟨SemidirectProduct.mk x γ.right, by rw [key, hx]⟩

/-- **Scholz solutions are stable under the rank change `F(m) ⇢ F(n)`.**  A surjective
`G`-operator homomorphism `Φ : F(m) ⇢ F(n)` induces `flowGroupMap Φ : Γ_m^τ →* Γ_n^τ`, and the
push-forward of a Scholz solution at level `m` is a Scholz solution at level `n`. -/
theorem scholz_pushdown (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K]
    {m n i j : ℕ} (Φ : OperatorMap (K ≃ₐ[ℚ] K) m n)
    (φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (hφ : SSGRoute.IsScholzSolution p K m i j φ) :
    SSGRoute.IsScholzSolution p K n i j ((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) := by
  obtain ⟨hflow, hsch⟩ := hφ
  obtain ⟨hsurj, hopen, hres⟩ := hflow
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact (flowGroupMap_surjective_p (p₀ := p) i j Φ).comp hsurj
  · refine Subgroup.isOpen_mono ?_ hopen
    intro σ hσ
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply] at hσ ⊢
    rw [hσ, map_one]
  · intro σ
    rw [MonoidHom.comp_apply, flowQuot_flowGroupMap]
    exact hres σ
  · intro A hA σ hσ hσK
    rw [MonoidHom.comp_apply, hsch.1 A hA σ hσ hσK, map_one]
  · intro c hc hcK
    rw [MonoidHom.comp_apply, hsch.2.1 c hc hcK, map_one]
  · intro A hA h
    obtain ⟨σ, hσ, hσK, hne⟩ := h
    have hne' : φ σ ≠ 1 := fun hc => hne (by rw [MonoidHom.comp_apply, hc, map_one])
    obtain ⟨h1, h2, h3⟩ := hsch.2.2 A hA ⟨σ, hσ, hσK, hne'⟩
    refine ⟨h1, ?_, ?_⟩
    · rw [← Subgroup.map_map (K := SSGRoute.decomp ℚ A) (f := φ)
        (g := flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ)]
      exact isCyclic_map_of_isCyclic _ _ h2
    · intro σ' hσ'
      obtain ⟨τ, hτ, hτφ⟩ := h3 σ' hσ'
      exact ⟨τ, hτ, by rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hτφ]⟩

/-- **A lift of a solution of the level-`τ` problem factors through the level projection**
`flowGroupProj : F(m)/F(m)^{(τ+1)} ⋊ G →* F(m)/F(m)^{(τ)} ⋊ G`. -/
theorem flowGroupProj_comp_of_LiftsFlow {p : ℕ} {K : IntermediateField ℚ SSGRoute.QBar}
    [Normal ℚ K] {m i j : ℕ}
    {ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2}
    {φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m i j}
    (h : SSGRoute.LiftsFlow ψ φ) :
    (flowGroupProj p (K ≃ₐ[ℚ] K) m i j).comp ψ = φ :=
  -- NOTE (memory): the *pointwise* form is taken from the sibling module
  -- (`flowGroupProj_eq_of_liftsFlowAt_local`); the direct `SemidirectProduct.ext` proof
  -- of this lemma made the elaboration of this file peak at ~19 GB (it forces the
  -- elaborator to unfold the `SemidirectProduct` action instance of `flowGroup` at the
  -- `tauSucc`-indexed level).  With the call below the whole file elaborates in ~15 s / 8 GB.
  MonoidHom.ext fun σ => flowGroupProj_eq_of_liftsFlowAt_local p K (h σ)

theorem properStage_of_solvableStage (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)
    (hμ : SSGRoute.HasRootsOfUnity p K i)
    (hS : ∀ m : ℕ, 1 ≤ m → SSGRoute.IsSolvableStage p K m i j)
    (n : ℕ) (hn : 1 ≤ n) :
    SSGRoute.IsProperStage p K n i j := by
  obtain ⟨m, _, hnm, φm, ψm, Φ, ψ, T0, hSchm, _, _, _, hLift, hOpen, hT1, hinv, hram, hgen⟩ :=
    properStageAssemblyData p K i j hj hji hμ hS n hn
  refine ⟨(flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φm, ψ,
    scholz_pushdown p K Φ φm hSchm, hLift, ⟨?_, hOpen, ?_⟩, hT1, hinv, hram⟩
  · -- properness of `ψ`, from the `T⁰`-generation of `flowEKer`
    have hProj : (flowGroupProj p (K ≃ₐ[ℚ] K) n i j).comp ψ
        = (flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φm :=
      flowGroupProj_comp_of_LiftsFlow hLift
    refine surjective_of_iSup_map_eq_flowEKer (p := p) (G := K ≃ₐ[ℚ] K) (m := n) (i := i) (j := j)
      (H0 := SSGRoute.GalQ) (φ := (flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φm) ?_ ?_
      (fun A : ↥T0 => SSGRoute.decomp ℚ (A : ValuationSubring SSGRoute.QBar)) ?_
    · intro σ
      exact DFunLike.congr_fun hProj σ
    · exact (flowGroupMap_surjective_p (p₀ := p) i j Φ).comp hSchm.1.1
    · rw [← hgen]
      exact (iSup_subtype' (p := fun A : ValuationSubring SSGRoute.QBar => A ∈ T0)
        (f := fun A _ => (SSGRoute.decomp ℚ A).map ψ)).symm
  · -- the solution is compatible with the restriction to `K`
    intro σ
    show (ψ σ).right = AlgEquiv.restrictNormalHom K σ
    have h1 : (ψ σ).right = (φm σ).right := by
      rw [(hLift σ).1]
      rfl
    rw [h1]
    exact hSchm.1.2.2 σ

end Work.SSGRoute
