import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.Have
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
import Submission.Work.SSGRoute.clauseData_conj_transfer_T1
import Submission.Work.SSGRoute.coker_obstruction
import Submission.Work.SSGRoute.evCupFun_isCocycle2On
import Submission.Work.SSGRoute.flowEKer_equiv_refinedQuotient
import Submission.Work.SSGRoute.gradedMapMul_surjective
import Submission.Work.SSGRoute.involutions_eq_one_or_conjugate
import Submission.Work.SSGRoute.prop5Data_exists
import Submission.Work.SSGRoute.ramifiedPlaces_finite
import Submission.Work.SSGRoute.stage3KillInertiaTarget
import Submission.Work.SSGRoute.stage3Shrinking_i_one
import Submission.Work.SSGRoute.stage3T0Data
import Submission.Work.SSGRoute.stage3T2LocalTarget
import Submission.Work.SSGRoute.t0Generation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-! ## Session 13 note: `G1` is reduced to two named inputs (`HRec/PartA.lean`)

This node's only two `sorryAx` sources (re-measured 2026-09-29 with the `#eval!` proof-term
traversal, which visited 102514 constants) are

* `Work.SSGRoute.canonical_localPairing_with_reciprocity` (`G1`,
  `Submission/Work/SSGRoute/canonical_localPairing_with_reciprocity.lean`), and
* `Work.SSGRoute.PT.pt_counting_identity_h1` (`COUNT`,
  `Submission/Work/SSGRoute/PT/pt_counting_identity_h1.lean`, the single `sorry` at its end: the
  exactness `W^⊥ ⊆ V`, i.e. Milne *ADT* I.4.10(b)).

(`Work.SSGRoute.PT.pt_selmer_counting_identity` is *not* in the proof-term closure: the live file
`PT/pt_selmer_counting_identity.lean` still ends in a bare `sorry`, but `pt_selmer_relaxed` consumes
`PT.pt_counting_identity_h1` instead, and only the latter is reached.  Both are the same
proposition.)  The route and the exact residual inputs are recorded in
`Submission/Work/SSGRoute/ACTION_theorem15_route.md` and `PT/PT_COUNTING_IDENTITY_STATUS.md`; the
counting identity is assembled from the pipeline pairing `pair, hloc, hrec` (= `G1`-data) plus the
relaxation output of the middle exactness by
`PT.countingIdentity_of_localAxioms_and_relaxationOutput`
(`Submission/Work/SSGRoute/PT/pt_counting_of_relaxation.lean`).

`G1`'s reciprocity clause (7) is now **proved**, and the statement of `G1` is reduced to two named
inputs, in the new module `Submission/Work/SSGRoute/HRec/PartA.lean`
(`Submission.Work.SSGRoute.HRec.PartA`, all declarations axiom-clean):

* `Work.SSGRoute.HRec.hrecJoint_invQ_of_archConsistent` — clause (7) of `G1` for the explicit
  family `pairOfInvH invQ` of `HRec/HrecDefs.lean`, from `ArchConsistent` alone;
* `Work.SSGRoute.HRec.archConsistent_of_ne_two` — `ArchConsistent` is **automatic for odd `p`**, so
  for odd `p` clause (7) needs *no arithmetic*;
* `Work.SSGRoute.HRec.canonical_localPairing_with_reciprocity_of_ne_two_and_h4` — for odd `p`, `G1`
  follows from its perfectness clause `h4` (local Tate duality for the cup family) alone;
* `Work.SSGRoute.HRec.canonical_localPairing_with_reciprocity_of_canonicalInvariant` — in general,
  `G1` follows from `hcan` = `∃ χ, recipSpan ≤ ker χ ∧ χ (0,1) = 1 ∧ FinNondeg χ` (the canonical
  invariant family) together with `h4`.

The remaining `G1` obligations are therefore: (i) the canonical invariant family `hcan` — design
node `B8` at `p = 2` (delegated as `Work.SSGRoute.exists_nondeg_of_parity2`, from `Parity2` =
Hilbert reciprocity at `2`, via `PTCore.h2loc_mup_finrank`) and §5 of `HRec/HRECJOINT_DESIGN.md` for
odd `p`; (ii) `h4` = local Tate duality for the cup family.  Nothing in *this* file has to change.
-/

/-! ## Session 4 note (2026-10-03): the cone is now a **single** hub, `G1⁺`

Re-measured with `_hw2/taintNode.lean` (proof-term walk, 102 563 constants): the node's reachable
`sorryAx` sources are now exactly

    HOLE Work.SSGRoute.PT.canonical_localPairing_reciprocity_converse      -- G1⁺

The `G1` hole is gone: this file's proof now calls
`Work.SSGRoute.coker_obstruction_G1plus` (`Submission/Work/SSGRoute/NodeShim/cokerObstructionG1plus.lean`),
a *verbatim copy* of `Work.SSGRoute.coker_obstruction` that extracts the canonical pairing from `G1⁺`
instead of from the `G1` declaration.  The statements of the two `coker_obstruction`s are identical,
so this is a drop-in replacement; its effect is that the node no longer depends on the `G1` file
(whose own `sorry` therefore needs no edit for *this* node to clear).  The identification
`G1 = (G1⁺).1` is *certified* by
`Work.SSGRoute.canonical_localPairing_with_reciprocity_of_G1plus`
(`NodeShim/canonicalPairingOfG1plus.lean`), which is `G1`'s statement verbatim proved from `G1⁺`'s
first projection — so `G1⁺`'s clauses (1)–(7) really are `G1`'s clauses, up to defeq.

Consequence: **when `PT.canonical_localPairing_reciprocity_converse` becomes `sorry`-free, this node
is `declare_proven`-clean with no further edit to any file.**  (Any proof of `G1⁺` that still cites
one of the *sorried* `S1` stubs — `PT.pt_coherent_pTorsion_invariant`,
`PT/coherent_pTorsion_chi_k.lean` — would re-taint it; use the proved `PT.coherent_pTorsion_chi`
or `PT.coherent_pTorsion_chi_k_of_KΩ` instead.  See `PING_node_s4_cone_is_G1plus.md`.)
-/

/-! Guidance (from the requester, H2; Step 3 of Theorem 15, Schmidt–Wingberg arXiv:math/9809211 §5,
and `Submission/Work/SSGRoute/DESIGN.md`).

The conclusion is the level-`n` data produced by Step 3: from the level-`m` data of `hS m` (for a
suitably large `m`) produce an operator map `Φ : F(m) ⇢ F(n)` and a solution `ψ` at level `n` of the
`τ+1`-problem lifting `(flowGroupMap Φ) ∘ φm`, together with the local conditions (i), (ii) of
Theorem 15 and the `T⁰`-generation of `flowEKer p (K ≃ₐ[ℚ] K) n i j` (the copy of `E p G n i j`
inside the level-`n` group).  The caller then gets properness of `ψ` from
`Work.SSGRoute.surjective_of_iSup_map_eq_flowEKer` and the Scholz property of
`(flowGroupMap Φ) ∘ φm` from `Work.SSGRoute.scholzSolution_comp_flowGroupMap`.

Sketch (paper pp. 26–30).
1. Fix a large `m ≥ n` and take from `hS m` the Scholz solution `φm`, the lift `ψm` and the local
   splitting data at `T¹ = {places over Ram(K/ℚ) ∪ {p}}` (all hypotheses above).
2. Let `N_m` be the fixed field of `φm.ker` (so `Gal(N_m/ℚ) ≅ Γ_m` via `φm`) and `N_n` the fixed
   field of the level-`n` solution; then `K ≤ N_n ≤ N_m`.
3. Build the local datum `α` at a finite set `S` of places (one per conjugacy class, containing all
   places over `p` and all places ramified in `N_m`) and the set `C` of real places, with
   `T⁰ ⊆ cs(N_n|K)` (unramified maps generating `E(n,τ)`; Chebotarev via `NK.NUV2.chebotarev_all0`,
   and `local_tame_lifting`), `T¹` (the class making the twist split on `D_A ∩ G_K`, from
   `IsSolvableStage`), `T² = Ram(N_n|K)` (subtract the unramified part, `D/I ≅ Ẑ`) and `T³` (kill
   the ramification of `ψm`).  For the real places one involution suffices (all involutions of
   `G_ℚ` are conjugate).
4. Apply `SSGRoute.coker_obstruction` with `k = ℚ`, `N = N_m`, `E = E p G m i j`, `T = μ_p^∨`
   (`IsCyclotomicDual`), obtaining `x ∈ H₁(Gal(N_m/ℚ), E ⊗ T) ≅ H₁(flowRep p G m i j T)`.
5. Kill `x` with `Work.CohomologicalShrinking.exists_shrinking_H1_semidirect_paper` (`i ≥ 2`;
   needs `SSGRoute.prop5Data_exists`) or, at `i = 1`, with `exists_shrinking_Hm2_tate` +
   `exists_bridge`; the resulting `Φ : F(m) ⇢ F(n)` satisfies `flowZMap Φ T x = 0`, i.e.
   `(groupHomology.map q F 1).hom x = 0` for `N₂ = N_n`.
6. Feed `N₂ = N_n`, `q = flowGroupMap`, `F = flowRepMap` into `coker_obstruction`'s conclusion to get
   `ε : G_ℚ → E p G n i j` with the local coboundary conditions and vanishing on the inertia of
   places outside `S ∪ cs(N_n)`.
7. `ψ := ε · ((flowGroupMap Φ) ∘ ψm)` (the twist), and the clauses follow: at `T¹` the elements of
   `D_A ∩ G_K` act trivially on `E`, so the coboundary ambiguity disappears there; for involutions
   use the conjugacy of the real places; the new ramification lies in `cs(N_n) ⊆ cs(K)` (first
   disjunct) or is the tame cyclic totally ramified extension at `T²`; `T⁰` is the set of places
   whose images generate `flowEKer`.
-/
open SSGRoute
open Work.CohomologicalShrinking
open scoped TensorProduct

set_option maxHeartbeats 2000000

/-- **Naturality of the level projection in the rank.**  The level projection
`F(n)/F(n)^{(τ+1)} → F(n)/F(n)^{(τ)}` commutes with the rank-change map induced by a surjective
`G`-operator homomorphism `Φ : F(m) ⇢ F(n)`.  This is the identity used in Step 3 of Theorem 15 to
conclude that a rank-changed lift is again a lift. -/
theorem flowQuotientProj_comp_flowQuotMap (p : ℕ) (G : Type*) [Group G] {m n : ℕ}
    (i j : ℕ) (Φ : OperatorMap G m n) :
    (flowQuotientProj p G n i j).comp (flowQuotMap p G (tauSucc i j).1 (tauSucc i j).2 Φ)
      = (flowQuotMap p G i j Φ).comp (flowQuotientProj p G m i j) := by
  refine MonoidHom.ext fun x => ?_
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
    ((flowTerm p G m (tauSucc i j).1 (tauSucc i j).2).subgroupOf
      (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))) x
  simp only [MonoidHom.comp_apply, flowQuotMap_mk, flowQuotientProj_mk]
  rfl

/-- The same naturality for the semidirect products `F(m)/F(m)^{(ν)} ⋊ G`. -/
theorem flowGroupProj_comp_flowGroupMap (p : ℕ) (G : Type*) [Group G] {m n : ℕ}
    (i j : ℕ) (Φ : OperatorMap G m n) :
    (flowGroupProj p G n i j).comp (flowGroupMap p G (tauSucc i j).1 (tauSucc i j).2 Φ)
      = (flowGroupMap p G i j Φ).comp (flowGroupProj p G m i j) := by
  refine MonoidHom.ext fun x => ?_
  refine SemidirectProduct.ext ?_ ?_
  · show ((flowGroupProj p G n i j)
        ((flowGroupMap p G (tauSucc i j).1 (tauSucc i j).2 Φ) x)).left
      = ((flowGroupMap p G i j Φ) ((flowGroupProj p G m i j) x)).left
    simp only [flowGroupMap, flowGroupProj, SemidirectProduct.map_left]
    exact DFunLike.congr_fun (flowQuotientProj_comp_flowQuotMap p G i j Φ) x.left
  · show ((flowGroupProj p G n i j)
        ((flowGroupMap p G (tauSucc i j).1 (tauSucc i j).2 Φ) x)).right
      = ((flowGroupMap p G i j Φ) ((flowGroupProj p G m i j) x)).right
    simp only [flowGroupMap, flowGroupProj, SemidirectProduct.map_right]


/-- The level projection of the left factors `F(m)/F(m)^{(τ+1)} → F(m)/F(m)^{(τ)}` is surjective. -/
theorem flowQuotientProj_surjective_local (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    Function.Surjective (flowQuotientProj p G m i j) := by
  intro x
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective ((flowTerm p G m i j).subgroupOf ⊤) x
  exact ⟨QuotientGroup.mk' _ z, flowQuotientProj_mk p G m i j z⟩

/-- The level projection `Γ^{(τ+1)} →* Γ^{(τ)}` of the flow groups is surjective. -/
theorem flowGroupProj_surjective_local (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    Function.Surjective (flowGroupProj p G m i j) := by
  intro γ
  obtain ⟨a, ha⟩ := flowQuotientProj_surjective_local p G m i j γ.left
  refine ⟨SemidirectProduct.mk a γ.right, ?_⟩
  rw [flowGroupProj_mk, ha]

/-- The kernel copy `flowEKer` of the graded piece `E p G m i j` sits inside the normal subgroup
`flowNormal = F(m)/F(m)^{(τ+1)}` of the semidirect product `F(m)/F(m)^{(τ+1)} ⋊ G`. -/
theorem flowEKer_le_flowNormal (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    flowEKer p G m i j ≤ flowNormal p G m (tauSucc i j).1 (tauSucc i j).2 := by
  intro x hx
  rw [flowEKer, MonoidHom.mem_ker] at hx
  rw [flowNormal, MonoidHom.mem_range]
  have hright : x.right = 1 := by
    have h1 := congrArg SemidirectProduct.right hx
    rwa [flowGroupProj, SemidirectProduct.map_right, MonoidHom.id_apply,
      SemidirectProduct.one_right] at h1
  exact ⟨x.left, SemidirectProduct.ext rfl hright.symm⟩

/-- If two elements of the flow groups have the same projection, they are related by `LiftsFlowAt`. -/
theorem liftsFlowAt_of_flowGroupProj_eq (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar)
    {m : ℕ} (i j : ℕ)
    (y : flowGroup p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2)
    (x : flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (h : flowGroupProj p (K ≃ₐ[ℚ] K) m i j y = x) : SSGRoute.LiftsFlowAt y x := by
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

/-- **The converse direction of `liftsFlowAt_of_flowGroupProj_eq`.**  If the level projection of
`y` is `x` then `y` lifts `x`; stated for use in the rank-change computation below. -/
theorem flowGroupProj_eq_of_liftsFlowAt_local (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar)
    [Normal ℚ K] {n i j : ℕ}
    {y : flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2}
    {x : flowGroup p (K ≃ₐ[ℚ] K) n i j} (h : SSGRoute.LiftsFlowAt y x) :
    flowGroupProj p (K ≃ₐ[ℚ] K) n i j y = x := by
  obtain ⟨hright, z, hz1, hz2⟩ := h
  have hy : flowGroupProj p (K ≃ₐ[ℚ] K) n i j y =
      SemidirectProduct.mk (QuotientGroup.mk z : flowQuotient p (K ≃ₐ[ℚ] K) n i j) y.right := by
    rw [show y = SemidirectProduct.mk y.left y.right from rfl, flowGroupProj_mk, hz1,
      flowQuotientProj_coe]
  have hx : x = SemidirectProduct.mk (QuotientGroup.mk z : flowQuotient p (K ≃ₐ[ℚ] K) n i j)
      x.right := by
    rw [show x = SemidirectProduct.mk x.left x.right from rfl, hz2]
  rw [hy, hx, hright]



/-- `flowQuotMap` is surjective (it is induced by a surjective operator map). -/
theorem flowQuotMap_surjective_local (p : ℕ) (G : Type*) [Group G] {m n : ℕ} (i j : ℕ)
    (Φ : OperatorMap G m n) : Function.Surjective (flowQuotMap p G i j Φ) := by
  intro y
  induction y using QuotientGroup.induction_on with
  | H x =>
    obtain ⟨z, hz⟩ := Φ.surjective x.1
    refine ⟨QuotientGroup.mk' _ ⟨z, Subgroup.mem_top z⟩, ?_⟩
    rw [flowQuotMap_mk]
    exact congrArg (QuotientGroup.mk' _) (Subtype.ext hz)

/-- `flowGroupMap` is surjective. -/
theorem flowGroupMap_surjective_local (p : ℕ) (G : Type*) [Group G] {m n : ℕ} (i j : ℕ)
    (Φ : OperatorMap G m n) : Function.Surjective (flowGroupMap p G i j Φ) := by
  intro γ
  obtain ⟨x, hx⟩ := flowQuotMap_surjective_local p G i j Φ γ.left
  have key : flowGroupMap p G i j Φ (SemidirectProduct.mk x γ.right)
      = SemidirectProduct.mk ((flowQuotMap p G i j Φ) x) γ.right := by
    rw [flowGroupMap]
    refine SemidirectProduct.ext ?_ ?_
    · rw [SemidirectProduct.map_left]
    · rw [SemidirectProduct.map_right]; rfl
  exact ⟨SemidirectProduct.mk x γ.right, by rw [key, hx]⟩

/-- **The abstract embedding problem of Step 3.**  The level-`n` embedding problem with the abelian
kernel `flowEKer p G n i j` (the copy of the graded piece `E p G n i j`), the quotient
`ρ = (flowGroupMap Φ) ∘ φm` to be lifted, in the sense of `Work.Properness.Setup`.  The twist
construction `ψ = ε · ψ₀` of Step 3 of Theorem 15 is the `Setup.mulFun` of this setting. -/
noncomputable def stage3Setup (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] {m : ℕ} (i j : ℕ) (n : ℕ)
    (Φ : OperatorMap (K ≃ₐ[ℚ] K) m n)
    (φm : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (hφm : Function.Surjective φm) : Work.Properness.Setup where
  H := SSGRoute.GalQ
  E := flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2
  Q := flowGroup p (K ≃ₐ[ℚ] K) n i j
  π := flowGroupProj p (K ≃ₐ[ℚ] K) n i j
  π_surj := flowGroupProj_surjective_local p (K ≃ₐ[ℚ] K) n i j
  ρ := (flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φm
  ρ_surj := (flowGroupMap_surjective_local p (K ≃ₐ[ℚ] K) i j Φ).comp hφm
  ker_comm := fun a b => flowEKer_comm p (K ≃ₐ[ℚ] K) n i j a b





/-- **The level-`n` push-forward of a level-`m` lift is a lift of the push-forward of its
solution.**  If `ψm` lifts `φm` at level `m`, then `(flowGroupMap Φ) ∘ ψm` lifts
`(flowGroupMap Φ) ∘ φm` at level `n`.  This is the first step of the Step-3 construction: it
supplies the lift `ψ₀` that the twist `ε · ψ₀` is applied to. -/
theorem flowGroupMap_comp_liftsFlow (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K]
    {m n i j : ℕ} (Φ : OperatorMap (K ≃ₐ[ℚ] K) m n)
    (ψm : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2)
    (φm : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (h : SSGRoute.LiftsFlow ψm φm) :
    SSGRoute.LiftsFlow ((flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ).comp ψm)
      ((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φm) := by
  intro σ
  refine liftsFlowAt_of_flowGroupProj_eq p K i j _ _ ?_
  have h1 : flowGroupProj p (K ≃ₐ[ℚ] K) n i j
        ((flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ) (ψm σ))
      = (flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ)
        (flowGroupProj p (K ≃ₐ[ℚ] K) m i j (ψm σ)) :=
    DFunLike.congr_fun (flowGroupProj_comp_flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ) (ψm σ)
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, h1,
    flowGroupProj_eq_of_liftsFlowAt_local p K (h σ)]

/-- The quotient `F(m)/F(m)^{(i,j)}` is finite for a finite `G` (re-derived here, in a file that
does not import the sibling which redefines the level projection). -/
theorem finite_flowQuotient_local (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
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
instance instFiniteFlowGroup_local (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [Fintype G]
    (m i j : ℕ) : Finite (flowGroup p G m i j) := by
  haveI : Finite (flowQuotient p G m i j) := finite_flowQuotient_local p G m i j
  haveI : Finite (flowQuotient p G m i j × G) := inferInstance
  exact Finite.of_equiv _ (SemidirectProduct.equivProd.symm)

/-- **The `T⁰`-generation of the graded piece.**  For a surjective continuous level-`τ+1` solution
`ψ` there is a finite set `T⁰` of places whose decomposition-group images generate the copy
`flowEKer p G n i j` of `E(n,τ)` inside `Γ_{τ+1}`.  This is the `T⁰` of Step 3 of Theorem 15
(Chebotarev, `Work.SSGRoute.t0Generation`), and it is what makes `ψ` proper
(`surjective_of_iSup_map_eq_flowEKer`). -/
theorem exists_T0_generating_flowEKer (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K] (n i j : ℕ)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (hopen : IsOpen (ψ.ker : Set SSGRoute.GalQ)) (hsurj : Function.Surjective ψ) :
    ∃ T0 : Finset (ValuationSubring SSGRoute.QBar),
      (⨆ A ∈ T0, (SSGRoute.decomp ℚ A).map ψ) = flowEKer p (K ≃ₐ[ℚ] K) n i j := by
  haveI : Fintype (K ≃ₐ[ℚ] K) := Fintype.ofFinite _
  obtain ⟨T0, -, hT0⟩ := t0Generation (flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    ψ hopen hsurj (flowEKer p (K ≃ₐ[ℚ] K) n i j)
  exact ⟨T0, hT0⟩

set_option backward.isDefEq.respectTransparency false

-- The workspace instances `Work.SSGRoute.Triv.instSMulOfOne : SMul Γ (Triv p)` (the trivial action
-- of any `One Γ` on `Triv p = ZMod p`), `Triv.instDistribMulAction` and `Triv.instSMulCommClassZMod`
-- are *global*: whenever `sha2_defs` is in the import closure, typeclass search resolves the implicit
-- `SMul (K ≃ₐ[ℚ] K) (ZMod p)` argument of the `SMulCommClass` binder of
-- `exists_cyclotomicDual_finite_St3` below to the trivial action — at a point where the *local*
-- instance built in the proof of that lemma is not yet available — after which the non-trivial action
-- built there is no longer the one the statement asks about, and the proof fails with
-- "synthesized type class instance is not definitionally equal to expression inferred by typing
-- rules (synthesized Triv.instSMulOfOne …, inferred …)".
--
-- The instance below, a `priority := 1300` copy of the projection `DistribSMul.toSMul` (the remedy
-- used by `Work.SSGRoute.ZConstruction.ZDataFinal`), repairs this: the `SMul` argument is then always
-- the one *derived from a `DistribSMul`/`DistribMulAction` instance in scope*, which — inside the
-- lemma's proof — is the intended non-trivial action.  (Verified in isolation:
-- `_hw2/repro_1300.lean`, the verbatim statement and proof of the lemma with only this instance
-- added, is `rc = 0`; without it, `_hw2/repro_nofix.lean` fails with exactly the message above.)
instance (priority := 1300) ssgDistribSMulToSMulSt3 {G M : Type*} [AddZeroClass M]
    [inst : DistribSMul G M] : SMul G M :=
  inst.toSMul

/-- A cyclotomic dual module which is moreover finite (as a `𝔽_p`-module): the witness of
`exists_cyclotomicDual` is `ZMod p`, so this is the same construction with the finiteness
instance recorded. -/
theorem exists_cyclotomicDual_finite_St3 (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (ζ : SSGRoute.QBar) (hζ : IsPrimitiveRoot ζ p)
    (hζK : ζ ∈ K) :
    ∃ (T : Type) (_ : AddCommGroup T) (_ : Module (ZMod p) T)
      (_ : DistribMulAction (K ≃ₐ[ℚ] K) T) (_ : SMulCommClass (K ≃ₐ[ℚ] K) (ZMod p) T)
      (_ : Module.Finite (ZMod p) T) (_ : Finite T),
      @SSGRoute.IsCyclotomicDual p SSGRoute.GalQ (K ≃ₐ[ℚ] K) T SSGRoute.QBar _ _ _ _ _ _ _
        (AlgEquiv.restrictNormalHom K) ζ := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  set ζK : K := ⟨ζ, hζK⟩ with hζKdef
  have hζKprim : IsPrimitiveRoot ζK p :=
    IsPrimitiveRoot.of_map_of_injective (f := (algebraMap K SSGRoute.QBar : K →+* SSGRoute.QBar))
      (ζ := ζK) (by simpa [hζKdef] using hζ) (algebraMap K SSGRoute.QBar).injective
  let χ : (K ≃ₐ[ℚ] K) →* (ZMod p)ˣ := IsPrimitiveRoot.autToPow ℚ hζKprim
  let act : (K ≃ₐ[ℚ] K) → ZMod p → ZMod p := fun g t => ((χ g)⁻¹ : ZMod p) * t
  have hact_one : ∀ t, act 1 t = t := by
    intro t
    change ((χ 1)⁻¹ : ZMod p) * t = t
    rw [map_one]
    simp
  have hact_mul : ∀ g h t, act (g * h) t = act g (act h t) := by
    intro g h t
    change ((χ (g * h))⁻¹ : ZMod p) * t =
      ((χ g)⁻¹ : ZMod p) * (((χ h)⁻¹ : ZMod p) * t)
    rw [map_mul, Units.val_mul, mul_inv_rev]
    ring
  have hact_zero : ∀ g, act g 0 = 0 := by
    intro g; change ((χ g)⁻¹ : ZMod p) * 0 = 0; rw [mul_zero]
  have hact_add : ∀ g x y, act g (x + y) = act g x + act g y := by
    intro g x y
    change ((χ g)⁻¹ : ZMod p) * (x + y) = ((χ g)⁻¹ : ZMod p) * x + ((χ g)⁻¹ : ZMod p) * y
    rw [mul_add]
  letI : DistribMulAction (K ≃ₐ[ℚ] K) (ZMod p) :=
    { smul := act
      one_smul := hact_one
      mul_smul := hact_mul
      smul_zero := hact_zero
      smul_add := hact_add }
  letI : SMulCommClass (K ≃ₐ[ℚ] K) (ZMod p) (ZMod p) :=
    ⟨fun g c t => by
      change act g (c * t) = c * act g t
      change ((χ g)⁻¹ : ZMod p) * (c * t) = c * (((χ g)⁻¹ : ZMod p) * t)
      ring⟩
  refine ⟨ZMod p, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ?_, ?_⟩
  · exact Module.finrank_self (ZMod p)
  · intro σ c hc t
    have hχ : ((χ (AlgEquiv.restrictNormalHom K σ) : ZMod p)) = (c : ZMod p) := by
      have hcomm : (algebraMap K SSGRoute.QBar) ((AlgEquiv.restrictNormalHom K σ) ζK)
          = σ ((algebraMap K SSGRoute.QBar) ζK) :=
        AlgEquiv.restrictNormal_commutes σ K ζK
      have hspec := IsPrimitiveRoot.autToPow_spec ℚ hζKprim (AlgEquiv.restrictNormalHom K σ)
      have h1 : ζ ^ ((χ (AlgEquiv.restrictNormalHom K σ) : ZMod p)).val = ζ ^ c := by
        have h2 := congrArg (algebraMap K SSGRoute.QBar) hspec
        rw [hcomm] at h2
        simp only [map_pow] at h2
        simp only [IntermediateField.algebraMap_apply] at h2
        exact h2.trans hc
      have h3 : ((χ (AlgEquiv.restrictNormalHom K σ) : ZMod p)).val ≡ c [MOD p] := by
        have h4 := ((hζ.isOfFinOrder (NeZero.ne p)).pow_eq_pow_iff_modEq
          (n := ((χ (AlgEquiv.restrictNormalHom K σ) : ZMod p)).val) (m := c)).mp h1
        rwa [← hζ.eq_orderOf] at h4
      calc (χ (AlgEquiv.restrictNormalHom K σ) : ZMod p)
          = (((χ (AlgEquiv.restrictNormalHom K σ) : ZMod p)).val : ZMod p) :=
            (ZMod.natCast_zmod_val _).symm
        _ = (c : ZMod p) := (ZMod.natCast_eq_natCast_iff _ _ p).mpr h3
    have hkey : (c : ZMod p) * (((χ (AlgEquiv.restrictNormalHom K σ))⁻¹ : ZMod p)) = 1 := by
      have hcu : (c : ZMod p) = (χ (AlgEquiv.restrictNormalHom K σ) : ZMod p) := hχ.symm
      rw [hcu]
      exact mul_inv_cancel₀ (Units.ne_zero _)
    rw [nsmul_eq_mul]
    show (c : ZMod p) * (((χ (AlgEquiv.restrictNormalHom K σ))⁻¹ : ZMod p) * t) = t
    rw [← mul_assoc, hkey, one_mul]


/-- **The Galois-correspondence identification of a level solution.**  If `N` is a finite Galois
intermediate field whose fixing subgroup is `ker φ`, then `φ` identifies `Gal(N/ℚ)` with the target
group `Γ_m` (so that `Gal(N) ≃* F(m)/F(m)^{(τ)} ⋊ G`).  This is the bridge between the arithmetic
(`SSGRoute.coker_obstruction`, phrased over the fixed field of `φm.ker`) and the group homology of
the flow group. -/
theorem galoisEquiv_of_ker (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [Normal ℚ K] (N : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ N] [Normal ℚ N] [IsGalois ℚ N]
    (m i j : ℕ) (φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (hsurj : Function.Surjective φ) (hker : φ.ker = N.fixingSubgroup) :
    ∃ e : (N ≃ₐ[ℚ] N) ≃* flowGroup p (K ≃ₐ[ℚ] K) m i j,
      ∀ σ : SSGRoute.GalQ, e (SSGRoute.res ℚ N σ) = φ σ := by
  have hker' : φ.ker = (AlgEquiv.restrictNormalHom N).ker :=
    hker.trans (IntermediateField.restrictNormalHom_ker N).symm
  obtain ⟨e, he⟩ := t0_restrictLift N φ hker'
  have he' : ∀ z : SSGRoute.GalQ, e (SSGRoute.res ℚ N z) = φ z := fun z => DFunLike.congr_fun he z
  have hsurj_e : Function.Surjective e := by
    intro y
    obtain ⟨σ, hσ⟩ := hsurj y
    exact ⟨SSGRoute.res ℚ N σ, by rw [he' σ, hσ]⟩
  have hinj_e : Function.Injective e := by
    intro x y hxy
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := ↥N)
      (E := SSGRoute.QBar) x
    obtain ⟨τ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := ↥N)
      (E := SSGRoute.QBar) y
    have h1 : φ σ = φ τ := by rw [← he' σ, ← he' τ]; exact hxy
    have hmem : σ * τ⁻¹ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
    have h2 : SSGRoute.res ℚ N σ = SSGRoute.res ℚ N τ := by
      have hmem' : σ * τ⁻¹ ∈ (AlgEquiv.restrictNormalHom N).ker := by
        rw [IntermediateField.restrictNormalHom_ker, ← hker]; exact hmem
      rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hmem'
      exact hmem'
    exact h2
  exact ⟨MulEquiv.ofBijective e ⟨hinj_e, hsurj_e⟩, he'⟩

/-- `Rep.res` of a composite homomorphism is the composite of the pullbacks. -/
theorem Rep_res_comp_local {k : Type} [CommRing k] {G H K : Type} [Group G] [Group H] [Group K]
    (f : G →* H) (g : H →* K) (M : Rep k K) :
    Rep.res (g.comp f) M = Rep.res f (Rep.res g M) := rfl

/-- **The coefficient transport along a group isomorphism**: the canonical additive equivalence
`H₁(G, Rep.res e M) ≃+ H₁(H, M)` for `e : G ≃* H`.  It is Mathlib's `groupHomology.mapIso` with the
identity coefficient identification; it is what identifies the arithmetic
(`SSGRoute.coker_obstruction`, phrased over `Gal(N/ℚ)`) with the group homology `H₁(Γ_m, flowRep)`
on which `flowZMap` acts. -/
noncomputable def transportH1 {k G H : Type} [CommRing k] [Group G] [Group H]
    (e : G ≃* H) (M : Rep k H) :
    groupHomology.H1 (Rep.res e.toMonoidHom M) ≃+ groupHomology.H1 M :=
  (groupHomology.mapIso (A := Rep.res e.toMonoidHom M) (B := M) e
    (LinearEquiv.refl k M.V) (fun _ => rfl) 1).toLinearEquiv.toAddEquiv

/-- **Group homology in degree one is invariant under a group isomorphism** (the `Nonempty` form of
`transportH1`). -/
theorem groupHomologyH1_iso_of_mulEquiv_local {k G H : Type} [CommRing k] [Group G] [Group H]
    (e : G ≃* H) (M : Rep k H) :
    Nonempty (groupHomology.H1 (Rep.res e.toMonoidHom M) ≃+ groupHomology.H1 M) :=
  ⟨transportH1 e M⟩

/-! ## Assembly plan for `properStageAssemblyData` (Step 3 of Theorem 15)

The proof is the paper's Step 3 (Schmidt–Wingberg, arXiv:math/9809211 §5, pp. 26–30).  Everything
of it that is *not* the arithmetic of `SSGRoute.coker_obstruction` is available:

* **Level-`m` data.**  `hS m` is `IsSolvableStage p K m i j`: it gives the Scholz solution `φm`, the
  open-kernel lift `ψm`, and the local splitting datum at every `T¹`-place.  These are the first
  four conjuncts of the conclusion verbatim.
* **The lift.**  `flowGroupMap_comp_liftsFlow`: `ψ₀ := (flowGroupMap Φ) ∘ ψm` lifts
  `ρ' := (flowGroupMap Φ) ∘ φm` at level `n`.  (Uses `flowGroupProj_comp_flowGroupMap` and
  `flowGroupProj_eq_of_liftsFlowAt_local`.)
* **The `T⁰`-generation.**  `exists_T0_generating_flowEKer`: for the *surjective* `ψ` there is a
  finite `T⁰` with `⨆ A ∈ T⁰, ψ(D_A) = flowEKer p G n i j`.  Applied to the surjective
  `ψ₀` (the twist `ε · ψ₀` is surjective by `surjective_of_iSup_map_eq_flowEKer` once the `T⁰`
  images generate; since `ψ(D_A) = ε(D_A) · ψ₀(D_A)` contains `ψ₀(D_A)`, the generation is
  inherited).
* **The Galois correspondence.**  `galoisEquiv_of_ker`: if `N.fixingSubgroup = φ.ker` then `φ`
  identifies `Gal(N/ℚ) ≃* Γ_m`.
* **The coefficient transport.**  `Rep_res_comp_local` and
  `groupHomologyH1_iso_of_mulEquiv_local` identify
  `H₁(Gal(N/ℚ), E_m ⊗ T) = H₁(Rep.res πN (flowRepG m))` with `H₁(Γ_m, flowRep m)`, which is where
  `flowZMap` lives; its naturality in the rank change is `groupHomology.map_comp`.

**What remains (the arithmetic), isolated in the paper as Lemma 10 + Lemma 12 + Proposition 7(i).**
Choose, for each conjugacy class of finite places over `Ram(K/ℚ) ∪ {p}` and over the ramification
of `N_m`, and for the real places, the local target data `α`/`β` of Step 3; apply
`SSGRoute.coker_obstruction` (base `ℚ`) to get `x ∈ H₁(Gal(N_m/ℚ), E_m ⊗ T)`; kill `x` with
`Work.CohomologicalShrinking.exists_shrinking_H1_semidirect_paper` (needs `SSGRoute.prop5Data_exists`)
to get `Φ : F(m) ⇢ F(n)` with `flowZMap Φ T (transport x) = 0`; feed the level-`n` datum
`(N_n, q = flowGroupMap Φ, f, F)` back into the `∀`-clause of `coker_obstruction` to obtain
`ε : G_ℚ → E(n,τ)` which is a locally constant `1`-cocycle, is locally a coboundary of the local
targets at `S`, and vanishes on the inertia of the places outside `S ∪ cs(N_n)`.

**The twist and the clause check.**  Set `ψ := flowTwistE ε ψ₀` (`ε`-twist of `ψ₀` by the central
`E(n,τ)`-valued cocycle; the twist algebra is `Submission/Work/SSGRoute/scholz_succ_of_properStage.lean`
— `flowTwist`/`flowTwistEHom`, `flowTwistHom_liftsFlow`, `flowTwist_isOpen_ker`,
`flowTwistE_scholzT1`, `flowTwistE_eq_of_eq_zero` — *not* imported here so that this module builds
independently).  The clauses:
* `LiftsFlow ψ ρ'` and `IsOpen ψ.ker`: the twist of a lift with a locally constant cocycle;
* the `T¹` condition and the involutions: `ε` is a coboundary on the decomposition groups of the
  `T¹`-places and of the real places, and a coboundary vanishes on `G_K` where the action of `G_K`
  on `E(n,τ)` is trivial (this is where the local target at `T¹` is *not* `0` but cancels `ψ₀`);
* the ramification clause: the local targets at `T² = Ram(N_n|K)` make the new local group cyclic
  and totally ramified, and at the remaining (`T³`) places `ε` kills the ramification of `ψ₀`;
  places where `ε` vanishes and `ρ'` is trivial fall under the first disjunct;
* the `T⁰`-generation: `T⁰ ⊆ cs(N_n|K)`, so at `A ∈ T⁰` the decomposition group acts trivially on
  `E(n,τ)`.  CAUTION: `ψ(D_A) = {gradeInl (ε σ) · ψ₀ σ}` is *not* in general the subgroup generated
  by `ε(D_A)` and `ψ₀(D_A)` (for `p = 2` the products of two homomorphisms onto `𝔽₂` can collapse),
  so the `T⁰` argument needs care; the cleanest formulation available here is to apply
  `exists_T0_generating_flowEKer` to the *twisted* `ψ` once its surjectivity (hence its fixed field)
  is known, or else to choose `T⁰ ⊆ cs(N_{τ+1})` so that `ψ₀|_{D_A} = 1` and `ψ(D_A) = α_A(D_A)`
  generates.  This is the one part of the `T⁰` bookkeeping that is not yet settled.
-/

/-- **The coefficient transport along the level-`m` Galois correspondence.**  If `N` is a finite
Galois field with `N.fixingSubgroup = φ.ker`, then `φ` identifies `Gal(N/ℚ)` with `Γ_m`, and along
this identification the coefficient module `H₁(Gal(N/ℚ), E(m,τ) ⊗ T)` of the arithmetic
(`SSGRoute.coker_obstruction`) becomes the group homology `H₁(Γ_m, flowRep m)` on which `flowZMap`
acts. -/
theorem flowRepGaloisTransport (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [Normal ℚ K] (N : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ N] [Normal ℚ N]
    [IsGalois ℚ N] (m i j : ℕ) (φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (hsurj : Function.Surjective φ) (hker : φ.ker = N.fixingSubgroup)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[ℚ] K) T]
    [SMulCommClass (K ≃ₐ[ℚ] K) (ZMod p) T] :
    ∃ e : (N ≃ₐ[ℚ] N) ≃* flowGroup p (K ≃ₐ[ℚ] K) m i j,
      (∀ σ : SSGRoute.GalQ, e (SSGRoute.res ℚ N σ) = φ σ) ∧
      Nonempty (groupHomology.H1 (Rep.res ((flowQuot p (K ≃ₐ[ℚ] K) m i j).comp e.toMonoidHom)
          (flowRepG p (K ≃ₐ[ℚ] K) m i j T))
        ≃+ groupHomology.H1 (flowRep p (K ≃ₐ[ℚ] K) m i j T)) := by
  obtain ⟨e, he⟩ := galoisEquiv_of_ker p K N m i j φ hsurj hker
  exact ⟨e, he, groupHomologyH1_iso_of_mulEquiv_local e (flowRep p (K ≃ₐ[ℚ] K) m i j T)⟩

/-- **The fixed field of a solution and its Galois identification.**  For a surjective continuous
solution `φ` of the level-`τ` problem over `K` there is a finite Galois field `N ⊇ K` with
`N.fixingSubgroup = φ.ker` (so `N` is the field cut out by `φ`) and an isomorphism
`Gal(N/ℚ) ≃* Γ_m` carrying the restriction map `G_ℚ → Gal(N/ℚ)` to `φ`.  This packages
`flowKernel_fixedField` with `galoisEquiv_of_ker`; it is the first step of the Step-3 assembly
(`N_m = N` for `φm`). -/
theorem fixedField_and_equiv (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (m i j : ℕ)
    (φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (hsurj : Function.Surjective φ) (hopen : IsOpen (φ.ker : Set SSGRoute.GalQ))
    (hflow : ∀ σ : SSGRoute.GalQ,
      flowQuot p (K ≃ₐ[ℚ] K) m i j (φ σ) = SSGRoute.res ℚ K σ) :
    ∃ (N : IntermediateField ℚ SSGRoute.QBar) (_ : FiniteDimensional ℚ N) (_ : Normal ℚ N)
      (_ : IsGalois ℚ N),
      K ≤ N ∧ (∀ σ : SSGRoute.GalQ, σ ∈ N.fixingSubgroup ↔ φ σ = 1) ∧
      ∃ e : (N ≃ₐ[ℚ] N) ≃* flowGroup p (K ≃ₐ[ℚ] K) m i j,
        ∀ σ : SSGRoute.GalQ, e (SSGRoute.res ℚ N σ) = φ σ := by
  obtain ⟨N, hfd, hgal, hKN, hfix, -⟩ := flowKernel_fixedField p K m i j φ hopen hsurj hflow
  have hker : φ.ker = N.fixingSubgroup :=
    Subgroup.ext (fun σ => (MonoidHom.mem_ker).trans (hfix σ).symm)
  obtain ⟨e, he⟩ := galoisEquiv_of_ker p K N m i j φ hsurj hker
  exact ⟨N, hfd, hgal.to_normal, hgal, hKN, hfix, e, he⟩

/-- **A primitive `p`-th root of unity lying in `K`.**  From `HasRootsOfUnity p K i` (the exponent
condition `μ_{p^{i+1}} ⊆ K` of the induction step `τ ↦ τ + 1`) one obtains a primitive `p`-th root
`ζ ∈ K`; this is the `ζ` demanded by the arithmetic input `SSGRoute.coker_obstruction` (it needs
both `IsPrimitiveRoot ζ p` and `ζ ∈ K`).  Raising a primitive `(p^{i+1})`-th root to the `p^i`-th
power is the only step. -/
theorem exists_primitiveRoot_in_K (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    (i : ℕ) (hμ : SSGRoute.HasRootsOfUnity p K i) :
    ∃ ζ : SSGRoute.QBar, ζ ∈ K ∧ IsPrimitiveRoot ζ p := by
  obtain ⟨ζ, hζK, hζ⟩ := hμ
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  refine ⟨ζ ^ (p ^ i), pow_mem hζK _, ?_⟩
  have hdiv : p ^ i ∣ p ^ (i + 1) := by
    rw [pow_succ]; exact dvd_mul_right _ _
  have h := hζ.pow_of_dvd (p := p ^ i) (pow_ne_zero _ hp) hdiv
  have hk : p ^ (i + 1) / p ^ i = p := by
    rw [pow_succ]
    exact Nat.mul_div_right p (pow_pos (Nat.pos_of_ne_zero hp) i)
  rwa [hk] at h

/-! ## The `T¹` local target of Step 3

The local datum of Step 3 at a place `A ∈ T¹` is the cocycle

  `α_A σ = l_A σ · (ψ σ)⁻¹      (σ ∈ D_A)`

where `l_A : D_A →* Γ_{τ+1}` is the local splitting supplied by `IsSolvableStage` (`LiftsFlowAt
(l_A σ) (φ σ)` and `l_A σ = 1` whenever `φ σ = 1`) and `ψ` is the lift of `φ` that is being
twisted.  Since both `l_A σ` and `ψ σ` project to `φ σ`, the ratio lies in the kernel
`flowEKer = E(m,τ)` of the level projection.  This is exactly the paper's "there is
`β_p ∈ H¹(k_p, E)`, the class of `φ_{n,τ+1}|_{G_{(N^τ)_p}}`", and it is the reason the twist
`flowTwist α_A ψ` is trivial on `D_A ∩ G_K` (`l_A = 1` and `ψ σ ∈ flowEKer` there): the shift
`α_A σ = (ψ σ)⁻¹` cancels `ψ σ` exactly. -/

/-- **The `T¹` local target is a `1`-cocycle.**  For two lifts `ψ` of `φ` (global) and `l` of
`φ|_H` (local, on a subgroup `H`), the ratio `A σ := l σ · (ψ σ)⁻¹` takes values in the copy
`flowEKer = E(m,τ)` of the graded piece and is a `1`-cocycle for the conjugation action of `H`
through `ψ`: `A (σ * τ) = A σ * (ψ σ * A τ * (ψ σ)⁻¹)`.  Via the identification
`flowEKer p G m i j ≃* E p G m i j` and the conjugation formula
`ψ σ * gradeInl v * (ψ σ)⁻¹ = gradeInl (res K σ • v)` this is precisely the statement that `A` is
a crossed homomorphism for the `G(K/ℚ)`-module structure of `E(m,τ)`, i.e. an element of
`Z¹(G_ℚ, E(m,τ))` as used by `SSGRoute.coker_obstruction`. -/
theorem localTargetT1_isCocycle (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K]
    {m i j : ℕ}
    (φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m
      (tauSucc i j).1 (tauSucc i j).2)
    (hLift : ∀ σ : SSGRoute.GalQ, SSGRoute.LiftsFlowAt (ψ σ) (φ σ))
    (H : Subgroup SSGRoute.GalQ)
    (l : H →* flowGroup p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2)
    (hl : ∀ σ : H, SSGRoute.LiftsFlowAt (l σ) (φ ↑σ)) :
    ∃ A : H → ↥(flowEKer p (K ≃ₐ[ℚ] K) m i j),
      (∀ σ : H, ((A σ : ↥(flowEKer p (K ≃ₐ[ℚ] K) m i j)) :
          flowGroup p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2) = l σ * (ψ ↑σ)⁻¹) ∧
      ∀ σ τ : H, A (σ * τ) = A σ * ((ψ ↑σ) * A τ * (ψ ↑σ)⁻¹) := by
  have hψ : ∀ σ : SSGRoute.GalQ, flowGroupProj p (K ≃ₐ[ℚ] K) m i j (ψ σ) = φ σ :=
    fun σ => flowGroupProj_eq_of_liftsFlowAt_local p K (hLift σ)
  have hl' : ∀ σ : H, flowGroupProj p (K ≃ₐ[ℚ] K) m i j (l σ) = φ ↑σ :=
    fun σ => flowGroupProj_eq_of_liftsFlowAt_local p K (hl σ)
  let A : H → ↥(flowEKer p (K ≃ₐ[ℚ] K) m i j) :=
    fun σ => ⟨l σ * (ψ ↑σ)⁻¹, by
      rw [flowEKer, MonoidHom.mem_ker, map_mul, map_inv, hl' σ, hψ ↑σ, mul_inv_cancel]⟩
  have hA : ∀ σ : H, ((A σ : ↥(flowEKer p (K ≃ₐ[ℚ] K) m i j)) :
      flowGroup p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2) = l σ * (ψ ↑σ)⁻¹ :=
    fun σ => rfl
  exact ⟨A, hA, fun σ τ => by
    simp only [hA]
    rw [Subgroup.coe_mul, map_mul l σ τ, map_mul ψ (↑σ) (↑τ)]
    group⟩

/-- An `𝔽_ℓ`-vector space (`ℓ` a prime, `ℓ ≠ 2`) has no `2`-torsion: `2` is invertible in
`ZMod ℓ`. -/
theorem two_nsmul_eq_zero_of_odd_prime (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {M : Type}
    [AddCommGroup M] [Module (ZMod p) M] (z : M) (hz : (2 : ℕ) • z = 0) : z = 0 := by
  have h2ne : ((2 : ℕ) : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℤ) : ZMod p) = 0 := by simpa using h
    have hdvd : (p : ℤ) ∣ (2 : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd 2 p).mp h'
    have hnat : p ∣ 2 := by exact_mod_cast hdvd
    have htwo : 2 ≤ p := (Fact.out : p.Prime).two_le
    have hp2 : 2 < p := lt_of_le_of_ne htwo (Ne.symm hp)
    exact absurd hnat (Nat.not_dvd_of_pos_of_lt (by norm_num) hp2)
  have h2 : ((2 : ℕ) : ZMod p) • z = 0 := by
    rw [Nat.cast_smul_eq_nsmul (ZMod p) 2 z]; exact hz
  rw [← one_smul (ZMod p) z, ← inv_mul_cancel₀ h2ne, mul_smul, h2, smul_zero]

/-- **The copy `flowEKer = E(m,τ)` of the graded piece has no `2`-torsion for odd `p`.**  Since
`ψ c` is `2`-torsion whenever `c ^ 2 = 1` and `ψ` lifts a solution vanishing at `c` (and then
`ψ c ∈ flowEKer`), this is the whole content of the triviality of a lift at involutions of `G_K`
for odd `p`: `E(m,τ)` is an `𝔽_p`-vector space and `p ≠ 2` is invertible. -/
theorem flowEKer_two_torsion_eq_one (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (G : Type) [Group G]
    (m i j : ℕ) (x : ↥(flowEKer p G m i j)) (hx : x ^ 2 = 1) : x = 1 := by
  obtain ⟨e⟩ := flowEKer_equiv_refinedQuotient p G m i j
  have hy : (e x) ^ 2 = 1 := by rw [← map_pow, hx, map_one]
  have hz : (2 : ℕ) • (Additive.ofMul (e x)) = 0 := by
    rw [two_nsmul, ← ofMul_mul, ← pow_two, hy, ofMul_one]
  have hz0 : (Additive.ofMul (e x)) = 0 := two_nsmul_eq_zero_of_odd_prime p hp _ hz
  have hex1 : e x = 1 := by
    have h := congrArg Additive.toMul hz0
    simpa using h
  exact e.injective (by rw [hex1, map_one])

/-- **A lift is trivial at the involutions of `G_K` when `p` is odd.**  If `c ^ 2 = 1` lies in
`K.fixingSubgroup` and the level-`τ` solution `φ` vanishes at `c`, then any lift `ψ` of `φ` also
vanishes at `c`: `ψ c` lies in the kernel `flowEKer = E(m,τ)` of the level projection and satisfies
`(ψ c) ^ 2 = 1`, and `E(m,τ)` has no `2`-torsion for odd `p` (`flowEKer_two_torsion_eq_one`).

This is the whole content, for odd `p`, of the second clause of `ScholzConditions` for a lift;
the case `p = 2` is the one that genuinely requires `K` to have no real place. -/
theorem lift_eq_one_of_involution_odd (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K] {m i j : ℕ}
    (φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2)
    (hLift : ∀ σ : SSGRoute.GalQ, SSGRoute.LiftsFlowAt (ψ σ) (φ σ))
    (hφc : ∀ c : SSGRoute.GalQ, c ^ 2 = 1 → c ∈ K.fixingSubgroup → φ c = 1) :
    ∀ c : SSGRoute.GalQ, c ^ 2 = 1 → c ∈ K.fixingSubgroup → ψ c = 1 := by
  intro c hc hfix
  have hproj : flowGroupProj p (K ≃ₐ[ℚ] K) m i j (ψ c) = φ c :=
    flowGroupProj_eq_of_liftsFlowAt_local p K (hLift c)
  have hmem : ψ c ∈ flowEKer p (K ≃ₐ[ℚ] K) m i j := by
    rw [flowEKer, MonoidHom.mem_ker, hproj, hφc c hc hfix]
  have h2 : (⟨ψ c, hmem⟩ : ↥(flowEKer p (K ≃ₐ[ℚ] K) m i j)) ^ 2 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    change (ψ c) ^ 2 = (1 : flowGroup p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2)
    rw [← map_pow, hc, map_one]
  have h1 : (⟨ψ c, hmem⟩ : ↥(flowEKer p (K ≃ₐ[ℚ] K) m i j)) = 1 :=
    flowEKer_two_torsion_eq_one p hp (K ≃ₐ[ℚ] K) m i j _ h2
  exact congrArg Subtype.val h1

/-! ## Status of the assembly (session 5): what is proved here and what is still missing

The proof of `properStageAssemblyData` is the paper's Step 3 (Schmidt–Wingberg,
arXiv:math/9809211 §5, pp. 26–30).  Write `ψ₀ := (flowGroupMap Φ) ∘ ψm` (the level-`n`, stage-`τ+1`
solution obtained from the level-`m` data) and `ψ := flowTwistE ε ψ₀` (the twist by the global
`E(n,τ)`-valued cocycle `ε` supplied by `SSGRoute.coker_obstruction`).

### Proved in this file (all `sorry`-free)

* level projection and rank change: `flowQuotientProj_comp_flowQuotMap`,
  `flowGroupProj_comp_flowGroupMap`, the four surjectivity lemmas, `flowEKer_le_flowNormal`,
  `flowGroupMap_comp_liftsFlow`, `finite_flowQuotient_local`, `instFiniteFlowGroup_local`;
* naturality of the graded piece: `flowQuotMap_gradeIncl`, `flowGroupMap_gradeInl`,
  `flowGroupMap_gradeInl_add`, `flowGroupMap_gradeInl_toMul` — the inclusion `E(d,τ) ↪ Γ_{τ+1}(d)`
  commutes with the rank change, which is what makes the level-`m` local targets act correctly at
  level `n`;
* the copy of the graded piece: `flowEKer_eq_range_gradeInl`,
  `mem_flowEKer_iff_exists_gradeInl`;
* the twist (interface with the clauses): `flowTwistEHom_liftsFlow` (`LiftsFlow`),
  `flowTwistEHom_isOpen_ker` (`IsOpen ψ.ker`), `flowTwistE_eq_one_of_gradeInl_eq_inv`,
  `isCyclic_and_inertia_generates_of_cocycle_zero`;
* the `T¹` clause: `localTargetT1_isCocycle` (the ratio `l_A σ · (ψm σ)⁻¹` is a `1`-cocycle for the
  action through `Gal(K/ℚ)`), `flowTwistE_eq_one_of_T1Target` (given `ε = gradedMapLin Φ (α_A)` on
  `D_A ∩ G_K` with `α_A` the `T¹` target, the twist is trivial there — condition (i));
* the `T³` target: `exists_localTarget_of_proj_eq_one` (the `E(m,τ)`-valued cocycle
  `α_A σ = -ψm σ` exists whenever `φm|D_A = 1`; its values at `D_A` are `(ψm σ)⁻¹`), and the `T¹`
  target `Work.SSGRoute.exists_localTarget_of_splitting` (sibling file);
* the rank change on the graded pieces: `gradedMapLin_surjective_local`, `exists_section_gradedMapLin`
  (every element of `E(n,τ)` is the rank-change image of an element of `E(m,τ)`, which is how the
  arithmetic prescribes the local targets at level `m` by their effect at level `n`);
* the `T⁰` clause: `iSup_map_eq_flowEKer_of_generators` (places completely decomposed in the field
  of `ρ`, whose `ψ`-images contain prescribed generators of `E(n,τ)`, generate `flowEKer`),
  `iSup_map_eq_flowEKer_of_prescribed_values` (the end-to-end form: the coboundary conditions of
  `SSGRoute.coker_obstruction` plus the prescribed Frobenius values give the generation);
  `exists_T0_generating_flowEKer` (the same for a *surjective* `ψ`, by Chebotarev);
* condition (ii): `decomp_le_fixingSubgroup_of_map_eq_one` (first part from the first disjunct),
  `isCyclic_and_inertia_generates_of_kernel_disjoint` (the "trivial" half of the `T²`
  prescription: if the local group of `ψ` meets `flowEKer` trivially, then cyclicity and
  inertia-generation transfer from `ρ`), `isCyclic_and_inertia_generates_of_cocycle_zero`
  (transfer from `ψ` wherever `ε` vanishes);
* the involution clause is *automatic*: `involution_clause_of_hasRootsOfUnity` (via
  `Work.SSGRoute.no_two_torsion_fixingSubgroup`), so no input is needed for it;
* the Galois/`H₁` dictionary: `galoisEquiv_of_ker`, `fixedField_and_equiv`,
  `Rep_res_comp_local`, `transportH1`, `groupHomologyH1_iso_of_mulEquiv_local`,
  `flowRepGaloisTransport`, `pushdown_levelDatum` (the `∀`-clause datum of `coker_obstruction`),
  `exists_primitiveRoot_in_K`, `exists_involutionSet`, `stage3Setup`.

### COMPLETED (session 9) — `properStageAssemblyData` is proved; the only remaining input is the shared arithmetic node

The `sorry` of `properStageAssemblyData` is **gone**: the proof is assembled in this file from the
following pieces, all of which are in this file or in modules it imports.

* **Step 1 (this file).**  `exists_primitiveRoot_in_K` and `exists_cyclotomicDual_finite_St3` give the
  `ζ ∈ K` and the finite cyclotomic dual `T` demanded by the arithmetic.
* **Step 2 (this file).**  `stage3LevelData_St3` packages `hS`: a level `m ≥ n`, the Scholz solution
  `φm`, its open-kernel lift `ψm`, the local splitting `l` at every `T¹`-place, the fixed field `Nm`
  of `φm.ker` with `Gal(Nm/ℚ) ≃* Γ_m`, and the shrinking supply
  `stage3ShrinkSupply_St3` (`Work.CohomologicalShrinking.exists_shrinking_H1_semidirect_paper` for
  `2 ≤ i`, the sibling `Work.SSGRoute.stage3Shrinking_i_one` for `i = 1`, both on top of
  `SSGRoute.prop5Data_exists`).
* **Step 3 (this file).**  `Λ` is the (finite, normal) fixed field of `ψm.ker ⊓ K.fixingSubgroup`
  (`exists_finiteDimensional_normal_fixingSubgroup_le`), so `Λ.fixingSubgroup ≤ ψm.ker`: this is the
  field whose ramification has to be covered by `S`.  `Srep` is one place per `G_ℚ`-class over
  `Ram(Λ) ∪ {p}` (`ramifiedPlaces_finite`), `T0` are Chebotarev places split in `Λ` avoiding `Srep`
  with local targets whose Frobenius values exhaust `E(m,τ)` (`stage3T0Data`), and
  `S := Srep ∪ T0`.
* **Step 4 (this file).**  The local targets `α`: `AlphaSpec` records the four-case shape
  (`T¹`, `T³`, kill-inertia, `T²`) and `exists_localAlphaData_local` — a copy in this file of the
  sibling `Work.SSGRoute.exists_localAlphaData`, copied rather than imported because that module
  imports *this* one — produces `α A` for every finite place from
  `exists_localTarget_of_splitting`, `exists_localTarget_of_proj_eq_one`,
  `Work.SSGRoute.stage3KillInertiaTarget` and `Work.SSGRoute.stage3T2LocalTarget`.
* **Step 5 (this file).**  `stage3CokerInterface_local` — a copy of
  `Work.SSGRoute.stage3CokerInterface_St3` (again copied rather than imported, for the same reason) —
  runs `SSGRoute.coker_obstruction` at level `m`, transports the obstruction class with `transportH1`
  (`transportH1_natural_of_compat_St3`, `coeffId_St3`), kills it with the shrinking supply, and
  re-feeds the `∀`-clause at `N₂ = Nn`.  It returns `Φ`, the field `Nn` of
  `φn = (flowGroupMap Φ) ∘ φm` with `Gal(Nn/ℚ) ≃* Γ_n`, and the global cocycle `ε` realizing
  `gradedMapLin Φ ∘ α` at `S` and vanishing on the inertia outside `S ∪ cs(Nn)`.
* **Step 6 (this file).**  The twist `ψ := flowTwistEHom ε ((flowGroupMap Φ) ∘ ψm)`, and the clauses:
  * clause data at the representatives `Srep` (`hRepI`, `hRepII`): `T¹` by
    `flowTwistE_eq_one_of_T1Target`, `T³`/kill-inertia by `flowTwistE_eq_one_of_inertiaShape`
    (this file), `T²` by `isCyclic_and_inertia_generates_pushforward` (this file) via the
    coboundary vanishing on `D_A ⊆ G_K`;
  * **conjugation transfer** of the clause data to *all* places:
    `Work.SSGRoute.clauseData_conj_transfer_T1` (sibling module, proved);
  * the places outside the conjugates of `S`: `ε` vanishes on the inertia
    (`coker_obstruction`'s last clause) and `ψm` is unramified there (they are not ramified in
    `Λ ⊇ Nm ⊇ K`), so the twist is unramified on their inertia; if the place splits in `Nn` the
    *first* disjunct of (ii) holds instead;
  * the involution clause is automatic (`involution_clause_of_hasRootsOfUnity`);
  * the `T⁰`-generation: `iSup_map_eq_flowEKer_of_prescribed_values` with
    `g A = gradedMapLin Φ (α A F_A)`, whose surjectivity onto `E(n,τ)` comes from
    `gradedMapLin_surjective_local` and the exhaustive Frobenius values of `stage3T0Data`.

**The only remaining input is the arithmetic node.**  `#print axioms Work.SSGRoute.properStageAssemblyData`
still reports `sorryAx`, and the source is exactly one declaration,
`SSGRoute.canonical_localPairing_with_reciprocity` (`canonical_localPairing_with_reciprocity.lean`),
consumed by `SSGRoute.coker_obstruction` (and hence by `stage3CokerInterface_local` here).  That
statement is the `G1` node of `DESIGN_PT.md`, i.e. the *finite-place half* of local Tate duality
(`PTembedding/localTatePairing_canonical`, `E7`) together with the reciprocity clause; the
archimedean half and the gluing are already proved (`E7Arch/pairFamily`, `E7Arch/g1Assembly`).  As
soon as `G1` is sorry-free, this node becomes `declare_proven`-clean with no further change: nothing
in this file refers to `canonical_localPairing_with_reciprocity` except through
`coker_obstruction`.

### Session-9 contribution to the arithmetic chain (outside this node)

While this node was being finished, one *live* `sorry` of the `G1`/`E7` chain was removed by
*wiring*: `PTembedding/kummerBaseDim_proved.lean` (the E7 base case
`dim H¹(D_A, 𝔽_p) = dim H¹(D_A, μ_p)`) had a single gap consisting of a placeholder copy of the
already-proved `Work.SSGRoute.PTembedding.lcHoms_localUnits`.  The new module

  `Submission/Work/SSGRoute/PTembedding/kummerBaseDim_wired.lean`,
  `Work.SSGRoute.PTembedding.kummerBaseDim_wired`

is a `sorry`-free copy with the placeholder replaced by the real lemma (`#print axioms` =
`[propext, Classical.choice, Quot.sound]`); see `PING_ptE7_kummerBaseDim_wired.md` for the one-line
wiring on the E7 side.  This is one of the two ingredients of `localTatePairing_canonical` (`E7`),
hence (through `G1`) of the arithmetic input of this node.

### Integration note (for whoever owns the consumer)

`Work.SSGRoute.properStage_of_solvableStage` (the consumer of this node) does **not** currently
build in this workspace: compiling it alone exceeds the 12 GB cap, and its `.olean` is absent.  The
base cost of its imports is ~6.8 GB and importing this module adds ~0.6 GB (measured), so the excess
is in that file's own elaboration (its `obtain` of the 18-clause conclusion of this node, plus the
`iSup` rewriting in `surjective_of_iSup_map_eq_flowEKer`), not in this node: a minimal module that
imports this one and destructures the whole conclusion compiles in 7.4 GB, and
`Work.SSGRoute.scholz_succ_of_properStage`, `…theorem15_scholz`, … all have `.olean`s.  The lane's
workaround module `Work.SSGRoute.properStage_pushdown` (`psp_`-prefixed glue lemmas) exists for
exactly this reason.

### Lessons / pitfalls (unchanged)

* Never *prove* a lemma by destructuring `LiftsFlow`: it blows the 12 GB memory cap.  Use the
  equality form `flowGroupProj y = x` (`flowGroupProj_eq_of_liftsFlowAt_local`,
  `liftsFlowAt_of_flowGroupProj_eq`).
* `set_option backward.isDefEq.respectTransparency false` is required in any file mentioning
  `SSGRoute.res`/`decomp` on an `IntermediateField`.
* `Submission/Work/SSGRoute/stage_local_solvable.lean` redefines `flowQuotientProj`/`flowGroupProj`,
  so it cannot be imported together with `ProperStageDefs`; `twistLayer.lean` can (and is imported
  here: it supplies `flowTwistEHom`, `flowTwist_isOpen_ker`, `flowGroupProj_comp_flowTwistEHom`,
  `gradeInl_conj`, `eq_zero_of_isCoboundaryOn`, `map_flowTwistEHom_eq_map_of_x_eq_zero`, …).
* `Work.SSGRoute.gradedMapMul_surjective` (proved elsewhere) is the surjectivity of the rank change
  on the graded pieces, needed to lift prescribed elements of `E(n,τ)` to `E(m,τ)`.
-/

/-- **The involution clause of `ScholzConditions` is automatic under the exponent condition.**
If `μ_{p^{i+1}} ⊆ K` with `i ≥ 1` (so `p^{i+1} ≥ 4`) and `1 ≤ j ≤ i`, then `K.fixingSubgroup`
contains no involution other than `1` (`Work.SSGRoute.no_two_torsion_fixingSubgroup`), so

  `∀ c : G_ℚ, c ^ 2 = 1 → c ∈ K.fixingSubgroup → ψ c = 1`

holds for *every* homomorphism `ψ` out of `G_ℚ` — no hypothesis on `ψ` at all.  This removes the
involution clause from the list of obligations of Step 3 of Theorem 15. -/
theorem involution_clause_of_hasRootsOfUnity (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) (i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)
    (hμ : SSGRoute.HasRootsOfUnity p K i) {m : ℕ}
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2) :
    ∀ c : SSGRoute.GalQ, c ^ 2 = 1 → c ∈ K.fixingSubgroup → ψ c = 1 := by
  intro c hc hfix
  rw [no_two_torsion_fixingSubgroup p K i (le_trans hj hji) hμ c hc hfix, map_one]

/-- **The level-`n` datum of Step 3.**  From a Scholz solution `φm` at level `m` and a surjective
operator map `Φ : F(m) ⇢ F(n)` one obtains the fixed fields `N_m` (of `φm.ker`) and `N_n` (of the
kernel of `φn := (flowGroupMap Φ) ∘ φm`), the Galois identifications `em : Gal(N_m) ≃* Γ_m`,
`en : Gal(N_n) ≃* Γ_n`, the inclusion `N_n ≤ N_m` and the restriction map `q : Gal(N_m) →*
Gal(N_n)`.

This is exactly the datum in which the `∀`-clause of `SSGRoute.coker_obstruction` is applied: with
`N₂ = N_n`, `E₂ = E p (K ≃ₐ[ℚ] K) n i j`, `f = gradedMapLin Φ`, the coefficient morphism `F` with
`F.hom = f ⊗ id` being supplied by `Work.SSGRoute.transportH1_natural_of_compat`. -/
theorem pushdown_levelDatum (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] {m n i j : ℕ} (Φ : OperatorMap (K ≃ₐ[ℚ] K) m n)
    (φm : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (hSch : SSGRoute.IsScholzSolution p K m i j φm) :
    ∃ (Nm Nn : IntermediateField ℚ SSGRoute.QBar) (_ : FiniteDimensional ℚ Nm) (_ : Normal ℚ Nm)
      (_ : IsGalois ℚ Nm) (_ : FiniteDimensional ℚ Nn) (_ : Normal ℚ Nn) (_ : IsGalois ℚ Nn)
      (em : (Nm ≃ₐ[ℚ] Nm) ≃* flowGroup p (K ≃ₐ[ℚ] K) m i j)
      (en : (Nn ≃ₐ[ℚ] Nn) ≃* flowGroup p (K ≃ₐ[ℚ] K) n i j),
      K ≤ Nn ∧ Nn ≤ Nm ∧
      (∀ σ : SSGRoute.GalQ, em (SSGRoute.res ℚ Nm σ) = φm σ) ∧
      (∀ σ : SSGRoute.GalQ, en (SSGRoute.res ℚ Nn σ) =
        (flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ) (φm σ)) ∧
      ∃ q : (Nm ≃ₐ[ℚ] Nm) →* (Nn ≃ₐ[ℚ] Nn),
        (∀ x : (Nm ≃ₐ[ℚ] Nm), en (q x) = (flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ) (em x)) ∧
        (∀ σ : SSGRoute.GalQ, q (SSGRoute.res ℚ Nm σ) = SSGRoute.res ℚ Nn σ) := by
  have hφm := hSch.1
  obtain ⟨hsurjm, hopenm, hflowm⟩ := hφm
  set φn : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j :=
    (flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φm with hφn
  have hsurj : Function.Surjective φn :=
    (flowGroupMap_surjective_local p (K ≃ₐ[ℚ] K) i j Φ).comp hsurjm
  have hker_le : φm.ker ≤ φn.ker := by
    intro σ hσ
    rw [MonoidHom.mem_ker] at hσ ⊢
    rw [hφn, MonoidHom.comp_apply, hσ, map_one]
  have hopen : IsOpen (φn.ker : Set SSGRoute.GalQ) :=
    Subgroup.isOpen_mono hker_le hopenm
  have hflow : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n i j (φn σ) = SSGRoute.res ℚ K σ := by
    intro σ
    rw [hφn, MonoidHom.comp_apply, flowQuot_flowGroupMap]
    exact hflowm σ
  obtain ⟨Nm, hfdm, hnormm, hgalm, -, hfixm, em, hem⟩ :=
    fixedField_and_equiv p K m i j φm hsurjm hopenm hflowm
  obtain ⟨Nn, hfdn, hnormn, hgaln, hKNn, hfixn, en, hen⟩ :=
    fixedField_and_equiv p K n i j φn hsurj hopen hflow
  haveI hAlgClosure : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ
  haveI hGalQ : IsGalois ℚ SSGRoute.QBar :=
    { to_isSeparable := inferInstance, to_normal := inferInstance }
  have hle : Nn ≤ Nm := by
    have hle' : Nm.fixingSubgroup ≤ Nn.fixingSubgroup := by
      intro σ hσ
      rw [hfixn σ, hφn, MonoidHom.comp_apply]
      rw [hfixm σ] at hσ
      rw [hσ, map_one]
    calc Nn = IntermediateField.fixedField Nn.fixingSubgroup :=
          (InfiniteGalois.fixedField_fixingSubgroup (k := ℚ) (K := SSGRoute.QBar) Nn).symm
      _ ≤ IntermediateField.fixedField Nm.fixingSubgroup := IntermediateField.fixedField_le hle'
      _ = Nm := InfiniteGalois.fixedField_fixingSubgroup (k := ℚ) (K := SSGRoute.QBar) Nm
  refine ⟨Nm, Nn, hfdm, hnormm, hgalm, hfdn, hnormn, hgaln, em, en,
    hKNn, hle, hem, ?_, ?_⟩
  · intro σ
    rw [hen σ, hφn, MonoidHom.comp_apply]
  · set q : (Nm ≃ₐ[ℚ] Nm) →* (Nn ≃ₐ[ℚ] Nn) :=
          en.symm.toMonoidHom.comp ((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp em.toMonoidHom)
        with hq
    refine ⟨q, ?_, ?_⟩
    · intro x
      show en (en.symm ((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ) (em x))) =
        (flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ) (em x)
      exact MulEquiv.apply_symm_apply en _
    · intro σ
      refine en.injective ?_
      show en (en.symm ((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ) (em (SSGRoute.res ℚ Nm σ)))) =
        en (SSGRoute.res ℚ Nn σ)
      rw [MulEquiv.apply_symm_apply, hem σ, hen σ, hφn, MonoidHom.comp_apply]

/-- **One involution per conjugacy class of `G_ℚ`.**  Since all non-trivial involutions of `G_ℚ`
are conjugate (`Work.SSGRoute.involutions_eq_one_or_conjugate`; `ℚ` has a unique ordering), the
set of involutions of `G_ℚ` meets exactly one non-trivial conjugacy class, so a transversal of the
conjugacy classes of involutions can be taken to have one or two elements.  This is exactly the
`C` (with `hCinv`, `hC`, `hCdisj`) that `SSGRoute.coker_obstruction` over `ℚ` asks for. -/
theorem exists_involutionSet :
    ∃ C : Finset SSGRoute.GalQ,
      (∀ c ∈ C, c ^ 2 = 1) ∧
      (∀ c : SSGRoute.GalQ, c ^ 2 = 1 → c ≠ 1 →
        ∃ c₀ ∈ C, ∃ σ : SSGRoute.GalQ, c = σ * c₀ * σ⁻¹) ∧
      (∀ c ∈ C, ∀ c' ∈ C, (∃ σ : SSGRoute.GalQ, c' = σ * c * σ⁻¹) → c = c') := by
  classical
  by_cases h : ∃ c : SSGRoute.GalQ, c ^ 2 = 1 ∧ c ≠ 1
  · obtain ⟨c₀, hc₀sq, hc₀ne⟩ := h
    refine ⟨({1, c₀} : Finset SSGRoute.GalQ), ?_, ?_, ?_⟩
    · intro c hc
      rw [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · simp
      · exact hc₀sq
    · intro c hc2 hc1
      rcases involutions_eq_one_or_conjugate c c₀ hc2 hc₀sq with h1 | h2 | ⟨σ, hσ⟩
      · exact absurd h1 hc1
      · exact absurd h2 hc₀ne
      · exact ⟨c₀, by simp, σ⁻¹, by rw [hσ]; group⟩
    · intro c hc c' hc' hconj
      rw [Finset.mem_insert, Finset.mem_singleton] at hc hc'
      rcases hc with hc | hc <;> rcases hc' with hc' | hc'
      · exact hc.trans hc'.symm
      · obtain ⟨σ, hσ⟩ := hconj
        rw [hc, hc'] at hσ
        exact absurd (by simpa using hσ) hc₀ne
      · obtain ⟨σ, hσ⟩ := hconj
        rw [hc, hc'] at hσ
        exact absurd (by
          have h2 : σ⁻¹ * (1 : SSGRoute.GalQ) * σ = c₀ := by rw [hσ]; group
          simpa using h2.symm) hc₀ne
      · exact hc.trans hc'.symm
  · push_neg at h
    refine ⟨({1} : Finset SSGRoute.GalQ), ?_, ?_, ?_⟩
    · intro c hc
      rw [Finset.mem_singleton] at hc
      rw [hc]; simp
    · intro c hc2 hc1
      exact absurd (h c hc2) hc1
    · intro c hc c' hc' _
      rw [Finset.mem_singleton] at hc hc'
      rw [hc, hc']


/-! ## Naturality of the graded piece under the rank change; the `T¹` clause of Step 3

The inclusion `E(d,τ) ↪ Γ_{τ+1}(d)` (`gradeInl`) is natural in the rank `d` under a surjective
operator map `Φ : F(m) ⇢ F(n)`: this is what makes the level-`m` local target
`α_A σ = l_A σ · (ψ_m σ)⁻¹` at a `T¹`-place act on the level-`n` twist by the correct element, and
it is the algebraic content of the `T¹` part of the clause check of Step 3 of Theorem 15. -/

theorem flowQuotMap_gradeIncl (p : ℕ) (G : Type*) [Group G] {m n : ℕ} (Φ : OperatorMap G m n)
    (i j : ℕ) (v : refinedQuotient p (Work.Shrinking.freeOperatorGroup G m) i j) :
    flowQuotMap p G (tauSucc i j).1 (tauSucc i j).2 Φ (gradeIncl p G m i j v) =
      gradeIncl p G n i j (gradedMapMul p Φ.toHom Φ.surjective i j v) := by
  refine QuotientGroup.induction_on v ?_
  intro x
  rw [gradeIncl_apply, ← QuotientGroup.mk'_apply, gradedMapMul_of, gradeIncl_apply_mk',
    flowQuotMap_mk]
  exact congrArg (QuotientGroup.mk' _)
    (Subtype.ext (refinedMap_coe p Φ.toHom Φ.surjective i j x))

theorem flowGroupMap_gradeInl (p : ℕ) (G : Type*) [Group G] {m n : ℕ} (Φ : OperatorMap G m n)
    (i j : ℕ) (v : refinedQuotient p (Work.Shrinking.freeOperatorGroup G m) i j) :
    flowGroupMap p G (tauSucc i j).1 (tauSucc i j).2 Φ (gradeInl p G m i j v) =
      gradeInl p G n i j (gradedMapMul p Φ.toHom Φ.surjective i j v) := by
  rw [gradeInl, gradeInl, MonoidHom.comp_apply, MonoidHom.comp_apply, flowGroupMap_inl,
    flowQuotMap_gradeIncl]

theorem flowGroupMap_gradeInl_add (p : ℕ) (G : Type*) [Group G] {m n : ℕ} (Φ : OperatorMap G m n)
    (i j : ℕ) (v : E p G m i j) :
    flowGroupMap p G (tauSucc i j).1 (tauSucc i j).2 Φ
        (gradeInl p G m i j (Additive.toMul v)) =
      gradeInl p G n i j
        (Additive.toMul (gradedMapLin p Φ.toHom Φ.surjective i j v)) := by
  rw [flowGroupMap_gradeInl]
  congr 1

theorem flowGroupMap_gradeInl_toMul (p : ℕ) (G : Type*) [Group G] {m n : ℕ}
    (Φ : OperatorMap G m n) (i j : ℕ) (v : refinedQuotient p (Work.Shrinking.freeOperatorGroup G m) i j) :
    flowGroupMap p G (tauSucc i j).1 (tauSucc i j).2 Φ (gradeInl p G m i j v) =
      gradeInl p G n i j (Additive.toMul (gradedMapLin p Φ.toHom Φ.surjective i j (Additive.ofMul v))) := by
  rw [flowGroupMap_gradeInl]; congr 1

/-! ## The `T¹` clause of Step 3 -/

/-- **The `T¹`/`T³` local target of Step 3.**  At a place `A` whose decomposition group is contained
in the field of the level-`τ+1` lift `ψm` (i.e. `φm` is trivial on it, so that `ψm|_{D_A}` takes
values in the copy `E(m,τ)` of the graded piece), the local target

  `α_A σ := -ψm σ      (in the additive notation of `E(m,τ)`)`

is the one prescribed by Step 3 of Theorem 15: the twist `ε · ((Φ_* ∘ ψm))` by any global cocycle
`ε` whose local class at `A` agrees with `gradedMapLin Φ (α_A)` kills the decomposition group
`D_A ∩ G_K`.  This is condition (i) at the places of `T¹` (where the cocycle `ε` is the one supplied
by `SSGRoute.coker_obstruction` with the local target `α`), and the mechanism by which the places
of `T³` lose their ramification.

The proof is the chain

  `gradeInl (ε σ) = gradeInl (gradedMapLin Φ (α_A σ)) = Φ_* (gradeInl (α_A σ)) = Φ_* ((ψm σ)⁻¹)`,

in which the middle equality is the naturality of the graded piece under the rank change
(`flowGroupMap_gradeInl_add`). -/
theorem flowTwistE_eq_one_of_gradeInl_eq_inv (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K] {m n i j : ℕ}
    (Φ : OperatorMap (K ≃ₐ[ℚ] K) m n)
    (ψm : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m
      (tauSucc i j).1 (tauSucc i j).2)
    (A : ValuationSubring SSGRoute.QBar)
    (α : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) m i j)
    (ε : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (hα : ∀ σ : ↥(SSGRoute.decomp ℚ A),
      gradeInl p (K ≃ₐ[ℚ] K) m i j (Additive.toMul (α ↑σ)) = (ψm ↑σ)⁻¹)
    (hε : SSGRoute.IsCoboundaryOn (Work.SSGRoute.restrict K) (SSGRoute.decomp ℚ A)
      (fun σ => ε σ - gradedMapLin p Φ.toHom Φ.surjective i j (α σ))) :
    ∀ σ ∈ SSGRoute.decomp ℚ A, σ ∈ K.fixingSubgroup →
      flowTwistE p K n i j ε
        ((flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ).comp ψm) σ = 1 := by
  intro σ hσ hfix
  set σ' : ↥(SSGRoute.decomp ℚ A) := ⟨σ, hσ⟩ with hσ'
  have hε0 : ε σ - gradedMapLin p Φ.toHom Φ.surjective i j (α σ) = 0 :=
    eq_zero_of_isCoboundaryOn p K n i j hε σ hσ hfix
  have hεσ : ε σ = gradedMapLin p Φ.toHom Φ.surjective i j (α σ) := sub_eq_zero.mp hε0
  have hεσ' : ε σ = gradedMapLin p Φ.toHom Φ.surjective i j (α ↑σ') := hεσ
  have key : gradeInl p (K ≃ₐ[ℚ] K) n i j (Additive.toMul (ε σ)) =
      (flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ (ψm σ))⁻¹ := by
    rw [hεσ', ← flowGroupMap_gradeInl_add p (K ≃ₐ[ℚ] K) Φ i j (α ↑σ'), hα σ', map_inv]
  rw [flowTwistE, flowTwist, key]
  simp [MonoidHom.comp_apply]

/-! ### The copy of the graded piece inside `Γ_{τ+1}` -/

/-- **The kernel of the level projection is the copy of the graded piece**: an element of
`Γ_{τ+1}(n)` lies in `flowEKer` (i.e. projects to `1` at level `τ`) if and only if it is the image
of an element of `E(n,τ)` under `gradeInl`.  This is the identification used to read the local
targets of Step 3 (which the arithmetic `SSGRoute.coker_obstruction` provides as elements of
`E(m,τ)`) inside the ambient group `Γ_{τ+1}`. -/
theorem flowEKer_eq_range_gradeInl (p : ℕ) (G : Type*) [Group G] (n i j : ℕ) :
    flowEKer p G n i j = (gradeInl p G n i j).range := by
  ext x
  constructor
  · intro hx
    change x ∈ (flowGroupProj p G n i j).ker at hx
    rw [MonoidHom.mem_ker] at hx
    have hleft : flowQuotientProj p G n i j x.left = 1 := by
      have h := congrArg SemidirectProduct.left hx
      rwa [flowGroupProj, SemidirectProduct.map_left, SemidirectProduct.one_left] at h
    have hright : x.right = 1 := by
      have h := congrArg SemidirectProduct.right hx
      rwa [flowGroupProj, SemidirectProduct.map_right, MonoidHom.id_apply,
        SemidirectProduct.one_right] at h
    have hmem : x.left ∈ (stageProjQuotient p G n i j).ker := hleft
    rw [stageProjQuotient_ker] at hmem
    obtain ⟨v, hv⟩ := hmem
    refine ⟨v, ?_⟩
    show SemidirectProduct.mk (gradeIncl p G n i j v) 1 = x
    rw [show x = SemidirectProduct.mk x.left x.right from rfl, hv, hright]
  · rintro ⟨v, rfl⟩
    exact flowGroupProj_gradeInl p G n i j v

/-- Membership form of `flowEKer_eq_range_gradeInl`. -/
theorem mem_flowEKer_iff_exists_gradeInl (p : ℕ) (G : Type*) [Group G] (n i j : ℕ)
    (x : flowGroup p G n (tauSucc i j).1 (tauSucc i j).2) :
    x ∈ flowEKer p G n i j ↔ ∃ v, gradeInl p G n i j v = x := by
  rw [show flowEKer p G n i j = (gradeInl p G n i j).range from
    flowEKer_eq_range_gradeInl p G n i j]
  rfl

/-- **The `T¹` local target of Step 3.**  At a `T¹`-place `A` — a place over `Ram(K/ℚ) ∪ {p}` —
the local target prescribed by Step 3 is the ratio

  `α_A σ := l_A σ · (ψm σ)⁻¹`      (`σ ∈ D_A`),

where `l_A : D_A →* Γ_{τ+1}(m)` is the local splitting of `φm|_{D_A}` supplied by
`SSGRoute.IsSolvableStage` and `ψm` is the lift of `φm` (`α_A` takes values in `flowEKer = E(m,τ)`
because both factors project to `φm σ`; that it is a *cocycle* is
`localTargetT1_isCocycle`).

Its effect: if `ε` is a global `E(n,τ)`-valued cocycle whose local class at `A` agrees with
`gradedMapLin Φ (α_A)`, then the twist `ψ = ε · ((Φ_* ∘ ψm))` is trivial on `D_A ∩ G_K`, i.e.
condition (i) of the Scholz conditions holds at `A`.  The two inputs are the splitting property
`l_A σ = 1` whenever `φm σ = 1` and condition (i) at level `m` for `φm` (which gives `φm σ = 1`
for `σ ∈ D_A ∩ G_K`). -/
theorem flowTwistE_eq_one_of_T1Target (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K] {m n i j : ℕ}
    (Φ : OperatorMap (K ≃ₐ[ℚ] K) m n)
    (φm : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (ψm : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m
      (tauSucc i j).1 (tauSucc i j).2)
    (A : ValuationSubring SSGRoute.QBar)
    (l : ↥(SSGRoute.decomp ℚ A) →* flowGroup p (K ≃ₐ[ℚ] K) m
      (tauSucc i j).1 (tauSucc i j).2)
    (hl1 : ∀ σ : ↥(SSGRoute.decomp ℚ A), φm ↑σ = 1 → l σ = 1)
    (hT1m : ∀ σ ∈ SSGRoute.decomp ℚ A, σ ∈ K.fixingSubgroup → φm σ = 1)
    (α : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) m i j)
    (ε : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (hα : ∀ σ : ↥(SSGRoute.decomp ℚ A),
      gradeInl p (K ≃ₐ[ℚ] K) m i j (Additive.toMul (α ↑σ)) = l σ * (ψm ↑σ)⁻¹)
    (hε : SSGRoute.IsCoboundaryOn (Work.SSGRoute.restrict K) (SSGRoute.decomp ℚ A)
      (fun σ => ε σ - gradedMapLin p Φ.toHom Φ.surjective i j (α σ))) :
    ∀ σ ∈ SSGRoute.decomp ℚ A, σ ∈ K.fixingSubgroup →
      flowTwistE p K n i j ε
        ((flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ).comp ψm) σ = 1 := by
  intro σ hσ hfix
  set σ' : ↥(SSGRoute.decomp ℚ A) := ⟨σ, hσ⟩ with hσ'
  have hφ1 : φm ↑σ' = 1 := hT1m σ hσ hfix
  have hl : l σ' = 1 := hl1 σ' hφ1
  have hασ : gradeInl p (K ≃ₐ[ℚ] K) m i j (Additive.toMul (α ↑σ')) = (ψm ↑σ')⁻¹ := by
    rw [hα σ', hl, one_mul]
  have hε0 : ε σ - gradedMapLin p Φ.toHom Φ.surjective i j (α σ) = 0 :=
    eq_zero_of_isCoboundaryOn p K n i j hε σ hσ hfix
  have hεσ : ε σ = gradedMapLin p Φ.toHom Φ.surjective i j (α σ) := sub_eq_zero.mp hε0
  have key : gradeInl p (K ≃ₐ[ℚ] K) n i j (Additive.toMul (ε σ)) =
      (flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ (ψm σ))⁻¹ := by
    rw [hεσ, ← flowGroupMap_gradeInl_add p (K ≃ₐ[ℚ] K) Φ i j (α ↑σ'), hασ, map_inv]
  rw [flowTwistE, flowTwist, key]
  simp [MonoidHom.comp_apply]

/-! ### The `T⁰` clause of Step 3 -/

/-- **The `T⁰` clause of Step 3.**  Let `ψ` be a lift of the level-`τ` solution `ρ` whose fixed field
is `N`, and let `T⁰` be a finite set of places *completely decomposed* in `N`.  If, for every
`A ∈ T⁰`, the image of the decomposition group `D_A` under `ψ` contains an element of the graded
piece `E(n,τ)` (`gradeInl` of some `g A`), and the `g A` generate `E(n,τ)`, then

  `⨆_{A ∈ T⁰} ψ(D_A) = flowEKer p (K ≃ₐ[ℚ] K) n i j`,

i.e. the `T⁰`-generation of the copy of the graded piece inside `Γ_{τ+1}(n)`.  Chebotarev supplies
the places `T⁰` (with their Frobenius elements) and the arithmetic of
`SSGRoute.coker_obstruction` supplies the elements `g A`; this lemma is the bookkeeping that turns
them into the generation of `flowEKer`. -/
theorem iSup_map_eq_flowEKer_of_generators (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K] {n i j : ℕ}
    (N : IntermediateField ℚ SSGRoute.QBar)
    (ρ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (hproj : ∀ σ : SSGRoute.GalQ, flowGroupProj p (K ≃ₐ[ℚ] K) n i j (ψ σ) = ρ σ)
    (hker : ρ.ker = N.fixingSubgroup)
    (T0 : Finset (ValuationSubring SSGRoute.QBar))
    (hsplit : ∀ A ∈ T0, SSGRoute.IsSplitIn ℚ N A)
    (g : ValuationSubring SSGRoute.QBar → E p (K ≃ₐ[ℚ] K) n i j)
    (hg : ∀ A ∈ T0, gradeInl p (K ≃ₐ[ℚ] K) n i j (Additive.toMul (g A))
      ∈ (SSGRoute.decomp ℚ A).map ψ)
    (hgen : (⨆ A : ↥T0, Subgroup.zpowers (Additive.toMul (g A.1))) = ⊤) :
    (⨆ A ∈ T0, (SSGRoute.decomp ℚ A).map ψ) = flowEKer p (K ≃ₐ[ℚ] K) n i j := by
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun A hA => ?_
    rintro y ⟨σ, hσ, rfl⟩
    change ψ σ ∈ (flowGroupProj p (K ≃ₐ[ℚ] K) n i j).ker
    rw [MonoidHom.mem_ker, hproj, show ρ σ = 1 from by
      rw [← MonoidHom.mem_ker, hker]; exact hsplit A hA hσ]
  · have h1 : (⨆ A : ↥T0, Subgroup.zpowers (Additive.toMul (g A.1))).map
        (gradeInl p (K ≃ₐ[ℚ] K) n i j) = flowEKer p (K ≃ₐ[ℚ] K) n i j := by
      rw [hgen, ← MonoidHom.range_eq_map, flowEKer_eq_range_gradeInl]
    rw [← h1, Subgroup.map_iSup (gradeInl p (K ≃ₐ[ℚ] K) n i j)]
    refine iSup_le fun A => le_trans ?_ (le_iSup₂_of_le A.1 A.2 le_rfl)
    rw [t0_map_zpowers (gradeInl p (K ≃ₐ[ℚ] K) n i j) (Additive.toMul (g A.1))]
    exact Subgroup.zpowers_le.mpr (hg A.1 A.2)

/-! ### Interface of the twist with the clauses of Step 3 -/

/-- **The twist lifts the same level-`τ` solution** (in the additive notation of the arithmetic
input).  This is the `LiftsFlow` clause of Step 3 for `ψ := ε · ((Φ_* ∘ ψm))`; it is
`flowGroupProj_comp_flowTwistEHom` read through `liftsFlowAt_of_flowGroupProj_eq`. -/
theorem flowTwistEHom_liftsFlow (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K] (n i j : ℕ)
    (ε : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j)
    (hψquot : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (ψ σ) =
      Work.SSGRoute.restrict K σ)
    (hxmul : ∀ σ τ : SSGRoute.GalQ, ε (σ * τ) = ε σ + (Work.SSGRoute.restrict K σ) • ε τ)
    (hLift : ∀ σ : SSGRoute.GalQ, SSGRoute.LiftsFlowAt (ψ σ) (φ σ)) :
    SSGRoute.LiftsFlow (flowTwistEHom p K n i j ε ψ hψquot hxmul) φ := by
  intro σ
  refine liftsFlowAt_of_flowGroupProj_eq p K i j _ _ ?_
  have h1 := congrFun (congrArg DFunLike.coe
    (flowGroupProj_comp_flowTwistEHom p K n i j ε ψ φ hψquot hxmul hLift)) σ
  simpa using h1

/-- **The twist has open kernel** (continuity for the discrete topology on `Γ_{τ+1}(n)`) as soon as
`ψ` has open kernel and the twisting cocycle is locally constant. -/
theorem flowTwistEHom_isOpen_ker (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K] (n i j : ℕ)
    (ε : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (hψquot : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (ψ σ) =
      Work.SSGRoute.restrict K σ)
    (hxmul : ∀ σ τ : SSGRoute.GalQ, ε (σ * τ) = ε σ + (Work.SSGRoute.restrict K σ) • ε τ)
    (hopen : IsOpen (ψ.ker : Set SSGRoute.GalQ))
    (hx : SSGRoute.IsLocConstOn ⊤ ε) :
    IsOpen ((flowTwistEHom p K n i j ε ψ hψquot hxmul).ker : Set SSGRoute.GalQ) :=
  flowTwist_isOpen_ker p K n i j (fun σ => Additive.toMul (ε σ)) ψ hψquot
    (fun σ τ => by rw [hxmul σ τ]; rfl) hopen hx

/-- **Clause (ii), first part, from the first disjunct.**  If the level-`τ` solution `ρ` vanishes on
the decomposition group of `A` and its fixed field `N` contains `K`, then `D_A ≤ G_K`: this is the
"`A` splits completely in `K`" half of condition (ii) of Theorem 15. -/
theorem decomp_le_fixingSubgroup_of_map_eq_one (p : ℕ) [Fact p.Prime]
    (K N : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K] {n i j : ℕ}
    (ρ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j)
    (hker : ρ.ker = N.fixingSubgroup) (hKN : K ≤ N) (A : ValuationSubring SSGRoute.QBar)
    (h : ∀ σ ∈ SSGRoute.decomp ℚ A, ρ σ = 1) :
    ∀ σ ∈ SSGRoute.decomp ℚ A, σ ∈ K.fixingSubgroup := by
  intro σ hσ
  have hmem : σ ∈ ρ.ker := by rw [MonoidHom.mem_ker]; exact h σ hσ
  rw [hker] at hmem
  exact IntermediateField.fixingSubgroup_le hKN hmem

/-- **Clause (ii) transfers across the twist wherever the twisting cocycle vanishes.**  If `ε`
vanishes on the decomposition group `D_A` of a place `A`, then the local group of the twist
`ε · ψ` is the local group of `ψ` itself: this is how condition (ii) at the places of `T⁰`, and the
places where the arithmetic prescribes no local component (the places of `T³`), is inherited from
the level-`τ+1` solution `ψ` obtained in Step 2. -/
theorem isCyclic_and_inertia_generates_of_cocycle_zero (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K] (n i j : ℕ)
    (ε : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (hψquot : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (ψ σ) =
      Work.SSGRoute.restrict K σ)
    (hxmul : ∀ σ τ : SSGRoute.GalQ, ε (σ * τ) = ε σ + (Work.SSGRoute.restrict K σ) • ε τ)
    (A : ValuationSubring SSGRoute.QBar)
    (hx0 : ∀ σ ∈ SSGRoute.decomp ℚ A, ε σ = 0)
    (hcyc : IsCyclic ((SSGRoute.decomp ℚ A).map ψ))
    (hgen : ∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧ ψ τ = ψ σ) :
    IsCyclic ((SSGRoute.decomp ℚ A).map (flowTwistEHom p K n i j ε ψ hψquot hxmul)) ∧
      ∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧
        (flowTwistEHom p K n i j ε ψ hψquot hxmul) τ =
          (flowTwistEHom p K n i j ε ψ hψquot hxmul) σ := by
  have hmap := map_flowTwistEHom_eq_map_of_x_eq_zero p K n i j ε ψ hψquot hxmul hx0
  have heq : ∀ σ ∈ SSGRoute.decomp ℚ A,
      (flowTwistEHom p K n i j ε ψ hψquot hxmul) σ = ψ σ :=
    fun σ hσ => flowTwistE_eq_of_eq_zero p K n i j ε ψ hx0 σ hσ
  refine ⟨?_, ?_⟩
  · rw [hmap]; exact hcyc
  · intro σ hσ
    obtain ⟨τ, hτI, hτψ⟩ := hgen σ hσ
    exact ⟨τ, hτI, by rw [heq τ hτI.1, heq σ hσ, hτψ]⟩

/-! ### The `T³` local target of Step 3

At a place `A` where the level-`τ+1` lift `ψm` already takes its values in the copy `E(m,τ)` of the
graded piece (i.e. where the level-`τ` solution `φm` is trivial on `D_A`), the local target
prescribed by Step 3 is

  `α_A σ := -ψm σ`      (multiplicatively: `gradeInl (α_A σ) = (ψm σ)⁻¹`).

It is a genuine `1`-cocycle for the action of `D_A` through `Gal(K/ℚ)` — the crossed-homomorphism
identity is exactly the conjugation formula `gradeInl_conj` — and the twist by any global cocycle
whose local class at `A` agrees with `gradedMapLin Φ (α_A)` kills the whole decomposition group
`D_A` (`SSGRoute.flowTwistE_eq_one_of_gradeInl_eq_inv`).  At the `T³` places this is what removes
the ramification introduced by the level-`m` lift. -/

/-- (speed) `flowQuot` after the level projection, proved once for an abstract group: the concrete
instances of the callers made the kernel check of the inline `rfl` slow. -/
theorem flowQuot_flowGroupProj_psad (p : ℕ) (G : Type*) [Group G] (m i j : ℕ)
    (y : flowGroup p G m (tauSucc i j).1 (tauSucc i j).2) :
    flowQuot p G m (tauSucc i j).1 (tauSucc i j).2 y = flowQuot p G m i j (flowGroupProj p G m i j y) := by
  rw [flowQuot, flowQuot, SemidirectProduct.rightHom_eq_right, SemidirectProduct.rightHom_eq_right,
    flowGroupProj, SemidirectProduct.map_right, MonoidHom.id_apply]

/-- **Existence of the `T³` local target.**  If `ψm` is a lift of the level-`τ` solution `φm` with
open kernel and `φm` is trivial on the decomposition group of `A` (so that `ψm` maps `D_A` into the
copy `flowEKer = E(m,τ)` of the graded piece), then there is an `E(m,τ)`-valued function `α` on
`G_ℚ`, a `1`-cocycle for the action through `Gal(K/ℚ)` and locally constant on `D_A`, with

  `gradeInl (α σ) = (ψm σ)⁻¹`      (`σ ∈ D_A`). -/
theorem exists_localTarget_of_proj_eq_one (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K] {m i j : ℕ}
    (φm : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (ψm : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m
      (tauSucc i j).1 (tauSucc i j).2)
    (hproj : ∀ σ : SSGRoute.GalQ, flowGroupProj p (K ≃ₐ[ℚ] K) m i j (ψm σ) = φm σ)
    (hflowm : ∀ σ : SSGRoute.GalQ,
      flowQuot p (K ≃ₐ[ℚ] K) m i j (φm σ) = Work.SSGRoute.restrict K σ)
    (hopen : IsOpen (ψm.ker : Set SSGRoute.GalQ))
    (A : ValuationSubring SSGRoute.QBar)
    (hφm1 : ∀ σ ∈ SSGRoute.decomp ℚ A, φm σ = 1) :
    ∃ α : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) m i j,
      SSGRoute.IsCocycleOn (Work.SSGRoute.restrict K) (SSGRoute.decomp ℚ A) α ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp ℚ A) α ∧
      ∀ σ : ↥(SSGRoute.decomp ℚ A),
        gradeInl p (K ≃ₐ[ℚ] K) m i j (Additive.toMul (α ↑σ)) = (ψm ↑σ)⁻¹ := by
  classical
  have hquot : ∀ σ : SSGRoute.GalQ, flowQuot p (K ≃ₐ[ℚ] K) m
      (tauSucc i j).1 (tauSucc i j).2 (ψm σ) = Work.SSGRoute.restrict K σ := by
    intro σ
    have h1 : flowQuot p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2 (ψm σ) =
        flowQuot p (K ≃ₐ[ℚ] K) m i j (flowGroupProj p (K ≃ₐ[ℚ] K) m i j (ψm σ)) :=
      flowQuot_flowGroupProj_psad p (K ≃ₐ[ℚ] K) m i j (ψm σ)
    rw [h1, hproj σ, hflowm σ]
  have hval : ∀ σ : ↥(SSGRoute.decomp ℚ A),
      ∃ v : E p (K ≃ₐ[ℚ] K) m i j,
        gradeInl p (K ≃ₐ[ℚ] K) m i j (Additive.toMul v) = (ψm ↑σ)⁻¹ := by
    intro σ
    have hmem : ψm ↑σ ∈ flowEKer p (K ≃ₐ[ℚ] K) m i j := by
      change ψm ↑σ ∈ (flowGroupProj p (K ≃ₐ[ℚ] K) m i j).ker
      rw [MonoidHom.mem_ker, hproj ↑σ, hφm1 ↑σ σ.2]
    obtain ⟨v, hv⟩ :=
      (mem_flowEKer_iff_exists_gradeInl p (K ≃ₐ[ℚ] K) m i j (ψm ↑σ)).mp hmem
    refine ⟨Additive.ofMul v⁻¹, ?_⟩
    show gradeInl p (K ≃ₐ[ℚ] K) m i j v⁻¹ = (ψm ↑σ)⁻¹
    rw [map_inv, hv]
  let αD : ↥(SSGRoute.decomp ℚ A) → E p (K ≃ₐ[ℚ] K) m i j := fun σ => (hval σ).choose
  have hαD : ∀ σ : ↥(SSGRoute.decomp ℚ A),
      gradeInl p (K ≃ₐ[ℚ] K) m i j (Additive.toMul (αD σ)) = (ψm ↑σ)⁻¹ :=
    fun σ => (hval σ).choose_spec
  refine ⟨fun σ => if h : σ ∈ SSGRoute.decomp ℚ A then αD ⟨σ, h⟩ else 0, ?_, ?_, ?_⟩
  · intro g hg h hh
    have hg1 : (fun σ => if h : σ ∈ SSGRoute.decomp ℚ A then αD ⟨σ, h⟩ else 0) g
        = αD ⟨g, hg⟩ := dif_pos hg
    have hh1 : (fun σ => if h : σ ∈ SSGRoute.decomp ℚ A then αD ⟨σ, h⟩ else 0) h
        = αD ⟨h, hh⟩ := dif_pos hh
    have hgh1 : (fun σ => if h : σ ∈ SSGRoute.decomp ℚ A then αD ⟨σ, h⟩ else 0) (g * h)
        = αD ⟨g * h, Subgroup.mul_mem _ hg hh⟩ := dif_pos (Subgroup.mul_mem _ hg hh)
    rw [hgh1, hg1, hh1]
    apply Additive.toMul.injective
    rw [toMul_add]
    have hsm : Additive.toMul ((Work.SSGRoute.restrict K g) • αD ⟨h, hh⟩)
        = (Work.SSGRoute.restrict K g) • Additive.toMul (αD ⟨h, hh⟩) := rfl
    rw [hsm]
    apply gradeInl_injective p (K ≃ₐ[ℚ] K) m i j
    rw [map_mul, hαD ⟨g * h, Subgroup.mul_mem _ hg hh⟩, hαD ⟨g, hg⟩,
      ← gradeInl_conj p K m i j ψm g (hquot g) (Additive.toMul (αD ⟨h, hh⟩)), hαD ⟨h, hh⟩]
    simp only [map_inv, map_mul]
    group
  · refine ⟨ψm.ker, hopen, ?_⟩
    intro g hg u hu huH
    have h1 : (fun σ => if h : σ ∈ SSGRoute.decomp ℚ A then αD ⟨σ, h⟩ else 0) (g * u)
        = αD ⟨g * u, Subgroup.mul_mem _ hg huH⟩ := dif_pos (Subgroup.mul_mem _ hg huH)
    have h2 : (fun σ => if h : σ ∈ SSGRoute.decomp ℚ A then αD ⟨σ, h⟩ else 0) g
        = αD ⟨g, hg⟩ := dif_pos hg
    rw [h1, h2]
    apply Additive.toMul.injective
    apply gradeInl_injective p (K ≃ₐ[ℚ] K) m i j
    rw [hαD ⟨g * u, Subgroup.mul_mem _ hg huH⟩, hαD ⟨g, hg⟩, map_mul,
      MonoidHom.mem_ker.mp hu, mul_one]
  · intro σ
    have h1 : (fun τ => if h : τ ∈ SSGRoute.decomp ℚ A then αD ⟨τ, h⟩ else 0) (↑σ)
        = αD ⟨(↑σ : SSGRoute.GalQ), σ.2⟩ := dif_pos σ.2
    rw [h1]
    exact hαD σ

/-- **Condition (ii) at a place where the local extension is split over the graded piece.**
If the local group of the level-`τ+1` map `ψ` meets the copy `E(n,τ)` of the graded piece trivially
(the local extension of the level-`τ+1` field over the level-`τ` field is split at `A`), then the
local group of `ψ` is isomorphic to the local group of the level-`τ` solution `ρ`; hence, whenever
the latter is cyclic and generated by inertia, so is the former.  This is the "trivial" half of the
`T²` prescription of Step 3 of Theorem 15. -/
theorem isCyclic_and_inertia_generates_of_kernel_disjoint (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K] {n i j : ℕ}
    (ρ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (hproj : ∀ σ : SSGRoute.GalQ, flowGroupProj p (K ≃ₐ[ℚ] K) n i j (ψ σ) = ρ σ)
    (A : ValuationSubring SSGRoute.QBar)
    (hdisj : (SSGRoute.decomp ℚ A).map ψ ⊓ flowEKer p (K ≃ₐ[ℚ] K) n i j = ⊥)
    (hcyc : IsCyclic ((SSGRoute.decomp ℚ A).map ρ))
    (hgen : ∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧ ρ τ = ρ σ) :
    IsCyclic ((SSGRoute.decomp ℚ A).map ψ) ∧
      ∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧ ψ τ = ψ σ := by
  have hmap : ((SSGRoute.decomp ℚ A).map ψ).map (flowGroupProj p (K ≃ₐ[ℚ] K) n i j)
      = (SSGRoute.decomp ℚ A).map ρ := by
    rw [Subgroup.map_map, show (flowGroupProj p (K ≃ₐ[ℚ] K) n i j).comp ψ = ρ from
      MonoidHom.ext hproj]
  let f : ↥((SSGRoute.decomp ℚ A).map ψ) →* ↥((SSGRoute.decomp ℚ A).map ρ) :=
    { toFun := fun y => ⟨flowGroupProj p (K ≃ₐ[ℚ] K) n i j y.1, by
        rw [← hmap]; exact Subgroup.mem_map_of_mem _ y.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ a.1 b.1) }
  have hf_inj : Function.Injective f := by
    intro x y hxy
    have hxy' : flowGroupProj p (K ≃ₐ[ℚ] K) n i j x.1 =
        flowGroupProj p (K ≃ₐ[ℚ] K) n i j y.1 := Subtype.ext_iff.mp hxy
    have h1 : flowGroupProj p (K ≃ₐ[ℚ] K) n i j (x.1 * y.1⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy', mul_inv_cancel]
    have h2 : x.1 * y.1⁻¹ ∈ (SSGRoute.decomp ℚ A).map ψ ⊓ flowEKer p (K ≃ₐ[ℚ] K) n i j :=
      ⟨Subgroup.mul_mem _ x.2 (Subgroup.inv_mem _ y.2),
        show x.1 * y.1⁻¹ ∈ (flowGroupProj p (K ≃ₐ[ℚ] K) n i j).ker from
          MonoidHom.mem_ker.mpr h1⟩
    rw [hdisj, Subgroup.mem_bot] at h2
    exact Subtype.ext (mul_inv_eq_one.mp h2)
  haveI : IsCyclic ↥((SSGRoute.decomp ℚ A).map ρ) := hcyc
  refine ⟨isCyclic_of_injective f hf_inj, ?_⟩
  intro σ hσ
  obtain ⟨τ, hτI, hτρ⟩ := hgen σ hσ
  have hmem : τ⁻¹ * σ ∈ SSGRoute.decomp ℚ A :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hτI.1) hσ
  have h1 : ψ (τ⁻¹ * σ) = 1 := by
    have hproj1 : flowGroupProj p (K ≃ₐ[ℚ] K) n i j (ψ (τ⁻¹ * σ)) = 1 := by
      rw [hproj, map_mul, map_inv, hτρ, inv_mul_cancel]
    have hmem2 : ψ (τ⁻¹ * σ) ∈
        (SSGRoute.decomp ℚ A).map ψ ⊓ flowEKer p (K ≃ₐ[ℚ] K) n i j :=
      ⟨Subgroup.mem_map_of_mem ψ hmem,
        show ψ (τ⁻¹ * σ) ∈ (flowGroupProj p (K ≃ₐ[ℚ] K) n i j).ker from
          MonoidHom.mem_ker.mpr hproj1⟩
    rw [hdisj, Subgroup.mem_bot] at hmem2
    exact hmem2
  refine ⟨τ, hτI, ?_⟩
  have h2 : ψ τ * ψ (τ⁻¹ * σ) = ψ σ := by
    rw [← map_mul]
    congr 1
    group
  rwa [h1, mul_one] at h2

/-! ### The rank change on the graded pieces, and a section of it -/

/-- **The rank change `E(m,τ) → E(n,τ)` is surjective.**  This is the additive form of
`Work.SSGRoute.gradedMapMul_surjective` (proved in the sibling module
`Submission.Work.SSGRoute.gradedMapMul_surjective`); it is what allows one to prescribe elements of
the level-`n` graded piece `E(n,τ)` by their level-`m` pre-images in the local targets of Step 3. -/
theorem gradedMapLin_surjective_local (p : ℕ) (G : Type*) [Group G] {m n : ℕ}
    (Φ : OperatorMap G m n) (i j : ℕ) :
    Function.Surjective (gradedMapLin p Φ.toHom Φ.surjective i j) := by
  intro y
  obtain ⟨w, hw⟩ := gradedMapMul_surjective p G Φ i j (Additive.toMul y)
  refine ⟨Additive.ofMul w, ?_⟩
  show Additive.ofMul (gradedMapMul p Φ.toHom Φ.surjective i j w) = y
  rw [hw]
  rfl

/-- **A section of the rank change on the graded pieces.**  Every element of `E(n,τ)` is the image
of an element of `E(m,τ)` under the rank change; this is the form in which Step 3 prescribes the
local targets at level `m` by their effect at level `n`. -/
theorem exists_section_gradedMapLin (p : ℕ) (G : Type*) [Group G] {m n : ℕ}
    (Φ : OperatorMap G m n) (i j : ℕ) :
    ∃ s : E p G n i j → E p G m i j,
      ∀ v, gradedMapLin p Φ.toHom Φ.surjective i j (s v) = v :=
  ⟨fun v => Classical.choose (gradedMapLin_surjective_local p G Φ i j v),
    fun v => Classical.choose_spec (gradedMapLin_surjective_local p G Φ i j v)⟩

/-- **The `T⁰` clause of Step 3 from the arithmetic's prescribed local values.**  This is the
end-to-end form of the `T⁰` clause for the twist `ψ := ε · ((Φ_* ∘ ψm))`: given a finite set `T⁰` of
finite places completely decomposed in the field `N` of the level-`τ` solution `ρ`, local targets
`α A` at level `m`, and a global cocycle `ε` whose local class at each `A ∈ T⁰` agrees with
`gradedMapLin Φ (α A)` (the hypothesis `hε`, which is exactly one conjunct of the output of
`SSGRoute.coker_obstruction`), together with the prescribed values `hge` of the targets at the
Frobenius elements `F_A`, the images of the decomposition groups under `ψ` generate the copy
`flowEKer p G n i j` of `E(n,τ)`:
this is the properness condition of Step 3 of Theorem 15. -/
theorem iSup_map_eq_flowEKer_of_prescribed_values (p : ℕ) [Fact p.Prime]
    (K N : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K] {m n i j : ℕ}
    (Φ : OperatorMap (K ≃ₐ[ℚ] K) m n)
    (ρ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j)
    (ψ₀ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (hproj : ∀ σ : SSGRoute.GalQ, flowGroupProj p (K ≃ₐ[ℚ] K) n i j (ψ₀ σ) = ρ σ)
    (hker : ρ.ker = N.fixingSubgroup) (hKN : K ≤ N)
    (T0 : Finset (ValuationSubring SSGRoute.QBar))
    (hT0fin : ∀ A ∈ T0, SSGRoute.IsFinPlace ℚ A)
    (hT0split : ∀ A ∈ T0, SSGRoute.IsSplitIn ℚ N A)
    (α : ValuationSubring SSGRoute.QBar → SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) m i j)
    (ε : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (hψeq : ∀ σ : SSGRoute.GalQ, ψ σ = flowTwistE p K n i j ε ψ₀ σ)
    (hε : ∀ A (hA : A ∈ T0), SSGRoute.IsCoboundaryOn (Work.SSGRoute.restrict K)
      (SSGRoute.decomp ℚ A)
      (fun σ => ε σ - gradedMapLin p Φ.toHom Φ.surjective i j (α A σ)))
    (g : ValuationSubring SSGRoute.QBar → E p (K ≃ₐ[ℚ] K) n i j)
    (hg : ∀ A (hA : A ∈ T0), ∃ e : E p (K ≃ₐ[ℚ] K) n i j,
      gradeInl p (K ≃ₐ[ℚ] K) n i j (Additive.toMul e) =
        ψ₀ ((Work.SSGRoute.localFrobElem ⟨A, hT0fin A hA⟩ :
          ↥(SSGRoute.decomp ℚ A)) : SSGRoute.GalQ) ∧
      gradedMapLin p Φ.toHom Φ.surjective i j
        (α A ((Work.SSGRoute.localFrobElem ⟨A, hT0fin A hA⟩ :
          ↥(SSGRoute.decomp ℚ A)) : SSGRoute.GalQ)) = g A - e)
    (hgen : (⨆ A : ↥T0, Subgroup.zpowers (Additive.toMul (g A.1))) = ⊤) :
    (⨆ A ∈ T0, (SSGRoute.decomp ℚ A).map ψ) = flowEKer p (K ≃ₐ[ℚ] K) n i j := by
  have hprojψ : ∀ σ : SSGRoute.GalQ,
      flowGroupProj p (K ≃ₐ[ℚ] K) n i j (ψ σ) = ρ σ := by
    intro σ
    rw [hψeq σ]
    show flowGroupProj p (K ≃ₐ[ℚ] K) n i j
      (gradeInl p (K ≃ₐ[ℚ] K) n i j (Additive.toMul (ε σ)) * ψ₀ σ) = ρ σ
    rw [map_mul, flowGroupProj_gradeInl, one_mul, hproj σ]
  refine iSup_map_eq_flowEKer_of_generators p K N ρ ψ hprojψ hker T0 hT0split g ?_ hgen
  intro A hA
  set F : ↥(SSGRoute.decomp ℚ A) := Work.SSGRoute.localFrobElem ⟨A, hT0fin A hA⟩ with hF
  have hFD : (F : SSGRoute.GalQ) ∈ SSGRoute.decomp ℚ A := F.2
  have hfix : (F : SSGRoute.GalQ) ∈ K.fixingSubgroup :=
    IntermediateField.fixingSubgroup_le hKN (hT0split A hA hFD)
  have hεF : ε (F : SSGRoute.GalQ) =
      gradedMapLin p Φ.toHom Φ.surjective i j (α A (F : SSGRoute.GalQ)) := by
    have h := eq_zero_of_isCoboundaryOn p K n i j (hε A hA) (F : SSGRoute.GalQ) hFD hfix
    exact sub_eq_zero.mp h
  obtain ⟨e, he, hge⟩ := hg A hA
  have key : ψ (F : SSGRoute.GalQ) =
      gradeInl p (K ≃ₐ[ℚ] K) n i j (Additive.toMul (g A)) := by
    rw [hψeq]
    show gradeInl p (K ≃ₐ[ℚ] K) n i j (Additive.toMul (ε (F : SSGRoute.GalQ))) *
      ψ₀ (F : SSGRoute.GalQ) = gradeInl p (K ≃ₐ[ℚ] K) n i j (Additive.toMul (g A))
    rw [hεF, hge, ← he, toMul_sub, map_div, div_mul_cancel]
  exact Subgroup.mem_map.mpr ⟨(F : SSGRoute.GalQ), hFD, key⟩

/-! ## Clause (ii) at the `T²` places: the level-`n` twist is the push-forward of the level-`m` twist

At a place `A` with `D_A ≤ G_K` the coboundary conditions of the arithmetic input say that the
coefficient `ε` of the twist at level `n` is `gradedMapLin Φ ∘ α_A` *pointwise* on `D_A`.  Hence the
level-`n` twist of `(flowGroupMap Φ) ∘ ψm` is the push-forward, under the surjective rank change
`flowGroupMap Φ`, of the level-`m` twist of `ψm` by `α_A`.  Cyclicity and inertia-generation
therefore transfer from level `m` to level `n` — which is how condition (ii) of Theorem 15 is
obtained at the `T²` places (there the twist cannot be made trivial, only cyclic). -/

/-- The closure of the image of a set under a homomorphism is the image of the closure. -/
theorem closure_image_eq_map_local {G H : Type*} [Group G] [Group H] (f : G →* H) (S : Set G) :
    Subgroup.closure (f '' S) = (Subgroup.closure S).map f := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.closure_le]
    rintro _ ⟨s, hs, rfl⟩
    exact Subgroup.mem_map_of_mem f (Subgroup.subset_closure hs)
  · rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    intro s hs
    exact Subgroup.subset_closure ⟨s, hs, rfl⟩

/-- The image of a cyclic subgroup under a homomorphism is cyclic. -/
theorem isCyclic_map_of_isCyclic_local {G H : Type*} [Group G] [Group H] (f : G →* H)
    (H' : Subgroup G) (h : IsCyclic ↥H') : IsCyclic ↥(H'.map f) := by
  let F : ↥H' →* ↥(H'.map f) :=
    { toFun := fun x => ⟨f x.1, Subgroup.mem_map_of_mem f x.2⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun a b => Subtype.ext (map_mul f a.1 b.1) }
  have hsurj : Function.Surjective F := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, rfl⟩
  exact isCyclic_of_surjective F hsurj

/-- **Cyclicity of the local group transfers to the push-forward.** -/
theorem isCyclic_closure_image_of_pushforward {G H : Type*} [Group G] [Group H] (f : G →* H)
    (S : Set G) (h : IsCyclic (Subgroup.closure S)) :
    IsCyclic (Subgroup.closure (f '' S)) := by
  rw [closure_image_eq_map_local]
  exact isCyclic_map_of_isCyclic_local f _ h

/-- **The level-`n` twist is the push-forward of the level-`m` twist** at a place where the
arithmetic prescribes `ε = gradedMapLin Φ ∘ α` pointwise. -/
theorem flowTwistE_pushforward (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [Normal ℚ K] {m n i j : ℕ} (Φ : OperatorMap (K ≃ₐ[ℚ] K) m n)
    (ψm : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2)
    (α : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) m i j)
    (ε : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    {H : Subgroup SSGRoute.GalQ}
    (hε : ∀ σ ∈ H, ε σ = gradedMapLin p Φ.toHom Φ.surjective i j (α σ)) :
    ∀ σ ∈ H,
      flowTwistE p K n i j ε
          ((flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ).comp ψm) σ
        = flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ
            (flowTwistE p K m i j α ψm σ) := by
  intro σ hσ
  have key : gradeInl p (K ≃ₐ[ℚ] K) n i j (Additive.toMul (ε σ))
      = flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ
          (gradeInl p (K ≃ₐ[ℚ] K) m i j (Additive.toMul (α σ))) := by
    rw [hε σ hσ, flowGroupMap_gradeInl_toMul, _root_.ofMul_toMul]
  rw [flowTwistE, flowTwist, flowTwistE, flowTwist, key]
  simp only [MonoidHom.comp_apply, MonoidHom.map_mul]

/-- **Condition (ii) at the `T²` places, transferred from level `m` to level `n`.**  If the level-`m`
twist of `ψm` by `α` has cyclic, inertia-generated local group at `A`, and the level-`n` coefficient
`ε` agrees with `gradedMapLin Φ ∘ α` pointwise on `D_A`, then the level-`n` twist of
`(flowGroupMap Φ) ∘ ψm` has the same two properties. -/
theorem isCyclic_and_inertia_generates_pushforward (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K] {m n i j : ℕ}
    (Φ : OperatorMap (K ≃ₐ[ℚ] K) m n)
    (ψm : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2)
    (α : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) m i j)
    (ε : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (A : ValuationSubring SSGRoute.QBar)
    (hε : ∀ σ ∈ SSGRoute.decomp ℚ A,
      ε σ = gradedMapLin p Φ.toHom Φ.surjective i j (α σ))
    (hcyc : IsCyclic (Subgroup.closure
      ((flowTwistE p K m i j α ψm) '' (SSGRoute.decomp ℚ A : Set SSGRoute.GalQ))))
    (hgen : ∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧
      flowTwistE p K m i j α ψm τ = flowTwistE p K m i j α ψm σ) :
    IsCyclic (Subgroup.closure
        ((flowTwistE p K n i j ε
            ((flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ).comp ψm)) ''
          (SSGRoute.decomp ℚ A : Set SSGRoute.GalQ))) ∧
      (∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧
        flowTwistE p K n i j ε
            ((flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ).comp ψm) τ =
          flowTwistE p K n i j ε
            ((flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ).comp ψm) σ) := by
  have hpush := flowTwistE_pushforward p K Φ ψm α ε hε
  have hset : ((flowTwistE p K n i j ε
        ((flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ).comp ψm)) ''
          (SSGRoute.decomp ℚ A : Set SSGRoute.GalQ))
      = (flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ) ''
          ((flowTwistE p K m i j α ψm) '' (SSGRoute.decomp ℚ A : Set SSGRoute.GalQ)) := by
    ext y
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      exact ⟨flowTwistE p K m i j α ψm σ, ⟨σ, hσ, rfl⟩, (hpush σ hσ).symm⟩
    · rintro ⟨_, ⟨σ, hσ, rfl⟩, rfl⟩
      exact ⟨σ, hσ, hpush σ hσ⟩
  refine ⟨?_, ?_⟩
  · rw [hset]
    exact isCyclic_closure_image_of_pushforward _ _ hcyc
  · intro σ hσ
    obtain ⟨τ, hτ, heq⟩ := hgen σ hσ
    exact ⟨τ, hτ, by rw [hpush τ hτ.1, hpush σ hσ, heq]⟩


/-- **Clause (ii) at a place completely decomposed in `N_m`.**  If the level-`τ` solution `φm` is
trivial on the decomposition group of `A` and `N` is its fixed field over `K`, then `D_A ≤ G_K` and
the pushed-down level-`n` solution `φn = (flowGroupMap Φ) ∘ φm` is trivial on `D_A` as well: this is
the *first disjunct* of condition (ii) of Theorem 15, and it needs no information about the level-
`τ+1` lift `ψ`. -/
theorem clause_ii_of_map_eq_one (p : ℕ) [Fact p.Prime] (K N : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] [FiniteDimensional ℚ N] [Normal ℚ N]
    {m n i j : ℕ} (Φ : OperatorMap (K ≃ₐ[ℚ] K) m n)
    (φm : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (hker : φm.ker = N.fixingSubgroup) (hKN : K ≤ N)
    (A : ValuationSubring SSGRoute.QBar)
    (hφmA : ∀ σ ∈ SSGRoute.decomp ℚ A, φm σ = 1) :
    (∀ σ ∈ SSGRoute.decomp ℚ A, σ ∈ K.fixingSubgroup) ∧
      (∀ σ ∈ SSGRoute.decomp ℚ A,
        ((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φm) σ = 1) :=
  ⟨decomp_le_fixingSubgroup_of_map_eq_one p K N φm hker hKN A hφmA,
    fun σ hσ => by rw [MonoidHom.comp_apply, hφmA σ hσ, map_one]⟩

/-! ## Status of the assembly (session 6 update): the shape of the remaining proof

The proof of `properStageAssemblyData` is Step 3 (Schmidt–Wingberg pp. 26–30).  This session fixed
the *shape* of the remaining argument; the pieces below are what a later session must assemble.

### The corrected reading of Step 3 (two simplifications found this session)

1. **The conclusion does not require `Φ` to kill the `T¹`-classes.**  Clause (i) of Theorem 15 (which
   `stage_local_shrinking` / `Work.SSGRoute.local_clause_all_places` provide) is required only at
   level `m` for `φm`, and is *assumed* there by `hS m` (`IsSolvableStage` gives the local splitting
   `l_A : D_A →* Γ_{τ+1}(m)` with `φm σ = 1 → l_A σ = 1`).  The only job of `Φ` is to kill the
   `H¹`-obstruction `x` of the `coker_obstruction` node.  So `Φ` comes from
   `Work.CohomologicalShrinking.exists_shrinking_H1_semidirect_paper` (for `2 ≤ i`) applied to `x`,
   and `N_n` is then the fixed field of `((flowGroupMap Φ) ∘ φm).ker ≤ N_m`.

2. **`S` exists already.**  `Work.SSGRoute.exists_representatives` (in `stage_local_shrinking.lean`,
   *axiom-clean*) gives a finite set `S` of finite places, one per conjugacy class over
   `Ram(K/ℚ) ∪ {p}`, with `hSfin`, `hSdisj` and the covering property `hSram`.  Apply it with
   `K := N_m` (finite Galois over `ℚ` by `fixedField_and_equiv`) to cover `Ram(N_m) ∪ {p}`; if the
   ramification of `ψm` outside `Ram(N_m)` must also be covered (see (3) below), apply it instead to
   `N_m ⊔ Λ` where `Λ` is the (finite, Galois) fixed field of `ψm.ker` (`Work.SSGRoute.fixedField_and_equiv`
   at level `τ+1`), so that `S ⊇ Ram(Λ) ∪ Ram(N_m) ∪ {p}`.

### The clause (ii) mechanisms, at each kind of place of `S`

* **`T¹`** (places over `Ram(K/ℚ) ∪ {p}`): the local splitting `l_A` of `hS m` gives the `T¹` target
  `α_A σ := l_A σ · (ψm σ)⁻¹` (`localTargetT1_isCocycle` here, or the sibling
  `Work.SSGRoute.exists_localTarget_of_splitting`); `flowTwistE_eq_one_of_T1Target` then yields
  clause (i), and clause (ii) is *vacuous* there.
* **`T³`** (places where `φm|D_A = 1`, so that `ψm(D_A) ≤ flowEKer(m) = E(m,τ)`): the target
  `α_A σ := -ψm σ` (`exists_localTarget_of_proj_eq_one`, proved here).  Because
  `flowGroupMap_gradeInl` identifies `gradeInl ∘ gradedMapLin Φ` with `flowGroupMap Φ ∘ gradeInl`,
  this target kills the level-`n` twist on **all** of `D_A`, independently of `Φ`; so clause (ii) is
  vacuous and the first disjunct (`φn|D_A = 1`) holds (`decomp_le_fixingSubgroup_of_map_eq_one`).
* **`T⁰`** (places completely decomposed in `N_n`, chosen by Chebotarev; the child
  `Work.SSGRoute.exists_cocycle_at_frob_of_split` supplies the target with a prescribed Frobenius
  value): the `T⁰`-generation of `flowEKer p G n i j` is `iSup_map_eq_flowEKer_of_prescribed_values`
  (proved here).
* **`T²`** (places where `φn|D_A ≠ 1`, i.e. ramified in `N_n|K`): the target cannot kill the twist;
  it must only make it **cyclic and inertia-generated**.  The mechanism proved this session is the
  *push-forward*: for `D_A ≤ G_K` the arithmetic gives `ε = gradedMapLin Φ ∘ α_A` pointwise on
  `D_A`, whence the level-`n` twist is `flowGroupMap Φ` applied to the level-`m` twist
  (`flowTwistE_pushforward`), and cyclicity / inertia-generation transfer
  (`isCyclic_and_inertia_generates_pushforward`).  The level-`m` target itself is delegated as
  `Work.SSGRoute.stage3T2LocalTarget` (file `Submission/Work/SSGRoute/stage3T2LocalTarget.lean`).

### The complete case analysis for clause (ii) (hard case: `∃σ ∈ I_A ∩ G_K, ψ σ ≠ 1`)

Let `φn := (flowGroupMap Φ) ∘ φm` and `N_m` = fixed field of `φm.ker` (so `N_m.fixingSubgroup =
φm.ker` by `fixedField_and_equiv`).  Five cases, all discharged by existing or delegated lemmas:

1. **`A ∈ T¹`** (over `p` or ramified in `K`): clause (i) gives `ψ σ = 1` for `σ ∈ D_A ∩ G_K`, so
   the hypothesis is false.  (`flowTwistE_eq_one_of_T1Target`.)
2. **`φm|D_A = 1`**: then `φn|D_A = 1` too, so the first disjunct holds, and `D_A ≤ G_K` by
   `decomp_le_fixingSubgroup_of_map_eq_one` (with `N := N_m`).  **Nothing about `ψ` is needed.**
   This covers the `T³` places and all places completely decomposed in `N_m`.
3. **`φm|(I_A ∩ G_K) ≠ 1`** (so `A ∈ Ram(N_m|K)`, and `A ∉ T¹`):  Scholz (ii) for `φm` gives
   `D_A ≤ G_K` and `∀σ ∈ D_A, ∃τ ∈ I_A, φm τ = φm σ`; the latter pushes forward to
   `∀σ ∈ D_A, ∃τ ∈ I_A, φn τ = φn σ`.  So the **delegated `Work.SSGRoute.stage3T2LocalTarget`**
   applies at level `m` (with `ρ := φm`, `ψ := ψm`), producing a level-`m` target `α_A` whose twist
   is cyclic and inertia-generated; `Work.SSGRoute.isCyclic_and_inertia_generates_pushforward`
   (proved here) transfers both properties to level `n` because on `D_A ≤ G_K` the coefficient is
   `ε = gradedMapLin Φ ∘ α_A` pointwise (`flowTwistE_pushforward`).
4. **`φm|(I_A ∩ G_K) = 1` but `φm|D_A ≠ 1`** (so `A` is unramified in `K` and `A ∈ Ram(Λ)` where
   `Λ` is the field of `ψm`): here clause (ii) *requires the hypothesis to be false*, since
   `ψ(I_A ∩ G_K) ⊆ flowEKer(n)` means `ψ(I_A) = ψ(D_A)` would force `φn(D_A) = 1`, while
   `φm|D_A ≠ 1`; and `D_A ≤ G_K` need not hold.  So one uses the **delegated
   `Work.SSGRoute.stage3KillInertiaTarget`** at level `m`: it produces a level-`m` target whose
   values on `I_A` cancel those of `ψm`, whence the level-`n` twist is `1` on `I_A` (hence on
   `I_A ∩ G_K`), and the hypothesis of clause (ii) fails.
5. **`A` not conjugate to any element of `S`**: then `A ∉ Ram(Λ · N_m) ∪ {p}`, so `ψm` (hence `ψ₀`)
   is unramified at `A`; and `coker_obstruction`'s last clause gives `ε|I_A = 0` when `A` is not
   split in `N_n`.  If `A` *is* split in `N_n` then `D_A ≤ G_{N_n} = ker φn`, so `φn|D_A = 1`
   (first disjunct); otherwise `ψ` is unramified on `I_A` and the hypothesis is false.
   This is why `S` must cover `Ram(Λ)` as well as `Ram(N_m) ∪ {p}`.

Consequently the only clause of the conclusion which is *not* covered by the above is the `T⁰`
clause (properness), discussed next.

### Clause (ii) at places *outside* `S` (the "unramified" case)

For `A` outside the conjugates of `S` (hence over no prime of `Ram(Λ·N_m) ∪ {p}`) and not split in
`N_n`, `coker_obstruction`'s last clause gives `ε = 0` on `I_A`, while `ψm` is unramified at `A`
(so `ψ₀` is), whence `ψ` is unramified on `I_A` and clause (ii) is vacuous.  For `A` outside `S`
but split in `N_n` one has `D_A ≤ G_{N_n} ≤ G_K` and `φn|D_A = 1` (first disjunct).  This is why
`S` must also cover `Ram(Λ)` (point (2) above): otherwise a place where `ψm` is tamely ramified in
`G_K` but `A` is not split in `K` would violate clause (ii)'s first conjunct `D_A ≤ G_K`.

### The `T⁰` clause (properness): why it must come from the arithmetic

The `T⁰`-clause of the conclusion is exactly the properness of `ψ` (`Work.SSGRoute.t0Generation`
*requires* `Function.Surjective ψ`; conversely `surjective_of_iSup_map_eq_flowEKer` derives it from
the clause).  At a place `A ∈ T⁰ ⊆ cs(N_n)` one has `D_A ≤ ker φn`, so `ψ|D_A` takes values in
`flowEKer(n) ≅ E(n,τ)` and is the *single* homomorphism `σ ↦ ε σ + e₀ σ`, where `e₀ σ` is the
element of `E(n,τ)` with `gradeInl (e₀ σ) = ψ₀ σ` (this is well defined for `σ ∈ ker φn`).
`Chebotarev` equidistribution therefore makes the `ψ(D_A)` for `A ∈ cs(N_n)` generate
`⟨f(y_A)⟩ + e₀(ker φn)` where `f = gradedMapLin Φ` and `y_A := α_A(F_A)` is the (free) value of the
local target at a Frobenius.  Two consequences, recorded for the assembling session:

* the generation of `E(n,τ)` follows **for every `Φ`** as soon as one takes, for the `T⁰` places,
  one place with `y_A = 0` in each conjugacy class of the (finite) Galois group of the field of
  `ψ₀|_{ker φn}` over `N_n` — those contribute `e₀(ker φn)` — together with one place with
  `y_A = y_i` for a generating family `y_1,…,y_d` of `E(m,τ)`; then
  `⟨e₀(ker φn)⟩ + ⟨f(y_1),…,f(y_d)⟩ = E(n,τ)` because `f` is surjective.  This is the
  `Φ`-independent form of the paper's `T⁰` prescription and it uses
  `Work.SSGRoute.exists_cocycle_at_frob_of_split` (the target with prescribed Frobenius value) and
  `Work.SSGRoute.exists_split_place_avoiding` (the places, with prescribed conjugacy classes and
  pairwise non-conjugate).
* alternatively, if the assembling session can prove `ψ₀|_{ker φn}` (equivalently
  `gradedMapLin Φ ∘ (ψm|_{ker φn})`) onto `E(n,τ)`, then `ψ` is surjective by the same argument and
  `Work.SSGRoute.exists_T0_generating_flowEKer` (proved here, no `⊆ S` requirement) gives the `T⁰`
  directly; the `Φ`-dependence of that surjectivity is the only difficulty.

### What is left

1. `Work.SSGRoute.stage3T2LocalTarget` (delegated, session 6) — the only missing *local* input.
Delegated in session 6 and **now proved** (all three are imported by this file, all
axiom-clean; their imports are upstream of this module, so no cycle is introduced):

* `Work.SSGRoute.stage3T2LocalTarget` (`Submission/Work/SSGRoute/stage3T2LocalTarget.lean`) — the
  cyclic local target at a place with `D_A ≤ G_K`, `A` not over `p` (the `T²` case).
* `Work.SSGRoute.stage3KillInertiaTarget` (`Submission/Work/SSGRoute/stage3KillInertiaTarget.lean`)
  — the "kill the inertia" target at a place unramified over `K` but where `ψm` is ramified.
* `Work.SSGRoute.stage3Shrinking_i_one` (`Submission/Work/SSGRoute/stage3Shrinking_i_one.lean`) —
  the `i = 1` (`τ = (1,1)`) instance of the shrinking (the `2 ≤ i` lemma
  `Work.CohomologicalShrinking.exists_shrinking_H1_semidirect_paper` does not cover it), to be used
  together with the latter: for `2 ≤ i` use `exists_shrinking_H1_semidirect_paper`, for `i = 1` use
  `stage3Shrinking_i_one` (with `j = 1`, the only possibility).

2*. **The interface of the remaining `coker_obstruction` step** (this is the largest remaining
piece; it is pure glue once stated).  Choose `m ≥ n` from the shrinking (item 2 below) and let
`N := N_m`, `e : Gal(N/ℚ) ≃* Γ_m` (`galoisEquiv_of_ker`), `ζ ∈ K` (`exists_primitiveRoot_in_K`),
`T := μ_p^∨` (`Work.CohomologicalShrinking.IsCyclotomicDual`).  Then the needed statement is

  `∃ Φ : OperatorMap (K ≃ₐ[ℚ] K) m n, ∀ (N₂ : IntermediateField ℚ QBar) [FD] [IsGalois]
     (hKN₂ : K ≤ N₂) (hN₂N : N₂ ≤ N)
     (e₂ : (N₂ ≃ₐ[ℚ] N₂) ≃* Γ_n) (he₂ : ∀σ, e₂ (res ℚ N₂ σ) = ((flowGroupMap Φ) ∘ φm) σ)
     (q : (N ≃ₐ[ℚ] N) →* (N₂ ≃ₐ[ℚ] N₂)) (hq : ∀σ, q (res ℚ N σ) = res ℚ N₂ σ)
     (hqcomp : ∀ x, e₂ (q x) = flowGroupMap Φ (e x))
     (π₂ : (N₂ ≃ₐ[ℚ] N₂) →* (K ≃ₐ[ℚ] K)) (hπ₂ : ∀σ, π₂ (res ℚ N₂ σ) = res ℚ K σ),
     ∃ ε : G_ℚ → E(n,τ), IsCocycleOn (res ℚ K) ⊤ ε ∧ IsLocConstOn ⊤ ε ∧
       (∀ A ∈ S, IsCoboundaryOn (res ℚ K) (D_A) (ε - gradedMapLin Φ ∘ α A)) ∧
       (∀ c ∈ C, IsCoboundaryOn (res ℚ K) (⟨c⟩) (ε - gradedMapLin Φ ∘ β c)) ∧
       (∀ B, IsFinPlace ℚ B → (∀ A ∈ S, ¬ IsConjPlace ℚ A B) → ¬ IsSplitIn ℚ N₂ B →
          ∀σ, IsInertia ℚ B σ → ε σ = 0)`,

whose proof is: instantiate `SSGRoute.coker_obstruction` (with `πN`, `hπN` from `galoisEquiv_of_ker`
at level `m`) to get `x`; transport `x` to `H¹(flowRep p G m i j T)` by `transportH1 e
(flowRep p G m i j T)`; the `hshrink` hypothesis (`∃ Φ, flowZMap Φ T x = 0`, supplied by
`exists_shrinking_H1_semidirect_paper` for `2 ≤ i` and by `stage3Shrinking_i_one` for `i = 1`)
gives `Φ`; the vanishing `(groupHomology.map q F 1).hom x = 0` needed by `coker_obstruction`'s
`∀`-clause comes from the naturality of the transport (`transportH1_natural_of_compat`, whose file
imports *this* module, so it must be re-proved here or the shared helpers moved to an upstream
module: the only ingredient is `flowGroupMap_gradeInl`, already in this file).  Then `ε` is the
output of the `∀`-clause for `f := gradedMapLin Φ` and `F` the morphism with
`F.hom = (gradedMapLin Φ).rTensor T`.

2. Extract `m`, `φm`, `ψm`, `l_A` from `hS m` with `m ≥ m₀` of the shrinking, build `N_m`, `N_n`, 
   `S` (via `exists_representatives`), the targets `α_A` at the four kinds of place, and the sets
   `T⁰`, `C` (`exists_involutionSet`), `ζ` (`exists_primitiveRoot_in_K`), `T := μ_p^∨`
   (`Work.CohomologicalShrinking.IsCyclotomicDual`).
   The level-`τ+1` field `Λ` of `ψm` is used in two ways: as the field whose ramification `S` must
   cover, and (via `fixedField_and_equiv`) as the identification of `Gal(Λ/ℚ)` with `Γ_{τ+1}(m)`.
3. Apply `SSGRoute.coker_obstruction` at `N = N_m` (`galoisEquiv_of_ker` for `e : Gal(N_m) ≃* Γ_m`),
   transport `x` to `H¹(flowRep p G m i j T)` (`flowRepGaloisTransport`, `transportH1`), kill it with
   `exists_shrinking_H1_semidirect_paper` (`2 ≤ i`) or `exists_shrinking_Hm2_tate` + `exists_bridge`
   (`i = 1`), and re-feed the `∀`-clause at `N₂ = N_n` with `f = gradedMapLin Φ` and
   `F` from `transportH1_natural_of_compat` (that lemma must be re-proved *inside* this file, or the
   helper lemmas moved to an upstream module, because
   `Submission/Work/SSGRoute/transportH1_natural_of_compat.lean` imports *this* module).
4. Set `ψ := flowTwistEHom p K n i j ε ((flowGroupMap Φ) ∘ ψm) ...` and check the clauses with
   `flowTwistEHom_liftsFlow`, `flowTwistEHom_isOpen_ker`, `flowTwistE_eq_one_of_T1Target`,
   `involution_clause_of_hasRootsOfUnity`, `flowTwistE_eq_one_of_gradeInl_eq_inv` (for `T³`),
   `isCyclic_and_inertia_generates_pushforward` (for `T²`), and
   `iSup_map_eq_flowEKer_of_prescribed_values` (for `T⁰`).
-/

/-! ## The arithmetic core of Step 3 (Schmidt–Wingberg, arXiv:math/9809211 §5)

This section contains the reduction of Step 3 of Theorem 15 to the arithmetic node
`SSGRoute.coker_obstruction` together with the shrinking of Proposition 7 (i).  The
`transportH1`-naturality helpers are local copies (under distinct names, since the
sibling module `Submission.Work.SSGRoute.transportH1_natural_of_compat` imports this one). -/

open CategoryTheory

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true




noncomputable def coeffId_St3 {k : Type} [CommRing k] {G H : Type} [Group G] [Group H]
    (e : G ≃* H) (M : Rep.{0,0,0} k H) :
    Rep.res e.toMonoidHom M ⟶ Rep.res e.toMonoidHom M :=
  Rep.ofHom ⟨LinearEquiv.refl k M.V, by intro g; ext x; rfl⟩

theorem transportH1_apply_St3 {k G H : Type} [CommRing k] [Group G] [Group H]
    (e : G ≃* H) (M : Rep.{0,0,0} k H)
    (x : (groupHomology.H1 (Rep.res e.toMonoidHom M) : Type)) :
    Work.SSGRoute.transportH1 e M x
      = (groupHomology.map (A := Rep.res e.toMonoidHom M) (B := M) e.toMonoidHom
          (coeffId_St3 e M) 1).hom x := by
  have he : ∀ g : G, ↑(LinearEquiv.refl k M.V) ∘ₗ (Rep.res e.toMonoidHom M).ρ g
      = M.ρ (e g) ∘ₗ ↑(LinearEquiv.refl k M.V) := fun g => rfl
  change (groupHomology.mapIso (A := Rep.res e.toMonoidHom M) (B := M) e
      (LinearEquiv.refl k M.V) he 1).hom.hom x = _
  rw [groupHomology.mapIso_hom]
  refine congrArg (fun m : groupHomology.H1 (Rep.res e.toMonoidHom M) ⟶ groupHomology.H1 M =>
    m.hom x) ?_
  exact groupHomology.map_congr rfl (by rfl) 1

theorem transportH1_natural_abstract_St3 {k : Type} [CommRing k] {P Q R S : Type}
    [Group P] [Group Q] [Group R] [Group S]
    (e : P ≃* R) (e₂ : Q ≃* S) (qq : P →* Q) (kk : R →* S)
    (hm : e₂.toMonoidHom.comp qq = kk.comp e.toMonoidHom)
    (M : Rep.{0,0,0} k R) (N : Rep.{0,0,0} k S)
    (F : Rep.res e.toMonoidHom M ⟶ Rep.res qq (Rep.res e₂.toMonoidHom N))
    (φ : M ⟶ Rep.res kk N)
    (hFφ : (Rep.Hom.hom F).toLinearMap = (Rep.Hom.hom φ).toLinearMap) :
    ∀ x : (groupHomology.H1 (Rep.res e.toMonoidHom M) : Type),
      Work.SSGRoute.transportH1 e₂ N ((groupHomology.map qq F 1).hom x)
        = (groupHomology.map kk φ 1).hom (Work.SSGRoute.transportH1 e M x) := by
  intro x
  have hL : Work.SSGRoute.transportH1 e₂ N ((groupHomology.map qq F 1).hom x)
      = (groupHomology.map (e₂.toMonoidHom.comp qq)
          (F ≫ (Rep.resFunctor qq).map (coeffId_St3 e₂ N)) 1).hom x := by
    rw [transportH1_apply_St3]
    change ((groupHomology.map qq F 1) ≫ (groupHomology.map e₂.toMonoidHom (coeffId_St3 e₂ N) 1)).hom x = _
    rw [groupHomology.map_comp (qq) (e₂.toMonoidHom) F (coeffId_St3 e₂ N) 1]
  have hR : (groupHomology.map kk φ 1).hom (Work.SSGRoute.transportH1 e M x)
      = (groupHomology.map (kk.comp e.toMonoidHom)
          (coeffId_St3 e M ≫ (Rep.resFunctor e.toMonoidHom).map φ) 1).hom x := by
    rw [transportH1_apply_St3]
    change ((groupHomology.map e.toMonoidHom (coeffId_St3 e M) 1) ≫ (groupHomology.map kk φ 1)).hom x = _
    rw [groupHomology.map_comp (e.toMonoidHom) (kk) (coeffId_St3 e M) φ 1]
  rw [hL, hR]
  refine congrArg (fun m : groupHomology.H1 (Rep.res e.toMonoidHom M) ⟶ groupHomology.H1 N =>
    m.hom x) ?_
  refine groupHomology.map_congr hm ?_ 1
  rw [show (Rep.resFunctor qq).map (coeffId_St3 e₂ N) = Rep.resMap qq (coeffId_St3 e₂ N) from rfl,
      show (Rep.resFunctor e.toMonoidHom).map φ = Rep.resMap e.toMonoidHom φ from rfl]
  simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap,
    Rep.resMap_hom_toLinearMap, coeffId_St3, Rep.hom_ofHom, Representation.IntertwiningMap.toLinearMap_mk,
    LinearMap.id_comp, LinearMap.comp_id, LinearEquiv.refl_toLinearMap, hFφ]


/-- Copy of `transportH1_natural_of_compat`. -/
theorem transportH1_natural_of_compat_St3 {p : ℕ} [Fact p.Prime] (G : Type) [Group G]
    {N N₂ : Type} [Field N] [Algebra ℚ N] [Field N₂] [Algebra ℚ N₂]
    (m n i j : ℕ) (Φ : Work.CohomologicalShrinking.OperatorMap G m n)
    (e : (N ≃ₐ[ℚ] N) ≃* Work.CohomologicalShrinking.flowGroup p G m i j)
    (e₂ : (N₂ ≃ₐ[ℚ] N₂) ≃* Work.CohomologicalShrinking.flowGroup p G n i j)
    (q : (N ≃ₐ[ℚ] N) →* (N₂ ≃ₐ[ℚ] N₂))
    (hq : ∀ x, e₂ (q x) = Work.CohomologicalShrinking.flowGroupMap p G i j Φ (e x))
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] :
    ∃ F : Rep.res e.toMonoidHom (Work.CohomologicalShrinking.flowRep p G m i j T) ⟶
          Rep.res q (Rep.res e₂.toMonoidHom (Work.CohomologicalShrinking.flowRep p G n i j T)),
      (∀ z : Work.CohomologicalShrinking.E p G m i j ⊗[ZMod p] T,
        F.hom z = (Work.CohomologicalShrinking.gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T z) ∧
      ∀ x : (↑(groupHomology.H1
            (Rep.res e.toMonoidHom (Work.CohomologicalShrinking.flowRep p G m i j T))) : Type),
        Work.SSGRoute.transportH1 e₂ (Work.CohomologicalShrinking.flowRep p G n i j T)
            ((groupHomology.map q F 1).hom x)
          = Work.CohomologicalShrinking.flowZMap p G i j Φ T
              (Work.SSGRoute.transportH1 e (Work.CohomologicalShrinking.flowRep p G m i j T) x) := by
  have hhom : e₂.toMonoidHom.comp q = (flowGroupMap p G i j Φ).comp e.toMonoidHom :=
    MonoidHom.ext hq
  let F : Rep.res e.toMonoidHom (flowRep p G m i j T) ⟶
      Rep.res q (Rep.res e₂.toMonoidHom (flowRep p G n i j T)) :=
    Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap
      (Rep.res e.toMonoidHom (flowRep p G m i j T)).ρ
      (Rep.res q (Rep.res e₂.toMonoidHom (flowRep p G n i j T))).ρ
      ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T)
      (fun g v => by
        simp only [MonoidHom.comp_apply]
        rw [flowRepG_ρ_apply, flowRepG_ρ_apply]
        rw [show e₂.toMonoidHom (q g) = (flowGroupMap p G i j Φ) (e.toMonoidHom g) from hq g,
          flowQuot_flowGroupMap]
        simpa using flowRepG_isIntertwining p G i j Φ T (flowQuot p G m i j (e.toMonoidHom g)) v))
  refine ⟨F, ?_, ?_⟩
  · intro z
    rfl
  · intro x
    exact transportH1_natural_abstract_St3 e e₂ q (flowGroupMap p G i j Φ) hhom
      (flowRep p G m i j T) (flowRep p G n i j T) F (flowRepMap p G i j Φ T) (by rfl) x


set_option backward.isDefEq.respectTransparency false

/-- **The supply of rank-change operator maps killing a single class of `H₁(Γ_m, E(m,τ)⊗T)`**,
obtained from Proposition 7 (i) of Schmidt–Wingberg: for every `m` above a threshold `m₀ ≥ n`, every
class of `H₁(Γ_m, E(m,τ)⊗T)` is killed by `flowZMap Φ T` for some `Φ : F(m) ⇢ F(n)`. -/
theorem stage3ShrinkSupply_St3
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K]
    (i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction (K ≃ₐ[ℚ] K) T] [SMulCommClass (K ≃ₐ[ℚ] K) (ZMod p) T]
    [Module.Finite (ZMod p) T]
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ m₀ : ℕ, n ≤ m₀ ∧ ∀ m ≥ m₀,
      ∀ y : (↑(groupHomology.H1 (flowRep p (K ≃ₐ[ℚ] K) m i j T)) : Type),
        ∃ Φ : OperatorMap (K ≃ₐ[ℚ] K) m n,
          flowZMap (p := p) (K ≃ₐ[ℚ] K) i j Φ T y = 0 := by
  haveI : Fintype (K ≃ₐ[ℚ] K) := Fintype.ofFinite _
  by_cases hi : 2 ≤ i
  · obtain ⟨m₀, hm₀, hkill⟩ := exists_shrinking_H1_semidirect_paper p (K ≃ₐ[ℚ] K) hi hj
      (Classical.choice (Work.SSGRoute.prop5Data_exists p (K ≃ₐ[ℚ] K) i j hj hji)) T 1 hn
    refine ⟨m₀, hm₀, fun m hm y => ?_⟩
    obtain ⟨Φ, hΦ⟩ := hkill m hm (fun _ : Fin 1 => y)
    exact ⟨Φ, hΦ 0⟩
  · have hi1 : i = 1 := by omega
    subst hi1
    have hj1 : j = 1 := le_antisymm (by omega) hj
    subst hj1
    obtain ⟨m₀, hm₀, hkill⟩ := stage3Shrinking_i_one p (K ≃ₐ[ℚ] K)
      (Classical.choice (Work.SSGRoute.prop5Data_exists p (K ≃ₐ[ℚ] K) 1 1 le_rfl le_rfl)) T 1 hn
    refine ⟨m₀, hm₀, fun m hm y => ?_⟩
    obtain ⟨Φ, hΦ⟩ := hkill m hm (fun _ : Fin 1 => y)
    exact ⟨Φ, hΦ 0⟩


/-- **The level-`m` datum of Step 3 of Theorem 15.**  From the properness/induction hypothesis
`hS` (`IsSolvableStage` at every level), a primitive `p`-th root `ζ ∈ K` and a cyclotomic dual `T`,
produce a level `m ≥ n` with the level-`m` Scholz solution `φm`, its open-kernel lift `ψm`, the
local splitting datum at every `T¹`-place, the fixed field `Nm` of `φm` with the Galois
identification `em : Gal(Nm/ℚ) ≃* Γ_m` through which `φm` factors, and the supply of rank-change
operator maps `Φ : F(m) ⇢ F(n)` killing every class of `H₁(Γ_m, E(m,τ)⊗T)`. -/
theorem stage3LevelData_St3 (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)
    (hμ : SSGRoute.HasRootsOfUnity p K i)
    (hS : ∀ m : ℕ, 1 ≤ m → SSGRoute.IsSolvableStage p K m i j) (n : ℕ) (hn : 1 ≤ n)
    (ζ : SSGRoute.QBar) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction (K ≃ₐ[ℚ] K) T] [SMulCommClass (K ≃ₐ[ℚ] K) (ZMod p) T]
    [Module.Finite (ZMod p) T]
    (hTdual : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res ℚ K) ζ) :
    ∃ (m : ℕ) (_ : 1 ≤ m) (_ : n ≤ m)
      (φm : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m i j)
      (ψm : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2)
      (Nm : IntermediateField ℚ SSGRoute.QBar) (_ : FiniteDimensional ℚ Nm) (_ : Normal ℚ Nm)
      (_ : IsGalois ℚ Nm),
      SSGRoute.IsScholzSolution p K m i j φm ∧ SSGRoute.LiftsFlow ψm φm ∧
      IsOpen (ψm.ker : Set SSGRoute.GalQ) ∧
      (∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsT1Place p K A →
        ∃ l : ↥(SSGRoute.decomp ℚ A) →* flowGroup p (K ≃ₐ[ℚ] K) m
            (tauSucc i j).1 (tauSucc i j).2,
          (∀ σ : ↥(SSGRoute.decomp ℚ A), SSGRoute.LiftsFlowAt (l σ) (φm σ)) ∧
          (∀ σ : ↥(SSGRoute.decomp ℚ A), φm σ = 1 → l σ = 1)) ∧
      K ≤ Nm ∧
      (∃ em : (Nm ≃ₐ[ℚ] Nm) ≃* flowGroup p (K ≃ₐ[ℚ] K) m i j,
        ∀ σ : SSGRoute.GalQ, em (SSGRoute.res ℚ Nm σ) = φm σ) ∧
      (∀ y : (↑(groupHomology.H1 (flowRep p (K ≃ₐ[ℚ] K) m i j T)) : Type),
        ∃ Φ : OperatorMap (K ≃ₐ[ℚ] K) m n,
          flowZMap (p := p) (K ≃ₐ[ℚ] K) i j Φ T y = 0) := by
  obtain ⟨m₀, hnle, hkill⟩ := stage3ShrinkSupply_St3 p K i j hj hji T n hn
  have hm1 : 1 ≤ m₀ := le_trans hn hnle
  obtain ⟨φm, ψm, hSch, hLift, hopen, hsplit⟩ := hS m₀ hm1
  obtain ⟨hsurjφ, hopenφ, hflowφ⟩ := hSch.1
  obtain ⟨Nm, hfdNm, hnormNm, hgalNm, hKNm, _hfixNm, em, hem⟩ :=
    fixedField_and_equiv p K m₀ i j φm hsurjφ hopenφ hflowφ
  have hshrink : ∀ y : (↑(groupHomology.H1 (flowRep p (K ≃ₐ[ℚ] K) m₀ i j T)) : Type),
      ∃ Φ : OperatorMap (K ≃ₐ[ℚ] K) m₀ n,
        flowZMap (p := p) (K ≃ₐ[ℚ] K) i j Φ T y = 0 := by
    intro y
    exact hkill m₀ le_rfl y
  exact ⟨m₀, hm1, hnle, φm, ψm, Nm, hfdNm, hnormNm, hgalNm,
    hSch, hLift, hopen, hsplit, hKNm, ⟨em, hem⟩, hshrink⟩


/-! ## Status of the assembly (session 7 update)

### Proved in this file this session (all axiom-clean)

* `coeffId_St3`, `transportH1_apply_St3`, `transportH1_natural_abstract_St3`,
  `transportH1_natural_of_compat_St3` — local copies of the transport-naturality helpers (under
  distinct names, because the sibling module `Submission.Work.SSGRoute.transportH1_natural_of_compat`
  imports *this* module and the two would otherwise clash);
* `exists_cyclotomicDual_finite_St3` — the cyclotomic dual `μ_p^∨` as a finite `𝔽_p`-module (a copy
  of `Work.SSGRoute.exists_cyclotomicDual_finite`, made here because importing
  `stage_global_lifting` is impossible: its closure contains `sha2_dual_control`, which clashes with
  `selmer_dual_inflated` from the closure of `coker_obstruction`);
* **`stage3CokerInterface_St3` — the arithmetic core of Step 3.**  From the level-`m` Galois datum
  `(N_m, e, φ_m)`, the local data `(S, α)`/`(C, β)` of Step 3, and a supply of rank-change maps
  killing classes of `H₁(Γ_m, E(m,τ)⊗T)`, it produces `Φ : F(m) ⇢ F(n)`, the field `N_n` of
  `φ_n = (flowGroupMap Φ) ∘ φ_m` with its Galois identification `en`, and the global cocycle `ε`
  realizing `gradedMapLin Φ ∘ α` (resp. `β`) locally at `S` (resp. `C`).  Its proof instantiates
  `SSGRoute.coker_obstruction` at level `m`, transports the class `x` by `transportH1` to
  `H₁(Γ_m, flowRep)`, kills it with the supplied `Φ`, and re-feeds the `∀`-clause at `N₂ = N_n`
  using `transportH1_natural_of_compat_St3`;
* `stage3ShrinkSupply_St3` — the shrinking supply (Proposition 7 (i), from
  `Work.CohomologicalShrinking.exists_shrinking_H1_semidirect_paper` for `2 ≤ i` and
  `Work.SSGRoute.stage3Shrinking_i_one` for `i = 1`, on top of `SSGRoute.prop5Data_exists`);
* `stage3LevelData_St3` — the level-`m` datum of Step 3: a level `m ≥ n`, the Scholz solution `φ_m`,
  its open-kernel lift `ψ_m`, the local splitting at every `T¹`-place, the fixed field `N_m` with
  `Gal(N_m/ℚ) ≃* Γ_m`, and the supply of `Φ`s.  This packages steps 1–3 of the assembly.

### What still remains for `properStageAssemblyData`

1. **The local data `(S, α, C, β)`** (the `hα`, `hβ`, `hS*`, `hC*` hypotheses of
   `stage3CokerInterface_St3`): `S` covers `Ram(Λ) ∪ {p}` (Λ = the field of `ψm`), and `α` is the
   case dispatch of the four local targets — `Work.SSGRoute.exists_localTarget_of_splitting` /
   `localTargetT1_isCocycle` (`T¹`), `exists_localTarget_of_proj_eq_one` (`φ_m|D_A = 1`),
   `Work.SSGRoute.stage3KillInertiaTarget` (`φ_m|D_A ≠ 1`, `φ_m|I_A = 1`),
   `Work.SSGRoute.stage3T2LocalTarget` (the rest: then `A` is unramified in `K`, so `I_A ≤ G_K`,
   `φ_m|I_A ≠ 1`, and Scholz (ii) for `φ_m` gives `D_A ≤ G_K` and inertia-generation).
2. **The `T⁰` places** (properness): delegated as `Work.SSGRoute.stage3T0Data` — pairwise
   non-conjugate places *split in Λ* (so that `D_A ≤ ψm.ker`, hence `φ_n|D_A = 1` for every `Φ`,
   and `ψ₀|D_A = 1`), avoiding `S`, together with cocycle targets `α A` with prescribed Frobenius
   values exhausting `E(m,τ)`; then `iSup_map_eq_flowEKer_of_prescribed_values` gives the generation
   (with `g A := gradedMapLin Φ (α A F_A)`, `e := 0`) for every `Φ`, because `gradedMapLin Φ` is
   onto.
3. **The clause checks** (mostly available): `flowTwistEHom_liftsFlow`, `flowTwistEHom_isOpen_ker`,
   `flowTwistE_eq_one_of_T1Target` (clause (i)), `involution_clause_of_hasRootsOfUnity` (automatic),
   `clause_ii_of_map_eq_one` / `isCyclic_and_inertia_generates_pushforward` (clause (ii)), and
   `flowTwistE_scholzT1` (`twistLayer.lean`: condition (i) is preserved by the twist as soon as the
   cocycle vanishes on `G_K`).

### Why the place-wise clauses may be checked only at the representatives of `S` (checked this session)

The conclusion of `properStageAssemblyData` quantifies its three place-wise conditions over **all**
`T¹`-places, all involutions and all finite places, whereas the local targets (and hence the
coboundary conditions on `ε` supplied by `SSGRoute.coker_obstruction`) are available only at the
representatives `A ∈ S` (one per `G_ℚ`-conjugacy class over `Ram(Λ) ∪ {p}`).  No transfer of the
*local data* is needed, because every condition in the conclusion is invariant under conjugating
the place by an element `σ₀ ∈ G_ℚ`:

* **Clause (i).**  If `B = σ₀ • A` then `D_B = σ₀ D_A σ₀⁻¹`, and since `G_K ⊴ G_ℚ` we also have
  `D_B ∩ G_K = σ₀ (D_A ∩ G_K) σ₀⁻¹`.  For `x ∈ D_B ∩ G_K` write `x = σ₀ y σ₀⁻¹` with
  `y ∈ D_A ∩ G_K` (so `y ∈ G_K` by normality); then `ψ x = ψ σ₀ · ψ y · (ψ σ₀)⁻¹ = 1` as soon as
  `ψ y = 1`.  So clause (i) at the representatives propagates to every `T¹`-place, using only that
  `ψ` is a **group homomorphism**.  (This is the point the session-6 note "at `T¹` the elements of
  `D_A ∩ G_K` act trivially on `E`" was reaching for; nothing about the cocycle `ε` is involved.)
* **Clause (ii).**  Likewise `I_B = σ₀ I_A σ₀⁻¹`, `D_B ≤ G_K ⟺ D_A ≤ G_K`, and
  `(D_B).map ψ = (σ₀ (D_A) σ₀⁻¹).map ψ = ψσ₀ · ((D_A).map ψ) · (ψσ₀)⁻¹` is cyclic (resp. generated
  by the image of inertia) iff `(D_A).map ψ` is; the hypothesis
  `∃σ ∈ I_B ∩ G_K, ψ σ ≠ 1` is the conjugate of the corresponding statement at `A`.  So the whole
  case analysis may be performed at the representatives of `S` only.
* **The involution clause** is conjugation-invariant on the nose (`c ↦ σ₀ c σ₀⁻¹` preserves `c² = 1`
  and `K.fixingSubgroup`, and `ψ (σ₀ c σ₀⁻¹) = ψσ₀ · ψc · (ψσ₀)⁻¹`), which is why the `T¹`-form of
  the clause is automatic from `hμ` (`involution_clause_of_hasRootsOfUnity`).
* **`T⁰`-generation.**  The `T⁰` places are chosen (by Chebotarev) among the representatives, and
  the generation is `iSup_map_eq_flowEKer_of_prescribed_values`, no transfer needed.

Consequently the local-data step really is the case dispatch, and the `T¹` clause needs the
`ε`-coboundary condition only at `S`.  (The earlier session-7 note claiming a delicate conjugation
*transfer of the coboundary condition* was based on forgetting that `ψ` is a homomorphism; it is
withdrawn.)
-/

/-! ## Specification of the local targets of Step 3, and its assembly lemmas

The conclusion of Step 3 is assembled from the level-`m` data (`stage3LevelData_St3`), the arithmetic
core (`stage3CokerInterface_St3`), and the local targets at the places of the chosen set `S`.
This section records the *specification* of those local targets (`AlphaSpec`), the auxiliary lemmas
needed to read off the clauses of Theorem 15 from them, and finally the assembly. -/

/-- `Subgroup.map` of a subgroup is the closure of the image (the version of
`closure_image_eq_map_local` for subgroups). -/
theorem map_eq_closure_image {G H : Type*} [Group G] [Group H] (f : G →* H) (S : Subgroup G) :
    S.map f = Subgroup.closure (f '' (S : Set G)) := by
  have h := closure_image_eq_map_local f (S : Set G)
  rw [Subgroup.closure_eq] at h
  exact h.symm

/-- The supremum of the cyclic subgroups generated by a family whose range is everything is the
whole group. -/
theorem iSup_zpowers_eq_top_of_surjective {E : Type*} [Group E] {ι : Type*} (f : ι → E)
    (h : ∀ y : E, ∃ i, f i = y) : (⨆ i, Subgroup.zpowers (f i)) = ⊤ := by
  refine top_le_iff.mp fun y _ => ?_
  obtain ⟨i, rfl⟩ := h y
  exact Subgroup.mem_iSup_of_mem i (Subgroup.mem_zpowers (f i))

/-- **The `flowQuot`-compatibility of a lift.**  If `ψ` lifts the level-`τ` solution `φ` and `φ` is
compatible with the restriction to `K`, then `ψ` is compatible on the nose as well. -/
theorem flowQuot_of_liftsFlow {p : ℕ} {K : IntermediateField ℚ SSGRoute.QBar} [Normal ℚ K]
    {n i j : ℕ}
    (φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (hproj : ∀ σ : SSGRoute.GalQ, flowGroupProj p (K ≃ₐ[ℚ] K) n i j (ψ σ) = φ σ)
    (hflow : ∀ σ : SSGRoute.GalQ, flowQuot p (K ≃ₐ[ℚ] K) n i j (φ σ)
      = Work.SSGRoute.restrict K σ) :
    ∀ σ : SSGRoute.GalQ, flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (ψ σ)
      = Work.SSGRoute.restrict K σ := by
  intro σ
  have h1 : flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (ψ σ)
      = flowQuot p (K ≃ₐ[ℚ] K) n i j (flowGroupProj p (K ≃ₐ[ℚ] K) n i j (ψ σ)) :=
    flowQuot_flowGroupProj_psad p (K ≃ₐ[ℚ] K) n i j (ψ σ)
  rw [h1, hproj σ, hflow σ]

/-- **The specification of the local target `α_A` at level `m`.**  The arithmetic core
`stage3CokerInterface_St3` only asks that the local data be a locally constant `1`-cocycle on the
decomposition group `D_A`; the shape of `α_A` inside the graded piece `E(m,τ)` is what encodes the
local conditions (i), (ii) of Theorem 15:

* if `A ∈ T¹` (over `p` or ramified in `K`): `α_A σ = l_A σ · (ψ_m σ)⁻¹` for the local splitting
  `l_A` of `φ_m|D_A` supplied by `IsSolvableStage` (condition (i));
* if `A ∉ T¹` and `φ_m|D_A = 1` (the `T³` places): `α_A σ = (ψ_m σ)⁻¹` on all of `D_A`, which kills
  the ramification of `ψ_m` at level `n`;
* if `A ∉ T¹`, `φ_m|D_A ≠ 1` but `φ_m|I_A = 1`: the same shape is required only on the inertia;
* if `A ∉ T¹` and `φ_m|I_A ≠ 1` (the `T²` places): `α_A` is a local target whose twist with `ψ_m` is
  cyclic and generated by the image of the inertia. -/
def AlphaSpec (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K]
    (m i j : ℕ) (φm : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (ψm : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2)
    (A : ValuationSubring SSGRoute.QBar) (αA : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) m i j) : Prop :=
  SSGRoute.IsCocycleOn (SSGRoute.res ℚ K) (SSGRoute.decomp ℚ A) αA ∧
  SSGRoute.IsLocConstOn (SSGRoute.decomp ℚ A) αA ∧
  (SSGRoute.IsT1Place p K A →
    ∃ l : ↥(SSGRoute.decomp ℚ A) →* flowGroup p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2,
      (∀ σ : ↥(SSGRoute.decomp ℚ A), SSGRoute.LiftsFlowAt (l σ) (φm ↑σ)) ∧
      (∀ σ : ↥(SSGRoute.decomp ℚ A), φm ↑σ = 1 → l σ = 1) ∧
      (∀ σ : ↥(SSGRoute.decomp ℚ A), gradeInl p (K ≃ₐ[ℚ] K) m i j (Additive.toMul (αA ↑σ))
        = l σ * (ψm ↑σ)⁻¹)) ∧
  (¬ SSGRoute.IsT1Place p K A → (∀ σ ∈ SSGRoute.decomp ℚ A, φm σ = 1) →
    ∀ σ ∈ SSGRoute.decomp ℚ A,
      gradeInl p (K ≃ₐ[ℚ] K) m i j (Additive.toMul (αA σ)) = (ψm σ)⁻¹) ∧
  (¬ SSGRoute.IsT1Place p K A → (∃ σ ∈ SSGRoute.decomp ℚ A, φm σ ≠ 1) →
    (∀ σ : SSGRoute.GalQ, SSGRoute.IsInertia ℚ A σ → φm σ = 1) →
    ∀ σ : SSGRoute.GalQ, SSGRoute.IsInertia ℚ A σ →
      gradeInl p (K ≃ₐ[ℚ] K) m i j (Additive.toMul (αA σ)) = (ψm σ)⁻¹) ∧
  (¬ SSGRoute.IsT1Place p K A → (∃ σ ∈ SSGRoute.decomp ℚ A, φm σ ≠ 1) →
    (∃ σ : SSGRoute.GalQ, SSGRoute.IsInertia ℚ A σ ∧ φm σ ≠ 1) →
    (∀ σ ∈ SSGRoute.decomp ℚ A, σ ∈ K.fixingSubgroup) ∧
    IsCyclic (Subgroup.closure
      ((flowTwistE p K m i j αA ψm) '' (SSGRoute.decomp ℚ A : Set SSGRoute.GalQ))) ∧
    (∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧
      flowTwistE p K m i j αA ψm τ = flowTwistE p K m i j αA ψm σ))

/-- **The clauses of Theorem 15 at a single place, in the case where the twist kills the inertia.**
If the local target `α_A` satisfies the shape `gradeInl (α_A σ) = (ψ_m σ)⁻¹` on the inertia of `A`,
and the local class of the global cocycle `ε` at `A` is that of `gradedMapLin Φ ∘ α_A`, then the
twist of `(Φ_* ∘ ψ_m)` by `ε` is trivial on the inertia of `A`.  This is the mechanism by which
condition (ii) is discharged at the `T³` and "kill-inertia" places: the hypothesis of (ii) — an
inertia element of `G_K` at which the twist is non-trivial — is *false* there. -/
theorem flowTwistE_eq_one_of_inertiaShape (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K] {m n i j : ℕ}
    (Φ : OperatorMap (K ≃ₐ[ℚ] K) m n)
    (ψm : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2)
    (A : ValuationSubring SSGRoute.QBar)
    (α : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) m i j)
    (ε : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (hu : ∀ σ : SSGRoute.GalQ, SSGRoute.IsInertia ℚ A σ → σ ∈ K.fixingSubgroup)
    (hα : ∀ σ : SSGRoute.GalQ, SSGRoute.IsInertia ℚ A σ →
      gradeInl p (K ≃ₐ[ℚ] K) m i j (Additive.toMul (α σ)) = (ψm σ)⁻¹)
    (hε : SSGRoute.IsCoboundaryOn (Work.SSGRoute.restrict K) (SSGRoute.decomp ℚ A)
      (fun σ => ε σ - gradedMapLin p Φ.toHom Φ.surjective i j (α σ))) :
    ∀ σ : SSGRoute.GalQ, SSGRoute.IsInertia ℚ A σ →
      flowTwistE p K n i j ε
        ((flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ).comp ψm) σ = 1 := by
  intro σ hσ
  have hd : σ ∈ SSGRoute.decomp ℚ A := hσ.1
  have hε0 : ε σ - gradedMapLin p Φ.toHom Φ.surjective i j (α σ) = 0 :=
    eq_zero_of_isCoboundaryOn p K n i j hε σ hd (hu σ hσ)
  have hεσ : ε σ = gradedMapLin p Φ.toHom Φ.surjective i j (α σ) := sub_eq_zero.mp hε0
  have key : gradeInl p (K ≃ₐ[ℚ] K) n i j (Additive.toMul (ε σ)) =
      (flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ (ψm σ))⁻¹ := by
    rw [hεσ, ← flowGroupMap_gradeInl_add p (K ≃ₐ[ℚ] K) Φ i j (α σ), hα σ hσ, map_inv]
  rw [flowTwistE, flowTwist, key]
  simp [MonoidHom.comp_apply]

/-- **The arithmetic core of Step 3.**  Given the level-`m` Galois datum `(N_m, e, φm)`, the
local data `(S, α)`/`(C, β)` of Step 3, and a supply of rank-change operator maps `Φ` killing
prescribed classes of `H₁(Γ_m, E(m,τ)⊗T)`, produce `Φ`, the level-`n` field `N_n` of
`(flowGroupMap Φ) ∘ φm` with its Galois identification `en`, and a global `E(n,τ)`-valued cocycle
`ε` realizing `gradedMapLin Φ ∘ α` (resp. `β`) locally at `S` (resp. `C`) and unramified outside
`S ∪ cs(N_n)`. -/
theorem stage3CokerInterface_local
    (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] {i j : ℕ} (hj : 1 ≤ j) (hji : j ≤ i)
    {m : ℕ}
    (Nm : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ Nm] [Normal ℚ Nm] [IsGalois ℚ Nm]
    (hKNm : K ≤ Nm)
    (e : (Nm ≃ₐ[ℚ] Nm) ≃* flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (φm : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (hsurjm : Function.Surjective φm)
    (hopenm : IsOpen (φm.ker : Set SSGRoute.GalQ))
    (hem : ∀ σ : SSGRoute.GalQ, e (SSGRoute.res ℚ Nm σ) = φm σ)
    (hflowm : ∀ σ : SSGRoute.GalQ,
      flowQuot p (K ≃ₐ[ℚ] K) m i j (φm σ) = SSGRoute.res ℚ K σ)
    (ζ : SSGRoute.QBar) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction (K ≃ₐ[ℚ] K) T] [SMulCommClass (K ≃ₐ[ℚ] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res ℚ K) ζ)
    (S : Finset (ValuationSubring SSGRoute.QBar))
    (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace ℚ A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace ℚ A B → A = B)
    (hSram : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (SSGRoute.IsRamifiedIn ℚ Nm B ∨ B.valuation (p : SSGRoute.QBar) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace ℚ A B)
    (C : Finset SSGRoute.GalQ) (hCinv : ∀ c ∈ C, c ^ 2 = 1)
    (hC : ∀ c : SSGRoute.GalQ, c ^ 2 = 1 → c ≠ 1 →
      ∃ c₀ ∈ C, ∃ σ : SSGRoute.GalQ, c = σ * c₀ * σ⁻¹)
    (hCdisj : ∀ c ∈ C, ∀ c' ∈ C, (∃ σ : SSGRoute.GalQ, c' = σ * c * σ⁻¹) → c = c')
    (α : ValuationSubring SSGRoute.QBar → SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) m i j)
    (hα : ∀ A ∈ S, SSGRoute.IsCocycleOn (SSGRoute.res ℚ K) (SSGRoute.decomp ℚ A) (α A) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp ℚ A) (α A))
    (β : SSGRoute.GalQ → SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) m i j)
    (hβ : ∀ c ∈ C, SSGRoute.IsCocycleOn (SSGRoute.res ℚ K) (Subgroup.zpowers c) (β c))
    (n : ℕ)
    (hshrink : ∀ y : (↑(groupHomology.H1 (flowRep p (K ≃ₐ[ℚ] K) m i j T)) : Type),
      ∃ Φ : OperatorMap (K ≃ₐ[ℚ] K) m n,
        flowZMap (p := p) (K ≃ₐ[ℚ] K) i j Φ T y = 0) :
    ∃ (Φ : OperatorMap (K ≃ₐ[ℚ] K) m n)
      (Nn : IntermediateField ℚ SSGRoute.QBar) (_ : FiniteDimensional ℚ Nn) (_ : Normal ℚ Nn)
      (_ : IsGalois ℚ Nn)
      (en : (Nn ≃ₐ[ℚ] Nn) ≃* flowGroup p (K ≃ₐ[ℚ] K) n i j),
      K ≤ Nn ∧ Nn ≤ Nm ∧
      (∀ σ : SSGRoute.GalQ, en (SSGRoute.res ℚ Nn σ) =
        (flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ) (φm σ)) ∧
      ∃ ε : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j,
        SSGRoute.IsCocycleOn (SSGRoute.res ℚ K) ⊤ ε ∧
        SSGRoute.IsLocConstOn ⊤ ε ∧
        (∀ A ∈ S, SSGRoute.IsCoboundaryOn (SSGRoute.res ℚ K) (SSGRoute.decomp ℚ A)
          (fun σ => ε σ - gradedMapLin p Φ.toHom Φ.surjective i j (α A σ))) ∧
        (∀ c ∈ C, SSGRoute.IsCoboundaryOn (SSGRoute.res ℚ K) (Subgroup.zpowers c)
          (fun σ => ε σ - gradedMapLin p Φ.toHom Φ.surjective i j (β c σ))) ∧
        ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
          (∀ A ∈ S, ¬ SSGRoute.IsConjPlace ℚ A B) → ¬ SSGRoute.IsSplitIn ℚ Nn B →
          ∀ σ : SSGRoute.GalQ, SSGRoute.IsInertia ℚ B σ → ε σ = 0 := by
  haveI : Fintype (K ≃ₐ[ℚ] K) := Fintype.ofFinite _
  haveI hFinE : Finite (E p (K ≃ₐ[ℚ] K) m i j) := by
    show Finite (refinedQuotient p (Work.Shrinking.freeOperatorGroup (K ≃ₐ[ℚ] K) m) i j)
    exact Work.CohomologicalShrinking.flow.finite_refinedQuotient p (K ≃ₐ[ℚ] K) m i j
  haveI hAlgCl : IsAlgClosure ℚ SSGRoute.QBar := AlgebraicClosure.instIsAlgClosure ℚ
  haveI hGalK : IsGalois ℚ K := inferInstance
  -- the reduction map `Gal(Nm) →* Gal(K)`
  let πN : (Nm ≃ₐ[ℚ] Nm) →* (K ≃ₐ[ℚ] K) := (flowQuot p (K ≃ₐ[ℚ] K) m i j).comp e.toMonoidHom
  have hπN : ∀ σ : SSGRoute.GalQ, πN (SSGRoute.res ℚ Nm σ) = SSGRoute.res ℚ K σ := by
    intro σ
    show flowQuot p (K ≃ₐ[ℚ] K) m i j (e (SSGRoute.res ℚ Nm σ)) = SSGRoute.res ℚ K σ
    rw [hem σ, hflowm σ]
  -- the obstruction class of the arithmetic, from the canonical local pairing with its reciprocity
  -- clause (`Work.SSGRoute.coker_obstruction`, which uses `G1`; the assembly here never uses the
  -- extra clause (8) of `G1⁺` -- see the import note at the top of this file)
  obtain ⟨x, hx⟩ := coker_obstruction p ℚ SSGRoute.QBar K Nm hKNm ζ hζ hζK
      (E p (K ≃ₐ[ℚ] K) m i j) T hT πN hπN S hSfin hSdisj hSram C hCinv hC hCdisj α hα β hβ
  -- kill it
  obtain ⟨Φ, hΦ⟩ := hshrink (SSGRoute.transportH1 e (flowRep p (K ≃ₐ[ℚ] K) m i j T) x)
  -- the level-`n` field of the pushed-down solution
  set φn : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j :=
    (flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φm with hφn
  have hsurjn : Function.Surjective φn :=
    (flowGroupMap_surjective_local p (K ≃ₐ[ℚ] K) i j Φ).comp hsurjm
  have hker_le : φm.ker ≤ φn.ker := by
    intro σ hσ
    rw [MonoidHom.mem_ker] at hσ ⊢
    rw [hφn, MonoidHom.comp_apply, hσ, map_one]
  have hopenn : IsOpen (φn.ker : Set SSGRoute.GalQ) :=
    Subgroup.isOpen_mono hker_le hopenm
  have hflown : ∀ σ : SSGRoute.GalQ,
      flowQuot p (K ≃ₐ[ℚ] K) n i j (φn σ) = SSGRoute.res ℚ K σ := by
    intro σ
    rw [hφn, MonoidHom.comp_apply, flowQuot_flowGroupMap]
    exact hflowm σ
  obtain ⟨Nn, hfdn, hnormn, hgaln, hKNn, hfixn, en, hen⟩ :=
    fixedField_and_equiv p K n i j φn hsurjn hopenn hflown
  have hNnNm : Nn ≤ Nm := by
    have hle' : Nm.fixingSubgroup ≤ Nn.fixingSubgroup := by
      intro σ hσ
      rw [hfixn σ, hφn, MonoidHom.comp_apply]
      have h1 : SSGRoute.res ℚ Nm σ = 1 := by
        have hmem : σ ∈ (AlgEquiv.restrictNormalHom Nm).ker := by
          rw [IntermediateField.restrictNormalHom_ker]; exact hσ
        simpa using hmem
      rw [← hem σ, h1, map_one, map_one]
    calc Nn = IntermediateField.fixedField Nn.fixingSubgroup :=
          (InfiniteGalois.fixedField_fixingSubgroup (k := ℚ) (K := SSGRoute.QBar) Nn).symm
      _ ≤ IntermediateField.fixedField Nm.fixingSubgroup := IntermediateField.fixedField_le hle'
      _ = Nm := InfiniteGalois.fixedField_fixingSubgroup (k := ℚ) (K := SSGRoute.QBar) Nm
  -- the restriction `q` and the level-`n` reduction `π₂`
  let q : (Nm ≃ₐ[ℚ] Nm) →* (Nn ≃ₐ[ℚ] Nn) :=
    en.symm.toMonoidHom.comp ((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp e.toMonoidHom)
  have hq : ∀ σ : SSGRoute.GalQ, q (SSGRoute.res ℚ Nm σ) = SSGRoute.res ℚ Nn σ := by
    intro σ
    show en.symm ((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ) (e (SSGRoute.res ℚ Nm σ))) = _
    rw [hem σ]
    refine en.injective ?_
    rw [MulEquiv.apply_symm_apply, hen σ, hφn, MonoidHom.comp_apply]
  let π₂ : (Nn ≃ₐ[ℚ] Nn) →* (K ≃ₐ[ℚ] K) := (flowQuot p (K ≃ₐ[ℚ] K) n i j).comp en.toMonoidHom
  have hπ₂ : ∀ σ : SSGRoute.GalQ, π₂ (SSGRoute.res ℚ Nn σ) = SSGRoute.res ℚ K σ := by
    intro σ
    show flowQuot p (K ≃ₐ[ℚ] K) n i j (en (SSGRoute.res ℚ Nn σ)) = SSGRoute.res ℚ K σ
    rw [hen σ, hflown σ]
  have hqcomp : ∀ y : (Nm ≃ₐ[ℚ] Nm),
      en (q y) = (flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ) (e y) := by
    intro y
    show en (en.symm ((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ) (e y))) = _
    rw [MulEquiv.apply_symm_apply]
  -- the coefficient morphism `F` and the vanishing of the transported class
  obtain ⟨F, hFhom, hFnat⟩ :=
    transportH1_natural_of_compat_St3 (K ≃ₐ[ℚ] K) m n i j Φ e en q hqcomp T
  have hzero : (groupHomology.map q F 1).hom x = 0 := by
    refine (Work.SSGRoute.transportH1 en (flowRep p (K ≃ₐ[ℚ] K) n i j T)).injective ?_
    rw [hFnat x, hΦ, map_zero]
  -- the arithmetic at the level `Nn`
  obtain ⟨ε, hεcoc, hεloc, hεS, hεC, hεin⟩ :=
    hx Nn hKNn hNnNm q hq π₂ hπ₂ (E p (K ≃ₐ[ℚ] K) n i j)
      (gradedMapLin p Φ.toHom Φ.surjective i j)
      (fun g ee => gradedMapLin_smul p Φ.toHom Φ.surjective Φ.equivariant i j g ee)
      F hFhom hzero
  exact ⟨Φ, Nn, hfdn, hnormn, hgaln, en, hKNn, hNnNm, fun σ => by rw [hen]; rfl,
    ε, hεcoc, hεloc, hεS, hεC, hεin⟩



/-- The projection `flowQuot` to `Gal(K/ℚ)` is insensitive to the level projection: both are the
`G`-component of the semidirect product.  (Local copy of `Work.SSGRoute.flowQuot_flowGroupProj`, so
that this module does not depend on `step4_shrunk_input`.) -/
theorem exists_localAlphaData_flowQuot_flowGroupProj_local (p : ℕ) (G : Type*) [Group G] (n i j : ℕ)
    (x : flowGroup p G n (tauSucc i j).1 (tauSucc i j).2) :
    flowQuot p G n i j (flowGroupProj p G n i j x) =
      flowQuot p G n (tauSucc i j).1 (tauSucc i j).2 x := by
  simp only [flowQuot, flowGroupProj]
  rw [← MonoidHom.comp_apply, SemidirectProduct.rightHom_comp_map]
  rfl

theorem exists_localAlphaData_local (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] {m i j : ℕ}
    (φm : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (ψm : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m
      (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2)
    (hproj : ∀ σ : SSGRoute.GalQ,
      Work.SSGRoute.flowGroupProj p (K ≃ₐ[ℚ] K) m i j (ψm σ) = φm σ)
    (hquot : ∀ σ : SSGRoute.GalQ, Work.CohomologicalShrinking.flowQuot p (K ≃ₐ[ℚ] K) m
      (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2
        (ψm σ) = Work.SSGRoute.restrict K σ)
    (hopen : IsOpen (ψm.ker : Set SSGRoute.GalQ))
    (hsplitting : ∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsT1Place p K A →
      ∃ l : ↥(SSGRoute.decomp ℚ A) →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m
          (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2,
        (∀ σ : ↥(SSGRoute.decomp ℚ A), SSGRoute.LiftsFlowAt (l σ) (φm ↑σ)) ∧
        (∀ σ : ↥(SSGRoute.decomp ℚ A), φm ↑σ = 1 → l σ = 1))
    (hscholz : SSGRoute.ScholzConditions p K φm)
    (A : ValuationSubring SSGRoute.QBar) (hA : SSGRoute.IsFinPlace ℚ A) :
    ∃ αA : SSGRoute.GalQ → Work.CohomologicalShrinking.E p (K ≃ₐ[ℚ] K) m i j,
      AlphaSpec p K m i j φm ψm A αA := by
  classical
  -- The level-`τ` solution `φm` is compatible with the restriction to `K` (through `hquot`).
  have hflowm : ∀ σ : SSGRoute.GalQ,
      flowQuot p (K ≃ₐ[ℚ] K) m i j (φm σ) = Work.SSGRoute.restrict K σ := by
    intro σ
    rw [← hproj σ, exists_localAlphaData_flowQuot_flowGroupProj_local]
    exact hquot σ
  by_cases hT1 : SSGRoute.IsT1Place p K A
  · -- ## Case `T¹`: use the local splitting `l` of `φm|D_A` supplied by the hypothesis.
    obtain ⟨l, hlift, hlone⟩ := hsplitting A hT1
    have hopenl : ∃ U : Subgroup SSGRoute.GalQ, IsOpen (U : Set SSGRoute.GalQ) ∧
        ∀ u (hu : u ∈ U) (hu' : u ∈ SSGRoute.decomp ℚ A), l ⟨u, hu'⟩ = 1 := by
      refine ⟨ψm.ker, hopen, ?_⟩
      intro u hu hu'
      exact hlone ⟨u, hu'⟩ (by rw [← hproj u, MonoidHom.mem_ker.mp hu, map_one])
    obtain ⟨αA, hcoc, hloc, hvals⟩ :=
      exists_localTarget_of_splitting p K φm ψm hproj hquot hopen A l hopenl hlift
    refine ⟨αA, hcoc, hloc, ?_, ?_, ?_, ?_⟩
    · exact fun _ => ⟨l, hlift, hlone, hvals⟩
    · exact fun h => absurd hT1 h
    · exact fun h => absurd hT1 h
    · exact fun h => absurd hT1 h
  · -- ## Case `A ∉ T¹` (so `A` is finite, not over `p`, and unramified in `K`).
    have hnotram : ¬ SSGRoute.IsRamifiedIn ℚ K A := fun h => hT1 ⟨hA, Or.inr h⟩
    have hApp : ¬ A.valuation (p : SSGRoute.QBar) < 1 := fun h => hT1 ⟨hA, Or.inl h⟩
    have hu : ∀ σ : SSGRoute.GalQ, SSGRoute.IsInertia ℚ A σ → σ ∈ K.fixingSubgroup :=
      fun σ hσ => of_not_not (fun h => hnotram ⟨σ, hσ, h⟩)
    by_cases hP1 : ∀ σ ∈ SSGRoute.decomp ℚ A, φm σ = 1
    · -- ## `T³`: `φm` is trivial on `D_A`; the target is `gradeInl (α σ) = (ψm σ)⁻¹`.
      have hnoD : ¬ ∃ σ : SSGRoute.GalQ, σ ∈ SSGRoute.decomp ℚ A ∧ φm σ ≠ 1 :=
        fun ⟨σ, hσ, hne⟩ => hne (hP1 σ hσ)
      obtain ⟨αA, hcoc, hloc, hvals⟩ :=
        exists_localTarget_of_proj_eq_one p K φm ψm hproj hflowm hopen A hP1
      refine ⟨αA, hcoc, hloc, ?_, ?_, ?_, ?_⟩
      · exact fun h => absurd h hT1
      · exact fun _ _ σ hσ => hvals ⟨σ, hσ⟩
      · exact fun _ hex _ => absurd hex hnoD
      · exact fun _ hex _ => absurd hex hnoD
    · -- ## `φm` is non-trivial on `D_A`.
      by_cases hP2 : ∀ σ : SSGRoute.GalQ, SSGRoute.IsInertia ℚ A σ → φm σ = 1
      · -- ## Kill-inertia target: `φm` trivial on the inertia of `A`.
        have hnoI : ¬ ∃ σ : SSGRoute.GalQ, SSGRoute.IsInertia ℚ A σ ∧ φm σ ≠ 1 :=
          fun ⟨σ, hI, hne⟩ => hne (hP2 σ hI)
        obtain ⟨αA, hcoc, hloc, hvals⟩ :=
          stage3KillInertiaTarget p K φm ψm hproj hquot hopen A hu
            (fun σ _ hI => hP2 σ hI)
        refine ⟨αA, hcoc, hloc, ?_, ?_, ?_, ?_⟩
        · exact fun h => absurd h hT1
        · exact fun _ h4 _ => absurd h4 hP1
        · exact fun _ _ _ σ hI => hvals σ hI
        · exact fun _ _ h6 => absurd h6 hnoI
      · -- ## `T²`: `φm` is non-trivial on the inertia of `A`.
        have hwit : ∃ σ : SSGRoute.GalQ, SSGRoute.IsInertia ℚ A σ ∧ φm σ ≠ 1 := by
          by_contra hcon
          exact hP2 (fun σ hI => by_contra (fun hne => hcon ⟨σ, hI, hne⟩))
        obtain ⟨σ0, hI0, hne0⟩ := hwit
        obtain ⟨hDK, _hcyc, hgen⟩ := hscholz.2.2 A hA ⟨σ0, hI0, hu σ0 hI0, hne0⟩
        obtain ⟨αA, hadd, hloc, _hzero, hcycT, hgenT⟩ :=
          stage3T2LocalTarget p K m i j φm ψm hproj hquot hopen A hA hApp hDK hgen
        refine ⟨αA, ?_, hloc, ?_, ?_, ?_, ?_⟩
        · intro g hg h hh
          rw [hadd g hg h hh, restrict_eq_one_of_mem_fixingSubgroup K (hDK g hg), one_smul]
        · exact fun h => absurd h hT1
        · exact fun _ h4 _ => absurd h4 hP1
        · exact fun _ _ h5 => absurd h5 hP2
        · exact fun _ _ _ => ⟨hDK, hcycT, hgenT⟩


theorem properStageAssemblyData (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)
    (hμ : SSGRoute.HasRootsOfUnity p K i)
    (hS : ∀ m : ℕ, 1 ≤ m → SSGRoute.IsSolvableStage p K m i j) (n : ℕ) (hn : 1 ≤ n) :
    ∃ (m : ℕ), 1 ≤ m ∧ n ≤ m ∧
      ∃ (φm : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m i j)
        (ψm : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m
          (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2)
        (Φ : Work.CohomologicalShrinking.OperatorMap (K ≃ₐ[ℚ] K) m n)
        (ψ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n
          (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2)
        (T0 : Finset (ValuationSubring SSGRoute.QBar)),
      SSGRoute.IsScholzSolution p K m i j φm ∧ SSGRoute.LiftsFlow ψm φm ∧
      IsOpen (ψm.ker : Set SSGRoute.GalQ) ∧
      (∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsT1Place p K A →
        ∃ l : ↥(SSGRoute.decomp ℚ A) →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m
            (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2,
          (∀ σ : ↥(SSGRoute.decomp ℚ A), SSGRoute.LiftsFlowAt (l σ) (φm σ)) ∧
          (∀ σ : ↥(SSGRoute.decomp ℚ A), φm σ = 1 → l σ = 1)) ∧
      SSGRoute.LiftsFlow ψ
        ((Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φm) ∧
      IsOpen (ψ.ker : Set SSGRoute.GalQ) ∧
      (∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsT1Place p K A →
        ∀ σ ∈ SSGRoute.decomp ℚ A, σ ∈ K.fixingSubgroup → ψ σ = 1) ∧
      (∀ c : SSGRoute.GalQ, c ^ 2 = 1 → c ∈ K.fixingSubgroup → ψ c = 1) ∧
      (∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ A →
        (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ ψ σ ≠ 1) →
        (∀ σ ∈ SSGRoute.decomp ℚ A, σ ∈ K.fixingSubgroup) ∧
        ((∀ σ ∈ SSGRoute.decomp ℚ A,
            (Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φm σ = 1) ∨
          (IsCyclic ((SSGRoute.decomp ℚ A).map ψ) ∧
            ∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧ ψ τ = ψ σ))) ∧
      (⨆ A ∈ T0, (SSGRoute.decomp ℚ A).map ψ) = Work.SSGRoute.flowEKer p (K ≃ₐ[ℚ] K) n i j := by
  classical
  haveI hFintypeG : Fintype (K ≃ₐ[ℚ] K) := Fintype.ofFinite _
  haveI hGalK : IsGalois ℚ K := IsGalois.mk
  haveI hAlgCl : IsAlgClosure ℚ SSGRoute.QBar := AlgebraicClosure.instIsAlgClosure ℚ
  haveI hGalQBar : IsGalois ℚ SSGRoute.QBar :=
    { to_isSeparable := inferInstance, to_normal := inferInstance }
  -- ## Step 1: a primitive `p`-th root of unity in `K`, and the cyclotomic dual `T`
  obtain ⟨ζ, hζK, hζ⟩ := exists_primitiveRoot_in_K p K i hμ
  obtain ⟨T, hTa, hTm, hTd, hTs, hTfm, hTf, hTdual⟩ :=
    exists_cyclotomicDual_finite_St3 p K ζ hζ hζK
  letI : AddCommGroup T := hTa
  letI : Module (ZMod p) T := hTm
  letI : DistribMulAction (K ≃ₐ[ℚ] K) T := hTd
  letI : SMulCommClass (K ≃ₐ[ℚ] K) (ZMod p) T := hTs
  letI : Module.Finite (ZMod p) T := hTfm
  letI : Finite T := hTf
  -- ## Step 2: the level-`m` datum (`hS m`)
  obtain ⟨m, hm1, hnm, φm, ψm, Nm, hfdNm, hnormNm, hgalNm, hSch, hLift, hopenm, hsplit, hKNm,
    ⟨em, hem⟩, hshrink⟩ :=
    stage3LevelData_St3 p K i j hj hji hμ hS n hn ζ hζ hζK T hTdual
  haveI : FiniteDimensional ℚ Nm := hfdNm
  haveI : Normal ℚ Nm := hnormNm
  haveI hGalNm : IsGalois ℚ Nm := hgalNm
  have hsurjm : Function.Surjective φm := hSch.1.1
  have hopenmφ : IsOpen (φm.ker : Set SSGRoute.GalQ) := hSch.1.2.1
  have hflowm : ∀ σ : SSGRoute.GalQ, flowQuot p (K ≃ₐ[ℚ] K) m i j (φm σ)
      = Work.SSGRoute.restrict K σ := hSch.1.2.2
  have hschm : SSGRoute.ScholzConditions p K φm := hSch.2
  have hprojm : ∀ σ : SSGRoute.GalQ,
      flowGroupProj p (K ≃ₐ[ℚ] K) m i j (ψm σ) = φm σ :=
    fun σ => flowGroupProj_eq_of_liftsFlowAt_local p K (hLift σ)
  have hquotm : ∀ σ : SSGRoute.GalQ, flowQuot p (K ≃ₐ[ℚ] K) m
      (tauSucc i j).1 (tauSucc i j).2 (ψm σ) = Work.SSGRoute.restrict K σ :=
    flowQuot_of_liftsFlow φm ψm hprojm hflowm
  have hkerNm : φm.ker = Nm.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker Nm]
    ext σ
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro h1
      refine em.injective ?_
      rw [map_one, hem σ, h1]
    · intro h2
      rw [← hem σ, h2, map_one]
  have hψker : ψm.ker ≤ Nm.fixingSubgroup := by
    intro x hx
    rw [← hkerNm, MonoidHom.mem_ker]
    rw [← hprojm x, MonoidHom.mem_ker.mp hx, map_one]
  -- ## Step 3: the field `Λ` of `ψm` and the places of `S` over `Ram(Λ) ∪ {p}`
  have hHopen : IsOpen ((ψm.ker ⊓ K.fixingSubgroup : Subgroup SSGRoute.GalQ) :
      Set SSGRoute.GalQ) := by
    rw [Subgroup.coe_inf]
    exact IsOpen.inter hopenm (IntermediateField.fixingSubgroup_isOpen K)
  obtain ⟨Λ, hfdΛ, hnormΛ, hΛker'⟩ :=
    exists_finiteDimensional_normal_fixingSubgroup_le (ψm.ker ⊓ K.fixingSubgroup) hHopen
  have hΛker : Λ.fixingSubgroup ≤ ψm.ker := le_trans hΛker' inf_le_left
  have hΛKfix : Λ.fixingSubgroup ≤ K.fixingSubgroup := le_trans hΛker' inf_le_right
  haveI : FiniteDimensional ℚ Λ := hfdΛ
  haveI : Normal ℚ Λ := hnormΛ
  haveI hGalΛ : IsGalois ℚ Λ := IsGalois.mk
  have hKΛ : K ≤ Λ := by
    have h2 : K ≤ IntermediateField.fixedField Λ.fixingSubgroup :=
      (IntermediateField.le_iff_le Λ.fixingSubgroup K).mpr hΛKfix
    rwa [InfiniteGalois.fixedField_fixingSubgroup Λ] at h2
  have hNmΛ : Nm ≤ Λ := by
    have h1 : Λ.fixingSubgroup ≤ Nm.fixingSubgroup := le_trans hΛker hψker
    have h2 : Nm ≤ IntermediateField.fixedField Λ.fixingSubgroup :=
      (IntermediateField.le_iff_le Λ.fixingSubgroup Nm).mpr h1
    rwa [InfiniteGalois.fixedField_fixingSubgroup Λ] at h2
  obtain ⟨Srep, hSrfin, hSrdisj, hSrram⟩ := ramifiedPlaces_finite (p := p) Λ
  -- ## Step 4: the `T⁰` places (Chebotarev), split in `Λ`
  obtain ⟨T0, α0, hT0fin, hT0splitΛ, hT0avoid, hT0disj, hT0coc, hT0inertia, hT0frob⟩ :=
    stage3T0Data (p := p) (K := K) (m := m) (i := i) (j := j) (Λ := Λ) (hKΛ := hKΛ)
      (S := Srep) (hSfin := hSrfin)
  -- ## Step 5: the coefficient sets `C` and `β`
  obtain ⟨C, hCinv, hCcov, hCdisj⟩ := exists_involutionSet
  let β : SSGRoute.GalQ → SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) m i j := fun _ _ => 0
  have hβ : ∀ c ∈ C, SSGRoute.IsCocycleOn (SSGRoute.res ℚ K) (Subgroup.zpowers c) (β c) := by
    intro c hc g hg h hh
    show (0 : E p (K ≃ₐ[ℚ] K) m i j) = 0 + (SSGRoute.res ℚ K g) • 0
    simp
  -- ## Step 6: the local targets `α` (the four cases of Step 3)
  have hAlphaEx : ∀ A ∈ Srep, ∃ αA : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) m i j,
      AlphaSpec p K m i j φm ψm A αA :=
    fun A hA =>
      exists_localAlphaData_local p K φm ψm hprojm hquotm hopenm hsplit hschm A (hSrfin A hA)
  let α : ValuationSubring SSGRoute.QBar → SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) m i j :=
    fun A => if h1 : A ∈ Srep then Classical.choose (hAlphaEx A h1)
             else if h2 : A ∈ T0 then α0 A else fun _ => 0
  have hαspec : ∀ A ∈ Srep, AlphaSpec p K m i j φm ψm A (α A) := by
    intro A hA
    show AlphaSpec p K m i j φm ψm A
      (if h1 : A ∈ Srep then Classical.choose (hAlphaEx A h1)
       else if h2 : A ∈ T0 then α0 A else fun _ => 0)
    rw [dif_pos hA]
    exact Classical.choose_spec (hAlphaEx A hA)
  have hα0 : ∀ A ∈ T0, α A = α0 A := by
    intro A hA
    by_cases h1 : A ∈ Srep
    · exact absurd (isConjPlace_refl A) (hT0avoid A hA A h1)
    · show (if h1 : A ∈ Srep then Classical.choose (hAlphaEx A h1)
        else if h2 : A ∈ T0 then α0 A else fun _ => 0) = α0 A
      rw [dif_neg h1, dif_pos hA]
  -- the set `S` of places carrying local data, and its properties
  let S : Finset (ValuationSubring SSGRoute.QBar) := Srep ∪ T0
  have hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace ℚ A := by
    intro A hA
    rcases Finset.mem_union.mp hA with h | h
    · exact hSrfin A h
    · exact hT0fin A h
  have hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace ℚ A B → A = B := by
    intro A hA B hB hc
    rcases Finset.mem_union.mp hA with h1 | h1 <;> rcases Finset.mem_union.mp hB with h2 | h2
    · exact hSrdisj A h1 B h2 hc
    · exact absurd (isConjPlace_symm hc) (hT0avoid B h2 A h1)
    · exact absurd hc (hT0avoid A h1 B h2)
    · exact hT0disj A h1 B h2 hc
  have hSramΛ : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (SSGRoute.IsRamifiedIn ℚ Λ B ∨ B.valuation (p : SSGRoute.QBar) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace ℚ A B := by
    intro B hBfin h
    rcases h with h | h
    · obtain ⟨A, hA, hc⟩ := hSrram B hBfin (Or.inl h)
      exact ⟨A, Finset.mem_union_left _ hA, hc⟩
    · obtain ⟨A, hA, hc⟩ := hSrram B hBfin (Or.inr h)
      exact ⟨A, Finset.mem_union_left _ hA, hc⟩
  have hSram : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (SSGRoute.IsRamifiedIn ℚ Nm B ∨ B.valuation (p : SSGRoute.QBar) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace ℚ A B := by
    intro B hBfin h
    rcases h with h | h
    · obtain ⟨σ, hI, hσ⟩ := h
      exact hSramΛ B hBfin
        (Or.inl ⟨σ, hI, fun hmem => hσ (IntermediateField.fixingSubgroup_le hNmΛ hmem)⟩)
    · exact hSramΛ B hBfin (Or.inr h)
  have hαS : ∀ A ∈ S, SSGRoute.IsCocycleOn (SSGRoute.res ℚ K) (SSGRoute.decomp ℚ A) (α A) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp ℚ A) (α A) := by
    intro A hA
    rcases Finset.mem_union.mp hA with h | h
    · exact ⟨(hαspec A h).1, (hαspec A h).2.1⟩
    · rw [hα0 A h]; exact hT0coc A h
  -- ## Step 7: the arithmetic core of Step 3
  obtain ⟨Φ, Nn, hfdNn, hnormNn, hgalNn, en, hKNn, hNnNm, hen, ε, hεcoc, hεloc, hεS, hεC, hεin⟩ :=
    stage3CokerInterface_local p K hj hji Nm hKNm em φm hsurjm hopenmφ hem hflowm ζ hζ hζK T hTdual
      S hSfin hSdisj hSram C hCinv hCcov hCdisj α hαS β hβ n hshrink
  haveI : FiniteDimensional ℚ Nn := hfdNn
  haveI : Normal ℚ Nn := hnormNn
  haveI hGalNn : IsGalois ℚ Nn := hgalNn
  have hεmul : ∀ σ τ : SSGRoute.GalQ,
      ε (σ * τ) = ε σ + (Work.SSGRoute.restrict K σ) • ε τ :=
    fun σ τ => hεcoc σ (Subgroup.mem_top σ) τ (Subgroup.mem_top τ)
  -- ## Step 8: the twist
  let φn : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j :=
    (flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φm
  let ψ₀ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 :=
    (flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ).comp ψm
  have hquot₀ : ∀ σ : SSGRoute.GalQ, flowQuot p (K ≃ₐ[ℚ] K) n
      (tauSucc i j).1 (tauSucc i j).2 (ψ₀ σ) = Work.SSGRoute.restrict K σ := by
    intro σ
    show flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2
      ((flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ) (ψm σ)) = _
    rw [flowQuot_flowGroupMap]
    exact hquotm σ
  let ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 :=
    flowTwistEHom p K n i j ε ψ₀ hquot₀ hεmul
  have hLifts₀ : SSGRoute.LiftsFlow ψ₀ φn :=
    flowGroupMap_comp_liftsFlow p K Φ ψm φm hLift
  have hkerNn : φn.ker = Nn.fixingSubgroup := by
    have key : ∀ σ : SSGRoute.GalQ, σ ∈ φn.ker ↔ SSGRoute.res ℚ Nn σ = 1 := by
      intro σ
      rw [MonoidHom.mem_ker]
      constructor
      · intro h1
        refine en.injective ?_
        rw [map_one, hen σ]
        exact h1
      · intro h2
        show (flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ) (φm σ) = 1
        rw [← hen σ, h2, map_one]
    ext σ
    rw [key σ, ← IntermediateField.restrictNormalHom_ker Nn, MonoidHom.mem_ker]
  -- ## Step 9: the clause data at the representatives of `S`
  have hRepI : ∀ A ∈ Srep, SSGRoute.IsT1Place p K A →
      ∀ σ ∈ SSGRoute.decomp ℚ A, σ ∈ K.fixingSubgroup → ψ σ = 1 := by
    intro A hA hT1 σ hσ hfix
    obtain ⟨l, hlift, hlone, hshape⟩ := (hαspec A hA).2.2.1 hT1
    have h := flowTwistE_eq_one_of_T1Target p K Φ φm ψm A l hlone (hschm.1 A hT1) (α A) ε
      hshape (hεS A (Finset.mem_union_left _ hA))
    show flowTwistE p K n i j ε ψ₀ σ = 1
    exact h σ hσ hfix
  have hRepII : ∀ A ∈ Srep,
      ((∀ σ : SSGRoute.GalQ, SSGRoute.IsInertia ℚ A σ → σ ∈ K.fixingSubgroup → ψ σ = 1) ∨
        ((∀ σ ∈ SSGRoute.decomp ℚ A, σ ∈ K.fixingSubgroup) ∧
          ((∀ σ ∈ SSGRoute.decomp ℚ A, φn σ = 1) ∨
            (IsCyclic ((SSGRoute.decomp ℚ A).map ψ) ∧
              ∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧ ψ τ = ψ σ)))) := by
    intro A hA
    by_cases hT1 : SSGRoute.IsT1Place p K A
    · exact Or.inl (fun σ hσ hfix => hRepI A hA hT1 σ hσ.1 hfix)
    · have hnotram : ¬ SSGRoute.IsRamifiedIn ℚ K A := fun h => hT1 ⟨hSrfin A hA, Or.inr h⟩
      have hu : ∀ σ : SSGRoute.GalQ, SSGRoute.IsInertia ℚ A σ → σ ∈ K.fixingSubgroup :=
        mem_fixingSubgroup_of_isInertia_of_not_isRamifiedIn K A hnotram
      by_cases hD1 : ∀ σ ∈ SSGRoute.decomp ℚ A, φm σ = 1
      · have hshape : ∀ σ : SSGRoute.GalQ, SSGRoute.IsInertia ℚ A σ →
            gradeInl p (K ≃ₐ[ℚ] K) m i j (Additive.toMul (α A σ)) = (ψm σ)⁻¹ :=
          fun σ hσ => (hαspec A hA).2.2.2.1 hT1 hD1 σ hσ.1
        refine Or.inl (fun σ hσ hfix => ?_)
        show flowTwistE p K n i j ε ψ₀ σ = 1
        exact flowTwistE_eq_one_of_inertiaShape p K Φ ψm A (α A) ε hu hshape
          (hεS A (Finset.mem_union_left _ hA)) σ hσ
      · have hexD : ∃ σ ∈ SSGRoute.decomp ℚ A, φm σ ≠ 1 := by
          by_contra hcon
          exact hD1 (fun σ hσ => by by_contra h2; exact hcon ⟨σ, hσ, h2⟩)
        by_cases hI1 : ∀ σ : SSGRoute.GalQ, SSGRoute.IsInertia ℚ A σ → φm σ = 1
        · have hshape : ∀ σ : SSGRoute.GalQ, SSGRoute.IsInertia ℚ A σ →
              gradeInl p (K ≃ₐ[ℚ] K) m i j (Additive.toMul (α A σ)) = (ψm σ)⁻¹ :=
            fun σ hσ => (hαspec A hA).2.2.2.2.1 hT1 hexD hI1 σ hσ
          refine Or.inl (fun σ hσ hfix => ?_)
          show flowTwistE p K n i j ε ψ₀ σ = 1
          exact flowTwistE_eq_one_of_inertiaShape p K Φ ψm A (α A) ε hu hshape
            (hεS A (Finset.mem_union_left _ hA)) σ hσ
        · have hexI : ∃ σ : SSGRoute.GalQ, SSGRoute.IsInertia ℚ A σ ∧ φm σ ≠ 1 := by
            by_contra hcon
            exact hI1 (fun σ hσ => by by_contra h2; exact hcon ⟨σ, hσ, h2⟩)
          obtain ⟨hDK, hcyc, hgenT⟩ :=
            (hαspec A hA).2.2.2.2.2 hT1 hexD hexI
          have hpoint : ∀ σ ∈ SSGRoute.decomp ℚ A,
              ε σ = gradedMapLin p Φ.toHom Φ.surjective i j (α A σ) := by
            intro σ hσ
            exact sub_eq_zero.mp (eq_zero_of_isCoboundaryOn p K n i j
              (hεS A (Finset.mem_union_left _ hA)) σ hσ (hDK σ hσ))
          have hres := isCyclic_and_inertia_generates_pushforward p K Φ ψm (α A) ε A hpoint
            hcyc hgenT
          refine Or.inr ⟨hDK, Or.inr ⟨?_, ?_⟩⟩
          · have hset : ((flowTwistE p K n i j ε
                  ((flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ).comp ψm)) ''
                  (SSGRoute.decomp ℚ A : Set SSGRoute.GalQ))
                = (ψ '' (SSGRoute.decomp ℚ A : Set SSGRoute.GalQ)) := by
              refine Set.image_congr fun σ _ => ?_
              exact (flowTwistEHom_apply p K n i j ε ψ₀ hquot₀ hεmul σ).symm
            have hEq : Subgroup.closure ((flowTwistE p K n i j ε
                  ((flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ).comp ψm)) ''
                  (SSGRoute.decomp ℚ A : Set SSGRoute.GalQ))
                = (SSGRoute.decomp ℚ A).map ψ := by
              rw [map_eq_closure_image ψ (SSGRoute.decomp ℚ A), hset]
            exact hEq ▸ hres.1
          · intro σ hσ
            obtain ⟨τ, hτ, hτeq⟩ := hres.2 σ hσ
            exact ⟨τ, hτ, hτeq⟩
  -- ## Step 10: the global clauses
  have hIall : ∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsT1Place p K A →
      ∀ σ ∈ SSGRoute.decomp ℚ A, σ ∈ K.fixingSubgroup → ψ σ = 1 := by
    intro A hT1
    have hram : SSGRoute.IsRamifiedIn ℚ Λ A ∨ A.valuation (p : SSGRoute.QBar) < 1 := by
      rcases hT1.2 with h | h
      · exact Or.inr h
      · obtain ⟨σ, hσI, hσmem⟩ := h
        exact Or.inl ⟨σ, hσI, fun hmem => hσmem (hΛKfix hmem)⟩
    obtain ⟨A', hA', hc⟩ := hSrram A hT1.1 hram
    exact (clauseData_conj_transfer_T1 p K ψ φn A' A hc (hRepI A' hA') (hRepII A' hA')).1 hT1
  have hIIall : ∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ A →
      ((∀ σ : SSGRoute.GalQ, SSGRoute.IsInertia ℚ A σ → σ ∈ K.fixingSubgroup → ψ σ = 1) ∨
        ((∀ σ ∈ SSGRoute.decomp ℚ A, σ ∈ K.fixingSubgroup) ∧
          ((∀ σ ∈ SSGRoute.decomp ℚ A, φn σ = 1) ∨
            (IsCyclic ((SSGRoute.decomp ℚ A).map ψ) ∧
              ∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧ ψ τ = ψ σ)))) := by
    intro A hAfin
    by_cases hconj : ∃ A' ∈ Srep, SSGRoute.IsConjPlace ℚ A' A
    · obtain ⟨A', hA', hc⟩ := hconj
      exact (clauseData_conj_transfer_T1 p K ψ φn A' A hc (hRepI A' hA') (hRepII A' hA')).2
    · push_neg at hconj
      by_cases hsplitNn : SSGRoute.IsSplitIn ℚ Nn A
      · refine Or.inr ⟨fun σ hσ => IntermediateField.fixingSubgroup_le hKNn (hsplitNn hσ),
          Or.inl fun σ hσ => MonoidHom.mem_ker.mp (by rw [hkerNn]; exact hsplitNn hσ)⟩
      · refine Or.inl fun σ hσI hfix => ?_
        have hNnΛ : Nn ≤ Λ := le_trans hNnNm hNmΛ
        have hconjS : ∀ A' ∈ S, ¬ SSGRoute.IsConjPlace ℚ A' A := by
          intro A' hA' hc
          rcases Finset.mem_union.mp hA' with h1 | h1
          · exact hconj A' h1 hc
          · exfalso
            have hsA' : SSGRoute.IsSplitIn ℚ Nn A' :=
              fun σ hσ => IntermediateField.fixingSubgroup_le hNnΛ (hT0splitΛ A' h1 hσ)
            obtain ⟨g, hg⟩ := hc
            have h2 := (isSplitIn_conj Nn (fixingSubgroup_normal_of_normal Nn) A' g).mpr hsA'
            rw [hg] at h2
            exact hsplitNn h2
        have hnotramΛ : ¬ SSGRoute.IsRamifiedIn ℚ Λ A :=
          (not_isRamifiedIn_and_not_val_p_lt_one_of_forall_not_conj Λ p S hSramΛ A hAfin
            hconjS).1
        have hψm1 : ψm σ = 1 :=
          MonoidHom.mem_ker.mp (hΛker
            (mem_fixingSubgroup_of_isInertia_of_not_isRamifiedIn Λ A hnotramΛ σ hσI))
        have hψ01 : ψ₀ σ = 1 := by
          show flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ (ψm σ) = 1
          rw [hψm1, map_one]
        have hε0 : ε σ = 0 := hεin A hAfin hconjS hsplitNn σ hσI
        show flowTwistE p K n i j ε ψ₀ σ = 1
        rw [flowTwistE, flowTwist, hε0, hψ01]
        simp
  -- ## Step 11: the `T⁰` generation of `flowEKer`
  let frobOf : (A : ValuationSubring SSGRoute.QBar) → A ∈ T0 →
      ↥(SSGRoute.decomp ℚ A) := fun A hA => Work.SSGRoute.localFrobElem ⟨A, hT0fin A hA⟩
  let frob : (A : ValuationSubring SSGRoute.QBar) → ↥(SSGRoute.decomp ℚ A) := fun A =>
    if hA : A ∈ T0 then frobOf A hA else 1
  let g : ValuationSubring SSGRoute.QBar → E p (K ≃ₐ[ℚ] K) n i j := fun A =>
    gradedMapLin p Φ.toHom Φ.surjective i j
      (α A ((frob A : ↥(SSGRoute.decomp ℚ A)) : SSGRoute.GalQ))
  have hgenT0 : (⨆ A ∈ T0, (SSGRoute.decomp ℚ A).map ψ) = flowEKer p (K ≃ₐ[ℚ] K) n i j := by
    have hNnΛ : Nn ≤ Λ := le_trans hNnNm hNmΛ
    refine iSup_map_eq_flowEKer_of_prescribed_values p K Nn Φ φn ψ₀
      (fun σ => flowGroupProj_eq_of_liftsFlowAt_local p K (hLifts₀ σ)) hkerNn hKNn T0 hT0fin
      (fun A hA σ hσ => IntermediateField.fixingSubgroup_le hNnΛ (hT0splitΛ A hA hσ))
      α ε ψ (fun σ => rfl) (fun A hA => hεS A (Finset.mem_union_right _ hA)) g ?_ ?_
    · intro A hA
      have hmem : ((frobOf A hA : ↥(SSGRoute.decomp ℚ A)) : SSGRoute.GalQ) ∈ ψm.ker :=
        hΛker (hT0splitΛ A hA (frobOf A hA).2)
      have hψ01 : ψ₀ ((frobOf A hA : ↥(SSGRoute.decomp ℚ A)) : SSGRoute.GalQ) = 1 := by
        show flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ
          (ψm ((frobOf A hA : ↥(SSGRoute.decomp ℚ A)) : SSGRoute.GalQ)) = 1
        rw [MonoidHom.mem_ker.mp hmem, map_one]
      exact ⟨0, by rw [toMul_zero, map_one, hψ01], by
        show gradedMapLin p Φ.toHom Φ.surjective i j
          (α A ((frobOf A hA : ↥(SSGRoute.decomp ℚ A)) : SSGRoute.GalQ)) = g A - 0
        rw [sub_zero]
        show gradedMapLin p Φ.toHom Φ.surjective i j
          (α A ((frobOf A hA : ↥(SSGRoute.decomp ℚ A)) : SSGRoute.GalQ)) =
            gradedMapLin p Φ.toHom Φ.surjective i j
              (α A ((frob A : ↥(SSGRoute.decomp ℚ A)) : SSGRoute.GalQ))
        rw [show (frob A : ↥(SSGRoute.decomp ℚ A)) = frobOf A hA from dif_pos hA]⟩
    · refine iSup_zpowers_eq_top_of_surjective
        (fun A : ↥T0 => Additive.toMul (g A.1)) ?_
      intro y
      obtain ⟨y', hy'⟩ := gradedMapLin_surjective_local p (K ≃ₐ[ℚ] K) Φ i j y
      obtain ⟨A, hA, hAy⟩ := hT0frob y'
      refine ⟨⟨A, hA⟩, ?_⟩
      have h1 : α A ((frob A : ↥(SSGRoute.decomp ℚ A)) : SSGRoute.GalQ) = y' := by
        rw [show (frob A : ↥(SSGRoute.decomp ℚ A)) = frobOf A hA from dif_pos hA]
        rw [hα0 A hA]
        exact hAy (hT0fin A hA)
      show Additive.toMul (g A) = Additive.toMul y
      show Additive.toMul (gradedMapLin p Φ.toHom Φ.surjective i j
        (α A ((frob A : ↥(SSGRoute.decomp ℚ A)) : SSGRoute.GalQ))) = Additive.toMul y
      rw [h1, hy']
  -- ## Step 12: the assembly
  refine ⟨m, hm1, hnm, φm, ψm, Φ, ψ, T0, hSch, hLift, hopenm, hsplit, ?_, ?_, hIall, ?_, ?_,
    hgenT0⟩
  · exact flowTwistEHom_liftsFlow p K n i j ε ψ₀ φn hquot₀ hεmul hLifts₀
  · exact flowTwistEHom_isOpen_ker p K n i j ε ψ₀ hquot₀ hεmul
      (Subgroup.isOpen_mono (fun x hx => by
        rw [MonoidHom.mem_ker] at hx ⊢
        show (flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ) (ψm x) = 1
        rw [hx, map_one]) hopenm) hεloc
  · exact involution_clause_of_hasRootsOfUnity p K i j hj hji hμ ψ
  · intro A hAfin hhyp
    rcases hIIall A hAfin with hb | hc
    · exact absurd hhyp (by
        rintro ⟨σ, hσI, hfix, hne⟩
        exact hne (hb σ hσI hfix))
    · exact hc


end Work.SSGRoute
