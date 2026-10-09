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
import Submission.Work.SSGRoute.step4CokerSide_proved
import Submission.Work.SSGRoute.step4Helpers
import Submission.Work.SSGRoute.scholz_two_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/SSGRoute/DESIGN.md first (orchestrator design; your lemma is one node of its DAG). Shared vocabulary: Submission/Work/SSGRoute/Interfaces.lean (namespace SSGRoute; do NOT edit — put any new shared definition in your own file). The proved class-field-theory library is available as NK.* (Chebotarev: NK.NUV2.chebotarev_all0 with hFC := NK.CFTLib.fundamentalClassElement; local reciprocity NK.NUV2.kernelCondition_all; existence NK.CFTLib.Existence.classField_exists_primeIndex (unramified only); Hasse–Brauer–Noether NK.GlobalCFTdeep.hbnUnits; NK.KC.localBaseChangeInput_of_kc; NK.HR2.transferStepOnePlace), all axiom-clean. NEVER use Work.HilbertSymbol.GrunwaldWang (false as written). Siblings run in parallel; import them when they land.

# Guidance: Step 4 of the proof of Theorem 15 — make new ramification cyclic totally ramified

From `IsProperStage` at all levels, produce a Scholz solution at τ+1 at level n. Twist ψ by x = cor(y).

**Sketch** (paper pp. 30–32).
1. Choose T⁰ ⊆ cs(N_m) whose decomposition groups generate Gal(N_{τ+1}/N_τ) (properness is preserved).
   Let T := Ram(N_{τ+1}) ∪ {p, ∞} ∪ T⁰.
2. Over **K**, apply `SSGRoute.coker_obstruction` with base k := ↥K (Ω = ℚ̄, `IsAlgClosure ↥K ℚ̄`),
   N := N_m, trivial Gal(K/K), E := E_m (trivial G_K-module), T := μ_p^∨ (trivial). The local targets η_P
   at the places over T:
   - 0 over Ram(N)∪{p}∪T⁰;
   - at one chosen place over each new-ramified ℓ, the unramified class removing the unramified part of ψ;
   - 0 at the other places over ℓ.

   The obstruction lies in H₁(Gal(N_m/K), E_m ⊗ T) = F(m)/F(m)² ⊗ (E_m ⊗ T) (universal coefficients:
   `Work.CohomologicalShrinking.universalCoefficient.h1AddEquivPQuotientSub`,
   `flow.flowNormalSquareEquiv`). Kill it with `exists_shrinking_H1` (Prop 7(ii)).
3. With y in hand, apply `SSGRoute.shafarevich_existence` (k = ℚ, Λ = N_n) to get x with x|_{D_A} = cor(y)
   on T and x cyclic outside T.
4. Twist, then check (ii). The new ramification of x is at primes in cs(N_n) and the local groups there are
   cyclic ⊆ E, hence cyclic of order p and totally ramified. The previously-new primes now have zero
   unramified part. (i) holds because x = 0 over T¹.

**Transport.** Between `Ω ≃ₐ[K] Ω` and `K.fixingSubgroup ≤ G_ℚ` use `IntermediateField.fixingSubgroupEquiv`,
and between places over K and over ℚ use the same valuation subrings. Delegate this transport as one lemma,
used twice.

**Imports.** Interfaces, `SSGRoute.coker_obstruction`, `SSGRoute.shafarevich_existence`,
`SSGRoute.prop5Data_exists`, `SSGRoute.local_tame_lifting`.
-/

/-! # Step 4 of Theorem 15 (Schmidt–Wingberg §5): the node file

The *algebraic core* of Step 4 (`flowTwistEHom`, the graded piece, the stage projection) lives
upstream in `Submission.Work.SSGRoute.twistLayer`, so that the arithmetic siblings
(`Work.SSGRoute.step4_shrunk_input`, `step4_local_target`, `twist_cyclic_of_psi_trivial`,
`step4_transport_of_sha13_psi`) can import it without creating a module cycle with this node.

This file contains:

* `isFlowSolution_flowTwistEHom`, `isScholzSolution_flowTwistEHom` — the twist of a stage-3 solution
  is a Scholz solution, given the local clauses on the twisting cocycle `x`;
* `exists_T0_cyclic_of_surjective` — the finite set `T⁰` of the paper (Chebotarev, not arithmetic);
* `Step4Input` — the output of the Step-4 shrinking, i.e. (definitionally) the conclusion of
  `Work.SSGRoute.step4_shrunk_input`;
* `scholz_succ_of_step4Input` — Step 4 from that input (no arithmetic: pure assembly);
* `step4Input_of_properStages` — the single remaining obligation of this node, quoted from
  `Work.SSGRoute.step4_shrunk_input`;
* `scholz_succ_of_properStage` — the target, assembled from the two.

See `## State of Step 4` below for the dictionary between the clauses of `Step4Input` and the paper.
-/

open scoped Pointwise

namespace Work.SSGRoute

/-! ## STATUS (09-30, after `_NOTE_STEP4_DESIGN.md` §1.5)

The Step-4 route of this file was redesigned by the project lead; the long addenda further down
describe the *superseded* route and are kept only as history.

Current chain (each item a separate module):

* `step4CokerSide_holds` := `Work.SSGRoute.step4CokerSide_proved` (which needs the extra
  hypothesis `hi : 2 ≤ i` and consumes `Work.SSGRoute.step4_y_exists_v2`);
* `step4_y_exists_v2` ← `step4_y_prescribed_v2` ← `Work.SSGRoute.step4_y_localData_escape`
  (SW's Fourth Step as a Grünwald-with-escape statement, no Poitou–Tate input), whose own inputs are
  `Work.SSGRoute.step4_tool_S_exists`, `Work.SSGRoute.step4_frattini_newPlace` and
  `Work.SSGRoute.grunwald_escape_support_E` (← `Work.SSGRoute.grunwald_escape_relative`);
* `step4Input_of_properStages` (this file) then hands the coker side to the guarded bundle
  `step4_bundle_of_sha13_guarded` (this file);
* the target `scholz_succ_of_properStage` keeps its statement and splits on `i`: for `i = 1` (so
  `j = 1`, `tauSucc 1 1 = (2,1)`) it is `Work.SSGRoute.scholz_two_one`, otherwise Step 4.

The `y`-side's remaining `sorry` sources are the four new nodes above; the `x`-side's is
`Work.SSGRoute.ZConstruction.ZDataGeneral.z_data_general_of_ramified`
(via `SSGRoute.shafarevich_existence`).  See `H9_STATUS.md` §§23–25 for the wiring and the audit.
-/

open SSGRoute
open _root_.SSGRoute
open Work.CohomologicalShrinking

variable {p : ℕ}


/-- **The coker side of Step 4** (`Work.SSGRoute.Step4CokerSide`), from the proper stages at all
levels: the second shrinking (Prop 7(ii)) with `SSGRoute.coker_obstruction` over the base `↥K`
(see the Addenda below for the workflow), producing the datum `y`, the class `x` with Theorem 13's
clauses, the local-target realisation `hreal` and the local dichotomy `hdich`.

This is the remaining arithmetic of the node, and it is stated in the *provable* shape: the level
`m ≥ n`, the operator map `Φ : F(m) ↠ F(n)` and the level-`m` stage-3 data are part of the
existential, since the shrinking needs that presentation of the level-`n` data.

**Placeholder.**  **A fleet-level blocker (reported here because it blocks this node's lane).**  The modules
`Submission.Work.SSGRoute.local_lifting_setup` (which defines `Work.SSGRoute.IsTrivialAtLevel`) and
`Submission.Work.SSGRoute.inertiaAtLevelDefs` (which declares an `abbrev` of the same name) cannot be
imported together: any module whose closure contains both fails with
``environment already contains 'Work.SSGRoute.IsTrivialAtLevel._proof_2'``.  The coker side needs
both sides of that pair (`SSGRoute.shafarevich_theorem13` reaches `inertiaAtLevelDefs`, and the
local targets `Work.SSGRoute.step4_local_target` reach `local_lifting_setup` through
`local_tame_lifting` → `inertia_of_isInertia`), so the delegated proof of `step4CokerSide_holds`
cannot start until one of the two declarations is renamed (a rename in
`inertiaAtLevelDefs.lean`, whose declaration is the newer of the two, plus its four users, would
suffice).

The same statement is being proved in the sibling module
`Submission.Work.SSGRoute.step4CokerSide_holds` (declaration `Work.SSGRoute.step4CokerSide_holds`);
this local copy exists only so that this file builds independently.  Once that module builds, this
copy should be replaced by `import Submission.Work.SSGRoute.step4CokerSide_holds`. -/
theorem step4CokerSide_holds (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i) (hi : 2 ≤ i)
    (hμ : SSGRoute.HasRootsOfUnity p K i)
    (hP : ∀ m : ℕ, 1 ≤ m → SSGRoute.IsProperStage p K m i j) (n : ℕ) (hn : 1 ≤ n) :
    Step4CokerSide p K n i j := by
  exact step4CokerSide_proved p K i j hj hji hi hμ hP n hn


/-! ### Guarded copies of the assembly: the corrected local-target clause `hreal`

`Work.SSGRoute.Step4CokerSide` states the local-target clause `hreal` with the guard "the twist is
ramified at `A`", which is the shape in which the local target `Work.SSGRoute.step4_local_target`
applies (see the KNOWN DEFECT note in `step4CokerSideDefs.lean` and `H9_STATUS.md` §3).  The pipeline
lemmas `Work.SSGRoute.item5_of_bundle` / `step4Input_of_bundle` / `step4_bundle_of_sha13`
(`step4_items_assembly.lean`, `step4_bundle_assembly.lean`) consume the *unguarded* clause; the two
copies below are the same proofs with the guard threaded through, and they are what
`step4Input_of_properStages` uses.  Nothing is lost: `item5_of_bundle` passes to `hreal` its own
hypothesis `hram` -- the twist ramified at `A` -- so the guard is available at the only place where
`hreal` is consumed. -/

-- (item5/item6_of_bundle_guarded: now imported from step4_bundle_assembly; the byte-identical local copies were removed by the lead 09-28 to fix the duplicate-declaration clash.)

theorem step4_bundle_of_sha13_guarded (p : ℕ) [Fact p.Prime] (K Λ : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] [FiniteDimensional ℚ Λ] (hΛgal : IsGalois ℚ Λ)
    (hKΛ : K ≤ Λ) (n i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)
    (φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2)
    (hφ : SSGRoute.IsScholzSolution p K n i j φ) (hLift : SSGRoute.LiftsFlow ψ φ)
    (hφquot : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n i j (φ σ) = Work.SSGRoute.restrict K σ)
    (hψquot : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (ψ σ) =
      Work.SSGRoute.restrict K σ)
    (hopen : IsOpen (ψ.ker : Set SSGRoute.GalQ)) (hΛker : ψ.ker = Λ.fixingSubgroup)
    (hT1ψ : ∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsT1Place p K A →
      ∀ σ ∈ SSGRoute.decomp ℚ A, σ ∈ K.fixingSubgroup → ψ σ = 1)
    (hInvψ : ∀ c : SSGRoute.GalQ, c ^ 2 = 1 → c ∈ K.fixingSubgroup → ψ c = 1)
    (hProp : ∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ A →
      (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ ψ σ ≠ 1) →
      (∀ σ ∈ SSGRoute.decomp ℚ A, σ ∈ K.fixingSubgroup) ∧
      ((∀ σ ∈ SSGRoute.decomp ℚ A, φ σ = 1) ∨
        (IsCyclic ((SSGRoute.decomp ℚ A).map ψ) ∧
          ∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧ ψ τ = ψ σ)))
    (S : Finset (ValuationSubring SSGRoute.QBar)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace ℚ A)
    (hSram : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (SSGRoute.IsRamifiedIn ℚ Λ B ∨ B.valuation (p : SSGRoute.QBar) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace ℚ A B)
    (T0 : Finset (ValuationSubring SSGRoute.QBar))
    (hT0gen : (⨆ A ∈ T0, (SSGRoute.decomp ℚ A).map ψ) = flowEKer p (K ≃ₐ[ℚ] K) n i j)
    (hT0cyc : ∀ A ∈ T0, IsCyclic ((SSGRoute.decomp ℚ A).map ψ))
    (hT0S : ∀ A ∈ T0, A ∈ S)
    (hT0split : ∀ A ∈ T0, SSGRoute.IsSplitIn ℚ K A)
    (sec : (K ≃ₐ[ℚ] K) → SSGRoute.GalQ) (hsec : ∀ s, AlgEquiv.restrictNormalHom K (sec s) = s)
    (y : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (hyT : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (∃ A ∈ S, SSGRoute.IsConjPlace ℚ A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia ℚ B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (∃ A ∈ S, SSGRoute.IsConjPlace ℚ A B) →
      (¬ SSGRoute.IsSplitIn ℚ K B ∨ B.valuation (p : SSGRoute.QBar) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp ℚ B → y σ = 0)
    (hyT0 : ∀ A ∈ T0, ∀ σ ∈ SSGRoute.decomp ℚ A,
      (∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹ * σ * sec s)) = 0)
    (x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (hxmul : ∀ σ τ : SSGRoute.GalQ, x (σ * τ) = x σ + (Work.SSGRoute.restrict K σ) • x τ)
    (hxloc : SSGRoute.IsLocConstOn ⊤ x)
    (hxsplit : ∀ A ∈ S, SSGRoute.IsSplitIn ℚ K A →
      SSGRoute.IsCoboundaryOn (AlgEquiv.restrictNormalHom K) (SSGRoute.decomp ℚ A)
        (fun δ => x δ - ∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹ * δ * sec s)))
    (hxnot : ∀ A ∈ S, ¬ SSGRoute.IsSplitIn ℚ K A →
      SSGRoute.IsCoboundaryOn (AlgEquiv.restrictNormalHom K) (SSGRoute.decomp ℚ A) x)
    (hxinertia : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace ℚ A B) → ¬ SSGRoute.IsSplitIn ℚ Λ B →
      ∀ σ : SSGRoute.GalQ, SSGRoute.IsInertia ℚ B σ → x σ = 0)
    (hinv : ∀ c : SSGRoute.GalQ, c ^ 2 = 1 →
      SSGRoute.IsCoboundaryOn (Work.SSGRoute.restrict K) (Subgroup.zpowers c) x)
    (hcyc7 : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace ℚ A B) →
      ∃ V : Subgroup SSGRoute.GalQ, IsOpen (V : Set SSGRoute.GalQ) ∧
        (∀ δ ∈ SSGRoute.decomp ℚ B, ∀ u ∈ SSGRoute.decomp ℚ B ⊓ V, δ * u * δ⁻¹ ∈ V) ∧
        (∃ g ∈ SSGRoute.decomp ℚ B, ∀ δ ∈ SSGRoute.decomp ℚ B, ∃ m : ℤ, δ⁻¹ * g ^ m ∈ V) ∧
        SSGRoute.IsCoboundaryOn (Work.SSGRoute.restrict K) (SSGRoute.decomp ℚ B ⊓ V) x)
    (hreal : ∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ A → A ∉ T0 →
      (∃ A₀ ∈ S, SSGRoute.IsConjPlace ℚ A₀ A) →
      (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧
        (flowTwistEHom p K n i j x ψ hψquot hxmul) σ ≠ 1) →
      (∀ σ ∈ SSGRoute.decomp ℚ A, φ σ = 1) →
      ∃ η : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j,
        (∀ σ ∈ SSGRoute.decomp ℚ A, ∀ τ ∈ SSGRoute.decomp ℚ A, η (σ * τ) = η σ + η τ) ∧
        SSGRoute.IsLocConstOn (SSGRoute.decomp ℚ A) η ∧
        (∀ σ, SSGRoute.IsInertia ℚ A σ → η σ = 0) ∧
        IsCyclic (Subgroup.closure
          ((flowTwistE p K n i j η ψ) '' (SSGRoute.decomp ℚ A : Set SSGRoute.GalQ))) ∧
        (∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧
          flowTwistE p K n i j η ψ τ = flowTwistE p K n i j η ψ σ) ∧
        ∀ σ ∈ SSGRoute.decomp ℚ A, x σ = η σ)
    (hdich : ∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ A →
      (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ ψ σ ≠ 1) →
      (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧
        (flowTwistEHom p K n i j x ψ hψquot hxmul) σ ≠ 1) →
      SSGRoute.IsCoboundaryOn (Work.SSGRoute.restrict K) (SSGRoute.decomp ℚ A) x ∨
        ∃ η : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j,
          (∀ σ ∈ SSGRoute.decomp ℚ A, ∀ τ ∈ SSGRoute.decomp ℚ A, η (σ * τ) = η σ + η τ) ∧
          SSGRoute.IsLocConstOn (SSGRoute.decomp ℚ A) η ∧
          (∀ σ, SSGRoute.IsInertia ℚ A σ → η σ = 0) ∧
          IsCyclic (Subgroup.closure
            ((flowTwistE p K n i j η ψ) '' (SSGRoute.decomp ℚ A : Set SSGRoute.GalQ))) ∧
          (∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧
            flowTwistE p K n i j η ψ τ = flowTwistE p K n i j η ψ σ) ∧
          ∀ σ ∈ SSGRoute.decomp ℚ A, x σ = η σ)
    : Step4InputData p K n i j := by
  haveI : Normal ℚ Λ := hΛgal.to_normal
  have hxT0 : ∀ A ∈ T0, ∀ σ ∈ SSGRoute.decomp ℚ A, x σ = 0 := by
    intro A hA σ hσ
    have hσK : σ ∈ K.fixingSubgroup := hT0split A hA hσ
    have hcob := hxsplit A (hT0S A hA) (hT0split A hA)
    have h0 : x σ - (∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹ * σ * sec s)) = 0 :=
      eq_zero_of_isCoboundaryOn p K n i j
        (x := fun δ => x δ - ∑ s : K ≃ₐ[ℚ] K, s • y ((sec s)⁻¹ * δ * sec s))
        hcob σ hσ hσK
    rw [hyT0 A hA σ hσ, sub_zero] at h0
    exact h0
  have hcycOut : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace ℚ A B) → SSGRoute.IsSplitIn ℚ Λ B →
      ∃ U : Subgroup SSGRoute.GalQ,
        (∃ V : Subgroup SSGRoute.GalQ, IsOpen (V : Set SSGRoute.GalQ) ∧
          U = V ⊓ SSGRoute.decomp ℚ B) ∧
        (∀ δ ∈ SSGRoute.decomp ℚ B, ∀ u ∈ U, δ * u * δ⁻¹ ∈ U) ∧
        (∃ g ∈ SSGRoute.decomp ℚ B, ∀ δ ∈ SSGRoute.decomp ℚ B, ∃ m : ℤ, δ⁻¹ * g ^ m ∈ U) ∧
        SSGRoute.IsCoboundaryOn (Work.SSGRoute.restrict K) U x := by
    intro B hB hconj _
    obtain ⟨V, hVopen, hnorm, hgen, hcob⟩ := hcyc7 B hB hconj
    refine ⟨SSGRoute.decomp ℚ B ⊓ V, ?_, ?_, ?_, ?_⟩
    · exact ⟨V, hVopen, inf_comm _ _⟩
    · intro δ hδ u hu
      exact Subgroup.mem_inf.mpr
        ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hδ hu.1) (Subgroup.inv_mem _ hδ),
          hnorm δ hδ u hu⟩
    · obtain ⟨g, hg, hgm⟩ := hgen
      refine ⟨g, hg, fun δ hδ => ?_⟩
      obtain ⟨m, hm⟩ := hgm δ hδ
      exact ⟨m, Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _
        (Subgroup.inv_mem _ hδ) (Subgroup.zpow_mem _ hg m), hm⟩⟩
    · exact hcob
  have hxcoc : SSGRoute.IsCocycleOn (Work.SSGRoute.restrict K) ⊤ x := fun g _ h _ => hxmul g h
  obtain ⟨hT1cob, hram⟩ :=
    step4_transport_general p K Λ hKΛ n i j
      (flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2) ψ hΛker S hSfin hSram sec hsec y hyT hy0
      x hxcoc hxsplit hxnot hxinertia
  refine ⟨φ, ψ, hψquot, T0, x, hxmul, hφ, hLift, hopen, hT1ψ, hInvψ, hProp, hxloc, hT1cob, hinv,
    ?_, ?_, ?_, hT0gen, hxT0, hT0cyc⟩
  · -- item (4): if `x` ramifies at `A` then `φ` is trivial on `D_A`
    intro A hAfin hramA
    obtain ⟨σ, hσI, hσK, hne⟩ := hramA
    obtain ⟨hnotconj, hψ1⟩ := hram A hAfin ⟨σ, hσI, hσK, hne⟩
    intro δ hδ
    have hδ' : flowGroupSucc p (K ≃ₐ[ℚ] K) n i j (ψ δ) = φ δ :=
      (liftsFlowAt_iff_flowGroupSucc p K n i j (ψ δ) (φ δ)).mp (hLift δ)
    rw [← hδ', hψ1 δ hδ, map_one]
  · -- item (5)
    exact item5_of_bundle_guarded p K Λ n i j φ ψ hφquot hψquot hΛker S hSram T0 x hxmul
      hxinertia hreal hcycOut
  · -- item (6)
    exact item6_of_bundle_guarded p K n i j ψ hψquot x hxmul hdich

/-- **Step 4 of Theorem 15 from the coker side**: the level-`m` data is pushed down along `Φ` to
level `n` (`Work.SSGRoute.isProperStageData_pushdown`), and the coker-side clauses are handed to
`Work.SSGRoute.step4_bundle_of_sha13`, which assembles the bundle `Step4Input p K n i j`
(definitionally `Step4InputData p K n i j`). -/
theorem step4Input_of_properStages (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i) (hi : 2 ≤ i)
    (hμ : SSGRoute.HasRootsOfUnity p K i)
    (hP : ∀ m : ℕ, 1 ≤ m → SSGRoute.IsProperStage p K m i j) (n : ℕ) (hn : 1 ≤ n) :
    Step4Input p K n i j := by
  obtain ⟨m, hm, hnm, Φ, φm, ψm, hdata, Λ, hfd, hgal, hKΛ, hΛker, S, T0, sec, y, x, hψquot,
    hxmul, hSfin, hSram, hsec, hyT, hy0, hyT0, hT0S, hT0split, hT0gen, hT0cyc, hxloc, hxsplit,
    hxnot, hxinertia, hinv, hcyc7, hreal, hdich⟩ :=
    step4CokerSide_holds p K i j hj hji hi hμ hP n hn
  haveI : FiniteDimensional ℚ Λ := hfd
  haveI : IsGalois ℚ Λ := hgal
  -- the stage-3 clauses at level `n`, by pushing the level-`m` data down along `Φ`
  have hdata' := isProperStageData_pushdown p K Φ φm ψm hdata
  exact step4_bundle_of_sha13_guarded p K Λ hgal hKΛ n i j hj hji
    ((flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φm)
    ((flowGroupMap p (K ≃ₐ[ℚ] K) (tauSucc i j).1 (tauSucc i j).2 Φ).comp ψm)
    hdata'.1 hdata'.2.1 hdata'.1.1.2.2 hψquot hdata'.2.2.1.2.1 hΛker
    hdata'.2.2.2.1 hdata'.2.2.2.2.1 hdata'.2.2.2.2.2
    S hSfin hSram T0 hT0gen hT0cyc hT0S hT0split sec hsec y hyT hy0 hyT0 x hxmul hxloc hxsplit
    hxnot hxinertia hinv hcyc7 hreal hdich


/-! ## State of Step 4: what is proved here, and what the arithmetic must supply

Everything of Step 4 of Schmidt–Wingberg (arXiv:math/9809211, §5, pp. 26–31) that is *not* the
arithmetic of the shrinking procedure is proved in this repository:

* **The twist** (`Submission/Work/SSGRoute/twistLayer.lean`): `flowTwist`/`flowTwistE`/
  `flowTwistHom`/`flowTwistEHom` twist a solution `ψ` at `τ + 1` by an `E(n,τ)`-valued `1`-cocycle
  `x` for the plain `G(K/ℚ)`-action.  Well defined because the graded piece is central in
  `F(n)/F(n)^{(τ+1)}` and the inclusion is equivariant
  (`commutator_refinedTerm_le_top`, `gradeIncl_smul`), which is exactly the reason the cocycle
  condition of `SSGRoute.shafarevich_theorem13` is the right one (`flowTwist_mul`, `flowTwistE_mul`,
  `gradeInl_conj`).
* **The twist is a flow solution** (`isFlowSolution_flowTwistEHom`, `twistLayer`): `flowQuot ∘ ψ' =
  res` (`flowQuot_flowTwistE`), open kernel (`flowTwist_isOpen_ker`), and surjectivity from the `T⁰`
  generation (`surjective_flowTwistEHom_of_iSup`).
* **Condition (i) and the involutions are preserved** (`flowTwistE_scholzT1`,
  `eq_zero_of_isCoboundaryOn`, `gradeInl_eq_one_iff`): this turns "`x` is a coboundary on the
  decomposition groups of the places over `Ram(K/ℚ) ∪ {p} ∪ {∞}`" into condition (i).
* **Condition (ii) is preserved** (`scholzConditions_of_stageData`, and the case analysis inside
  `isScholzSolution_flowTwistEHom`).
* **The "totally ramified" half of (ii) is derived**, not assumed: `inertia_map_eq_flowTwistEHom`
  reduces it to the *cyclicity* of the local group of the twist at the places of new ramification
  (via `Work.SSGRoute.inertia_map_eq_of_isCyclic`, `map_le_range_gradeIncl_of_flowQuot_eq_one`,
  `pow_p_eq_of_mem_range_gradeInl`).
* **The `T⁰` of the paper is a theorem, not arithmetic**: `exists_T0_cyclic_of_surjective` (via
  `Work.SSGRoute.t0Generation_cyclic`) produces a finite set of places whose `ψ`-images generate
  `flowEKer p (K ≃ₐ[ℚ] K) n i j` and are cyclic.

**What remains is the arithmetic**, and it is isolated in the hypothesis `Step4Input p K n i j` of
`scholz_succ_of_step4Input`, i.e. in the single obligation `step4Input_of_properStages`:

1. the stage-3 data at level `n` (from `hP`, after the shrinking), with `φ` Scholz at `τ` and `ψ` a
   proper lift at `τ+1`;
2. `x` a `1`-cocycle for the `G(K/ℚ)`-action which is locally constant — the first two conjuncts of
   `SSGRoute.shafarevich_theorem13`, applied with `k = ℚ`, `Λ = N_{τ+1}` (the field of `ψ`, *not* of
   `φ`), the class `y ∈ H¹(k_S|K, E(n,τ))` being supplied by `SSGRoute.coker_obstruction` over `K`
   together with `Work.CohomologicalShrinking.exists_shrinking_H1`;
3. `x` a coboundary on `D_A` for every place over `Ram(K/ℚ) ∪ {p} ∪ {∞}` and on the subgroup
   generated by every involution: two clauses of Theorem 13, transported to arbitrary places by
   `Work.SSGRoute.step4_transport_of_sha13_psi`;
4. the places where `x` ramifies over `K` are completely decomposed in `N_τ/ℚ` (same transport);
5. cyclicity of the local group of the twist at the places of new ramification: at the primes outside
   the finite set `S` this is Theorem 13's cyclicity clause together with
   `Work.SSGRoute.twist_cyclic_of_psi_trivial`; at the primes of `S` (in particular over `p` and over
   `Ram(N_{τ+1})`) it is the *choice* of the local target `η_P` of
   `Work.SSGRoute.step4_local_target` — cyclicity is not derivable from abstract properties of `ψ`
   and `x` alone;
6. the same for the cyclic branch of the dichotomy at the places ramified for `ψ` (item 5 of the
   list above, again the choice of `η_P`);
7. the finite set `T⁰` with the generation and cyclicity properties, and `x = 0` on its
   decomposition groups (the paper's `x_p = 0` for `p ∈ Ram(N_{τ+1}) ∪ S_p ∪ S_1 ∪ T⁰`).

Items 2–4 are *proved* for arbitrary such data in `Work.SSGRoute.step4_transport_of_sha13_psi`; item
7's generation/cyclicity is proved here (`exists_T0_cyclic_of_surjective`).  What is genuinely
missing is the existence of `y` (the second shrinking: `coker_obstruction` over the base `K`, still a
`sorry`) and Theorem 13's cyclicity clause (`Work.SSGRoute.shafarevich_z_construction`, still a
`sorry`).
-/

/-! ## Addendum VI: the node is now the coker side alone

The wiring sketched in Addendum V has been carried out:

* `Work.SSGRoute.Step4CokerSide` (`Submission/Work/SSGRoute/step4CokerSideDefs.lean`) states the
  coker side of Step 4 in the shape in which it is *provable*: the level `m ≥ n`, the operator map
  `Φ : F(m) ↠ F(n)` and the level-`m` stage-3 data are part of the existential (the shrinking needs
  that presentation of the level-`n` data), and all the clauses are phrased for the push-downs
  `Φ ∘ φm`, `Φ ∘ ψm`;
* `step4CokerSide_holds` (below) is the single remaining input of this node: the second shrinking
  with `SSGRoute.coker_obstruction` over the base `↥K`, producing the datum `y`, the class `x` with
  Theorem 13's clauses (`SSGRoute.shafarevich_existence` applied with `Λ` the field of `ψ`), the
  local-target realisation `hreal` and the local dichotomy `hdich`;
* `step4Input_of_properStages` is now **proved**: it destructures the coker side, pushes the level-`m`
  data down along `Φ` with `Work.SSGRoute.isProperStageData_pushdown`, and hands everything to
  `Work.SSGRoute.step4_bundle_of_sha13` — whose conclusion `Step4InputData p K n i j` is
  definitionally `Step4Input p K n i j`.  So no assembly remains in this file: the target is proved
  from the coker side alone.

The same statement is being proved in the sibling module
`Submission.Work.SSGRoute.step4CokerSide_holds`; that module is intended to replace the local
placeholder copy of `step4CokerSide_holds` below (one `import` line) as soon as it builds — its
initial import list contained both `Submission.Work.SSGRoute.local_lifting_setup` and
`Submission.Work.SSGRoute.inertiaAtLevelDefs`, which both declare `Work.SSGRoute.IsTrivialAtLevel`
and therefore cannot be imported together (a name collision in the fleet's own library that
deserves a rename).
-/

/-! ## Addendum V: the lane has landed; the node is one input away

As of the session following the one above, the whole Step-4 lane is upstream of this file (the
import flips of `twist_cyclic_of_psi_trivial`, `step4_local_target`, `step4_transport_of_sha13` to
`Submission.Work.SSGRoute.twistLayer` have been done, exactly as checked in Addendum IV), and the
following modules are `sorry`-free:

* `Submission.Work.SSGRoute.step4_bundle_assembly` — the assembly of the node's input:
  * `exists_step4_data`: from the stage-3 data of `hP n hn`, the field `Λ` of `ψ`
    (`exists_field_of_flowKernel`), the finite set `S` of places over `Ram(Λ) ∪ {p}` (one per
    prime, `ramifiedPlaces_finite`), the finite set `T⁰` (Chebotarev, `t0Generation_cyclic`) and a
    section `sec` of `AlgEquiv.restrictNormalHom K` (`exists_section_local`);
  * `step4_local_target_over_p`: the local target `0` at the places over `p`;
  * `step4Input_of_bundle` and `step4_bundle_of_sha13`: the assembly of the bundle
    `Step4InputData p K n i j` from the stage-3 data, the datum `y` (with its local clauses), the
    class `x` with Theorem 13's clauses, the local-target realisation `hreal` and the local
    dichotomy `hdich`;
* `step4_items_assembly`, `step4_local_cyclic_bridge`, `step4_shrunk_input`, `step4_local_target`,
  `step4_transport_of_sha13[_psi]`, `twist_cyclic_of_psi_trivial`.

Moreover `Step4InputData p K n i j` is **definitionally** `Step4Input p K n i j` in this file
(checked: `Step4InputData p K n i j ↔ Step4Input p K n i j` is `Iff.rfl`), and the sibling node
`Work.SSGRoute.step4_shrunk_input` is definitionally the same bundle.

**What is left** is therefore exactly the "coker side" of the paper (SW pp. 30–31): the datum `y`
obtained from `SSGRoute.coker_obstruction` over the base `↥K` (the local targets of
`step4_local_target` at the places of `S`, `0` on `T⁰` and over `p`/`Ram(K)`, the local data
realised by a global cocycle `y` over `K` — the Grunwald statement of `DESIGN.md` §(d), for which
`Work.SSGRoute.grunwald_*`, `Work.SSGRoute.coker_assembly` and `Submission/Work/SSGRoute/H1Pair/`
now provide the machinery), together with the two clauses `hreal`/`hdich` and the choice of `T⁰`;
the class `x` then comes from `SSGRoute.shafarevich_existence` with `Λ` the field of `ψ`.

**One caveat, worth settling before the input is stated as a lemma** (DESIGN2's defect (b) again):
the shrinking (Prop 7(ii), `Work.CohomologicalShrinking.exists_shrinking_H1`) is applied to an
obstruction class in
`H₁(Gal(N_m/K), E_m ⊗ μ_p^∨) = F(m)/F(m)² ⊗ (E_m ⊗ μ_p^∨)` *at a level `m ≥ n` chosen by the
shrinking*, and the diagrams that identify the level-`n` obstruction with it involve a surjection
`Φ : F(m) ↠ F(n)` presenting the level-`n` data.  If the level-`n` data `(φ, ψ)` is a *parameter*
of the input (as in `step4_bundle_of_sha13`), no such presentation is available; if instead the
input is allowed to *choose* `(m, Φ)` and the level-`m` data (as the paper does, and as
`Work.SSGRoute.isProperStageData_pushdown` permits), the presentation is free.  The `hP`-derived
level-`n` data of this node *does* have such a presentation (it is produced by
`properStage_of_solvableStage` through `properStageAssemblyData`, which pushes down from a level
`m ≥ n`), so the arithmetic input should be stated in the `∃ m, Φ`-form; the bundle it produces is
then pushed down to level `n` with `Work.SSGRoute.isProperStageData_pushdown` before being handed to
`step4_bundle_of_sha13`.
-/

/-! ## Addendum IV (session 5): the node is at its floor

**The module split.**  The algebraic core of the twist (the graded piece, the stage projection, the
twist `flowTwistEHom` and its calculus, the coboundary/conjugacy lemmas, and the conjugacy transport
of local coboundary conditions) has been moved into the upstream module
`Submission.Work.SSGRoute.twistLayer`, which this file imports.  Names are unchanged.

**Why.**  The arithmetic siblings of this node (`Work.SSGRoute.step4_shrunk_input`,
`step4_local_target`, `twist_cyclic_of_psi_trivial`, `step4_transport_of_sha13[_psi]`) need
`Work.SSGRoute.flowTwistEHom` / `Work.SSGRoute.restrict` / `Work.SSGRoute.flowTwistE` /
`Work.SSGRoute.isCoboundaryOn_map_conj` in order to *state* what Step 4 consumes, and at present they
obtain them by importing *this* node file — which is the wrong direction, since this node is the one
that consumes the arithmetic, and a Lean module cycle is impossible.  It has been checked
(2026-09-25) that all five of those files elaborate and prove their statements with
`import Submission.Work.SSGRoute.scholz_succ_of_properStage` replaced by
`import Submission.Work.SSGRoute.twistLayer`; each is a one-line change in those five files.
After the flip, this node may (and should) import `Work.SSGRoute.step4_shrunk_input`, whose
conclusion is *definitionally* `Step4Input p K n i j` (checked with `Iff.rfl`), so that the body of
`step4Input_of_properStages` becomes that single call.

**No further reduction is possible.**  The prover of `Work.SSGRoute.step4_shrunk_input` has proved
that node *from the target of this one* (its file contains a complete, `sorry`-free proof of the
bundle with `φ := flowGroupProj ∘ ψ`, `x := 0`, taking for `ψ` the level-`(i,j)+1` Scholz solution
whose existence is the conclusion of this node).  Hence, given `hP`,

  `Step4Input p K n i j`  ⟺  `∃ ψ, IsScholzSolution p K n (τ+1) ψ`

i.e. the obligation `step4Input_of_properStages` has exactly the content of the target, and the
assembly `scholz_succ_of_step4Input` is the whole algebraic difference between them.  There is no
weaker or differently-packaged input.

**The arithmetic, and where it sticks.**  The input `Step4Input` is the paper's Step 4
(SW pp. 30–31); the ingredients that are already available are:

* the field of `ψ`: `Work.SSGRoute.flowKernel_fixedField` (proved) turns the stage-3 solution `ψ`
  into `Λ = ℚ̄^{ker ψ}` with `IsSplitIn ℚ Λ A ↔ ψ(D_A) = 1` and
  `IsRamifiedIn ℚ Λ A ↔ ∃ σ ∈ I_A, ψ σ ≠ 1`;
* the finite set `S` of Theorem 13: `Work.SSGRoute.ramifiedPlaces_finite` (proved) supplies a
  pairwise non-conjugate set of places containing every place over `Ram(Λ/ℚ) ∪ {p}`;
* the section `sec` of `AlgEquiv.restrictNormalHom K`: `exists_section_restrict` (proved here);
* `ζ ∈ K` with `IsPrimitiveRoot ζ p`: raise the `ζ` of `HallRootsOfUnity` to the power `p ^ i`
  (`Work.SSGRoute.exists_primitiveRoot_in_K` in `properStageAssemblyData.lean` is exactly this);
* `E(n,τ)` is a genuine `(K ≃ₐ[ℚ] K)`-module with `SMulCommClass`, so it can be used as the
  coefficient module of Theorem 13 directly;
* the second shrinking is `Work.CohomologicalShrinking.exists_shrinking_H1` (Prop 7(ii), proved);
* the transport of Theorem 13's local clauses to arbitrary places is
  `Work.SSGRoute.step4_transport_of_sha13_psi` (proved), and the cyclicity at the places of new
  ramification is `Work.SSGRoute.twist_cyclic_of_psi_trivial` (proved) together with
  `Work.SSGRoute.step4_local_target` (the `η_P` of the paper).

**The genuine obstacle** is the construction of the class `y ∈ H¹(k_S|K, E(n,τ))` with the local
targets `η_P` (equivalently: the instantiation of `SSGRoute.coker_obstruction` over the base `↥K`
with the trivial `G_K`-module), which needs

* `IsAlgClosure ↥K ℚ̄` — **not** synthesizable as it stands (`infer_instance` fails, checked
  2026-09-25); the guidance is to transport along `AlgebraicClosure ↥K ≃ₐ[↥K] ℚ̄`;
* `Algebra ↥K ℚ̄` and hence `IntermediateField ↥K ℚ̄` — also not synthesizable (the `ℚ`-algebra
  diamond on `↥K` is the reason `DESIGN.md` warns against writing conditions that unfold it), so
  `N_τ` has to be promoted from `IntermediateField ℚ ℚ̄` to `IntermediateField ↥K ℚ̄` by hand;
* the obstruction bookkeeping: `coker_obstruction` over `K` gives a class in
  `H₁(Gal(N_m/K), E_m ⊗ μ_p^∨) = F(m)/F(m)² ⊗ (E_m ⊗ μ_p^∨)` (universal coefficients), which
  `exists_shrinking_H1` kills after choosing `m ≥ n` and `Φ : F(m) ↠ F(n)`; the naturality clause of
  `coker_obstruction` evaluated at `N₂ = N_n` then produces `y`.

Because `step4_shrunk_input` imports this file, this arithmetic must land *here* (or in a module
upstream of both) — landing it in the sibling is not possible without a module cycle.

**The crux, stated.**  The Theorem-13 side is *available*: `SSGRoute.shafarevich_existence` (the
full Theorem 13, in its *repaired* open-`V` form) is proved modulo the single `sorry` of
`Work.SSGRoute.shafarevich_z_construction`, and it produces, from a class `y` on `G_ℚ` which is
additive on `G_K` and satisfies the five local conditions `hyS`, `hyT`, `hy0`, `hyinf` (and is
locally constant), a class `x` with the cocycle, T¹, involution, inertia-vanishing and *cyclicity*
clauses — i.e. exactly the `x`-clauses of `Step4Input`.  So the whole remaining content of this node
is the construction of `y` (SW pp. 30–31, the second shrinking).  In the paper's notation, with
`η_P` the local target at a place `P` of `K` (a cocycle on `D_P ⊓ G_K` which is unramified,
supported on the primes that are split in `K/ℚ`, prime to `p` and in
`Ram(N_{τ+1}/K) ∖ Ram(N_τ/K)`, and which makes the twist of `ψ` by `η_P` cyclic — the object
produced by `Work.SSGRoute.step4_local_target`), the required `y : G_ℚ → E(n,τ)` is an
*everywhere unramified* class (the conditions `hyS` and `hyT` together say that `y` vanishes on the
inertia of every finite place) whose local class at each `P` agrees with `η_P`:

  `IsCoboundaryOn (restrict K) (decomp ℚ A ⊓ K.fixingSubgroup) (fun σ => y σ - η_A σ)`

(for every `A` in the finite set `S` of Theorem 13), and which vanishes on the decomposition groups
of the places of `S` that are not split in `K/ℚ` or lie over `p` (`hy0`) and on every involution in
`G_K` (`hyinf`).

**Provenance of the fifteen clauses of `Step4Input`** (all the lemmas named as *proved* are
axiom-clean in this workspace; the `sorry`-nodes are marked):

| # | clause | where it comes from |
|---|---|---|
| 1 | `IsScholzSolution p K n i j φ` | `SSGRoute.IsProperStage p K n i j` (hypothesis `hP n hn`) |
| 2 | `LiftsFlow ψ φ` | idem |
| 3 | `IsOpen ψ.ker` | idem |
| 4 | `ψ = 1` on `D_A ⊓ G_K`, `A ∈ T¹` | idem |
| 5 | `ψ = 1` on involutions of `G_K` | idem (vacuous: `no_two_torsion_fixingSubgroup`, in flight) |
| 6 | the dichotomy at the places ramified for `ψ` | idem |
| 7 | `IsLocConstOn ⊤ x` | Theorem 13 (`shafarevich_existence`, proved modulo `shafarevich_z_construction`) |
| 8 | `x` a coboundary on `D_A` for `A ∈ T¹` | Theorem 13 + `step4_transport_of_sha13_psi` |
| 9 | `x` a coboundary on `⟨c⟩` for involutions | Theorem 13 (vacuous) |
| 10 | `x` ramified ⟹ `φ = 1` on `D_A` | Theorem 13 + `step4_transport_of_sha13_psi` |
| 11 | cyclicity of the twist at new ramification | `twist_cyclic_of_psi_trivial` (proved) + `step4_local_target` (proved) + `step4_local_cyclic_bridge` |
| 12 | inertia-generation at the `ψ`-ramified places | `isCyclic_map_flowTwistEHom_of_isCoboundaryOn` / `step4_items_assembly` |
| 13 | `⨆_{A ∈ T⁰} (D_A).map ψ = flowEKer` | Chebotarev (`exists_T0_cyclic_of_surjective`, proved here) |
| 14 | `x = 0` on the `T⁰`-groups | choice of `T⁰` inside the shrinking (paper's `x_p = 0` for `p ∈ … ∪ T⁰`) |
| 15 | `IsCyclic ((D_A).map ψ)` for `A ∈ T⁰` | Chebotarev (`exists_T0_cyclic_of_surjective`, proved here) |

So clauses 1–6 are *free* (they are `hP`), clauses 13 and 15 are *free* (Chebotarev), clauses 7–12
come from Theorem 13 and the (proved) step-4 item assembly, and the only genuinely missing inputs
are the class `x` itself (Theorem 13 applied to a `y`) and the conjunction of clause 14 with the
choice of `T⁰` — i.e. exactly the `y`-construction of the previous paragraph.

**How the arguments of `SSGRoute.coker_obstruction` are meant to be filled** (session-5 reading of
its statement, `Submission/Work/SSGRoute/coker_obstruction.lean`).  That theorem is *not* a
construction of the local data: it takes the local data `α` (at the places of `S`), `β` (at the real
places) **and a global cocycle `ε₀` gluing them** (`hglue`: the local defects `ε₀ - α_A` and
`ε₀ - β_c` are coboundaries, and `ε₀` vanishes on the inertia of the places outside
`S ∪ cs(N)`) and returns a class `x` in `H₁(Gal(N/k), E ⊗ μ_p^∨)` with the universal property that
*for every intermediate level `N₂ ⊇ K` on which `x` dies (`(groupHomology.map q F 1).hom x = 0`)* the
pushed-down data `f ∘ α` is realised by a global cocycle `ε` on `G_ℚ` with the same local defects and
inertia vanishing.  (The case `x = 0` is `coker_obstruction_of_level_gluing`, already proved with the
explicit witness `ε := f ∘ ε₀`.)

Consequently the Step-4 workflow is:

1. take the level-`m` data `(φ_m, ψ_m)`; the needed local data `α_m` can be taken to be the local
   components of a *genuine* global cocycle `ε₀` built from the local lifting data of `ψ_m`, so that
   `hglue` holds with that `ε₀` (the defects are then `0`), exactly as in Step 3 of the paper;
2. choose `m ≥ n` and `Φ : F(m) ↠ F(n)` so that the obstruction class `x` is killed (Prop 7(ii),
   `Work.CohomologicalShrinking.exists_shrinking_H1`), using the universal-coefficients
   identifications `Work.CohomologicalShrinking.universalCoefficient.h1AddEquivPQuotientSub` and
   `flow.flowNormalSquareEquiv` for
   `H₁(Gal(N_m/K), E_m ⊗ μ_p^∨) = F(m)/F(m)² ⊗ (E_m ⊗ μ_p^∨)`;
3. read the universal property at `N₂ = N_n` with `f = (E_m → E_n)`, `F = flowRepMap` to get the
   class `y := ε` on `G_ℚ`, additive on `G_K`, realising the *pushed-down* level-`n` local targets —
   which is exactly the `y` that `SSGRoute.shafarevich_existence` consumes (with
   `k = ℚ`, `K := ↥K` seen over `ℚ`, i.e. `y` is additive on `G_K`).

**A concrete reformulation of `y`.**  Since the `η_P` of
`Work.SSGRoute.step4_local_target` are *unramified* local classes, and since `hyS ∧ hyT` says that
`y` vanishes on the inertia of *every* finite place, `y` is an **everywhere unramified**
`E(n,τ)`-valued class over `K`: because the `G_K`-action on `E(n,τ)` is trivial, such a class is a
homomorphism `G_K → E(n,τ)` vanishing on all inertia, i.e. (class field theory) a homomorphism
`Cl(K) → E(n,τ)` on the class group, and prescribing it at the places of `S` means prescribing a
linear functional on the Frobenius classes `[P] ∈ Cl(K)`.  The obstruction to prescribing arbitrary
values is therefore the group of relations among the classes `[P]`, `P ∈ S` — and it is exactly this
relation group (the `coker(k_S,T,E)` of the paper, `F(m)/F(m)² ⊗ (E_m ⊗ μ_p^∨)` at level `m`) that
Prop 7(ii) kills by the shrinking.  This is the "Poitou–Tate degree 1" workshop of `DESIGN2.md`; for
the *trivial* coefficient module it is the classical Grunwald/Chebotarev statement over `K` that
`DESIGN.md` §(d) reduces to Kummer theory, the idèle sequence, global reciprocity
(`NK.CFTLib.artinReciprocityIdeal_proved`), local reciprocity (`NK.NUV2.kernelCondition_all`) and the
prime-index existence theorem (`Work.SSGRoute.classField_exists_ramified`, proved).

-/

/-! ## Addendum VII (2026-09-26, this session): the import clash is fixed, and the exact frontier

**1. The `levelSub`/`levelPrime` clash is fixed (outside this file).**  Any module importing both
cliques of the Step-4 lane failed at *import* time:

```
import Submission.Work.SSGRoute.local_tame_defs
  → environment already contains 'Work.SSGRoute.levelSub' from levelInertia_defs
```

Two distinct declarations shared the name `Work.SSGRoute.levelSub`, and likewise
`Work.SSGRoute.levelPrime` (`levelInertia_defs`/`inertiaAtLevelDefs` on the `NK.FrobeniusBridge`
side vs `local_tame_defs`/`levelIndex` on the local-tame side).  The *specialised* (ℚ̄-)versions
are renamed to `levelSubQBar` and `levelPrimeQBar` in `local_tame_defs.lean`, `local_tame_lifting.lean`
and `levelIndex.lean` (the ℚ̄-naming convention already used by `IsTrivialAtLevelQBar`); lemma
names are untouched.  Verified: a module importing `coker_obstruction`, `shafarevich_existence`,
`step4_bundle_assembly`, `step4_items_assembly`, `step4_transport_of_sha13`,
`twist_cyclic_of_psi_trivial` **and** `step4_local_target` now elaborates, and
`Work.SSGRoute.step4_local_target` is axiom-clean.

*Empirical fact about Lean used here (verified with a two-module experiment):* two modules may
declare the same name with the *same* statement (Lean accepts it, as in `refinedTerm_tauSucc_le`,
`Work.CohomologicalShrinking.tensorAssoc_smul`); an error is raised only when the statements
*differ*.  So among the "36 duplicate declarations" of `CLASH_REPORT.md` only the pairs with
different statements need renaming; exactly two of them were in this node's closure.

**2. The exact frontier of this node.**  `lake build` of this module reports the `sorry`ed
declarations of its *import* closure; the ones that actually enter this node's proof terms are

| file | hole | role |
|---|---|---|
| this file | `step4CokerSide_holds` | **the node's only hole**: the Step-4 arithmetic |
| `ZConstruction/ZDataGeneral.lean` | `z_data_general_of_ramified` | behind `shafarevich_z_construction` → `SSGRoute.shafarevich_existence` (Theorem 13's `z`) |
| `NK/CFTLib/ARL/kernelLe_of_auxField_B.lean`, `NeukirchUchida/Core.lean`, `Submission/Shafarevich.lean` | one each | imported through `Interfaces`; *unused* by this node's proof term |

`properStageAssemblyData` (2 holes) is imported by `step4_bundle_assembly`, but the declarations
used here (`exists_step4_data`, `step4_bundle_of_sha13`, ...) are proved and axiom-clean; only
`step4CokerSide_holds` and (transitively) `z_data_general_of_ramified` matter.  Adding
`coker_obstruction` to this file's imports would add two more holes
(`pt_selmer_relaxed`, `canonical_localPairing_with_reciprocity`), which is why the *Grünwald* route
below is preferable to the `coker_obstruction` route.

**2b. KNOWN DEFECT of the `hreal` clause of `Step4CokerSide`** (reported by the prover of that
sibling; see `H9_STATUS.md` §3 for the five-step argument): its guard only asks that `φ` be trivial
on `D_A`, so it also applies at the conjugates `A'` of a `T⁰` place, where `M(D_{A'}) ≠ 1` but
`M(I_{A'}) = 1` (the `T⁰` places of `exists_T0_cyclic_of_surjective` are split in `N_τ` and
unramified in `N_{τ+1}`), while `hxsplit ∧ hyT0 ∧ hxmul` force `x = 0` on `D_{A'}`; `hreal` then
demands `M(D_{A'}) = M(I_{A'})` — false.  Before `step4CokerSide_holds` can be proved, `hreal`'s
hypothesis must be strengthened by the `hdich` guard
(`∃ σ ∈ decomp ℚ A, IsInertia ℚ A σ ∧ (flowTwistE p K n i j x ψ) σ ≠ 1`), and the corrected side
must be fed to `isScholzSolution_flowTwistEHom` below rather than to `step4_bundle_of_sha13`.

**3. Recommended route for `step4CokerSide_holds` (Grünwald, not Poitou–Tate).**  `hSdisj` (the
places of `S` are pairwise non-conjugate, one per prime) has a consequence that makes the whole
coker side elementary: put `y`'s local data equal to the local target `η_A` of
`Work.SSGRoute.step4_local_target` at a single place `A` of each new-ramified prime, and `0` at
every other place (hence at every other place of `S`, in particular over `Ram(K/ℚ) ∪ {p}` and at
`T⁰`).  Normalising the section `sec` so that `sec 1 = 1` and using that `D_A ≤ K.fixingSubgroup`
at these places, the corestriction is *pointwise the identity on `D_A`*:

  `∑_s s • y ((sec s)⁻¹ δ (sec s)) = y δ = η_A δ`  for `δ ∈ D_A`,

because `(sec s)⁻¹ δ (sec s) ∈ D_{sec s⁻¹ • A}`, and `sec s⁻¹ • A = A` forces `s = 1` by
`hSdisj` (the `s ≠ 1` places carry the datum `0`).  This is exactly the paper's construction of
`x = cor y` and it makes `hreal`, `hxsplit` and the `T⁰` clauses immediate; `x := cor y` also has
`hxloc`, `hxmul`, `hinv` and `hxinertia` *by construction* (the `corCocycle_*` lemmas of
`shafarevich_existence.lean`, which are proved and axiom-clean), and `hcyc7` from
`isCoboundaryOn_of_eq_zero`.

The local data are *scalar* (`E(n,τ)` is a finite `𝔽_p`-vector space with trivial `G_K`-action
because `μ_p ⊆ K` and `i ≥ 1`, since `res` is trivial on `G_K`), so the existence of `y` with the
prescribed local data on the places of `S` is the **E-valued Grünwald surjectivity**
`Work.SSGRoute.grunwald_surjective_E` (module `Submission.Work.SSGRoute.grunwald_surjective_E`),
**proved and axiom-clean in this session**: it is the E-valued form of the proved, axiom-clean
`grunwald_surjective_odd` (`p ≠ 2`) / `grunwald_surjective_two` (`p = 2`), obtained by running them
on an `𝔽_p`-basis of `E p (K ≃ₐ[ℚ] K) n i j` — no Poitou–Tate.  (This is the same substitution that
`properStageAssemblyDataV2.lean` proposes for Step 3.)  The only remaining delicate point is the
`step4_transport_of_sha13_psi`-style bookkeeping of the cyclic clause `hcyc7` off `S`, which in this
route is *vacuous* (`x = cor y` is unramified off `S`).

-/

/-! ## Addendum VIII (session 6): the `hreal` defect is repaired; the road to the coker side

**1. The repair.**  The `hreal` clause of `Work.SSGRoute.Step4CokerSide` now carries the guard "the
twist is ramified at `A`" — the condition `Work.SSGRoute.item5_of_bundle` already carries as `hram`
and the only context in which `hreal` is consumed (`H9_STATUS.md` §3 and 6.1 give the reported
counterexample to the unguarded clause).  The guarded copies of the two pipeline lemmas
(`item5_of_bundle_guarded`, `step4_bundle_of_sha13_guarded`) live in this file, so the other lanes'
files are untouched; the guarded clause is *weaker* and *sufficient*, and the node's single `sorry`
is now a satisfiable statement (it asks for the local target only where `step4_local_target`
applies).

**2. New proved pieces** (this file, all axiom-clean): `exists_section_restrict_one`,
`cocycle_conj_eq_zero`, `smul_inv_sec_ne_self`, `corestriction_eq_self_on_decomp` (the statement that
`cor y|D_A = y|D_A` at split places, which `hxsplit`/`hreal`/`hxsplit`-style clauses need) and
`corestriction_eq_zero_on_decomp_of_eq_zero` (the `hyT0` clause).  `Work.SSGRoute.step4_conjugate_vanish`
and `Work.SSGRoute.step4_involution_vanish` (the `hyT`/`hy0`/`hyinf` clauses at all conjugates) were
delegated in parallel and are **proved and axiom-clean**, as are
`Work.SSGRoute.flowTwistE_conj_of_mem_decomp` (the twist at `θ • A` is the `ψ θ`-conjugate of the
twist at `A` when `D_A ≤ G_K`, the paper's reason why the local target at one prolongation per prime
suffices) and `Work.SSGRoute.hreal_conj_transfer` (the transfer of the whole `hreal` clause to the
conjugates); `Work.SSGRoute.exists_T0_split_generating` (a `T⁰` of *finite, completely decomposed in
the stage-`τ` field* primes whose `ψ`-images generate `flowEKer` and are cyclic — the paper's choice
of `T⁰`) is proved too.  All five are `#print axioms`-clean.  `H9_STATUS.md` §7–8 record how these close the local clauses.

**3. The road.**  With these, the coker side reduces to (i) the data — `hP m hm` + pushdown,
`exists_field_of_flowKernel`, `ramifiedPlaces_finite`, Chebotarev `T⁰`, `sec` — which are all proved
already, and (ii) the instantiation of `SSGRoute.coker_obstruction` over the base `↥K` with the local
data "`η_A` at the split places of new ramification (`step4_local_target`), `0` over `p` and at the
non-split places", its **naturality clause** at `N₂ = N_n` delivering the global `ε`, and the second
shrinking (`Work.CohomologicalShrinking.exists_shrinking_H1`, Prop 7(ii)) killing the obstruction —
this is what `m` and `Φ` are for.  Then `y := ε` on `G_K = K.fixingSubgroup`, Theorem 13
(`SSGRoute.shafarevich_existence`, whose conclusion is *literally* the `x`-clauses of the coker side)
gives `x`, and clauses 5/6 (`hreal`/`hdich`) come from `step4_local_target` plus the pointwise
agreement `x = η_A` on `D_A` furnished by `hxsplit` and `corestriction_eq_self_on_decomp`.  The
Grünwald route (`grunwald_surjective_E`) is *not* enough on its own: it does not give the support
clauses (`hxinertia`, `hyS`) that Theorem 13 needs; those are built into `coker_obstruction`.

**4. A possible simplification.**  `coker_obstruction` may also be instantiated at base `ℚ`
(`K := K`, `N := N_m`, `E := E p (K ≃ₐ[ℚ] K) n i j`, `T := ZMod p` with the trivial action, which is
the cyclotomic dual since `μ_p ⊆ K` as `i ≥ 1`); then its output is a cocycle on `G_ℚ` with all the
place clauses already over `ℚ`, and no `fixingSubgroupEquiv` transport is needed.  (The transport is
trivial anyway: `IntermediateField.fixingSubgroupEquiv` is the identity on the underlying map, so
`decomp`- and `IsInertia`-statements transfer by `MulAction.mem_stabilizer_iff` and `rfl`.) -/

/-! ### The target: Step 4 for `2 ≤ i`, and the direct first step for `(i,j) = (1,1)`

`_NOTE_STEP4_DESIGN.md` §1.5 (09-30): Step 4 of the tower is available only for `2 ≤ i`
(`step4CokerSide_proved` and the two in-file wrappers above now carry `hi : 2 ≤ i`).  The first step
`(1,1) → (2,1)` is *not* a case of Step 4 (at `(i,j) = (1,1)` the obstruction group
`Hom(Gal(Λ/K), E')` does not vanish on the `Tnew` places); it is proved directly as
`Work.SSGRoute.scholz_two_one`.  The statement below is unchanged and splits on `i < 2` vs `2 ≤ i`.
-/
/-- **Step 4 of Theorem 15**, Schmidt–Wingberg arXiv:math/9809211 §5, pp. 30–31: from a proper
solution at stage `τ = (i,j)` at *every* level, produce a Scholz solution at stage `τ+1` and level
`n`.  The arithmetic of the shrinking is `step4Input_of_properStages`. -/
theorem scholz_succ_of_properStage (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)
    (hμ : SSGRoute.HasRootsOfUnity p K i)
    (hP : ∀ m : ℕ, 1 ≤ m → SSGRoute.IsProperStage p K m i j)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ ψ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n
        (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2,
      SSGRoute.IsScholzSolution p K n (Work.CohomologicalShrinking.tauSucc i j).1
        (Work.CohomologicalShrinking.tauSucc i j).2 ψ := by
  rcases Nat.lt_or_ge i 2 with h1 | hi
  · -- `(i,j) = (1,1)`: the first step of the tower is done directly, by `scholz_two_one`
    have hi1 : i = 1 := by omega
    have hj1 : j = 1 := by omega
    have hμ1 : SSGRoute.HasRootsOfUnity p K 1 := hi1 ▸ hμ
    have hτ : Work.CohomologicalShrinking.tauSucc i j = (2, 1) := by
      rw [hi1, hj1]; decide
    rw [hτ]
    exact scholz_two_one p K hμ1 n hn
  · -- `2 ≤ i`: Step 4, with the extra hypothesis `hi` threaded to `step4CokerSide_holds`
    exact scholz_succ_of_step4Input p K i j hj hji hμ hP n hn
      (step4Input_of_properStages p K i j hj hji hi hμ hP n hn)

end Work.SSGRoute

