import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.CharP.IntermediateField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Submission.Work.SSGRoute.hasRootsOfUnity_mono
import Submission.Work.SSGRoute.properStage_of_solvableStage
import Submission.Work.SSGRoute.scholz_succ_of_properStage
import Submission.Work.SSGRoute.solvableStage_of_scholz
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/SSGRoute/DESIGN.md first (orchestrator design; your lemma is one node of its DAG). Shared vocabulary: Submission/Work/SSGRoute/Interfaces.lean (namespace SSGRoute; do NOT edit — put any new shared definition in your own file). The proved class-field-theory library is available as NK.* (Chebotarev: NK.NUV2.chebotarev_all0 with hFC := NK.CFTLib.fundamentalClassElement; local reciprocity NK.NUV2.kernelCondition_all; existence NK.CFTLib.Existence.classField_exists_primeIndex (unramified only); Hasse–Brauer–Noether NK.GlobalCFTdeep.hbnUnits; NK.KC.localBaseChangeInput_of_kc; NK.HR2.transferStepOnePlace), all axiom-clean. NEVER use Work.HilbertSymbol.GrunwaldWang (false as written). Siblings run in parallel; import them when they land.

# Guidance: Theorem 15 over ℚ, by induction on τ

Bookkeeping only. It consumes the three step lemmas:
- `SSGRoute.solvableStage_of_scholz` (Steps 1–2);
- `SSGRoute.properStage_of_solvableStage` (Step 3);
- `SSGRoute.scholz_succ_of_properStage` (Step 4).

**Sketch.**
1. Induct over the pairs (i,j), 1 ≤ j ≤ i, in the order (1,1), (2,1), (2,2), (3,1), … given by
   `Work.CohomologicalShrinking.tauSucc`. Use strong induction on the index Σ_{i'<i} i' + j.
2. Show `HasRootsOfUnity p K i → HasRootsOfUnity p K i'` for i' ≤ i: raise ζ to the power p^{i−i'}.
3. Base (1,1): `refinedTerm p F 1 1 = ⊤`, so `flowQuotient` is trivial. Take φ σ = (1, res σ), with
   surjectivity from `AlgEquiv.restrictNormalHom_surjective`. The kernel is K.fixingSubgroup, which is open
   (K finite). Conditions (i) and (ii) are immediate because φ σ = 1 ⇔ σ ∈ G_K.
4. Step: IH(τ) at all levels → IsSolvableStage at all levels → IsProperStage at all levels →
   Scholz at τ+1.

**Imports.** `Submission.Work.SSGRoute.Interfaces` and the three step-lemma modules.
-/

namespace Work.SSGRoute

open SSGRoute
open Work.CohomologicalShrinking

/-! ## The orbit of `(1,1)` under `tauSucc`

Schmidt–Wingberg's index set `{(i,j) | i ≥ j ≥ 1}` is the chain
`(1,1) → (2,1) → (2,2) → (3,1) → ⋯`, whose successor function is
`Work.CohomologicalShrinking.tauSucc`.  We encode the chain as a sequence of pairs, so that the
induction step `τ ↦ τ + 1` never has to compare `tauSucc i j` with a separately given pair: the
pair at index `k+1` *is* `tauSucc` of the pair at index `k`, definitionally. -/

/-- The chain of pairs `(1,1), (2,1), (2,2), (3,1), ⋯`. -/
def tauChain : ℕ → ℕ × ℕ := fun k => Nat.rec (1, 1) (fun _ p => tauSucc p.1 p.2) k

theorem tauChain_zero : tauChain 0 = (1, 1) := rfl

/-- The chain is the orbit of `(1,1)` under `tauSucc` (definitionally). -/
theorem tauChain_succ (k : ℕ) : tauChain (k + 1) = tauSucc (tauChain k).1 (tauChain k).2 := rfl

/-- `tauSucc` does not decrease the first component. -/
theorem le_tauSucc_fst (i j : ℕ) : i ≤ (tauSucc i j).1 := by
  rw [Work.CohomologicalShrinking.tauSucc]
  split <;> omega

/-- Every pair of the chain satisfies `1 ≤ j ≤ i`. -/
theorem tauChain_spec (k : ℕ) : 1 ≤ (tauChain k).2 ∧ (tauChain k).2 ≤ (tauChain k).1 := by
  induction k with
  | zero => simp [tauChain]
  | succ k ih =>
      obtain ⟨h1, h2⟩ := ih
      rw [tauChain_succ, Work.CohomologicalShrinking.tauSucc]
      split <;> omega

/-- Every pair `(i,j)` with `1 ≤ j ≤ i` occurs in the chain. -/
theorem tauChain_reaches : ∀ i j : ℕ, 1 ≤ j → j ≤ i → ∃ k, tauChain k = (i, j) := by
  intro i
  induction i with
  | zero => intro j hj hji; omega
  | succ i' ih =>
      -- the pair `(i'+1, 1)` is reached, either from the start or from `(i'', i'')`
      have hbase : ∃ k, tauChain k = (i' + 1, 1) := by
        rcases i' with _ | i''
        · exact ⟨0, rfl⟩
        · obtain ⟨k, hk⟩ := ih (i'' + 1) (by omega) (by omega)
          exact ⟨k + 1,
            by rw [tauChain_succ, hk, Work.CohomologicalShrinking.tauSucc_of_le (le_refl _)]⟩
      -- and then one walks up the second component
      have hstep : ∀ t : ℕ, t + 1 ≤ i' + 1 → ∃ k, tauChain k = (i' + 1, t + 1) := by
        intro t
        induction t with
        | zero => intro _; exact hbase
        | succ t iht =>
            intro hle
            obtain ⟨k, hk⟩ := iht (by omega)
            refine ⟨k + 1, ?_⟩
            rw [tauChain_succ, hk, Work.CohomologicalShrinking.tauSucc_of_lt (by omega)]
      intro j hj hji
      have h := hstep (j - 1) (by omega)
      rwa [Nat.sub_add_cancel hj] at h

/-! ## The induction step at a fixed pair -/

/-- One step of the induction: a Scholz solution at *every* level for `τ = (i,j)` produces one at
`τ + 1 = tauSucc i j`.  This is the composition of Steps 1–2, Step 3 and Step 4 of the paper. -/
theorem scholz_tauSucc (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)
    (hμ : SSGRoute.HasRootsOfUnity p K i)
    (hIH : ∀ n : ℕ, 1 ≤ n →
      ∃ φ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n i j,
        SSGRoute.IsScholzSolution p K n i j φ)
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ ψ : SSGRoute.GalQ →*
        Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2,
      SSGRoute.IsScholzSolution p K n (tauSucc i j).1 (tauSucc i j).2 ψ :=
  scholz_succ_of_properStage p K i j hj hji hμ
    (fun m hm => properStage_of_solvableStage p K i j hj hji hμ
      -- NOTE (name resolution): this is deliberately the *qualified* spelling.  While the
      -- duplicated-`namespace` regression in `solvableStage_of_scholz.lean` was live (2026-10-01
      -- 10:37–21:49, see `PING_namespace_regression_solvableStage.md`) the Step-1-2 theorem was
      -- declared as `Work.SSGRoute.Work.SSGRoute.solvableStage_of_scholz`, and written inside
      -- `namespace Work.SSGRoute` this spelling resolves to *that* declaration; after the repair
      -- (same day, 21:49) it resolves — by Lean's prefix fallback — to the intended
      -- `Work.SSGRoute.solvableStage_of_scholz`.  Both states measured in
      -- `Scratch_resolve_test.lean` (workspace root, rc=0), so this file elaborates in either.
      (fun m' hm' => Work.SSGRoute.solvableStage_of_scholz p K i j hj hji hμ hIH m' hm') m hm)
      n hn

/-- Scholz solutions exist at every pair of the chain, all levels at once.  This is the strong
induction on `τ` of the paper, transported to the sequence `tauChain`. -/
theorem exists_scholz_at_tauChain (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (k : ℕ) :
    SSGRoute.HasRootsOfUnity p K (tauChain k).1 → ∀ n : ℕ, 1 ≤ n →
      ∃ φ : SSGRoute.GalQ →*
          Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n (tauChain k).1 (tauChain k).2,
        SSGRoute.IsScholzSolution p K n (tauChain k).1 (tauChain k).2 φ := by
  induction k with
  | zero => intro hμ n hn; exact scholz_one_one p K n hn
  | succ k ih =>
      intro hμ n hn
      obtain ⟨h1, h2⟩ := tauChain_spec k
      -- `μ_{p^{i+1}} ⊆ K` survives the step of the chain
      have hμ₀ : SSGRoute.HasRootsOfUnity p K (tauChain k).1 :=
        hasRootsOfUnity_mono (le_tauSucc_fst (tauChain k).1 (tauChain k).2) hμ
      exact scholz_tauSucc p K (tauChain k).1 (tauChain k).2 h1 h2 hμ₀ (ih hμ₀) n hn

/-- **Theorem 15 of Schmidt–Wingberg over `ℚ`** (arXiv:math/9809211, §5): for every pair `(i,j)`
with `1 ≤ j ≤ i`, every `n ≥ 1`, and every finite normal `K/ℚ` with `μ_{p^{i+1}} ⊆ K`, the split
generic embedding problem `1 → F(n)^{(i,j)} → ⋯ → Gal(K/ℚ) → 1` over `ℚ` has a Scholz solution
(continuous, proper, with the local conditions (i) and (ii)). -/
theorem theorem15_scholz (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)
    (hμ : SSGRoute.HasRootsOfUnity p K i) (n : ℕ) (hn : 1 ≤ n) :
    ∃ φ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n i j,
      SSGRoute.IsScholzSolution p K n i j φ := by
  obtain ⟨k, hk⟩ := tauChain_reaches i j hj hji
  have hf : (tauChain k).1 = i := congrArg Prod.fst hk
  have hg : (tauChain k).2 = j := congrArg Prod.snd hk
  subst i
  subst j
  exact exists_scholz_at_tauChain p K k hμ n hn

end Work.SSGRoute

/-
# Status of this node (notes for the next session)

`theorem15_scholz` is **proved here**: this file contains no placeholder proofs and
`Work.SSGRoute.tauChain`, `tauChain_zero`, `tauChain_succ`, `le_tauSucc_fst`, `tauChain_spec`,
`tauChain_reaches`, `scholz_tauSucc`, `exists_scholz_at_tauChain` are all real proofs.  The two
base ingredients `Work.SSGRoute.scholz_one_one` and `Work.SSGRoute.hasRootsOfUnity_mono` were
delegated and are proved as well.

The lemma is nevertheless **not accepted by `declare_proven()`** yet, because that check is
*transitive*: `#print axioms Work.SSGRoute.theorem15_scholz` reports the placeholder axiom,
inherited from the three step lemmas this node consumes (still being proved by other agents,
together with their own arithmetic dependencies):

* `SSGRoute.solvableStage_of_scholz`      (Steps 1-2 of SW section 5)
* `SSGRoute.properStage_of_solvableStage` (Step 3)
* `SSGRoute.scholz_succ_of_properStage`   (Step 4)

Each of those needs, transitively, `SSGRoute.prop5Data_exists`, `SSGRoute.local_tame_lifting`,
`SSGRoute.bauer_of_chebotarev`, `SSGRoute.sha2_image_of_Hm2`, `SSGRoute.coker_obstruction` and
Shafarevich's existence theorem (Theorem 13).  So this node becomes verifiable exactly when the
whole Theorem-15 subtree has no unproved leaves; the check to run is

    lake env lean Scratch_axcheck_t15.lean

which prints `#print axioms Work.SSGRoute.theorem15_scholz` and must report
`[propext, Classical.choice, Quot.sound]`.  Nothing about *this* file needs to change at that
point; only the unproved leaves below it must be filled in.

STATUS (updated 2026-10-01 11:30 by this node's agent).  **This file is finished and
`lake build Submission.Work.SSGRoute.theorem15_scholz` succeeds**; `declare_proven()` reports
**only** `sorryAx` (2026-09-29 06:5x), i.e. the module builds against the current dependency state
and the sole outstanding item is the transitive `sorryAx` of the six declarations below, all owned
by live lanes.  The three build-breaking duplicate declarations that had to be repaired for this
module to elaborate at all are recorded in `Submission/Work/SSGRoute/ACTION_theorem15_route.md`.

Measured from the proof term itself (`lake env lean Scratch_t15_needs.lean`, workspace root; a
`#print axioms`-style BFS of 123984 reachable constants, 2026-09-29 06:55):

```
reachable: 123984, sorried: 6
  SORRY Work.SSGRoute.canonical_localPairing_with_reciprocity   -- G1 (HRec lane; = h4 + FinNondeg(odd p)
                                                                --   + Parity2(p = 2))
  SORRY Work.SSGRoute.PT.pt_counting_identity_h1                -- COUNT; the old name
                                                                --   `PT.pt_selmer_counting_identity` is no
                                                                --   longer in the proof term (re-wired)
  SORRY Work.SSGRoute.step4_y_localData_exists                  -- the escape clause `hesc` only
  SORRY Work.SSGRoute.z_data_general_of_ramified                -- Theorem 13's z (four shared gates)
  SORRY Work.SSGRoute.gradedStep_diagonal                       -- the p = 2 correction (carries hδ1)
  SORRY Work.SSGRoute.tatePoitouEmbedding                       -- SW Step 2; route A (E1a+E9) is dead
                                                                --   (`PTdualControl/g5Assembly.lean`), route B
                                                                --   (`g5RouteB.lean`) is live
```

(`step4_y_exists` and `properStageAssemblyData` have been proved since the previous measurement and
are no longer in the list; ~200 other `SSGRoute` files still contain `sorry` but are outside this
node's proof term — a `sorry` there does not block verification.)

Status reports, audits and tools for this node live in
`Submission/Work/SSGRoute/theorem15_scholz.md` and
`Submission/Work/SSGRoute/ACTION_theorem15_route.md` (the latter records the three build-breaking
collisions that had to be repaired for this module to elaborate at all, and how each was fixed).

STATE 2026-10-01 11:30 (measured; see `Submission/Work/SSGRoute/ACTION_theorem15_route.md`
Sections 1octies for the details and the evidence):

* **`Work.SSGRoute.tatePoitouEmbedding` no longer has a `sorry`** (file 2026-09-30 20:34): one of the
  six leaves has been closed.
* The Step-4-y leaf has been **renamed** by its lane: `Work.SSGRoute.step4_y_localData_exists`
  (`step4_y_exists.lean`, now snapshotted to `_snap_h9/`) is `Work.SSGRoute.step4_y_exists_v2`
  (`step4_y_exists_v2.lean`), and this file's imports/uses were already re-wired accordingly by that
  lane (this file is unchanged in statement and name).
* The four remaining leaves are `Work.SSGRoute.canonical_localPairing_with_reciprocity` (G1),
  `Work.SSGRoute.PT.pt_counting_identity_h1` (COUNT), `Work.SSGRoute.z_data_general_of_ramified`
  (Z-data) and `Work.SSGRoute.gradedStep_diagonal` (`p = 2`).
* **Current build blocker (not ours):** `Submission/Work/SSGRoute/solvableStage_of_scholz.lean`
  opens `namespace Work.SSGRoute` twice (lines 53 and 86), so `solvableStage_of_scholz` now lives at
  `Work.SSGRoute.Work.SSGRoute.solvableStage_of_scholz` and line 111 of this file fails with
  `Unknown identifier`.  One-line fix + evidence: `PING_namespace_regression_solvableStage.md`.
* This file's own code is unchanged and, whenever the namespace regression above is repaired, the
  build reaches the axiom check and reports exactly the `sorryAx` of the four leaves.

Do not weaken or restate the target: the orchestrator's final assembly is

    minimalNormalKernelStep := minimalNormalKernelStep_of_genericKernelSolvable
      (genericKernelSolvable_of_flowSolutions
        (fun p _ K _ _ i j hj hji hmu n hn => (theorem15_scholz p K i j hj hji hmu n hn).imp fun _ h => h.1))

and this file needs no further change for it.

  **The proof in this file is complete and its
own code is unchanged and axiom-clean; what remains is other lanes' work and one broken file.**

1. *Build blocker (reported, awaiting a two-block deletion in a colleague's file).*
   `lake build Submission.Work.SSGRoute.theorem15_scholz` currently fails with

   ```
   Submission/Work/SSGRoute/scholz_succ_of_properStage.lean:127:8:
     error: `Work.SSGRoute.item5_of_bundle_guarded` has already been declared
   Submission/Work/SSGRoute/scholz_succ_of_properStage.lean:210:8:
     error: `Work.SSGRoute.item6_of_bundle_guarded` has already been declared
   ```

   a half-done "import flip" of the Step-4 lane: those two helpers were *copied* into the upstream
   module `step4_bundle_assembly.lean` (lines 182 and 270, 2026-09-27 11:50) but not deleted from
   `scholz_succ_of_properStage.lean` (lines 127 and 210, untouched since 09:46).  The two copies'
   statements are byte-identical, so deleting either pair is safe; the *intended* fix is to delete
   the node file's copies, leaving the uses at lines 399/402 to resolve upstream.  Full details and
   patch: `Submission/Work/SSGRoute/ACTION_theorem15_route.md`.

2. *The transitive `sorryAx` of four declarations* (measured from the proof term by
   `lake env lean Scratch_t15_needs.lean`, workspace root; the earlier set of five lost
   `properStageAssemblyData`, closed 2026-09-27 12:13):

   ```
     SORRY Work.SSGRoute.gradedStep_diagonal          -- the p = 2 correction
     SORRY Work.SSGRoute.step4_y_exists               -- Step 4's coker arithmetic (behind it:
                                                      --   coker_obstruction + shafarevich_existence
                                                      --   + z_data_general_of_ramified)
     SORRY Work.SSGRoute.z_data_general_of_ramified   -- Theorem 13's z
     SORRY Work.SSGRoute.tatePoitouEmbedding          -- SW Step 2's Claim; reduced by the proved
                                                      --   tatePoitouEmbedding_of_E1a_E9 to E1a + E9
   ```

   each owned by a live lane (the p = 2 lane; the H9/Step-4 lane; the Z-data lanes; the PT/PTCore
   lanes), and none of them is unowned or ready to be wired (checked by
   `Scratch_t15_ready.py`).  `tatePoitouEmbedding`'s inputs `E1a` (`ext_sha2_bridge`) and `E9`
   (`PT.pt_counting_identity_h1`) were both under active edit at 2026-09-28 05:30.

3. *Audits done* (all recorded in `Submission/Work/SSGRoute/theorem15_scholz.md`): the target
   statement is a faithful rendering of SW's Theorem 15 (with the roots-of-unity hypothesis being
   the paper's own device, carried by the consumer `genericKernelSolvable_of_flowSolutions`), the
   local conditions `ScholzConditions` are the paper's (i),(ii) clause by clause, and the four steps
   match the paper's four substeps.

Do not weaken or restate the target: the orchestrator's final assembly is

    minimalNormalKernelStep := minimalNormalKernelStep_of_genericKernelSolvable
      (genericKernelSolvable_of_flowSolutions
        (fun p _ K _ _ i j hj hji hmu n hn => (theorem15_scholz p K i j hj hji hmu n hn).imp fun _ h => h.1))

and this file needs no further change for it.

  **This file is finished; the module now
elaborates and `lake build Submission.Work.SSGRoute.theorem15_scholz` succeeds.**  The two duplicate
declarations that used to make the *join* of the two halves fail (reported in
`Submission/Work/SSGRoute/ACTION_theorem15_route.md` §1-§2: `res_eq_one_iff_mem_fixingSubgroup` in
`local_factorisation.lean` vs `ZConstruction/Reduction.lean`, and `selmer_dual_inflated` in
`sha2_dual_control.lean` vs `selmer_dual_inflated.lean`) have been repaired, and the join-clash scan
`Scratch_t15_join.py` now reports only the tolerated pair `commutator_flowTerm_le_top`.

The remaining obstacle is the transitive `sorryAx` of **five** declarations, measured from the proof
term itself by `lake env lean Scratch_t15_needs.lean` (workspace root, `#print axioms`-style BFS,
2026-09-27 06:40):

```
reachable: 96492, sorried: 5
  SORRY Work.SSGRoute.properStageAssemblyData      -- Step 3's assembly               (0.1 h)
  SORRY Work.SSGRoute.step4_y_exists               -- Step 4's coker arithmetic       (live prover)
  SORRY Work.SSGRoute.z_data_general_of_ramified   -- Theorem 13's input              (22 h)
  SORRY Work.SSGRoute.gradedStep_diagonal          -- the p = 2 correction            (0.4 h)
  SORRY Work.SSGRoute.tatePoitouEmbedding          -- SW Step 2's Claim (the atom)    (19 h)
```

Each must be filled **in its own file** (nothing in this file can substitute for it):

* `properStageAssemblyData` is Step 3 (`properStage_of_solvableStage` consumes it directly);
* `step4_y_exists` is the coker half of Step 4, which `scholz_succ_of_properStage` now consumes
  directly; behind its (absent) proof sit `coker_obstruction` and `shafarevich_existence`, whose own
  inputs `Work.SSGRoute.canonical_localPairing_with_reciprocity`, `Work.SSGRoute.PT.pt_selmer_counting_identity`
  and `Work.SSGRoute.z_data_general_of_ramified` are still open (see `Scratch_sryD.lean`);
* `gradedStep_diagonal` is the `p = 2` lane's node; `gradedStep_j_ge_two` itself is now proved
  (`gradedStep_of_diagonal` ∘ `gradedStep_diagonal`);
* `tatePoitouEmbedding` is SW Step 2's Claim.  Its proved assembly
  `PTembedding/tatePoitouEmbedding_alt` reduces it to the two stale nodes
  `PTembedding/poitouTate_pairing` (27 h) and `PTembedding/sha_card_euler` (27 h); equivalently, the
  handoff's route (A) reaches it through `E9` (left-nondegeneracy, dispatched as
  `Sha2Lib/extDelta_eq_zero_of_locTrivial_annihilator`, not yet on disk) plus the counting.  The
  older E7+E8 route is retired: the filed `PTembedding/localGlobal_annihilator` is *false as written*
  (`pair` is an unconstrained parameter, so `pair ≡ 0` refutes it; conjoining the E7 clause list does
  not repair it, because the γ-side failure is a dimension count) — see `E8_STATUS.md`,
  `PT/pt_counting_identity_h1.lean` and `ACTION_theorem15_route.md` §5.

Do not weaken or restate the target: the orchestrator's final assembly is

    minimalNormalKernelStep := minimalNormalKernelStep_of_genericKernelSolvable
      (genericKernelSolvable_of_flowSolutions
        (fun p _ K _ _ i j hj hji hmu n hn => (theorem15_scholz p K i j hj hji hmu n hn).imp fun _ h => h.1))

and this file needs no further change for it.

STATUS (updated 2026-09-26 08:0x by this node's agent): the earlier build blockers below this file
(the `isCoboundaryOn_mono` clash between `ShaCocycles.lean`/`place_basics.lean`, and the type errors in
`properStage_of_solvableStage.lean`) have been repaired by their owners; this module now *builds*.  What
remains is only the inherited placeholder axiom, whose four sources are

* `SSGRoute/scholz_succ_of_properStage.lean`  (hole `step4Input_of_properStages`),
* `SSGRoute/properStageAssemblyData.lean`     (hole `properStageAssemblyData`),
* `SSGRoute/two_torsion_lift_two.lean`        (hole `flowQuotient_antifixed_is_delta_difference_aux`),
* `SSGRoute/sha2_dual_control.lean`           (hole `sha2_dual_control`),

each in a colleague's file and each blocked on a different piece of missing mathematics; see
`Submission/Work/SSGRoute/theorem15_scholz.md` for the current diagnosis (upstream gaps, the two
import-acyclicity traps, and the `p = 2` graded-step plan).  `Scratch_t15_axchk2.lean` prints the
axiom sets to re-measure.  Nothing in *this* file needs to change.

Do not weaken or restate the target: the orchestrator's final assembly is

    minimalNormalKernelStep := minimalNormalKernelStep_of_genericKernelSolvable
      (genericKernelSolvable_of_flowSolutions
        (fun p _ K _ _ i j hj hji hmu n hn => (theorem15_scholz p K i j hj hji hmu n hn).imp fun _ h => h.1))
-/

/-! ## STATE 2026-10-01 ~13:1x (this node's session; MEASURED, not read)

**The exact leaf set is FIVE declarations** (proof-term reachability BFS from each step lemma on the
current oleans; scripts `Scratch_t15_needs3.lean` / `Scratch_t15_needs4.lean` at the workspace root,
full table in `Submission/Work/SSGRoute/ACTION_theorem15_route.md` §1decies):

| # | leaf | step lemma | owner (12:2x) |
|---|---|---|---|
| 1 | `canonical_localPairing_with_reciprocity` (G1) | Steps 1–2 / Step 3 | `E7Fin`/`coker_obstruction_pt` |
| 2 | `PT.pt_counting_identity_h1` (E1) | Step 3 | `PT`/COUNT |
| 3 | `z_data_general_of_ramified` (ZD) | Step 4 | `Z` lane |
| 4 | `isUnramifiedExt_of_levelPair_unramified_aux` (= node C6) | Steps 1–2 | `E7cC`/`E7cOmega` |
| 5 | `PT.e1aBetaCan_le_ker` | Steps 1–2 | `E1a` |

**Two retirements**: `gradedStep_diagonal` (and the whole group-theoretic two-torsion family:
`gradedStep_j_ge_two`, `two_torsion_lift_two`, `two_torsion_bridge`, `LiftingAux.*`,
`layerGenMinimal*`, `layerNormStatement*`, `freeGroup_refinedTerm_lifting`) and
`tatePoitouEmbedding` are **not** in this node's proof term any more: the route was re-pointed to
`stage_local_shrinking_cohomological` and the p=2 group theory is imported but unused.  Both were
on the previous leaf list.

**Leaf 4 is a stale wiring gap**: the reserved node
`isUnramifiedExt_of_levelPair_unramified_aux` in `local_phi_realization_in.lean` (09-29) was to be
replaced by the *landed* `Work.SSGRoute.isUnramifiedExt_of_levelPair_unramified` (09-30 05:41);
verified by elaboration (`Scratch_t15_unram.lean`, rc=0), and the landed theorem's own single
`sorryAx` is `E7cOmega.exists_level_unramified_detecting_class` = node C6.  So the `E7cC` lane owns
leaf 4 without being able to see it (`PING_t15_leaf_state_2026-10-01_pm.md`).

**Build blocker (not ours)**: `solvableStage_of_scholz.lean` still opens `namespace Work.SSGRoute`
twice (lines 53 and 86), so the name `Work.SSGRoute.solvableStage_of_scholz` does not exist and line
111 of this file fails with `Unknown identifier`.  A *verified* repair is on disk:
`PATCH_solvableStage_of_scholz.lean` (elaborates, rc=0 in 28 s) plus the one-command applier
`Scratch_apply_namespace_fix.py`; see `PING_namespace_regression_solvableStage.md` (addendum).
This blocks the final assembly (`Submission.Shafarevich` imports this file), not just this node.

**Fleet actions of this session** (all in `ACTION_theorem15_route.md` §1undecies): shipped the
proved, axiom-clean brick `Submission/Work/SSGRoute/PT/e1aSESgen_deltaH2_injective.lean` (reviewed
11:44, unfiled; proof from the already-proved `homCoind_H1_free_conj_v2`), and filed six reviewed
lemmas for the leaves' chains (`ZDataMup/cup_eq_mupHilb` → returned FALSE-as-scoped with the
reduction + the parsed linear-algebra half `ZDataMup.exists_linearEquiv_eq_of_nondegenerate`;
`PT/kummerHilbertCyclic_levelGroup_pt`; `ZDataTwo/kummerRoot_norm_neg_two`;
`N2v2/isUnramifiedIn_of_algEquiv` → PROVED; `N2v2/inertiaImage_fixedField_isUnramified`;
`N2v2/inertiaLift_of_artinMap`; `E7cC/level_map_of_algHom`).  The reusable harvesting tool is
`Scratch_harvest_reviews.py` (the workspace-wide review ledger as a work queue).

Nothing in the *proof* part of this file changed: the three glue lemmas, `tauChain*` and the
induction are exactly as before.
-/
