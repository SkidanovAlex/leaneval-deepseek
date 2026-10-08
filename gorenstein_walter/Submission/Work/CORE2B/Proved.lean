import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.Deliverable
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.isQuasisimple_four_dvd
import Submission.Work.CORE2B.BenderCtx_sylow_not_cyclic
import Submission.Work.CORE2B.oddCore_odd
import Submission.Work.CORE2B.L27Hyp_of_L28MHyp
import Submission.Work.CORE2B.L28_t_mem_layer_proved
import Submission.Work.CORE2B.UNeBotProp_of_h22_proved
import Submission.Work.CORE2B.L28_S0U_ne_bot_h26_proved
import Submission.Work.CORE2B.layer_eq_bot_of_normal_contains_t
import Submission.Work.CORE2B.L27_normal_contains_t_proved
import Submission.Work.CORE2B.L27_two_part_centralized_proved
import Submission.Work.CORE2B.L27_odd_part_inverted_proved
import Submission.Work.CORE2B.c11iv_nilpotent
import Submission.Work.CORE2B.L27v12_eq_bot_of_le_pCoreIn_Hhat
import Submission.Work.CORE2B.L27_commutator_le_final
import Submission.Work.CORE2B.L27su_assembly
import Submission.Work.CORE2B.L29_contra_h27_final
import Submission.Work.CORE2B.L29_lemma_assembly
import Submission.Work.CORE2B.Thm210_assembly

/-!
# AREA CORE2B — collected results

This module re-exports everything area CORE2B has proved, under stable names, and (as the leaf
`Prop`s land) assembles the four contract `Prop`s:

```
Work.CORE2B.lemma27 : LocalToolkit → Lemma23Prop → Thm26Prop → Work.GW2.Lemma27Prop
Work.CORE2B.lemma28 : LocalToolkit → Lemma22Prop → Lemma27Prop → Work.GW2.Lemma28Prop
Work.CORE2B.lemma29 : LocalToolkit → Work.GW2.Lemma29Prop
Work.CORE2B.thm210  : LocalToolkit → Thm26Prop → Lemma27Prop → Lemma28Prop → Work.GW2.Thm210Prop
```

`Submission/Work/CORE2B/NOTES_CORE2B.md` is the design document (source-mapped proof of each leaf,
satisfiability check, status).
-/

open scoped MatrixGroups

set_option linter.unusedVariables false

namespace Work.CORE2B

open Subgroup

/-! ## Structural facts about `BenderCtx` / `BenderSetup` (proved in sibling files) -/

/-- A non-abelian finite simple group with cyclic-or-dihedral Sylow 2-subgroups has non-cyclic
Sylow 2-subgroups.  (`L27Hyp.sylow_nc` for `M = G`; also the source of `S` dihedral.) -/
theorem benderCtx_sylow_not_cyclic_holds {G : Type} [Group G] [Finite G]
    (h : Work.GW2.BenderCtx G) (S : Sylow 2 G) : ¬ IsCyclic (S : Subgroup G) :=
  BenderCtx_sylow_not_cyclic h S

/-- `O(G)` has odd order. -/
theorem oddCore_odd_holds {G : Type} [Group G] [Finite G] :
    Odd (Nat.card (Work.GW2.oddCore G)) := oddCore_odd (G := G)

/-- A quasisimple `E ≠ ⊥` has order divisible by `4`. -/
theorem isQuasisimple_four_dvd_holds {G : Type} [Group G] [Finite G] (E : Subgroup G)
    (h : Work.GW2.IsQuasisimple E) (hne : E ≠ ⊥) : 4 ∣ Nat.card E :=
  isQuasisimple_four_dvd E h hne

/-- `U ≠ 1` (Bender 2.2's rider), from `Lemma22Prop`. -/
theorem UNeBotProp_of_h22_holds : UNeBotProp_of_h22 := UNeBotProp_of_h22_proved

/-- **Bender Lemma 2.7, step 1** (proved): every normal subgroup of `M` of order divisible by `4`
contains `t`. -/
theorem L27_normal_contains_t_holds : L27_normal_contains_t := L27_normal_contains_t_proved

/-- **Bender Lemma 2.7, step 2** (proved): `E(M) = ⊥`. -/
theorem L27_layer_eq_bot_holds : L27_layer_eq_bot :=
  layer_eq_bot_of_normal_contains_t L27_normal_contains_t_proved

/-- **Bender Lemma 2.7, step 3** (proved): `t` centralizes `F₂(M)`. -/
theorem L27_two_part_centralized_holds : L27_two_part_centralized :=
  L27_two_part_centralized_proved

/-- **Bender Lemma 2.7, step 3** (proved): `t` inverts `F_{π'}(M)`. -/
theorem L27_odd_part_inverted_holds : L27_odd_part_inverted := L27_odd_part_inverted_proved

/-- The reduction step 2 from step 1 (kept for reuse). -/
theorem layer_eq_bot_of_normal_contains_t_holds (h : L27_normal_contains_t) : L27_layer_eq_bot :=
  layer_eq_bot_of_normal_contains_t h

/-! ## Leafs of the lead's design pass 12 (Lemma 2.7(a)) -/

/-- Bender 1.1(iv) with a self-centralizing `K₀` in a nilpotent `K` (leaf N1). -/
theorem c11iv_nilpotent_holds (T : Work.GW2.LocalToolkit) {G : Type} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (P K K0 : Subgroup G) (hP : IsPGroup p P)
    (hcop : Nat.Coprime p (Nat.card K)) (hPK : P ≤ Subgroup.normalizer (K : Set G))
    (hKnil : Group.IsNilpotent ↥K) (hK0 : K0 ≤ K)
    (hPK0 : P ≤ Subgroup.centralizer (K0 : Set G))
    (hself : K ⊓ Subgroup.centralizer (K0 : Set G) ≤ K0) :
    P ≤ Subgroup.centralizer (K : Set G) :=
  c11iv_nilpotent T p P K K0 hP hcop hPK hKnil hK0 hPK0 hself

/-- Leaf N4 (`L27su_eq_bot_of_le_pCoreIn_Hhat` without its unused `Lemma22Prop` binder). -/
theorem L27v12_eq_bot_of_le_pCoreIn_Hhat_holds (T : Work.GW2.LocalToolkit)
    (h26 : Work.GW2.Thm26Prop) (G : Type) [Group G] [Finite G]
    (hFT : Work.GW2.FeitThompsonProp) (hCtx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (M : Subgroup G) (hD : L27Hyp B M)
    (hle : Work.GW2.pCoreIn 2 M ≤ Work.GW2.pCoreIn 2 B.Hhat) :
    Work.GW2.pCoreIn 2 M = ⊥ :=
  L27v12_eq_bot_of_le_pCoreIn_Hhat T h26 G hFT hCtx B M hD hle

/-! ## Lemma 2.8 -/

/-- **Bender Lemma 2.8, second assertion** (proved): if `I_U(s) ⊴ U` for all `s ∈ S − S₀` and
`Ĥ ⇝ M` with `M ≠ ⊤`, `¬ M ≤ Ĥ`, `S ≤ M`, then `t ∈ E(M)`. -/
theorem L28_t_mem_layer_holds : L28_t_mem_layer := L28_t_mem_layer_proved

/-- The hypotheses of Lemma 2.7 hold for a maximal `M ⊇ S` with `t ∉ E(M)`. -/
theorem L27Hyp_of_L28MHyp_holds {G : Type} [Group G] [Finite G] (hctx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (M : Subgroup G) (h : L28MHyp B M)
    (htl : B.t ∉ Work.GW2.layerIn M) : L27Hyp B M :=
  L27Hyp_of_L28MHyp hctx B M h htl

/-! ## The four deliverables

Each is stated as soon as its leaves are available; see `NOTES_CORE2B.md` §5 for the current list
of outstanding leaves.
-/

/-- **Bender Lemma 2.8, first assertion** (proved): `[S₀,U] ≠ 1`, using Theorem 2.6. -/
theorem L28_S0U_ne_bot_h26_holds : L28_S0U_ne_bot_h26 := L28_S0U_ne_bot_h26_proved

/-! ## The deliverable `Lemma28Prop` -/

/-- **Bender Lemma 2.8 = the contract `Work.GW2.Lemma28Prop`**, complete: inputs are the toolkit,
Bender 2.2, Theorem 2.6 and Bender 2.7 (as amended in the lead's design pass 6). -/
theorem lemma28 (T : Work.GW2.LocalToolkit) (h22 : Work.GW2.Lemma22Prop)
    (h26 : Work.GW2.Thm26Prop) (h27 : Work.GW2.Lemma27Prop) : Work.GW2.Lemma28Prop :=
  lemma28_of_leaves_h26 T h22 h26 h27 L28_S0U_ne_bot_h26_proved L28_t_mem_layer_proved

/-- **Bender Theorem 2.10 = the contract `Work.GW2.Thm210Prop`** (proved in
`Submission.Work.CORE2B.Thm210_assembly`). -/
theorem thm210_holds (T : Work.GW2.LocalToolkit) (h26 : Work.GW2.Thm26Prop)
    (h27 : Work.GW2.Lemma27Prop) (h28 : Work.GW2.Lemma28Prop) : Work.GW2.Thm210Prop :=
  thm210 T h26 h27 h28

/-! ## Lemma 2.9 -/

/-- **Bender Lemma 2.9, corrected call-site form** (the lead's design pass 15): under
`L29CallSite B V N` (i.e. `L29Hyp` plus `N` maximal, `Ĥ ⇝ N`, `¬ N ≤ Ĥ`, `S ≤ N`) and the two
trivial intersections, `V ⊓ O₂(N) = ⊥` and `V ⊓ E(N) = ⊥` are contradictory. -/
theorem L29_contra_h27_holds : Work.CORE2B.L29_contra_h27 := L29_contra_h27_final

end Work.CORE2B
