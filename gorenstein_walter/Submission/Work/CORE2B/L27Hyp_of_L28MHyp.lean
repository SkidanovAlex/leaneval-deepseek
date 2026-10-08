import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.BenderCtx_sylow_not_cyclic

/-!
# AREA CORE2B — glue: `L28MHyp` together with `t ∉ E(M)` gives the `L27Hyp` of `M`

Bender 1981, Lemma 2.8 is proved by applying Lemma 2.7 to a subgroup `M` with `Ĥ ⇝ M`, `¬ M ≤ Ĥ`
and `S ≤ M`.  The hypotheses of Lemma 2.7 (`Work.CORE2B.L27Hyp`) are the same as those of Lemma 2.8
(`Work.CORE2B.L28MHyp`) plus `t ∈ M`, `t ∉ E(M)`, `Sylow 2-subgroups of `M` are non-cyclic`, and a
`size` condition.  This file supplies the three extra fields from `S ≤ M`:

* `t ∈ M` is immediate from `t ∈ S₀ ≤ S ≤ M`;
* every Sylow 2-subgroup of `M` is non-cyclic, because `S` (which is a Sylow 2-subgroup of `M` as
  `S ≤ M`) is non-cyclic (`Work.CORE2B.BenderCtx_sylow_not_cyclic`) and all Sylow 2-subgroups of `M`
  are `M`-conjugate;
* the `size` condition follows since `S ⊓ M = S` and `4 ∣ |S|` (from `|S| = 2|S₀|` and
  `2 ∣ |S₀|`, as `t ∈ S₀` has order `2`), so `|S| = 4` or `8 ≤ |S|`.
-/

open scoped MatrixGroups

set_option linter.unusedVariables false

namespace Work.CORE2B

open Subgroup

/-! ## Sylow 2-subgroups of a subgroup containing `S` are non-cyclic -/

/-- If `S ≤ M` then every Sylow 2-subgroup of `M` is non-cyclic.  Indeed `S` is a Sylow
2-subgroup of `M` (`S.subtype`), every Sylow 2-subgroup of `M` is `M`-conjugate to it
(`Sylow.equiv`), and `S` itself is non-cyclic by `BenderCtx_sylow_not_cyclic`. -/
private theorem sylow_two_M_not_cyclic {G : Type} [Group G] [Finite G] (hCtx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (M : Subgroup G) (hSM : (B.S : Subgroup G) ≤ M) :
    ∀ P : Sylow 2 M, ¬ IsCyclic P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnc : ¬ IsCyclic ↥(B.S : Subgroup G) := Work.CORE2B.BenderCtx_sylow_not_cyclic hCtx B.S
  intro P hP
  let S' : Sylow 2 M := B.S.subtype hSM
  have hS' : (S' : Subgroup M) = (B.S : Subgroup G).subgroupOf M := Sylow.coe_subtype B.S hSM
  have h1 : IsCyclic ↥(S' : Subgroup M) := (MulEquiv.isCyclic (Sylow.equiv P S')).mp hP
  rw [hS'] at h1
  exact hnc ((MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hSM)).mp h1)

/-! ## The `size` condition of `L27Hyp` -/

/-- The `size` condition of `L27Hyp` holds when `S ≤ M`: `S ⊓ M = S` and `4 ∣ |S|`, so
`|S| = 4` or `8 ≤ |S|`. -/
private theorem size_hyp_of_S_le_M {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G)
    (M : Subgroup G) (hSM : (B.S : Subgroup G) ≤ M) :
    8 ≤ Nat.card ((B.S : Subgroup G) ⊓ M : Subgroup G) ∨ Nat.card (B.S : Subgroup G) = 4 ∨
      B.t ∈ Work.GW2.twoResidualIn M := by
  -- `|S| = 2 * |S₀|`
  have hcard : Nat.card (B.S : Subgroup G) = 2 * Nat.card B.S0 := by
    have h := Subgroup.relIndex_mul_card B.S0 (B.S : Subgroup G)
    rw [B.S0_index, inf_eq_left.mpr B.S0_le] at h
    exact h.symm
  -- `2 ∣ |S₀|`, because `t ∈ S₀` has order `2`
  have h2 : 2 ∣ Nat.card B.S0 := by
    have h := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr B.t_mem)
    rwa [Nat.card_zpowers, B.t_order] at h
  -- hence `4 ∣ |S|`
  obtain ⟨j, hj⟩ := h2
  have h4 : 4 ∣ Nat.card (B.S : Subgroup G) := ⟨j, by rw [hcard, hj]; ring⟩
  obtain ⟨k, hk⟩ := h4
  -- `S ⊓ M = S`
  have hinf : Nat.card ((B.S : Subgroup G) ⊓ M : Subgroup G) = Nat.card (B.S : Subgroup G) := by
    rw [inf_eq_left.mpr hSM]
  have hpos : 0 < Nat.card (B.S : Subgroup G) := Nat.card_pos
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · -- `k = 1`, so `|S| = 4`
    have hk1 : k = 1 := by omega
    right; left; omega
  · -- `2 ≤ k`, so `8 ≤ |S|`
    left; rw [hinf]; omega

/-! ## The glue theorem -/

-- Glue in area CORE2B (Bender 1981, Lemma 2.8): the hypotheses of Lemma 2.7 hold for `M` when
-- `S ≤ M` and `t ∉ E(M)`, so that a prover of `L28_t_mem_layer` can apply `Lemma27Prop`.
-- The `sylow_nc` field is proved from `Work.CORE2B.BenderCtx_sylow_not_cyclic`: with `S ≤ M`, `S` is a
-- Sylow 2-subgroup of `M` (its index is odd), and every Sylow 2-subgroup of `M` is `S^m` for some
-- `m ∈ M` by Sylow conjugacy, hence non-cyclic; the `size` field follows from `S ≤ M` and the fact that
-- `S` is a non-cyclic 2-group (so `|S| = 4` or `8 ≤ |S|`), and `t ∈ M` from `t ∈ S₀ ≤ S ≤ M`.
theorem L27Hyp_of_L28MHyp {G : Type} [Group G] [Finite G] (hctx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (M : Subgroup G) (h : Work.CORE2B.L28MHyp B M)
    (htl : B.t ∉ Work.GW2.layerIn M) : Work.CORE2B.L27Hyp B M := by
  refine ⟨h.M_ne_top, h.rel, h.not_le, ?_, htl, ?_, ?_⟩
  -- `t ∈ S₀ ≤ S ≤ M`
  · exact h.S_le_M (B.S0_le B.t_mem)
  -- Sylow 2-subgroups of `M` are non-cyclic
  · exact sylow_two_M_not_cyclic hctx B M h.S_le_M
  -- the `size` condition
  · exact size_hyp_of_S_le_M B M h.S_le_M

end Work.CORE2B
