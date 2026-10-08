import Mathlib
import Submission.Work.CORE2B.L29CallSite
import Submission.Work.CORE2B.L29_callSite_nonvacuous

namespace Work.CORE2B

open Subgroup
open scoped commutatorElement

/-- **The call-site data of Bender's Lemma 2.9 supplies the hypotheses of Lemma 2.7.**

At the call sites the subgroup `N` is a maximal subgroup with `Ĥ ⇝ N`, `¬ N ≤ Ĥ` and `S ≤ N`,
and `V ≤ N` is a four-group with `t ∈ V`; together with `V ∩ E(N) = ⊥` this exhibits every one of
the seven pieces of `L27Hyp B N`:

* `N ≠ ⊤` is `L29Hyp.N_ne_top`, `Ĥ ⇝ N` and `¬ N ≤ Ĥ` are the two call-site inputs;
* `t ∈ N` because `t ∈ V ≤ N`;
* `t ∉ E(N)`: otherwise `t ∈ V ∩ E(N) = ⊥`, but `orderOf t = 2`;
* every Sylow `2`-subgroup of `N` is non-cyclic: `V.subgroupOf N ≅ 2²` is a non-cyclic `2`-group,
  so no Sylow `2`-subgroup of `N` is cyclic (`sylow_not_cyclic_of_sub`);
* the size clause: `S ⊓ N = S` since `S ≤ N`, while `4 = |V| ≤ |S|` with `S` a `2`-group, so
  `8 ≤ |S ⊓ N|` or `|S| = 4` (`eight_le_or_eq_four`) — note it is the *second* alternative
  which is dropped, the disjunction `|S| = 4 ∨ t ∈ O²(N)` being the last two clauses of the
  `L27Hyp.size` disjunction. -/
theorem L29CallSite_L27Hyp {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G)
    (V N : Subgroup G) (hcs : Work.CORE2B.L29CallSite B V N)
    (h2 : V ⊓ Work.GW2.layerIn N = ⊥) : Work.CORE2B.L27Hyp B N := by
  classical
  -- `t ≠ 1`, since `orderOf t = 2`.
  have ht_ne_one : B.t ≠ 1 := by
    intro h1
    have hord := B.t_order
    rw [h1, orderOf_one] at hord
    exact absurd hord (by norm_num)
  -- `t ∈ N` because `t ∈ V ≤ N`.
  have htN : B.t ∈ N := hcs.hyp.V_le_N hcs.hyp.t_mem
  refine ⟨hcs.hyp.N_ne_top, hcs.rel, hcs.not_le, htN, ?_, ?_, ?_⟩
  · -- `t ∉ E(N)`: otherwise `t ∈ V ⊓ E(N) = ⊥`.
    intro ht
    have hmem : B.t ∈ V ⊓ Work.GW2.layerIn N := ⟨hcs.hyp.t_mem, ht⟩
    rw [h2] at hmem
    exact ht_ne_one (Subgroup.mem_bot.mp hmem)
  · -- Sylow `2`-subgroups of `N` are non-cyclic, since `2² ≅ V ≤ N`.
    intro P
    obtain ⟨hP2, hPnc⟩ := subgroupOf_four_not_cyclic V N hcs.hyp.four hcs.hyp.V_le_N
    exact sylow_not_cyclic_of_sub (V.subgroupOf N) hP2 hPnc P
  · -- The size clause: `S ⊓ N = S` and `4 = |V| ≤ |S|` with `S` a `2`-group.
    have hS2 : IsPGroup 2 ↥(B.S : Subgroup G) := Sylow.isPGroup' B.S
    rcases eight_le_or_eq_four (B.S : Subgroup G) N V hS2 hcs.S_le_N hcs.hyp.four
        hcs.hyp.V_le_S with h8 | h4
    · exact Or.inl h8
    · exact Or.inr (Or.inl h4)

end Work.CORE2B
