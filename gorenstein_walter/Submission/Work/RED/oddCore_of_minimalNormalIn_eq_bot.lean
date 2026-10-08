import Mathlib
import Submission.Work.RED.Basic

/-!
# `O(K) = 1` for a non-solvable minimal normal subgroup `K` of a minimal normal `N`

Blueprint §4: if `N` is a minimal normal subgroup of `G` and `K` is a minimal normal subgroup
of `↥N` (i.e. `IsMinimalNormalIn N K`) which is *not* solvable, then `K` has no nontrivial
normal subgroup of odd order, i.e. `O(K) = O_{2'}(K) = ⊥`.

The argument is the standard "characteristic in normal is normal" one:

* `O(K)` is characteristic in `K` (`OddCoreFactsProp.characteristic`), and `K ⊴ N`, so
  `O(K)`, viewed inside `G`, is normal in `N` (`MinimalNormalFactsProp.char_normal`);
* since `K` is minimal among the nontrivial normal subgroups of `N` inside it, either
  `O(K) = 1` (done) or `O(K) = K`;
* in the second case `|K| = |O(K)|` is odd (`OddCoreFactsProp.odd`), so Feit–Thompson
  (`FeitThompsonProp`) makes `K` solvable — contradicting the hypothesis.

This is exactly the field `RedFacts.oddCoreK` used by the RED induction.
-/

namespace Work.RED

open Subgroup

/-- A subgroup of `↥K` is the `subgroupOf K` of its image in `G` under `K.subtype`. -/
private theorem map_subtype_subgroupOf' {G : Type*} [Group G] (K : Subgroup G)
    (C : Subgroup ↥K) : (C.map K.subtype).subgroupOf K = C := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨l, hl, hlx⟩
    have hlx' : l = x := Subtype.ext hlx
    rwa [← hlx']
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem oddCore_of_minimalNormalIn_eq_bot
    (hmin : Work.RED.GW2.MinimalNormalFactsProp) (hodd : Work.RED.GW2.OddCoreFactsProp)
    (hFT : Work.RED.GW2.FeitThompsonProp)
    {G : Type} [Group G] [Finite G] {N K : Subgroup G} (hN : Work.RED.GW2.IsMinimalNormal N)
    (hK : Work.RED.GW2.IsMinimalNormalIn N K) (hsol : ¬ Group.IsSolvable ↥K) :
    Work.RED.GW2.oddCore ↥K = ⊥ := by
  -- `O(K)` transported to a subgroup of the ambient group `G`.
  set Cg : Subgroup G := (Work.RED.GW2.oddCore ↥K).map K.subtype with hCg
  have hsub : Cg.subgroupOf K = Work.RED.GW2.oddCore ↥K := by
    rw [hCg]; exact map_subtype_subgroupOf' K _
  have hle : Cg ≤ K := by rw [hCg]; exact Subgroup.map_subtype_le _
  -- `O(K)` is characteristic in `K`, hence normal in `N`.
  have hchar : (Cg.subgroupOf K).Characteristic := by
    rw [hsub]; exact hodd.characteristic ↥K
  have hnorm : (Cg.subgroupOf N).Normal :=
    hmin.char_normal G N K Cg hN hle hK.le hK.normal hchar
  -- Minimality of `K` among the nontrivial normal subgroups of `N` inside `K`.
  by_cases hbot : Cg = ⊥
  · rw [← hsub, hbot, Subgroup.bot_subgroupOf]
  · exfalso
    have hCK : Cg = K := hK.minimal Cg hle hnorm hbot
    have htop : Work.RED.GW2.oddCore ↥K = ⊤ := by
      rw [← hsub, hCK, Subgroup.subgroupOf_self]
    -- So `|K| = |O(K)|` is odd, and Feit–Thompson makes `K` solvable.
    have hcard : Nat.card (Work.RED.GW2.oddCore ↥K) = Nat.card ↥K := by
      rw [htop]
      exact Nat.card_congr Subgroup.topEquiv.toEquiv
    have hOdd : Odd (Nat.card ↥K) := by
      rw [← hcard]; exact hodd.odd ↥K
    exact hsol (hFT ↥K hOdd)

end Work.RED
