import Mathlib
import Submission.Work.ThreePoints.Basic
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.BrauerSuzuki.OddCore.le_of_normal_odd
import Submission.Work.BrauerSuzuki.OddCore.oddCard_oddCore

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `O(G/O(G)) = 1`

`O(G) = O_{2'}(G)` is the largest normal subgroup of odd order (`Submission.Blueprint.oddCore`).
The point of this file is that the odd core of the quotient by the odd core is trivial:
`O(G/O(G)) = 1` is true and basic, but it is **not** immediate from the definition of
`oddCore` as a supremum -- the definition only says that `O(G)` is *generated* by the normal
subgroups of odd order, and one has to know that this supremum is itself a normal subgroup of
odd order (`Work.BrauerSuzuki.OddCore.oddCard_oddCore`) before the familiar argument runs:

if `M ◁ G/O(G)` has odd order, its full preimage `N ◁ G` satisfies `O(G) ≤ N` and
`|N| = |O(G)| · |M|` (the first isomorphism theorem applied to `N → G ⧸ O(G)`), so `|N|` is
odd; being normal and of odd order, `N ≤ O(G)` by maximality, and then `M = N/O(G) = 1`.
-/

set_option autoImplicit false

namespace Work.ThreePoints

open Submission.Blueprint

/-- **Every normal subgroup of odd order of `G ⧸ H` is trivial**, where `H ◁ G` is a normal
subgroup of odd order which contains every normal odd-order subgroup of `G` (so that
`H = O(G)`).  The only non-trivial input is the cardinality count
`|M.comap f| = |H| * |M|`, for `f : G →* G ⧸ H` the canonical projection. -/
theorem eq_bot_of_normal_odd_quotient {G : Type} [Group G] [Finite G] (H : Subgroup G)
    [H.Normal] (hHodd : Odd (Nat.card H))
    (hmax : ∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → N ≤ H)
    (M : Subgroup (G ⧸ H)) (hMnorm : M.Normal) (hModd : Odd (Nat.card M)) : M = ⊥ := by
  let f : G →* G ⧸ H := QuotientGroup.mk' H
  let N : Subgroup G := Subgroup.comap f M
  have hfker : f.ker = H := QuotientGroup.ker_mk' H
  have hfsurj : Function.Surjective f := QuotientGroup.mk'_surjective H
  have hNnormal : N.Normal := hMnorm.comap f
  have hHN : H ≤ N := by
    have h := Subgroup.ker_le_comap f M
    rwa [hfker] at h
  have hNmap : Subgroup.map f N = M := Subgroup.map_comap_eq_self_of_surjective hfsurj M
  -- The canonical projection `N → G ⧸ H` has kernel `H` and image `M`.
  let g : N →* G ⧸ H := f.comp N.subtype
  have hgker : g.ker = H.subgroupOf N := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.subtype_apply, Subgroup.mem_subgroupOf,
      ← MonoidHom.mem_ker, hfker]
  have hgrange : g.range = M := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hNmap]
  -- `|N| = |H| * |M|`, hence `|N|` is odd.
  have hcard : Nat.card N = Nat.card H * Nat.card M := by
    calc Nat.card N = Nat.card ↥(H.subgroupOf N) * (H.subgroupOf N).index :=
          (Subgroup.card_mul_index (H.subgroupOf N)).symm
      _ = Nat.card ↥(H.subgroupOf N) * Nat.card (N ⧸ g.ker) := by
          rw [Subgroup.index_eq_card (H.subgroupOf N), hgker]
      _ = Nat.card ↥H * Nat.card (N ⧸ g.ker) := by
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHN).toEquiv]
      _ = Nat.card ↥H * Nat.card ↥M := by
          rw [← hgrange]
          exact congrArg (Nat.card ↥H * ·)
            (Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv)
  have hNodd : Odd (Nat.card N) := by
    rw [hcard]
    exact hHodd.mul hModd
  have hNH : N ≤ H := hmax N hNnormal hNodd
  have hMbot : M ≤ ⊥ := by
    have hle : Subgroup.map f N ≤ Subgroup.map f H := Subgroup.map_mono hNH
    rw [hNmap] at hle
    have hmapH : Subgroup.map f H = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, hfker]
    rwa [hmapH] at hle
  exact le_bot_iff.mp hMbot

theorem oddCore_quotient_oddCore {G : Type} [Group G] [Finite G] :
    Submission.Blueprint.oddCore (G ⧸ Submission.Blueprint.oddCore G) = ⊥ := by
  have hHodd : Odd (Nat.card (Submission.Blueprint.oddCore G)) :=
    Work.BrauerSuzuki.OddCore.oddCard_oddCore
  have hmax : ∀ N : Subgroup G, N.Normal → Odd (Nat.card N) →
      N ≤ Submission.Blueprint.oddCore G :=
    fun N hN hNo => Work.BrauerSuzuki.OddCore.le_of_normal_odd hN hNo
  unfold Submission.Blueprint.oddCore
  refine le_antisymm (sSup_le_iff.mpr ?_) bot_le
  intro M hM
  exact le_of_eq (eq_bot_of_normal_odd_quotient (Submission.Blueprint.oddCore G) hHodd hmax M
    hM.1 hM.2)

end Work.ThreePoints
