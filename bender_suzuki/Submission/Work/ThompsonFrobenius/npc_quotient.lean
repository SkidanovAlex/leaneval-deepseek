import Mathlib
import Submission.Work.ThompsonFrobenius.GTDefs
import Submission.Work.ThompsonFrobenius.npc_of_le
import Submission.Work.ThompsonFrobenius.npc_normalizer_of_not_normal
import Submission.Work.ThompsonFrobenius.pCore_ne_bot
import Submission.Work.ThompsonFrobenius.pCore_lt
import Submission.Work.ThompsonFrobenius.Prelim
import Submission.Work.ThompsonFrobenius.ZJ_le
import Submission.Work.ThompsonFrobenius.ZJ_ne_bot
import Submission.Work.ThompsonFrobenius.normalizer_le_normalizer_ZJ
import Submission.Work.HallHigman.ModRep

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# GT-3: `G ⧸ O_p(G)` is `p`-nilpotent (area `ThompsonFrobenius`)

Step GT-3 of `NOTES_LEAD_bs_thompson.md` (Farris §3.4 Step Three).  Let `G` be a minimal
counterexample with Sylow `p`-subgroup `P`, `H = O_p(G) ≠ 1` (GT-1) with `H < P` (GT-2'), and
`Ḡ = G ⧸ H`, `P̄ = P H / H` the Sylow image of `P` (`Sylow.mapSurjective`).

* `W := Z(J(P̄))` pulled back to `G` satisfies `H < W ≤ P`: `W ≤ P` because `Z(J(P̄)) ≤ P̄` and
  `P̄` pulls back to `P · H = P`; `H < W` because `Z(J(P̄)) ≠ 1` (GT-2' gives `P̄ ≠ 1` and `Z(J)`
  of a nontrivial `p`-group is nontrivial).
* `P ≤ N_G(W)`: `P̄ ≤ N_{\bar G}(Z(J(P̄)))` and the normalizer pulls back
  (`Subgroup.le_normalizer_comap`).
* `W` is not normal in `G`, because a normal `p`-subgroup lies in `O_p(G) = H`
  (`Work.HallHigman.le_pCore_of_isPGroup`).
* So GT-d gives `NPC(N_G(W))`; since `N_G(W) = (N_{\bar G}(Z(J(P̄)))).comap (mk H)`
  (`Subgroup.comap_normalizer_eq_of_le_range`), the normalizer in `Ḡ` has a normal `p`-complement
  (`hasNormalPComplement_of_surjective`, `MonoidHom.subgroupComap`).
* The induction hypothesis `h.ih` applied to `Ḡ` (smaller order since `H ≠ 1`) gives the claim.
-/

set_option autoImplicit false

namespace Work.ThompsonFrobenius

theorem npc_quotient {p : ℕ} {G : Type} [Group G] [Finite G] {P : Sylow p G}
    (h : GTMinimal p G P) :
    Work.NPC.HasNormalPComplement p (G ⧸ Work.HallHigman.pCore p G) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  let H : Subgroup G := Work.HallHigman.pCore p G
  have hHne : H ≠ ⊥ := pCore_ne_bot h
  have hHltP : H < (P : Subgroup G) := pCore_lt h
  -- the quotient has smaller order
  have hcardQ : Nat.card (G ⧸ H) < Nat.card G := by
    have hmul : Nat.card (G ⧸ H) * Nat.card ↥H = Nat.card G := by
      rw [← Subgroup.index_eq_card]
      exact Subgroup.index_mul_card H
    have h1 : 1 < Nat.card ↥H := (Subgroup.one_lt_card_iff_ne_bot H).mpr hHne
    have h2 : 0 < Nat.card (G ⧸ H) := Nat.card_pos
    calc Nat.card (G ⧸ H) < Nat.card (G ⧸ H) * Nat.card ↥H := lt_mul_of_one_lt_right h2 h1
      _ = Nat.card G := hmul
  -- the quotient map and the image Sylow
  let π : G →* G ⧸ H := QuotientGroup.mk' H
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective H
  have hker : π.ker = H := QuotientGroup.ker_mk' H
  let Pbar : Sylow p (G ⧸ H) := P.mapSurjective hπsurj
  let Zbar : Subgroup (G ⧸ H) := Submission.Blueprint.ZJ (Pbar : Subgroup (G ⧸ H))
  let W : Subgroup G := Zbar.comap π
  -- `P̄ ≠ 1` (GT-2')
  have hPbar_ne : (Pbar : Subgroup (G ⧸ H)) ≠ ⊥ := by
    intro hbot
    have h1 : (P : Subgroup G).map π = ⊥ := hbot
    rw [Subgroup.map_eq_bot_iff] at h1
    rw [hker] at h1
    exact absurd h1 (not_le_of_gt hHltP)
  have hZbar_ne : Zbar ≠ ⊥ := ZJ_ne_bot (Pbar.isPGroup') hPbar_ne
  -- `H ≤ W ≤ P`
  have hHleW : H ≤ W := by
    intro x hx
    have hx1 : π x = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact hx
    show π x ∈ Zbar
    rw [hx1]
    exact Zbar.one_mem
  have hWleP : W ≤ (P : Subgroup G) := by
    intro x hx
    have hxPbar : π x ∈ (Pbar : Subgroup (G ⧸ H)) := ZJ_le (Pbar : Subgroup (G ⧸ H)) hx
    obtain ⟨p, hp, hpx⟩ := Subgroup.mem_map.mp hxPbar
    have hkerx : p⁻¹ * x ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hpx]
      simp
    rw [hker] at hkerx
    have : x = p * (p⁻¹ * x) := by group
    rw [this]
    exact P.mul_mem hp (hHltP.le hkerx)
  have hWneH : W ≠ H := by
    intro heq
    apply hZbar_ne
    refine le_antisymm (fun y hy => ?_) bot_le
    obtain ⟨x, rfl⟩ := hπsurj y
    have hxW : x ∈ W := hy
    rw [heq] at hxW
    have hx1 : π x = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact hxW
    exact hx1
  have hHltW : H < W := lt_of_le_of_ne hHleW (Ne.symm hWneH)
  -- `P ≤ N_G(W)`
  have hPleNW : (P : Subgroup G) ≤ Subgroup.normalizer (W : Set G) := by
    have h1 : (Pbar : Subgroup (G ⧸ H)) ≤
        Subgroup.normalizer (Zbar : Set (G ⧸ H)) :=
      le_trans Subgroup.le_normalizer
        (normalizer_le_normalizer_ZJ (Pbar : Subgroup (G ⧸ H)))
    intro x hx
    exact Subgroup.le_normalizer_comap π (h1 (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩))
  -- `W` is not normal
  have hWp : IsPGroup p W := isPGroup_of_le P.isPGroup' hWleP
  have hWn : ¬ W.Normal := by
    intro hWnorm
    exact (not_le_of_gt hHltW) (Work.HallHigman.le_pCore_of_isPGroup hWnorm hWp)
  -- GT-d and the transport to the quotient
  have hNW : Work.NPC.HasNormalPComplement p
      ↥((Subgroup.normalizer (Zbar : Set (G ⧸ H))).comap π) := by
    rw [Subgroup.comap_normalizer_eq_of_le_range (f := π) (H := Zbar)
      (by rw [MonoidHom.range_eq_top.mpr hπsurj]; exact le_top)]
    exact npc_normalizer_of_not_normal h hWp hPleNW hWn
  have hNPC : Work.NPC.HasNormalPComplement p
      ↥(Subgroup.normalizer (Zbar : Set (G ⧸ H))) :=
    Work.NPC.Basic.hasNormalPComplement_of_surjective
      (MonoidHom.subgroupComap π (Subgroup.normalizer (Zbar : Set (G ⧸ H))))
      (MonoidHom.subgroupComap_surjective π _ hπsurj) hNW
  exact h.ih (G ⧸ H) hcardQ Pbar hNPC

end Work.ThompsonFrobenius
