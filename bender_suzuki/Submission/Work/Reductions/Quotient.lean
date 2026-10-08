import Mathlib
import Submission.Blueprint.Interfaces
import Submission.Work.Reductions.Defs
import Submission.Work.Reductions.OddResidual

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Quotient lemmas for the `Reductions` chapter

* `card_quotient_lt`: a proper quotient is strictly smaller;
* `benderConclusion_of_quotient`: the conclusion of Theorem B lifts through `O(G)`.

The second lemma takes the conclusion `BenderConclusion (G ⧸ N)` for `N = O(G)` and reconstructs
the subgroup of `G` as `L = M.comap (G →* G ⧸ N)`, using the third isomorphism theorem: the
composed map `L → M → Y` is surjective with kernel `O(G)`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Submission.Blueprint
open LeanEval.GroupTheory.Defs

namespace Work.Reductions

/-- A proper normal subgroup has a strictly smaller quotient. -/
theorem card_quotient_lt {G : Type} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (hN : N ≠ ⊥) : Nat.card (G ⧸ N) < Nat.card G := by
  have hne : ∃ x ∈ N, x ≠ 1 := by
    by_contra h
    push_neg at h
    exact hN (le_bot_iff.mp fun x hx => Subgroup.mem_bot.mpr (h x hx))
  obtain ⟨x, hxN, hx1⟩ := hne
  have hcard2 : 1 < Nat.card ↥N := by
    haveI : Fintype ↥N := Fintype.ofFinite ↥N
    rw [Nat.card_eq_fintype_card, Fintype.one_lt_card_iff]
    exact ⟨⟨x, hxN⟩, 1, fun h => hx1 (by simpa using congrArg Subtype.val h)⟩
  have h2 : Nat.card ↥N * Nat.card (G ⧸ N) = Nat.card G := by
    rw [← Subgroup.card_mul_index N, Subgroup.index_eq_card]
  have hpos : 0 < Nat.card (G ⧸ N) := Nat.card_pos
  calc Nat.card (G ⧸ N) = 1 * Nat.card (G ⧸ N) := (one_mul _).symm
    _ < Nat.card ↥N * Nat.card (G ⧸ N) := Nat.mul_lt_mul_of_pos_right hcard2 hpos
    _ = Nat.card G := h2

/-- The conclusion of Theorem B lifts through the odd core. -/
theorem benderConclusion_of_quotient {G : Type} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (hN : N = oddCore G)
    (hbot : oddCore (G ⧸ N) = ⊥)
    (h : BenderConclusion (G ⧸ N)) :
    BenderConclusion G := by
  obtain ⟨M, hMnorm, hMcore, hMindex, Y, hYgrp, ψ, hψsurj, hψker, hYsimple⟩ := h
  letI := hYgrp
  -- the preimage of `M` in `G`, and the induced map `L →* M`
  let L : Subgroup G := M.comap (QuotientGroup.mk' N)
  have hLnorm : L.Normal := hMnorm.comap _
  have hNL : N ≤ L := by
    intro x hx
    rw [Subgroup.mem_comap]
    have : (QuotientGroup.mk' N) x = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hx
    rw [this]
    exact M.one_mem
  let g : ↥L →* ↥M :=
    { toFun := fun x => ⟨(QuotientGroup.mk' N) ((x : ↥L) : G), Subgroup.mem_comap.mp x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp [map_mul]) }
  have hψker_bot : ψ.ker = ⊥ := by
    rw [hψker]
    show (oddCore (G ⧸ N)).subgroupOf M = ⊥
    rw [hbot]
    simp
  have gsurj : Function.Surjective g := by
    intro y
    obtain ⟨w, hw⟩ := QuotientGroup.mk'_surjective N (y : G ⧸ N)
    have hwL : w ∈ L := by
      rw [Subgroup.mem_comap]
      rw [hw]
      exact y.2
    refine ⟨⟨w, hwL⟩, Subtype.ext ?_⟩
    show (QuotientGroup.mk' N) w = ((y : ↥M) : G ⧸ N)
    exact hw
  refine ⟨L, hLnorm, ?_, ?_, Y, hYgrp, ψ.comp g, hψsurj.comp gsurj, ?_, hYsimple⟩
  · -- `O(G) ≤ L`
    intro x hx
    exact hNL (hN ▸ hx)
  · -- `|G : L|` is odd
    show Odd (Subgroup.comap (QuotientGroup.mk' N) M).index
    rw [Subgroup.index_comap_of_surjective M (QuotientGroup.mk'_surjective N)]
    exact hMindex
  · -- the kernel of `L → M → Y` is `O(G)`
    show (ψ.comp g).ker = (oddCore G).subgroupOf L
    ext x
    constructor
    · intro hx
      have hx2 : g x ∈ ψ.ker := by
        rw [MonoidHom.mem_ker]
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
        exact hx
      rw [hψker_bot, Subgroup.mem_bot] at hx2
      have h3 : (QuotientGroup.mk' N) ((x : ↥L) : G) = 1 := congrArg Subtype.val hx2
      rw [Subgroup.mem_subgroupOf, ← hN]
      exact (QuotientGroup.eq_one_iff ((x : ↥L) : G)).mp
        (by simpa only [QuotientGroup.mk'_apply] using h3)
    · intro hx
      rw [Subgroup.mem_subgroupOf, ← hN] at hx
      have h3 : ((x : ↥L) : G) ∈ N := hx
      have h4 : (((x : ↥L) : G) : G ⧸ N) = 1 := (QuotientGroup.eq_one_iff _).mpr h3
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hψker_bot,
        Subgroup.mem_bot]
      exact Subtype.ext h4

end Work.Reductions
