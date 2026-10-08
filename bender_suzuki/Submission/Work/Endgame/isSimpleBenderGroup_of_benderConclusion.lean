import Submission.Work.Endgame.Defs
import Submission.Work.Endgame.oddCore_eq_bot_of_isSimpleGroup_of_even

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Reading `IsSimpleBenderGroup` off the conclusion of Theorem B

`BenderConclusion G` provides a normal `L ⊴ G` with `O(G) ≤ L`, `|G : L|` odd, and a surjection
`L ↠ Y` with kernel `O(G)` and `Y` a simple Bender group.  In a simple group `G` of even order,
`L` cannot be trivial (a nontrivial `Y` would surject onto it) so `L = ⊤` by simplicity, and
`O(G) = ⊥`, so the surjection becomes an isomorphism `G ≃* Y`; the statement follows from
invariance of `IsSimpleBenderGroup` under isomorphism.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.Endgame

/-- The *only* use of the model facts in the endgame: a Bender group is nontrivial (it carries a
four-group), so a nontrivial group cannot be a quotient of the trivial group. -/
theorem nontrivial_of_modelFacts (hMod : ModelFactsProp) {Y : Type} [Group Y] [Finite Y]
    (h : IsSimpleBenderGroup Y) : Nontrivial Y := by
  obtain ⟨a, b, ha, hb, hne, hcomm⟩ := (hMod Y h).2.1
  exact ⟨a, 1, fun hcon => by
    rw [hcon, orderOf_one] at ha
    exact absurd ha (by norm_num)⟩

theorem isSimpleBenderGroup_of_benderConclusion (hMod : ModelFactsProp) {G : Type} [Group G]
    [Finite G] [IsSimpleGroup G] (h : BenderConclusion G) (heven : Even (Nat.card G)) :
    IsSimpleBenderGroup G := by
  obtain ⟨L, hLnorm, hcoreL, hLidx, Y, hYgrp, φ, hφsurj, hφker, hY⟩ := h
  letI : Group Y := hYgrp
  haveI : Finite Y := Finite.of_surjective φ hφsurj
  haveI : Nontrivial Y := nontrivial_of_modelFacts hMod hY
  -- `L` is nontrivial, because a nontrivial group cannot be a quotient of `⊥`
  have hLne : L ≠ ⊥ := by
    intro hbot
    haveI : Nontrivial ↥L := hφsurj.nontrivial
    rw [Subgroup.nontrivial_iff_ne_bot] at this
    exact this hbot
  have hLtop : L = ⊤ := by
    rcases hLnorm.eq_bot_or_eq_top with hb | ht
    · exact absurd hb hLne
    · exact ht
  subst hLtop
  have hcore : oddCore G = ⊥ := oddCore_eq_bot_of_isSimpleGroup_of_even heven
  have hker : φ.ker = ⊥ := by
    rw [hφker, hcore, Subgroup.subgroupOf_eq_bot, disjoint_top]
  have hinj : Function.Injective φ := MonoidHom.ker_eq_bot_iff φ |>.mp hker
  have e : ↥(⊤ : Subgroup G) ≃* Y := MulEquiv.ofBijective φ ⟨hinj, hφsurj⟩
  have e' : G ≃* Y := Subgroup.topEquiv.symm.trans e
  exact IsSimpleBenderGroup.of_mulEquiv hY e'.symm

end Work.Endgame
