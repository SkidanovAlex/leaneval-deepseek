import Mathlib
import Submission.Blueprint.Interfaces
import Submission.Work.Reductions.Defs
import Submission.Work.Reductions.OddResidual
import Submission.Work.Reductions.Quotient
import Submission.Work.Reductions.hasFourGroup_quotient
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.BrauerSuzuki.OddCore.oddCard_oddCore
import Submission.Work.ThreePoints.oddCore_le_of_stronglyEmbedded
import Submission.Work.ThreePoints.isStronglyEmbedded_map_quotient
import Submission.Work.ThreePoints.oddCore_quotient_oddCore
import Submission.Work.ThreePoints.isStronglyEmbedded_inf_subgroupOf
import Submission.Work.ThreePoints.hasFourGroupIn_of_odd_index

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The reductions of Theorem B

* `benderConclusion_of_oddCore_ne_bot` (`O(G) ≠ 1`): apply the induction hypothesis to
  `G ⧸ O(G)` and lift the result.
* `benderConclusion_of_oddResidual_ne_top` (`O(G) = 1`, `O^{2'}(G) ≠ G`): apply the induction
  hypothesis to `O^{2'}(G)`; every involution of `G` lies in `O^{2'}(G)`, and `O^{2'}` is
  idempotent, so the subgroup found in `O^{2'}(G)` is all of it.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Submission.Blueprint
open LeanEval.GroupTheory.Defs

namespace Work.Reductions

/-- Case (1) of the reduction: `O(G) ≠ 1`. -/
theorem benderConclusion_of_oddCore_ne_bot {G : Type} [Group G] [Finite G]
    (hFT : FeitThompsonProp) (hfour : HasFourGroup G) {H : Subgroup G}
    (hH : IsStronglyEmbedded H) (hB : ThmBBelow (Nat.card G))
    (hne : oddCore G ≠ ⊥) : BenderConclusion G := by
  have hNodd : Odd (Nat.card (oddCore G)) := Work.BrauerSuzuki.OddCore.oddCard_oddCore
  exact benderConclusion_of_quotient (oddCore G) rfl
    (Work.ThreePoints.oddCore_quotient_oddCore)
    (hB (G ⧸ oddCore G) (card_quotient_lt (oddCore G) hne)
      ⟨hasFourGroup_quotient (oddCore G) hfour hNodd,
        ⟨_, Work.ThreePoints.isStronglyEmbedded_map_quotient (oddCore G) hNodd
          (Work.ThreePoints.oddCore_le_of_stronglyEmbedded hH hfour) hH⟩⟩)

/-- Case (2) of the reduction: `O(G) = 1` and `O^{2'}(G) ≠ G`. -/
theorem benderConclusion_of_oddResidual_ne_top {G : Type} [Group G] [Finite G]
    (hFT : FeitThompsonProp) (hA : ThmAProp) (hfour : HasFourGroup G) {H : Subgroup G}
    (hH : IsStronglyEmbedded H) (hB : ThmBBelow (Nat.card G)) (hc : oddCore G = ⊥)
    (hr : oddResidual G ≠ ⊤) : BenderConclusion G := by
  have hLnorm : (oddResidual G).Normal := oddResidual_basic.1
  haveI := hLnorm
  have hLodd : Odd (oddResidual G).index := oddResidual_basic.2.1
  -- `O^{2'}(G) ⊄ H`: an involution of `H` would lie in `H ⊓ xHx⁻¹` for `x ∉ H`
  have hnotle : ¬ oddResidual G ≤ H := by
    intro hle
    obtain ⟨g, hg⟩ : ∃ g : G, g ∉ H := by
      by_contra h
      push_neg at h
      refine hH.1 (by ext x; exact ⟨fun _ => Subgroup.mem_top x, fun _ => h x⟩)
    have hodd := hH.2.2 g hg
    have hinv : ∃ t : G, t ∈ H ∧ orderOf t = 2 := by
      have h2 : 2 ∣ Nat.card ↥H := even_iff_two_dvd.mp hH.2.1
      obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 (G := ↥H) h2
      exact ⟨(t : G), t.2, by simpa using (Subgroup.orderOf_coe t).trans ht⟩
    obtain ⟨t, htH, ht2⟩ := hinv
    have htL : t ∈ oddResidual G :=
      oddResidual_basic.2.2.2 t (by
        have h := pow_orderOf_eq_one t
        rw [ht2] at h
        simpa [pow_two] using h)
    have hLg : oddResidual G ≤ conj g H := by
      have hfix : (oddResidual G).map (MulAut.conj g).toMonoidHom = oddResidual G :=
        Subgroup.normal_iff_map_conj_eq.mp hLnorm g
      calc oddResidual G = (oddResidual G).map (MulAut.conj g).toMonoidHom := hfix.symm
        _ ≤ H.map (MulAut.conj g).toMonoidHom := Subgroup.map_mono hle
    have htmem : t ∈ H ⊓ conj g H := ⟨hle htL, hLg htL⟩
    have h2dvd : 2 ∣ Nat.card ↥(H ⊓ conj g H) := by
      have h := orderOf_dvd_natCard (⟨t, htmem⟩ : ↥(H ⊓ conj g H))
      rwa [Subgroup.orderOf_mk, ht2] at h
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2dvd)
  have hstrong : IsStronglyEmbedded ((H ⊓ oddResidual G).subgroupOf (oddResidual G)) :=
    Work.ThreePoints.isStronglyEmbedded_inf_subgroupOf hH hLnorm hLodd hnotle
  have hfourL : HasFourGroup ↥(oddResidual G) :=
    (Work.ThreePoints.hasFourGroupIn_of_odd_index hLodd hfour).to_subgroup
  have hcard : Nat.card ↥(oddResidual G) < Nat.card G := by
    simpa using Subgroup.card_lt_of_lt (H := oddResidual G) (K := (⊤ : Subgroup G))
      (lt_top_iff_ne_top.mpr hr)
  obtain ⟨M, hMnorm, hMcore, hMindex, Y, hYgrp, ψ, hψsurj, hψker, hYsimple⟩ :=
    hB ↥(oddResidual G) hcard ⟨hfourL, ⟨_, hstrong⟩⟩
  -- `O^{2'}` is idempotent, so the subgroup produced by (B1) in `O^{2'}(G)` is all of it
  have hres := (oddCore_oddResidual_basic hc).2
  have hMtop : M = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← hres]
    exact oddResidual_basic.2.2.1 M hMnorm hMindex
  have hker : ψ.ker = ⊥ := by
    rw [hψker, (oddCore_oddResidual_basic hc).1]
    simp
  have hmem : ∀ x : ↥(oddResidual G), x ∈ M := fun x => hMtop.symm ▸ Subgroup.mem_top x
  letI := hYgrp
  let φ : ↥(oddResidual G) →* Y :=
    { toFun := fun x => ψ ⟨x, hmem x⟩
      map_one' := by
        rw [show (⟨1, hmem 1⟩ : ↥M) = 1 from Subtype.ext rfl]
        simp
      map_mul' := fun a b => by
        rw [show (⟨a * b, hmem (a * b)⟩ : ↥M)
            = (⟨a, hmem a⟩ : ↥M) * (⟨b, hmem b⟩ : ↥M) from Subtype.ext rfl]
        exact map_mul ψ _ _ }
  refine ⟨oddResidual G, hLnorm, hc ▸ bot_le, hLodd, Y, hYgrp, φ, ?_, ?_, hYsimple⟩
  · -- surjectivity
    intro y
    obtain ⟨z, hz⟩ := hψsurj y
    have hz' : (⟨z.1, hmem z.1⟩ : ↥M) = z := Subtype.ext rfl
    refine ⟨z.1, ?_⟩
    calc φ z.1 = ψ ⟨z.1, hmem z.1⟩ := rfl
      _ = ψ z := congrArg ψ hz'
      _ = y := hz
  · -- the kernel is `O(G)`, which is trivial here
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have hx1 : (⟨x, hmem x⟩ : ↥M) ∈ ψ.ker := by
        rw [MonoidHom.mem_ker]
        simpa [φ] using hx
      rw [hker, Subgroup.mem_bot] at hx1
      rw [hc, Subgroup.mem_subgroupOf, Subgroup.mem_bot]
      exact congrArg (fun z : ↥M => (((z.1 : ↥(oddResidual G)) : G))) hx1
    · intro hx
      rw [hc, Subgroup.mem_subgroupOf, Subgroup.mem_bot] at hx
      show φ x = 1
      have hxL : x = 1 := Subtype.ext hx
      rw [show φ x = ψ ⟨x, hmem x⟩ from rfl]
      rw [show (⟨x, hmem x⟩ : ↥M) = 1 from Subtype.ext hxL]
      simp

end Work.Reductions
