import Mathlib
import Submission.Work.PSU3.StageB.Step1
import Submission.Work.PSU3.StageB.SemiregVendored
import Submission.Work.PSU3.StageA.lemma2cAux
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.ThmF.ChV12.Q0sub_elementary
import Submission.Work.ThmF.Setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.PSU3.StageB

/-
# The involutions of `F ⊓ H`, `F = O^{2'}(C_G(P))` (input to Peterfalvi II.7.4(1))

The number of involutions of `F ⊓ H` is `|C_{Q₀}(P)| - 1`, i.e.

  `#Inv(F ⊓ H) + 1 = |Q0sub H ⊓ C_G(P)|`.

This is the ambient half of the transfer that makes `#Inv(B_Y) + 1 = ℓ` for the Borel `B_Y` of
`Y = F/Z(F)` (`ℓ = |C_{Q₀}(P)|`), which is what pins down the model index in step 5 of the
reduction.

Proof.  Both inclusions are elementary, using `Q0sub H = Ω₁(Q)` (involutions of `H` lie in `Q`
because `|H : Q| = |D|` is odd; conversely every element of `Q0sub H` other than `1` is an
involution of `H`, by `Work.ThmF.ChV12.Q0sub_elementary`, whose commutativity input comes from
`ChIIFourProp` + the situation):
* an involution `x ∈ F ⊓ H` is an involution of `H`, hence lies in `Q` and in `Ω₁(Q) = Q0sub H`,
  and `F ≤ C_G(P)` puts it in `C_G(P)`;
* conversely `x ∈ Q0sub H ⊓ C_G(P)`, `x ≠ 1`, is an involution of `H ⊆ G` and a `2`-element of
  `C_G(P)`, hence lies in `O^{2'}(C_G(P)) = F` and in `H`.
-/
theorem ncard_involutions_inf_H {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    {P : Subgroup G} (hPV : P ≤ Submission.Blueprint.centD H t) :
    (Submission.Blueprint.involutions
        ((Work.PSU3.StageB.centralizerOddResidual P ⊓ H : Subgroup G) : Set G)).ncard + 1
      = Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G)) := by
  classical
  -- `F = O^{2'}(C_G(P))` is contained in `C_G(P)`
  have hFle : Work.PSU3.StageB.centralizerOddResidual P ≤ Subgroup.centralizer (P : Set G) :=
    Subgroup.map_subtype_le _
  -- `Q₀ = Q0sub H = Ω₁(Q)`: squares are `1`, and every `x ≠ 1` is an involution
  have hQ0 := Work.PSU3.StageA.V_Q0sub_structure hS hC4
  -- **The two sets differ exactly by the identity**: `Inv(F ⊓ H) = (Q0sub H ⊓ C_G(P)) ∖ {1}`
  have hset : Submission.Blueprint.involutions
        ((Work.PSU3.StageB.centralizerOddResidual P ⊓ H : Subgroup G) : Set G)
      = ((Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) : Set G) \ {1} := by
    ext x
    constructor
    · -- an involution of `F ⊓ H` is an involution of `H`, hence lies in `Q₀`, and in `C_G(P)`
      intro hx
      obtain ⟨hxF, hxH⟩ := Subgroup.mem_inf.mp hx.1
      refine (Set.mem_sdiff x).mpr ⟨Subgroup.mem_inf.mpr ⟨?_, hFle hxF⟩, ?_⟩
      · exact Work.ThmF.Q0_le_Q0sub H (Work.ThmF.mem_Q0_iff.mpr (Or.inl ⟨hxH, hx.2⟩))
      · intro h1
        rw [h1] at hx
        simp [Submission.Blueprint.involutions] at hx
    · -- conversely `x ∈ Q₀ ⊓ C_G(P)`, `x ≠ 1`, is an involution of `H` and a `2`-element
      intro hx
      rw [Set.mem_sdiff, Set.mem_singleton_iff] at hx
      obtain ⟨⟨hxQ0, hxC⟩, hxne⟩ := hx
      obtain ⟨hxH, hx2⟩ := hQ0.2.2.2 x hxQ0 hxne
      refine ⟨Subgroup.mem_inf.mpr ⟨?_, hxH⟩, hx2⟩
      -- `x` is a `2`-element of `C_G(P)`, hence lies in `O^{2'}(C_G(P)) = F`
      rw [Work.PSU3.StageB.centralizerOddResidual]
      refine Subgroup.mem_map.mpr ⟨⟨x, hxC⟩, ?_, rfl⟩
      exact Work.PSU3.StageA.mem_oddResidual_of_pow_two_eq_one (k := 1) (by
        apply Subtype.ext
        simpa [pow_two] using hQ0.1 x hxQ0)
  rw [hset]
  -- counting: `(S \ {1}).ncard + 1 = S.ncard = |S|`
  have h1S : (1 : G) ∈ (Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) :=
    ⟨(Work.ThmF.Q0sub H).one_mem, (Subgroup.centralizer (P : Set G)).one_mem⟩
  have hcardS : Nat.card ↥(Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G) : Subgroup G)
      = ((Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) : Set G).ncard :=
    Nat.card_coe_set_eq _
  rw [Set.ncard_sdiff_singleton_of_mem h1S, hcardS]
  exact Nat.sub_add_cancel ((Set.ncard_pos (Set.toFinite _)).mpr ⟨1, h1S⟩)

end Work.PSU3.StageB
