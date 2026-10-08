import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.ChV12.Ksub_cyclic_normal
import Submission.Work.ThmF.ChV12.prop3
import Submission.Work.ThmF.ChV12.prop3_card_fixed_pow
import Submission.Work.PSU3.StageA.centD_ne_bot
import Submission.Work.PSU3.StageA.distinguished_exists
import Submission.Work.PSU3.StageA.twoPoint_eq_Kset_mul_centD
import Submission.Work.PSU3.StageA.W_centralizes_Q0sub
import Submission.Work.PSU3.StageA.centD_eq_centralizer_s
import Submission.Work.PSU3.StageA.galois_step_of_Ksub

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.StageA.caseWbot_branch_three_false`

Branch (iii) of Ch. V §2 Lemma 2c is *impossible* in the branch `W = ⊥` of Peterfalvi II
Ch. VI §1.  In the notation of that lemma (`C = Q ⊓ C_G(P)`, `ℓ = |Q0sub H ⊓ C_G(P)|`) the
third alternative reads

  `orderOf (s*t) = 3`, `|C| = ℓ³`, and there is `x ∈ D ⊓ C_G(P)`, `x ∉ P`, commuting with every
  element of `C_{Q₀}(P) = Q0sub H ⊓ C_G(P)`.

The requested statement isolates exactly the *last* clause, stripped of the arithmetic
hypotheses on `C`: given `P ≤ V = centD H t` of prime order, no such `x` exists when
`W H t = ⊥`.

## The argument

`FeitThompsonProp` and `ChIIFourProp` give Peterfalvi II Ch. V §1 Prop. 2
(`Work.ThmF.ChV12.Ksub_cyclic_normal`): `K = J(D,t)` is a *cyclic normal* subgroup of `D`
whose underlying set is `Kset H t = {y ∈ D | t y t⁻¹ = y⁻¹}`.

Let `s` be the distinguished involution of the structure identity
(`Work.PSU3.StageA.distinguished_exists`), so that Ch. V §2 Lemma 3 a) identifies

  `V = centD H t = D ⊓ C_G(s)`   (`Work.PSU3.StageA.centD_eq_centralizer_s`).

Since `P ≤ V = D ⊓ C_G(s)`, every `y ∈ P` commutes with `s`, i.e. `s ∈ C_G(P)`, and
`s ∈ Q0sub H` (it is an involution of `H`).  Hence `s ∈ C_{Q₀}(P)`, so the element `x` of the
statement commutes with `s`; together with `x ∈ D` this puts `x ∈ D ⊓ C_G(s) = V`.

Now the Galois step of Ch. V §1 Prop. 3 (`Work.PSU3.StageA.galois_step_of_Ksub`): `Q₀` is the
additive group of a finite field `F` on which `V` acts by field automorphisms with kernel `W`.
An element of `V` fixing the fixed field of the image of `P` (`= C_{Q₀}(P)`, Ch. V §1 Prop. 3)
lies in `P · W` by Artin's theorem.  Since `W = ⊥` this gives `x ∈ P` — contradicting `x ∉ P`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.PSU3.StageA

theorem caseWbot_branch_three_false {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hFT : Submission.Blueprint.FeitThompsonProp)
    (hW : Work.ThmF.W H t = ⊥)
    {P : Subgroup G} (hP : P ≤ Submission.Blueprint.centD H t) (hp : (Nat.card P).Prime) :
    ¬ ∃ x ∈ Submission.Blueprint.twoPoint H t ⊓ Subgroup.centralizer (P : Set G), x ∉ P ∧
      ∀ z ∈ Work.ThmF.Q0sub H ⊓ Subgroup.centralizer (P : Set G), x * z = z * x := by
  classical
  -- ## Ch. V §1 Prop. 2 (with `FeitThompsonProp`): `K = J(D,t)` is cyclic and equals `Kset H t`
  obtain ⟨hKcyc, hKsub, -⟩ :=
    Work.ThmF.ChV12.Ksub_cyclic_normal hFT hC4 hS.situation hS.split
  rintro ⟨x, hxmem, hxnotP, hxfix⟩
  -- ## the distinguished involution `s` and the identity `V = D ⊓ C_G(s)`
  obtain ⟨s, hsQ, hs2, r, hrQ, hsr⟩ := Work.PSU3.StageA.distinguished_exists hS
  have hV : Submission.Blueprint.centD H t =
      Submission.Blueprint.twoPoint H t ⊓ Subgroup.centralizer ({s} : Set G) :=
    Work.PSU3.StageA.centD_eq_centralizer_s hS hsQ hs2 hrQ hsr
  -- ## `s ∈ C_G(P)`, because every `y ∈ P ≤ V = D ⊓ C_G(s)` commutes with `s`
  have hsC : s ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyV : y ∈ Submission.Blueprint.centD H t := hP hy
    rw [hV] at hyV
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hyV).2
  -- ## `s ∈ Q₀ = ⟨Inv H⟩`
  have hsQ0 : s ∈ Work.ThmF.Q0sub H :=
    Work.ThmF.Q0_le_Q0sub H (Work.ThmF.involutions_subset_Q0 H ⟨hS.split.le hsQ, hs2⟩)
  -- ## hence `x` commutes with `s`, and `x ∈ V`
  have hxs : x * s = s * x := hxfix s ⟨hsQ0, hsC⟩
  have hxV : x ∈ Submission.Blueprint.centD H t := by
    rw [hV]
    exact ⟨(Subgroup.mem_inf.mp hxmem).1, Subgroup.mem_centralizer_singleton_iff.mpr hxs⟩
  -- ## the Galois step: `P ⊓ W = ⊥`, so an element of `V` fixing `C_{Q₀}(P)` lies in `P · W = P`
  have hPW : P ⊓ Work.ThmF.W H t = ⊥ := by rw [hW, inf_bot_eq]
  obtain ⟨p, hpP, w, hwW, hxeq⟩ :=
    Work.PSU3.StageA.galois_step_of_Ksub hS hC4 hKsub hKcyc hP hPW x hxV
      (fun z hz hzc => hxfix z ⟨hz, hzc⟩)
  rw [hW] at hwW
  have hw1 : w = 1 := Subgroup.mem_bot.mp hwW
  exact hxnotP (by rw [hxeq, hw1, mul_one]; exact hpP)

end Work.PSU3.StageA
