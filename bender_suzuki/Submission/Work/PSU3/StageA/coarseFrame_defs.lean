import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.Setup
import Submission.Work.PSU3.GaloisField
import Submission.Work.PSU3.StageB.Frame
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.ThmF.ChV12.corProp2
import Submission.Work.ThmF.ChV12.conj_action_data
import Submission.Work.ThmF.Bender.cardInvGeTwo
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.mem_of_sq_eq_one_of_odd_index

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.PSU3.StageA

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-- `Q₀ = ⟨Inv H⟩` is contained in `Q`: the involutions of `H` are `2`-elements, and
`H = Q ⋊ D` with `D` of odd order, so `Q` (a normal Sylow `2`-subgroup of `H`) contains every
`2`-element of `H`. -/
theorem Q0sub_le_Q {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) : Work.ThmF.Q0sub H ≤ Q := by
  rw [Work.ThmF.Q0sub]
  refine (Subgroup.closure_le _).mpr ?_
  intro x hx
  rw [Work.ThmF.mem_Q0_iff] at hx
  rcases hx with ⟨hxH, hx2⟩ | rfl
  · haveI : (Q.subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff (show Q ≤ H from h.le)).mpr
        (fun a b ha hb => (Subgroup.mem_normalizer_iff.mp (h.normal hb) a).mp ha)
    have hodd : Odd (Q.subgroupOf H).index := by
      have h1 : Nat.card ↥(Q.subgroupOf H) * (Q.subgroupOf H).index = Nat.card H :=
        Subgroup.card_mul_index _
      have h2 : Nat.card ↥(Q.subgroupOf H) = Nat.card Q :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le).toEquiv
      have h3 : Nat.card H = Nat.card Q * Nat.card ↥(twoPoint H t) :=
        Work.ThmF.card_H_eq_mul_of_data (Work.ThmF.IsSplitRankOne.toData h)
      have hpos : 0 < Nat.card Q := Nat.card_pos
      have h4 : (Q.subgroupOf H).index = Nat.card ↥(twoPoint H t) := by
        have h5 : Nat.card Q * (Q.subgroupOf H).index =
            Nat.card Q * Nat.card ↥(twoPoint H t) := by
          calc Nat.card Q * (Q.subgroupOf H).index
              = Nat.card ↥(Q.subgroupOf H) * (Q.subgroupOf H).index := by rw [h2]
            _ = Nat.card H := h1
            _ = Nat.card Q * Nat.card ↥(twoPoint H t) := h3
        exact Nat.eq_of_mul_eq_mul_left hpos h5
      rw [h4]
      exact Work.ThmF.split_odd_card_twoPoint h
    have hx22 : x * x = 1 := by
      have hp := pow_orderOf_eq_one x
      rw [hx2] at hp
      simpa [pow_two] using hp
    have hsq : (⟨x, hxH⟩ : H) * ⟨x, hxH⟩ = 1 := Subtype.ext hx22
    have hmem : (⟨x, hxH⟩ : H) ∈ Q.subgroupOf H :=
      Commons.GroupTheory.Subgroup.mem_of_sq_eq_one_of_odd_index (Q.subgroupOf H) hodd hsq
    exact hmem
  · exact Q.one_mem

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- Conjugation of `Q₀ = ⟨Inv H⟩` by an element of `K = Ksub H t ≤ H` (which normalises `Q₀`). -/
noncomputable def conjQ0 (H : Subgroup G) (t : G) (k : ↥(Work.ThmF.Ksub H t))
    (y : ↥(Work.ThmF.Q0sub H)) : ↥(Work.ThmF.Q0sub H) :=
  ⟨(k : G) * (y : G) * (k : G)⁻¹,
    ((Subgroup.mem_normalizer_iff.mp
      (Work.ThmF.ChV12.H_le_normalizer_Q0sub H
        ((Work.ThmF.Ksub_le_twoPoint (H := H) t).trans inf_le_left k.2)))
        (y : G)).mp y.2⟩

@[simp] theorem conjQ0_coe (k : ↥(Work.ThmF.Ksub H t)) (y : ↥(Work.ThmF.Q0sub H)) :
    ((conjQ0 H t k y : ↥(Work.ThmF.Q0sub H)) : G) = (k : G) * (y : G) * (k : G)⁻¹ := rfl

/-- Conjugation of `Q` by an element of `H` (recall `Q ⊴ H`). -/
noncomputable def conjQ (h : IsSplitRankOne H Q t) (g : G) (hg : g ∈ H) (x : ↥Q) : ↥Q :=
  ⟨g * (x : G) * g⁻¹, (Subgroup.mem_normalizer_iff.mp (h.normal hg) (x : G)).mp x.2⟩

@[simp] theorem conjQ_coe (h : IsSplitRankOne H Q t) (g : G) (hg : g ∈ H) (x : ↥Q) :
    ((conjQ h g hg x : ↥Q) : G) = g * (x : G) * g⁻¹ := rfl

/-- Conjugation action of `K = Ksub H t` on `Q` (via its inclusion into `H`). -/
noncomputable def conjQK (h : IsSplitRankOne H Q t) (k : ↥(Work.ThmF.Ksub H t))
    (x : ↥Q) : ↥Q :=
  conjQ h (k : G) ((Work.ThmF.Ksub_le_twoPoint (H := H) t).trans inf_le_left k.2) x

@[simp] theorem conjQK_coe (h : IsSplitRankOne H Q t) (k : ↥(Work.ThmF.Ksub H t)) (x : ↥Q) :
    ((conjQK h k x : ↥Q) : G) = (k : G) * (x : G) * (k : G)⁻¹ := rfl

/-- **The field and module data of the case-c configuration.**

`F` is a field of order `q = |Q₀|`; `phi` identifies `Q₀` additively with `(F, +)` in such a way
that `K = Ksub H t` acts by multiplication through `rho`; and `psi` identifies the elementary
abelian quotient `Q/Q₀` additively with `F × F` in such a way that `K` acts by the scalars
`Lam`.  (This is the content of Peterfalvi II, Ch. V §1 Prop. 3 together with Lemma 6: `Q₀` is a
`1`-dimensional `F_q`-space on which `K ≅ F_q^*` acts by homotheties, and `Q/Q₀` is a
`2`-dimensional `F_q`-space on which `K` acts by scalars.) -/
structure CaseCModuleData (H Q : Subgroup G) (t : G) where
  /-- `H = Q ⋊ D` is a split rank-one datum. -/
  hsplit : IsSplitRankOne H Q t
  /-- The field `F_q`. -/
  F : Type
  instField : Field F
  instFintype : Fintype F
  /-- `|F| = |Q₀|`. -/
  cardF : Nat.card F = Nat.card ↥(Work.ThmF.Q0sub H)
  /-- The additive identification `Q₀ ≅ (F,+)`. -/
  phi : ↥(Work.ThmF.Q0sub H) → F
  phi_bij : Function.Bijective phi
  phi_add : ∀ a b : ↥(Work.ThmF.Q0sub H), phi (a * b) = phi a + phi b
  /-- The character by which `K` acts on `Q₀ ≅ F`. -/
  rho : ↥(Work.ThmF.Ksub H t) →* Fˣ
  phi_conj : ∀ (k : ↥(Work.ThmF.Ksub H t)) (y : ↥(Work.ThmF.Q0sub H)),
    phi (conjQ0 H t k y) = (rho k : F) * phi y
  /-- The additive identification `Q/Q₀ ≅ F × F`. -/
  psi : ↥Q → F × F
  psi_add : ∀ a b : ↥Q, psi (a * b) = psi a + psi b
  psi_ker : ∀ x : ↥Q, psi x = 0 ↔ (x : G) ∈ Work.ThmF.Q0sub H
  psi_surj : Function.Surjective psi
  /-- The scalars by which `K` acts on `Q/Q₀ ≅ F × F`. -/
  Lam : ↥(Work.ThmF.Ksub H t) →* Fˣ
  Lam_injective : Function.Injective Lam
  psi_conj : ∀ (k : ↥(Work.ThmF.Ksub H t)) (x : ↥Q),
    psi (conjQK hsplit k x) = ((Lam k : F) * (psi x).1, (Lam k : F) * (psi x).2)

end Work.PSU3.StageA
