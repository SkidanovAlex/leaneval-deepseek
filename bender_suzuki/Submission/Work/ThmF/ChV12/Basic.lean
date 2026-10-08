import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.Bender.Basic
import Submission.Work.ThmF.Bender.cardInvertedMulCardCentralizer

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Chapter V: elementary consequences of the split rank-one data

These are the trivial-but-necessary translations between the vocabulary of `Setup.lean` and the
source (`K = J(D,t) ⊆ D`, `|V| |K| = |D|`, `|H| = |Q| |D|`, `Q` of even order, `Q₀` elementary
abelian).  Everything here is stated for `IsSplitRankOneData`, so it applies both to `G` itself
and to the subgroup `C_G(P)` used in §3.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ThmF

open Submission.Blueprint

variable {G : Type*} [Group G]

/-! ## `K ⊆ D`, `V ⊆ D` -/

theorem Kset_le_twoPoint {H : Subgroup G} (t : G) : Kset H t ⊆ twoPoint H t :=
  Kset_subset H t

theorem Ksub_le_twoPoint {H : Subgroup G} (t : G) : Ksub H t ≤ twoPoint H t :=
  (Subgroup.closure_le _).mpr (Kset_subset H t)

theorem centD_le_twoPoint {H : Subgroup G} (t : G) : centD H t ≤ twoPoint H t :=
  fun _ hx => (Subgroup.mem_inf.mp hx).1

/-! ## `Q₀` is an elementary abelian 2-group when `Inv(H)` commutes -/

theorem Q0_elementary {H : Subgroup G}
    (hcomm : ∀ u ∈ involutions (H : Set G), ∀ v ∈ involutions (H : Set G), u * v = v * u) :
    (∀ u ∈ Q0 H, ∀ v ∈ Q0 H, u * v = v * u) ∧ (∀ u ∈ Q0 H, u ^ 2 = 1) := by
  constructor
  · intro u hu v hv
    rcases mem_Q0_iff.mp hu with ⟨huH, hu2⟩ | rfl
    · rcases mem_Q0_iff.mp hv with ⟨hvH, hv2⟩ | rfl
      · exact hcomm u ⟨huH, hu2⟩ v ⟨hvH, hv2⟩
      · rw [mul_one, one_mul]
    · rw [one_mul, mul_one]
  · intro u hu
    rcases mem_Q0_iff.mp hu with ⟨-, hu2⟩ | rfl
    · have h1 := pow_orderOf_eq_one u
      rw [hu2] at h1
      simpa using h1
    · exact one_pow 2

/-! ## `|H| = |Q| * |D|` and parity -/

section Data

variable {H Q : Subgroup G} {t : G}

theorem card_H_eq_mul_of_data (h : IsSplitRankOneData G H Q t) :
    Nat.card H = Nat.card Q * Nat.card (twoPoint H t) := by
  have hle : twoPoint H t ≤ Subgroup.normalizer (Q : Set G) :=
    fun _ hx => h.normal (Subgroup.mem_inf.mp hx).1
  have hbij : Function.Bijective
      (fun p : (twoPoint H t) × Q =>
        (⟨(p.1 : G) * (p.2 : G),
          H.mul_mem (Subgroup.mem_inf.mp p.1.2).1 (h.le p.2.2)⟩ : H)) := by
    constructor
    · intro p q hpq
      have hval : (p.1 : G) * (p.2 : G) = (q.1 : G) * (q.2 : G) := by
        simpa using congrArg (fun z : H => (z : G)) hpq
      have h5 : (q.1 : G) = (p.1 : G) * (p.2 : G) * (q.2 : G)⁻¹ := by
        have := congrArg (fun z => z * (q.2 : G)⁻¹) hval
        simpa [mul_assoc] using this.symm
      have hmem : (p.1 : G)⁻¹ * (q.1 : G) ∈ twoPoint H t ⊓ Q := by
        refine ⟨(twoPoint H t).mul_mem ((twoPoint H t).inv_mem p.1.2) q.1.2, ?_⟩
        have : (p.1 : G)⁻¹ * (q.1 : G) = (p.2 : G) * (q.2 : G)⁻¹ := by rw [h5]; group
        rw [this]
        exact Q.mul_mem p.2.2 (Q.inv_mem q.2.2)
      rw [inf_comm, h.inf_eq, Subgroup.mem_bot] at hmem
      have h1 : (q.1 : G) = (p.1 : G) := by
        have := congrArg (fun z => (p.1 : G) * z) hmem
        simpa using this
      have h2 : (q.2 : G) = (p.2 : G) := by
        have h8 : (p.1 : G) * ((p.2 : G) * (q.2 : G)⁻¹) = (p.1 : G) * 1 := by
          rw [mul_one, ← mul_assoc, h5.symm, h1]
        have h9 : (p.2 : G) * (q.2 : G)⁻¹ = 1 := mul_left_cancel h8
        have h10 : (p.2 : G) = (q.2 : G) := by
          have h11 := congrArg (fun z => z * (q.2 : G)) h9
          simpa [mul_assoc] using h11
        exact h10.symm
      exact Prod.ext (Subtype.ext h1.symm) (Subtype.ext h2.symm)
    · intro x
      have hx' : (x : G) ∈ (↑(twoPoint H t ⊔ Q) : Set G) := by
        rw [sup_comm, h.sup_eq]; exact x.2
      rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle] at hx'
      rw [Set.mem_mul] at hx'
      obtain ⟨d, hd, q, hq, hdq⟩ := hx'
      exact ⟨(⟨d, hd⟩, ⟨q, hq⟩), Subtype.ext hdq⟩
  have hcard : Nat.card H = Nat.card ((twoPoint H t) × Q) :=
    (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
  rw [hcard, Nat.card_prod, Nat.mul_comm]

theorem odd_card_twoPoint_of_data (h : IsSplitRankOneData G H Q t) :
    Odd (Nat.card (twoPoint H t)) :=
  h.odd_inter t h.not_mem

/-- `Q` has even order: `|H| = |Q| |D|` with `|H|` even and `|D|` odd. -/
theorem even_card_Q_of_data (h : IsSplitRankOneData G H Q t) : Even (Nat.card Q) := by
  have heven : Even (Nat.card Q * Nat.card (twoPoint H t)) :=
    (card_H_eq_mul_of_data h) ▸ h.even_card
  rcases Nat.even_mul.mp heven with hq | hd
  · exact hq
  · exact absurd hd (Nat.not_even_iff_odd.mpr (odd_card_twoPoint_of_data h))

/-- `t` normalises `D = H ∩ H^t`. -/
theorem normalizes_twoPoint_of_data (h : IsSplitRankOneData G H Q t) :
    t ∈ Subgroup.normalizer ((twoPoint H t : Subgroup G) : Set G) := by
  have htt : t * t = 1 := by
    have h1 := pow_orderOf_eq_one t
    rw [h.invol] at h1
    simpa [pow_two] using h1
  have hconj : conj t (twoPoint H t) = twoPoint H t := by
    rw [Work.Models.twoPoint_def]
    change (H ⊓ conj t H).map (MulAut.conj t).toMonoidHom = H ⊓ conj t H
    rw [Subgroup.map_inf H (conj t H) (MulAut.conj t).toMonoidHom (MulAut.conj t).injective]
    change conj t H ⊓ conj t (conj t H) = H ⊓ conj t H
    rw [← Work.Models.conj_mul, htt, Work.Models.conj_one, inf_comm]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hconj

/-- `|V| * |K| = |D|` (Peterfalvi I App. I (1)(b) at `d = 2`). -/
theorem card_centD_mul_card_Kset [Finite G] (h : IsSplitRankOneData G H Q t) :
    Nat.card (centD H t) * (Kset H t).ncard = Nat.card (twoPoint H t) := by
  have hodd : Odd (Nat.card (twoPoint H t)) := odd_card_twoPoint_of_data h
  have htX := normalizes_twoPoint_of_data h
  have hmain := Bender.cardInvertedMulCardCentralizer (X := twoPoint H t) hodd htX h.invol
  rw [mul_comm]
  simpa [Kset, centD] using hmain

end Data

end Work.ThmF
