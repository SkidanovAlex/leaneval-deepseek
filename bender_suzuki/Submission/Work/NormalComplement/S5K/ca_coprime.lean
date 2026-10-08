/-
# `p ∤ |C_A(P)|` under `Setup45A` + `P` a `p`-Sylow of `D` (Ch. III §4 Prop. 1, step 4)

PORT NOTE (S5K): the two lemmas below are the port of the corresponding lemmas of
`Submission/Work/NormalComplement/NC4/prop1.lean` (same names, same proofs, copied 2026-10-05) into
a module compatible with the `sec4_P2d` world.  They are the first clause of §4 Prop. 1 step 4:
`p ∤ |C_A(P)|`, from `P` being a `p`-Sylow of `D = twoPoint H t`.
-/
import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.card_sup_mul_card_inf

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement.S5K

variable {G : Type} [Group G] [Finite G]
variable {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G}

/-- An element of `⟨x⟩` with `orderOf x = p` prime is either `1` or has order `p`. -/
lemma orderOf_eq_prime_of_mem_zpowers {x b : G} {p : ℕ} (hp : p.Prime) (hx : orderOf x = p)
    (hb : b ∈ Subgroup.zpowers x) (hb1 : b ≠ 1) : orderOf b = p := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have hpow : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hbp : (x ^ k) ^ p = 1 := by
    have hz : x ^ (p : ℤ) = 1 := by rw [zpow_natCast]; exact hpow
    rw [← zpow_natCast (x ^ k) p, ← zpow_mul, mul_comm, zpow_mul, hz]
    simp
  have hpdvd : orderOf (x ^ k) ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hbp
  rcases (Nat.dvd_prime hp).mp hpdvd with h1 | h1
  · exact absurd (orderOf_eq_one_iff.mp h1) hb1
  · exact h1

/-- **`p ∤ |C_A(P)|`** (`C_A(P) = A ⊓ C_G(P)`): if `C_A(P)` contained an element `x` of order `p`,
then `P ⊔ ⟨x⟩` would be a `p`-subgroup of `D = twoPoint H t` of order `p ^ 2` containing the Sylow
`p`-subgroup `P` properly, contradicting the index condition in `IsSylowIn p P D`.

This is Peterfalvi I Ch. III §4 Proposition 1 step 4, first clause (there from Lemma 1(d)); it is
the only place where the Sylow-ness of `P` in `D` is used in the arguments below. -/
lemma not_dvd_p_card_CA (h : Work.NormalComplement.Design.Setup45A G H t W p P A)
    (hPsyl : Work.NormalComplement.IsSylowIn p P (twoPoint H t)) :
    ¬ p ∣ Nat.card ↥(A ⊓ Subgroup.centralizer (P : Set G)) := by
  classical
  haveI : Fact p.Prime := ⟨h.prime⟩
  haveI : Fintype ↥(A ⊓ Subgroup.centralizer (P : Set G)) := Fintype.ofFinite _
  intro hdiv
  -- an element of order `p` of `C_A(P)`
  obtain ⟨x, hxmem, hxord⟩ : ∃ x ∈ (A ⊓ Subgroup.centralizer (P : Set G)), orderOf x = p := by
    have hcard : p ∣ Fintype.card ↥(A ⊓ Subgroup.centralizer (P : Set G)) := by
      rwa [Nat.card_eq_fintype_card] at hdiv
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card
      (G := ↥(A ⊓ Subgroup.centralizer (P : Set G))) p hcard
    exact ⟨(y : G), y.2, by rw [Subgroup.orderOf_coe]; exact hy⟩
  obtain ⟨hxA, hxC⟩ := Subgroup.mem_inf.mp hxmem
  have hxNe : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hxord
    exact h.prime.ne_one hxord.symm
  have hxNotP : x ∉ P := by
    intro hxP
    have : x ∈ A ⊓ P := Subgroup.mem_inf.mpr ⟨hxA, hxP⟩
    rw [h.A_inf] at this
    exact hxNe (Subgroup.mem_bot.mp this)
  -- `x` commutes with `P`
  have hcomm : ∀ q ∈ P, x * q = q * x := fun q hq =>
    ((Subgroup.mem_centralizer_iff.mp hxC) q hq).symm
  have hnorm : (Subgroup.zpowers x : Subgroup G) ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer (P : Set G) hxC)
  -- `P ⊓ ⟨x⟩ = ⊥`
  have hinf : P ⊓ (Subgroup.zpowers x : Subgroup G) = ⊥ := by
    by_contra hne
    have hex : ∃ b ∈ P ⊓ (Subgroup.zpowers x : Subgroup G), b ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      exact hne (le_antisymm (fun b hb => by rw [Subgroup.mem_bot]; exact hcon b hb) bot_le)
    obtain ⟨b, hb, hb1⟩ := hex
    have hbP : b ∈ P := (Subgroup.mem_inf.mp hb).1
    have hbz : b ∈ Subgroup.zpowers x := (Subgroup.mem_inf.mp hb).2
    have hbord : orderOf b = p := orderOf_eq_prime_of_mem_zpowers h.prime hxord hbz hb1
    have hbz_le : Subgroup.zpowers b ≤ Subgroup.zpowers x := Subgroup.zpowers_le.mpr hbz
    have hcard_eq : Nat.card ↥(Subgroup.zpowers b) = Nat.card ↥(Subgroup.zpowers x) := by
      rw [Nat.card_zpowers, Nat.card_zpowers, hbord, hxord]
    have heq : Subgroup.zpowers b = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge hbz_le (le_of_eq hcard_eq.symm)
    have hbzP : Subgroup.zpowers b ≤ P := Subgroup.zpowers_le.mpr hbP
    exact hxNotP (hbzP (heq ▸ Subgroup.mem_zpowers x))
  -- cardinality: `|P ⊔ ⟨x⟩| = p ^ 2`
  have hcardSup := Work.NormalComplement.card_sup_mul_card_inf (H := (P : Subgroup G))
    (K := (Subgroup.zpowers x : Subgroup G)) hnorm
  have hcard2 : Nat.card ↥(P ⊔ (Subgroup.zpowers x : Subgroup G)) = p ^ 2 := by
    rw [hinf, Subgroup.card_bot, mul_one, h.P_card, Nat.card_zpowers, hxord] at hcardSup
    simpa [pow_two] using hcardSup
  -- the index of `P` in `D` is divisible by `p`
  have hle : P ⊔ (Subgroup.zpowers x : Subgroup G) ≤ twoPoint H t :=
    sup_le hPsyl.2.1
      (Subgroup.zpowers_le.mpr ((inf_le_left : centD H t ≤ twoPoint H t) (h.A_le hxA)))
  have hrel : P.relIndex (P ⊔ (Subgroup.zpowers x : Subgroup G)) * Nat.card ↥P =
      Nat.card ↥(P ⊔ (Subgroup.zpowers x : Subgroup G)) :=
    Work.NormalComplement.relIndex_mul_card_of_le' le_sup_left
  have hp_rel : p ∣ P.relIndex (P ⊔ (Subgroup.zpowers x : Subgroup G)) := by
    have hcard' : Nat.card ↥(P ⊔ (Subgroup.zpowers x : Subgroup G)) = p * p := by
      rw [hcard2, pow_two]
    have hrel' : P.relIndex (P ⊔ (Subgroup.zpowers x : Subgroup G)) * p =
        Nat.card ↥(P ⊔ (Subgroup.zpowers x : Subgroup G)) := by
      rw [← hrel, h.P_card]
    rw [hcard'] at hrel'
    have hone : P.relIndex (P ⊔ (Subgroup.zpowers x : Subgroup G)) = p :=
      Nat.mul_right_cancel (Nat.pos_of_ne_zero h.prime.ne_zero) hrel'
    exact ⟨1, by rw [hone, mul_one]⟩
  have hrelD := Subgroup.relIndex_mul_relIndex P (P ⊔ (Subgroup.zpowers x : Subgroup G))
    (twoPoint H t) le_sup_left hle
  have hp_relD : p ∣ P.relIndex (twoPoint H t) := by
    rw [← hrelD]
    exact dvd_mul_of_dvd_left hp_rel _
  exact hPsyl.2.2 (by
    rwa [show (P.subgroupOf (twoPoint H t)).index = P.relIndex (twoPoint H t) from rfl])

/-! ## Infrastructure for `step2` (`N_H(P) = C_H(P)`) and `step1` (`hallCA`) -/


end Work.NormalComplement.S5K
