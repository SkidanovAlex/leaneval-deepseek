import Mathlib
import Submission.Work.BSW.Cases.K4.case1Aux

namespace Work.BSW.Cases.K4

open Subgroup

/-- In the Bender §3, Case 1 setting, an involution `u` outside `H = C_G(X)⟨t⟩` centralises only
`≤ 2` elements of `H`.  Equivalently `|C_G(u) ∩ H| ≤ 2`.

The argument is purely structural: `C_G(u)` has order `8` while `A = C_G(X)` has odd order, so
`C_G(u) ∩ A = 1`; since `A` has index `2` in `H`, a subgroup of `H` meeting `A` trivially has
order at most `2`. -/
theorem case1H_centralizer_le_two {G : Type} [Group G] [Finite G]
    (h : Work.BSW.Cases.K4.K4Hyp G) (X : Subgroup G) (t : G) (hX3 : Nat.card ↥X = 3)
    (ht2 : orderOf t = 2) (htN : t ∈ Subgroup.normalizer (X : Set G)) {u : G}
    (hu2 : orderOf u = 2) (huH : u ∉ Work.BSW.Cases.K4.case1H X t) :
    Nat.card ↥(Subgroup.centralizer ({u} : Set G) ⊓ Work.BSW.Cases.K4.case1H X t) ≤ 2 := by
  have hodd : Odd (Nat.card ↥(case1A X)) := case1A_odd h hX3
  have hAleH : case1A X ≤ case1H X t := le_sup_left
  -- `C_G(u) ∩ A = ⊥`: `C_G(u)` has order `8`, `A` has odd order.
  have hinf : Subgroup.centralizer ({u} : Set G) ⊓ case1A X = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxC, hxA⟩ := hx
    rw [Subgroup.mem_bot]
    have hxu : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
    have hmemC : x ∈ cent G u := Subgroup.mem_centralizer_singleton_iff.mpr hxu
    have hdvd8 : orderOf x ∣ 8 := by
      have h1 := orderOf_dvd_natCard_of_mem hmemC
      rwa [h.2.1 u hu2] at h1
    have hoddx : Odd (orderOf x) := hodd.of_dvd_nat (orderOf_dvd_natCard_of_mem hxA)
    exact orderOf_eq_one_iff.mp (eq_one_of_dvd_eight_of_odd hdvd8 hoddx)
  -- `(C_G(u) ∩ H) ∩ A = ⊥`, because `A ≤ H`.
  have hKinfA : (Subgroup.centralizer ({u} : Set G) ⊓ case1H X t) ⊓ case1A X = ⊥ := by
    rw [inf_assoc, inf_eq_right.mpr hAleH, hinf]
  -- `H ≤ N(A)` because `A` has index `2` in `H`.
  have hHnorm : case1H X t ≤ Subgroup.normalizer (case1A X : Set G) :=
    le_normalizer_of_two_mul_card hAleH (case1H_card h hX3 ht2 htN).symm
  have hKnorm : (Subgroup.centralizer ({u} : Set G) ⊓ case1H X t) ≤
      Subgroup.normalizer (case1A X : Set G) := le_trans inf_le_right hHnorm
  have hcard := card_sup_of_le_normalizer_of_inf_eq_bot hKnorm (by rw [inf_comm]; exact hKinfA)
  -- `|A ⊔ K| ≤ |H|`.
  have hsub : case1A X ⊔ (Subgroup.centralizer ({u} : Set G) ⊓ case1H X t) ≤ case1H X t :=
    sup_le hAleH inf_le_right
  have hle : Nat.card ↥(case1A X ⊔ (Subgroup.centralizer ({u} : Set G) ⊓ case1H X t)) ≤
      Nat.card ↥(case1H X t) :=
    Nat.card_le_card_of_injective
      (fun x : ↥(case1A X ⊔ (Subgroup.centralizer ({u} : Set G) ⊓ case1H X t)) =>
        (⟨(x : G), hsub x.2⟩ : ↥(case1H X t)))
      (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab))
  -- Combine: `|A| * |K| = |A ⊔ K| ≤ |H| = 2 |A|`, so `|K| ≤ 2`.
  have hle' : Nat.card ↥(case1A X) *
      Nat.card ↥(Subgroup.centralizer ({u} : Set G) ⊓ case1H X t) ≤
      2 * Nat.card ↥(case1A X) := by
    rw [← hcard, ← case1H_card h hX3 ht2 htN]
    exact hle
  have hApos : 0 < Nat.card ↥(case1A X) := Nat.card_pos
  rw [mul_comm 2 (Nat.card ↥(case1A X))] at hle'
  exact Nat.le_of_mul_le_mul_left hle' hApos

end Work.BSW.Cases.K4
