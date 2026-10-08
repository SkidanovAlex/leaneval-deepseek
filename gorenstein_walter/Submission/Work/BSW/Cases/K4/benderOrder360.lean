import Mathlib
import Submission.Work.BSW.Cases.K4.K4Hyp
import Submission.Work.BSW.Cases.K4.CardSup
import Submission.Work.BSW.Cases.K4.countingFacts
import Submission.Work.BSW.Cases.K4.case1Aux
import Submission.Work.BSW.Cases.K4.case1Arith
import Submission.Work.BSW.Cases.K4.exists_involution_mem_normalizer
import Submission.Work.BSW.Cases.K4.case1H_centralizer_involution
import Submission.Work.BSW.Cases.K4.case1H_centralizer_le_two
import Submission.Work.BSW.Cases.K4.case1A_inv_trivial
import Submission.Work.BSW.Cases.K4.case1H_four_partners
import Submission.Work.BSW.Cases.K4.case1Count
import Submission.Work.BSW.Cases.K4.case1H_bCount_ge_three

namespace Work.BSW.Cases.K4

theorem benderOrder360 {G : Type} [Group G] [Finite G] (h : Work.BSW.Cases.K4.K4Hyp G)
    (V X : Subgroup G) (hV : Work.BSW.Cases.K4.IsV4 V)
    (hXle : X ≤ Subgroup.normalizer (V : Set G)) (hX3 : Nat.card ↥X = 3)
    (hCX : ¬ Subgroup.centralizer (X : Set G) ≤ Subgroup.normalizer (V : Set G)) :
    Nat.card G = 360 := by
  -- an involution normalizing `X` (from the Sylow structure of `N_G(V)`)
  obtain ⟨t, ht2, -, htN⟩ := exists_involution_mem_normalizer h V X hV hXle hX3
  have hodd : Odd (Nat.card ↥(case1A X)) := case1A_odd h hX3
  -- the centralizers in `H` of involutions: `C_H(z) = zpowers z` and `|C_H(u)| ≤ 2`
  have hCz : ∀ z ∈ case1H X t, orderOf z = 2 →
      Subgroup.centralizer ({z} : Set G) ⊓ case1H X t = Subgroup.zpowers z :=
    fun z hzH hz2 => case1H_centralizer_involution h X t hX3 ht2 htN hzH hz2
  have hle2 : ∀ u : G, u ∉ case1H X t → orderOf u = 2 →
      Nat.card ↥(Subgroup.centralizer ({u} : Set G) ⊓ case1H X t) ≤ 2 :=
    fun u huH hu2 => case1H_centralizer_le_two h X t hX3 ht2 htN hu2 huH
  -- the cosets of `H` contain as many involutions as `|C_H(u)|`
  have hcoset : ∀ u : G, orderOf u = 2 → u ∉ case1H X t →
      ({y : G | orderOf y = 2 ∧ ∃ k ∈ case1H X t, y = k * u} : Set G).ncard =
        Nat.card ↥(Subgroup.centralizer ({u} : Set G) ⊓ case1H X t) := by
    intro u hu2 huH
    exact case1H_coset_involutions_aux h X t hX3 ht2 htN hu2 huH
      (fun a ha ha1 => case1A_inv_trivial h X t hX3 ht2 htN hu2 huH ha ha1)
  -- each involution of `H` commutes with exactly four involutions outside `H`
  have hpartners : ∀ z ∈ case1H X t, orderOf z = 2 →
      ({u : G | u ∉ case1H X t ∧ orderOf u = 2 ∧ z * u = u * z} : Set G).ncard = 4 :=
    fun z hzH hz2 => case1H_four_partners h X t hzH hz2 (hCz z hzH hz2)
  -- Bender's double count
  have hb2 : Work.GW2.bCount (case1H X t) 2 = 2 * Nat.card ↥(case1A X) :=
    case1_bCount_two_aux h X t hX3 ht2 htN hpartners hle2 hcoset
  have h3 : ∀ n : ℕ, 3 ≤ n → Work.GW2.bCount (case1H X t) n = 0 :=
    case1H_bCount_ge_three (case1H X t) hle2 hcoset
  obtain ⟨hC1, hC2⟩ := countingFacts (case1H X t) h3
  -- the involutions of `H` and the order of `H`
  have hJH : ({x : G | orderOf x = 2 ∧ x ∈ case1H X t} : Set G).ncard =
      Nat.card ↥(case1A X) := case1H_involutions h hX3 ht2 htN
  have hHcard : Nat.card ↥(case1H X t) = 2 * Nat.card ↥(case1A X) :=
    case1H_card h hX3 ht2 htN
  -- the number of involutions of `G` is `|G : C_G(t)| = |G| / 8`
  have hJidx : ({x : G | orderOf x = 2} : Set G).ncard = (cent G t).index := by
    rw [Subgroup.index_centralizer_eq_ncard]
    congr 1
    ext x
    constructor
    · intro hx
      exact (h.2.2.2.2 x t hx ht2).symm
    · intro hx
      obtain ⟨c, hc⟩ := isConj_iff.mp hx
      change orderOf x = 2
      rw [← hc, ← MulAut.conj_apply, MulEquiv.orderOf_eq, ht2]
  have hJ8 : ({x : G | orderOf x = 2} : Set G).ncard * 8 = Nat.card G := by
    have h1 : Nat.card ↥(cent G t) * (cent G t).index = Nat.card G :=
      Subgroup.card_mul_index (cent G t)
    rw [h.2.1 t ht2] at h1
    rw [hJidx]
    omega
  -- the arithmetic relations
  have hJform : ({x : G | orderOf x = 2} : Set G).ncard =
      Nat.card ↥(case1A X) + Work.GW2.bCount (case1H X t) 1 +
        2 * Work.GW2.bCount (case1H X t) 2 := by
    rw [hC1, hJH]
  have hidxform : (case1H X t).index =
      1 + Work.GW2.bCount (case1H X t) 0 + Work.GW2.bCount (case1H X t) 1 +
        Work.GW2.bCount (case1H X t) 2 := by
    have hpos : 1 ≤ (case1H X t).index := Nat.one_le_iff_ne_zero.mpr
      (Subgroup.index_ne_zero_of_finite (H := case1H X t))
    omega
  have h4 : ({x : G | orderOf x = 2} : Set G).ncard * 4 =
      (case1H X t).index * Nat.card ↥(case1A X) := by
    have h1 : Nat.card G = (case1H X t).index * Nat.card ↥(case1H X t) := by
      rw [mul_comm]
      exact (Subgroup.card_mul_index (case1H X t)).symm
    have h2 : ({x : G | orderOf x = 2} : Set G).ncard * 8 =
        ((case1H X t).index * Nat.card ↥(case1A X)) * 2 := by
      rw [hJ8, h1, hHcard]
      ring
    have h3 : (({x : G | orderOf x = 2} : Set G).ncard * 4) * 2 =
        ((case1H X t).index * Nat.card ↥(case1A X)) * 2 := by
      rw [← h2]; ring
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h3
  have ha3 : 3 ∣ Nat.card ↥(case1A X) := by
    have hle : X ≤ case1A X := le_centralizer_of_card_three hX3
    have := Subgroup.card_dvd_of_le hle
    rwa [hX3] at this
  have hane : Nat.card ↥(case1A X) ≠ 3 := by
    intro hA3
    refine hCX ?_
    have hXeq : X = case1A X := Subgroup.eq_of_le_of_card_ge (le_centralizer_of_card_three hX3)
      (by rw [hX3, hA3])
    have hle : case1A X ≤ Subgroup.normalizer (V : Set G) := hXeq ▸ hXle
    exact hle
  have hG8 : Nat.card G = 8 * ({x : G | orderOf x = 2} : Set G).ncard := by
    rw [← hJ8]
    ring
  exact case1_arith ha3 hane hodd hJform hidxform h4 hb2 hG8

end Work.BSW.Cases.K4
