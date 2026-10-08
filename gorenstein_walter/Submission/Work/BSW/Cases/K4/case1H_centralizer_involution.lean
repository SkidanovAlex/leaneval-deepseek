import Mathlib
import Submission.Work.BSW.Cases.K4.case1Aux

namespace Work.BSW.Cases.K4

open Subgroup

variable {G : Type} [Group G] [Finite G]

/-- An element of `A = C_G(X)` which is an involution is trivial, because `|A|` is odd. -/
theorem case1A_eq_one_of_sq_eq_one (h : K4Hyp G) {X : Subgroup G} (hX3 : Nat.card ↥X = 3)
    {c : G} (hc : c ∈ case1A X) (hsq : c * c = 1) : c = 1 := by
  have hodd := case1A_odd h hX3
  have hd2 : orderOf c ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hsq)
  have hdA : orderOf c ∣ Nat.card ↥(case1A X) := orderOf_dvd_natCard_of_mem hc
  rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two (orderOf c) hd2 with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · exact absurd (even_iff_two_dvd.mpr (h1 ▸ hdA)) (Nat.not_even_iff_odd.mpr hodd)

theorem case1H_centralizer_involution {G : Type} [Group G] [Finite G]
    (h : Work.BSW.Cases.K4.K4Hyp G) (X : Subgroup G) (t : G) (hX3 : Nat.card ↥X = 3)
    (ht2 : orderOf t = 2) (htN : t ∈ Subgroup.normalizer (X : Set G)) {z : G}
    (hzH : z ∈ Work.BSW.Cases.K4.case1H X t) (hz2 : orderOf z = 2) :
    Subgroup.centralizer ({z} : Set G) ⊓ Work.BSW.Cases.K4.case1H X t = Subgroup.zpowers z := by
  have hcomm := (case1A_comm_and_inv h hX3 ht2 htN).1
  have hinv := (case1A_comm_and_inv h hX3 ht2 htN).2
  have hodd := case1A_odd h hX3
  have htt : t * t = 1 := by rw [← pow_two, ← ht2]; exact pow_orderOf_eq_one t
  -- `z` lies in the coset `A t`
  have hzform : ∃ a ∈ case1A X, z = a * t := by
    rcases (mem_case1H_iff ht2 htN).mp hzH with hzA | hz
    · exfalso
      exact (Nat.not_even_iff_odd.mpr hodd)
        (even_iff_two_dvd.mpr (by rw [← hz2]; exact orderOf_dvd_natCard_of_mem hzA))
    · exact hz
  obtain ⟨a, ha, hza⟩ := hzform
  -- `t a = a⁻¹ t`
  have hta : t * a = a⁻¹ * t := by
    calc t * a = t * a * t⁻¹ * t := by group
      _ = a⁻¹ * t := by rw [hinv a ha]
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff] at hx
    obtain ⟨hxcen, hxH⟩ := hx
    have hx' : x * (a * t) = (a * t) * x := by rw [← hza]; exact hxcen
    rcases (mem_case1H_iff ht2 htN).mp hxH with hxA | ⟨b, hb, hxb⟩
    · -- x ∈ A
      have hxa : x * a = a * x := hcomm x hxA a ha
      have hxt : x * t = t * x := by
        have h1 : a * (x * t) = a * (t * x) := by
          calc a * (x * t) = x * (a * t) := by
                rw [← mul_assoc a x t, ← hxa, mul_assoc x a t]
            _ = (a * t) * x := hx'
            _ = a * (t * x) := by rw [mul_assoc]
        exact mul_left_cancel h1
      have h2 : x = x⁻¹ := by
        calc x = t * x * t⁻¹ := by rw [← hxt]; group
          _ = x⁻¹ := hinv x hxA
      have hxx : x * x = 1 := by
        nth_rewrite 1 [h2]
        rw [inv_mul_cancel]
      rw [case1A_eq_one_of_sq_eq_one h hX3 hxA hxx]
      exact Subgroup.one_mem _
    · -- x = b * t
      have hbt : t * b = b⁻¹ * t := by
        calc t * b = t * b * t⁻¹ * t := by group
          _ = b⁻¹ * t := by rw [hinv b hb]
      have hL : (b * t) * (a * t) = b * a⁻¹ := by
        calc (b * t) * (a * t) = b * (t * a) * t := by group
          _ = b * (a⁻¹ * t) * t := by rw [hta]
          _ = b * a⁻¹ * (t * t) := by group
          _ = b * a⁻¹ := by rw [htt, mul_one]
      have hR : (a * t) * (b * t) = a * b⁻¹ := by
        calc (a * t) * (b * t) = a * (t * b) * t := by group
          _ = a * (b⁻¹ * t) * t := by rw [hbt]
          _ = a * b⁻¹ * (t * t) := by group
          _ = a * b⁻¹ := by rw [htt, mul_one]
      have hrel : b * a⁻¹ = a * b⁻¹ := by
        have h2 := hx'
        rw [hxb, hL, hR] at h2
        exact h2
      have hcinv : (b * a⁻¹)⁻¹ = b * a⁻¹ := by
        rw [mul_inv_rev, inv_inv]
        exact hrel.symm
      have hsq : (b * a⁻¹) * (b * a⁻¹) = 1 := by
        calc (b * a⁻¹) * (b * a⁻¹) = (b * a⁻¹) * (b * a⁻¹)⁻¹ := by rw [hcinv]
          _ = 1 := mul_inv_cancel _
      have hcA : b * a⁻¹ ∈ case1A X := (case1A X).mul_mem hb ((case1A X).inv_mem ha)
      have hb_eq : b = a := by
        have h1 : b * a⁻¹ = 1 := case1A_eq_one_of_sq_eq_one h hX3 hcA hsq
        calc b = b * a⁻¹ * a := by group
          _ = 1 * a := by rw [h1]
          _ = a := one_mul a
      rw [hxb, hb_eq, ← hza]
      exact Subgroup.mem_zpowers z
  · rw [Subgroup.zpowers_le]
    exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, hzH⟩

end Work.BSW.Cases.K4
