import Mathlib
import Submission.Work.CORE3.Defs

namespace Work.CORE3

open Subgroup
open Work.GW2

set_option linter.unusedVariables false

/-- If `x` has odd order and `x ^ 2 ∈ H` for a subgroup `H`, then `x ∈ H`:
writing `orderOf x = 2 * m + 1`, one has `x = (x ^ 2) ^ (m + 1)`. -/
private lemma mem_of_sq_mem_of_odd_order {G : Type*} [Group G] {H : Subgroup G} {x : G}
    (hx2 : x ^ 2 ∈ H) (hodd : Odd (orderOf x)) : x ∈ H := by
  obtain ⟨m, hm⟩ := hodd.exists_bit1
  have hx : (x ^ 2) ^ (m + 1) = x := by
    rw [← pow_mul]
    have : 2 * (m + 1) = orderOf x + 1 := by omega
    rw [this, pow_succ, pow_orderOf_eq_one, one_mul]
  rw [show x = (x ^ 2) ^ (m + 1) from hx.symm]
  exact H.pow_mem hx2 (m + 1)

/-- Design pass 13 §1, D4 (pure group theory).  An odd-order subgroup `P ≤ M` inverted by an
element `t₂` of a subgroup `L ≤ M` that is normalized by `M` lies in `L`.

Proof: for `x ∈ P`, `x * t₂ * x⁻¹ ∈ L` and `t₂⁻¹ ∈ L`, and
`x² = (x * t₂ * x⁻¹) * t₂⁻¹` (because `t₂ * x⁻¹ * t₂⁻¹ = x`), so `x² ∈ L`; as `x` has odd order,
`x ∈ ⟨x²⟩ ≤ L`. -/
theorem Core13LeOfInverted (G : Type) [Group G] {M L P : Subgroup G} {t2 : G} (hLM : L ≤ M)
    (hLn : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L) (ht2 : t2 ∈ L) (hPM : P ≤ M)
    (hodd : Odd (Nat.card P)) (hinv : ∀ x ∈ P, t2 * x * t2⁻¹ = x⁻¹) : P ≤ L := by
  intro x hxP
  have hxM : x ∈ M := hPM hxP
  -- `x * t₂ * x⁻¹ ∈ L` because `M` normalizes `L`.
  have hconj : x * t2 * x⁻¹ ∈ L := hLn x hxM t2 ht2
  -- `x² = (x * t₂ * x⁻¹) * t₂⁻¹ ∈ L`, using `t₂ * x⁻¹ * t₂⁻¹ = x`.
  have hx2L : x ^ 2 ∈ L := by
    have ht : t2 * x⁻¹ * t2⁻¹ = x := by
      have h := hinv x⁻¹ (P.inv_mem hxP)
      rwa [inv_inv] at h
    have e : x ^ 2 = (x * t2 * x⁻¹) * t2⁻¹ := by
      rw [sq]
      calc x * x = x * (t2 * x⁻¹ * t2⁻¹) := by rw [ht]
        _ = x * t2 * x⁻¹ * t2⁻¹ := by group
    rw [e]
    exact L.mul_mem hconj (L.inv_mem ht2)
  -- `orderOf x` is odd since it divides the odd number `Nat.card P`.
  have hodd_ord : Odd (orderOf x) := by
    have hzx : Subgroup.zpowers x ≤ P := Subgroup.zpowers_le.mpr hxP
    have hdvd : Nat.card (Subgroup.zpowers x) ∣ Nat.card P := Subgroup.card_dvd_of_le hzx
    obtain ⟨k, hk⟩ := hdvd
    have hodd_z : Odd (Nat.card (Subgroup.zpowers x)) := Nat.Odd.of_mul_left (hk ▸ hodd)
    rwa [Nat.card_zpowers] at hodd_z
  exact mem_of_sq_mem_of_odd_order hx2L hodd_ord

end Work.CORE3
