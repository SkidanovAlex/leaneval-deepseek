import Mathlib

set_option linter.unusedVariables false

open scoped Pointwise

namespace Work.CORE3.J4

/-- If `A` and `B` are subgroups of a finite group with `A ⊓ B = ⊥`, `B` normalising `A` and
`B` of odd order, then every element `g` of `A ⊔ B` with `g * g = 1` already lies in `A`.

Since `B ≤ N_G(A)`, the carrier of `A ⊔ B` is the pointwise product `A * B`, so `g = b * a`
with `b ∈ A`, `a ∈ B`.  From `(b * a)² = 1` we get `a * b * a = b⁻¹`, hence, as `a ∈ B`
normalises `A`, the element `a² = (a * b * a⁻¹)⁻¹ * b⁻¹` lies in `A`; on the other hand
`a² ∈ B`, so `a² ∈ A ⊓ B = ⊥`, i.e. `a² = 1`.  As `|B|` is odd this forces `a = 1`, and
therefore `g = b ∈ A`. -/
theorem MemLeftOfSupOfSqEqOne {G : Type*} [Group G] [Finite G]
    {A B : Subgroup G} (hAB : A ⊓ B = ⊥) (hAn : A ≤ Subgroup.normalizer (B : Set G))
    (hBn : B ≤ Subgroup.normalizer (A : Set G)) (hBodd : Odd (Nat.card B))
    {g : G} (hg : g ∈ A ⊔ B) (hg2 : g * g = 1) : g ∈ A := by
  have hcoe : (↑(A ⊔ B) : Set G) = (A : Set G) * (B : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left A B hBn
  have hgmem : g ∈ (A : Set G) * (B : Set G) := by rw [← hcoe]; exact hg
  obtain ⟨b, hb, a, ha, hba⟩ := Set.mem_mul.mp hgmem
  -- `b ∈ A`, `a ∈ B` and `g = b * a`; from `g ^ 2 = 1` we get `a * b * a = b⁻¹`.
  have hsq : g ^ 2 = 1 := by rw [pow_two]; exact hg2
  have hmul : (b * a) ^ 2 = 1 := by rw [hba]; exact hsq
  have hmain : a * b * a = b⁻¹ := by
    have h1 : b * (a * b * a) = 1 := by
      calc b * (a * b * a) = (b * a) * (b * a) := by group
        _ = 1 := by rw [← pow_two]; exact hmul
    exact mul_left_cancel (h1.trans (mul_inv_cancel b).symm)
  have hsplit : a * b * a = (a * b * a⁻¹) * a ^ 2 := by group
  -- `a ∈ B` normalises `A`, so `a * b * a⁻¹ ∈ A`; hence `a ^ 2 ∈ A`.
  have hconj : a * b * a⁻¹ ∈ A := by
    have haN : a ∈ Subgroup.normalizer (A : Set G) := hBn ha
    exact (Subgroup.mem_normalizer_iff.mp haN b).mp hb
  have ha2A : a ^ 2 ∈ A := by
    have hkey : (a * b * a⁻¹) * a ^ 2 = b⁻¹ := by rw [← hsplit]; exact hmain
    have ha2eq : a ^ 2 = (a * b * a⁻¹)⁻¹ * b⁻¹ := by rw [← hkey]; group
    rw [ha2eq]
    exact A.mul_mem (A.inv_mem hconj) (A.inv_mem hb)
  have ha2B : a ^ 2 ∈ B := B.pow_mem ha 2
  -- `a ^ 2 ∈ A ⊓ B = ⊥`, so `a ^ 2 = 1`.
  have ha2one : a ^ 2 = 1 := by
    have hmem : a ^ 2 ∈ A ⊓ B := ⟨ha2A, ha2B⟩
    rw [hAB] at hmem
    exact Subgroup.mem_bot.mp hmem
  -- with `|B|` odd, `a = 1`.
  have haB2 : (⟨a, ha⟩ : ↥B) ^ 2 = 1 := by
    apply Subtype.ext; simpa using ha2one
  have hone : orderOf (⟨a, ha⟩ : ↥B) = 1 := by
    have hdvd2 : orderOf (⟨a, ha⟩ : ↥B) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr haB2
    have hdvdU : orderOf (⟨a, ha⟩ : ↥B) ∣ Nat.card B := orderOf_dvd_natCard _
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
    · exact h
    · exfalso
      have h2 : 2 ∣ Nat.card B := h ▸ hdvdU
      rw [Nat.dvd_iff_mod_eq_zero] at h2
      have hodd : Nat.card B % 2 = 1 := Nat.odd_iff.mp hBodd
      omega
  have ha1 : a = 1 := by
    have h := congrArg (fun x : ↥B => (x : G)) (orderOf_eq_one_iff.mp hone)
    simpa using h
  rw [← hba, ha1, mul_one]
  exact hb

end Work.CORE3.J4
