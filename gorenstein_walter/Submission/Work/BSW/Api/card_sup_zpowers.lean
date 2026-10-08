import Mathlib
import Submission.Work.BSW.Basic

open scoped Pointwise

namespace Work.BSW.Api

/-- `|K ⊔ ⟨s⟩| = 2|K|`, i.e. `|C_G(t)| = 2|K|`.  Since `s ∉ K` and `⟨s⟩ = {1, s}`
(`Work.BSW.K_inf_zpowers_s`), we have `K ⊓ ⟨s⟩ = ⊥`. -/
theorem card_sup_zpowers {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) :
    Nat.card ↥(K ⊔ Subgroup.zpowers s) = 2 * Nat.card ↥K := by
  -- `s` normalizes `K` (it inverts it), so the two factors commute.
  have hLE : Subgroup.zpowers s ≤ Subgroup.normalizer K := by
    rw [Subgroup.le_normalizer_iff]
    intro u hu k hk
    rcases Work.BSW.mem_zpowers_s h hu with rfl | rfl
    · simpa using hk
    · rw [Work.BSW.inverts_s_K h k hk]
      exact K.inv_mem hk
  -- hence `K ⊔ ⟨s⟩ = K * ⟨s⟩` as a set product.
  have hcoeeq : (↑(K ⊔ Subgroup.zpowers s) : Set G) =
      (K : Set G) * (Subgroup.zpowers s : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left K (Subgroup.zpowers s) hLE
  -- multiplication `K × ⟨s⟩ → K ⊔ ⟨s⟩` is a bijection.
  have hbij : Function.Bijective
      (fun p : (↥K × ↥(Subgroup.zpowers s)) =>
        (⟨(p.1 : G) * (p.2 : G),
          Subgroup.mul_mem_sup p.1.2 p.2.2⟩ : ↥(K ⊔ Subgroup.zpowers s))) := by
    refine ⟨?_, ?_⟩
    · rintro ⟨k1, x1⟩ ⟨k2, x2⟩ heq
      simp only [Subtype.mk.injEq] at heq
      have h1 : (k2 : G)⁻¹ * (k1 : G) = (x2 : G) * (x1 : G)⁻¹ := by
        have := congrArg (fun z : G => (k2 : G)⁻¹ * z * (x1 : G)⁻¹) heq
        simpa [mul_assoc] using this
      have hbot : (k2 : G)⁻¹ * (k1 : G) ∈ (⊥ : Subgroup G) := by
        rw [← Work.BSW.K_inf_zpowers_s h]
        exact ⟨K.mul_mem (K.inv_mem k2.2) k1.2,
          h1 ▸ (Subgroup.zpowers s).mul_mem x2.2 ((Subgroup.zpowers s).inv_mem x1.2)⟩
      have hk : (k2 : G)⁻¹ * (k1 : G) = 1 := Subgroup.mem_bot.mp hbot
      have hx : (x2 : G) * (x1 : G)⁻¹ = 1 := by rw [← h1]; exact hk
      exact Prod.ext (Subtype.ext (inv_mul_eq_one.mp hk).symm)
        (Subtype.ext (mul_inv_eq_one.mp hx).symm)
    · intro z
      have hz : (z : G) ∈ (K : Set G) * (Subgroup.zpowers s : Set G) := by
        rw [← hcoeeq]
        exact z.2
      obtain ⟨k, hk, x, hx, hkx⟩ := Set.mem_mul.mp hz
      exact ⟨(⟨k, hk⟩, ⟨x, hx⟩), by apply Subtype.ext; simpa using hkx⟩
  calc Nat.card ↥(K ⊔ Subgroup.zpowers s)
      = Nat.card (↥K × ↥(Subgroup.zpowers s)) :=
        (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
    _ = Nat.card ↥K * Nat.card ↥(Subgroup.zpowers s) := Nat.card_prod _ _
    _ = Nat.card ↥K * orderOf s := by rw [Nat.card_zpowers]
    _ = Nat.card ↥K * 2 := by rw [Work.BSW.orderOf_s h]
    _ = 2 * Nat.card ↥K := by rw [mul_comm]

end Work.BSW.Api
