import Mathlib

namespace Work.CORE3

theorem relIndex_of_factorization_eq {G : Type} [Group G] [Finite G]
    (H K : Subgroup G) (hle : H ≤ K) (p : ℕ) (hp : p.Prime)
    (hfac : (Nat.card ↥H).factorization p = (Nat.card ↥K).factorization p) :
    ¬ p ∣ H.relIndex K := by
  -- Since `H ≤ K`, the relative index multiplies the order of `H` up to `|K|`.
  have hsub : H ⊓ K = H := inf_of_le_left hle
  have hm_ne : Nat.card ↥H ≠ 0 := by
    rw [Nat.card_ne_zero]
    exact ⟨⟨1, H.one_mem⟩, inferInstance⟩
  have hk_ne : Nat.card ↥K ≠ 0 := by
    rw [Nat.card_ne_zero]
    exact ⟨⟨1, K.one_mem⟩, inferInstance⟩
  have hcard : H.relIndex K * Nat.card ↥H = Nat.card ↥K := by
    have h := Subgroup.relIndex_mul_card H K
    rwa [hsub] at h
  have hr_ne : H.relIndex K ≠ 0 := by
    intro h
    rw [h, zero_mul] at hcard
    exact hk_ne hcard.symm
  -- Compare the `p`-adic valuations of the two sides.
  have hfac' : (H.relIndex K * Nat.card ↥H).factorization p
      = (Nat.card ↥H).factorization p := by
    rw [hcard, ← hfac]
  rw [Nat.factorization_mul hr_ne hm_ne] at hfac'
  have hzero : (H.relIndex K).factorization p = 0 := Nat.add_eq_right.mp hfac'
  intro hdvd
  have h1 : 1 ≤ (H.relIndex K).factorization p :=
    (Nat.Prime.dvd_iff_one_le_factorization hp hr_ne).mp hdvd
  omega

end Work.CORE3
