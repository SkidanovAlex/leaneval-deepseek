import Mathlib
import Submission.Work.PSL2.Card

namespace Work.CORE4

open scoped MatrixGroups

theorem QOddCentShapeCard {S : Type*} [Group S] [Finite S]
    (h : Nonempty (S ⧸ Subgroup.center S ≃* alternatingGroup (Fin 7)) ∨
      ∃ p k : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
        Nonempty (S ⧸ Subgroup.center S ≃*
          Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)))
    (hA7 : Nat.card (alternatingGroup (Fin 7)) = 2520) :
    60 ≤ Nat.card (S ⧸ Subgroup.center S) := by
  rcases h with h1 | h2
  · -- `S ⧸ Z(S) ≃* A₇`, so the order is `|A₇| = 2520 ≥ 60`.
    rcases h1 with ⟨e⟩
    rw [Nat.card_congr e.toEquiv, hA7]
    norm_num
  · -- `S ⧸ Z(S) ≃* PSL(2, q)` with `q = p^k`, `p` odd prime and `q ≥ 5`.
    rcases h2 with ⟨p, k, hp, hodd, h5, ⟨e⟩⟩
    haveI : Fact p.Prime := hp
    have hk : k ≠ 0 := by
      intro hk
      rw [hk, pow_zero] at h5
      omega
    have hcard := Work.PSL2.card_PSL2_galoisField p k hodd hk
    rw [Nat.card_congr e.toEquiv]
    -- `2 * |PSL(2,q)| = q(q²-1)` and `q ≥ 5` force `2 * |PSL(2,q)| ≥ 120`.
    have hge : 120 ≤ p ^ k * (p ^ (2 * k) - 1) := by
      have hsq : p ^ (2 * k) = (p ^ k) ^ 2 := by rw [mul_comm 2 k, pow_mul]
      have h25 : 25 ≤ p ^ (2 * k) := by
        rw [hsq]
        exact le_trans (by norm_num) (Nat.pow_le_pow_left h5 2)
      have h24 : 24 ≤ p ^ (2 * k) - 1 := by omega
      calc 120 = 5 * 24 := by norm_num
        _ ≤ p ^ k * (p ^ (2 * k) - 1) := Nat.mul_le_mul h5 h24
    omega

end Work.CORE4
