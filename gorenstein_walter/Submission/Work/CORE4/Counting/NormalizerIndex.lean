import Mathlib
import Submission.Work.PSL2.Card

namespace Work.CORE4.Counting

/-- Pure arithmetic core: if `2k, 2k'` are the two halves of `q ± 1` and `2·(m·(2k)) = q(q²-1)`,
then `m = q·k'`.  The equality `2·(m·(2k)) = q(q²-1)` is what one obtains from
`|N(Y)| = 2k` together with `2·|PSL(2,q)| = q(q²-1)`. -/
private lemma arith (q k k' m : ℕ) (hq : 2 ≤ q)
    (hdisj : (2 * k = q + 1 ∧ 2 * k' = q - 1) ∨ (2 * k = q - 1 ∧ 2 * k' = q + 1))
    (h : (2 * m) * (2 * k) = q * (q ^ 2 - 1)) : m = q * k' := by
  have hq1 : q ^ 2 - 1 = (q + 1) * (q - 1) := Nat.sq_sub_sq q 1
  rcases hdisj with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1] at h
    have h' : (2 * m) * (q + 1) = (q * (q - 1)) * (q + 1) := by rw [h, hq1]; ring
    have h2m : 2 * m = q * (q - 1) := Nat.mul_right_cancel (by omega) h'
    have hmul : 2 * m = 2 * (q * k') := by rw [h2m, ← h2]; ring
    exact Nat.mul_left_cancel (by norm_num) hmul
  · rw [h1] at h
    have h' : (2 * m) * (q - 1) = (q * (q + 1)) * (q - 1) := by rw [h, hq1]; ring
    have h2m : 2 * m = q * (q + 1) := Nat.mul_right_cancel (by omega) h'
    have hmul : 2 * m = 2 * (q * k') := by rw [h2m, ← h2]; ring
    exact Nat.mul_left_cancel (by norm_num) hmul

/-- `|N(Y)| = 2k` determines the index of `N(Y)` in `PSL(2,q)`, `q = pF^kF`: the index is the
quotient `|PSL(2,q)| / (2k) = q(q²-1)/(4k) = q·k'`. -/
theorem NormalizerIndex (pF kF k k' : ℕ) [Fact pF.Prime]
    (hodd : Odd pF) (hq5 : 5 ≤ pF ^ kF)
    (hdisj : (2 * k = pF ^ kF + 1 ∧ 2 * k' = pF ^ kF - 1) ∨
             (2 * k = pF ^ kF - 1 ∧ 2 * k' = pF ^ kF + 1))
    (Y : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF)))
    (hN : Nat.card (Subgroup.normalizer (Y : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF)))) = 2 * k) :
    (Subgroup.normalizer (Y : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF)))).index = pF ^ kF * k' := by
  have hkF : kF ≠ 0 := by rintro rfl; simp at hq5
  set H := Subgroup.normalizer (Y : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF))) with hH
  have hcard := Work.PSL2.card_PSL2_galoisField pF kF hodd hkF
  have hsq : (pF ^ kF) ^ 2 = pF ^ (2 * kF) := by rw [← pow_mul, Nat.mul_comm]
  have hcard2 : 2 * Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF))
      = pF ^ kF * ((pF ^ kF) ^ 2 - 1) := by
    rw [hsq]
    exact hcard
  have hci : H.index * Nat.card H =
      Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF)) :=
    Subgroup.index_mul_card H
  have hci' : H.index * (2 * k) =
      Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField pF kF)) := by
    rw [← hN]
    exact hci
  have hmain : (2 * H.index) * (2 * k) = pF ^ kF * ((pF ^ kF) ^ 2 - 1) := by
    rw [← hcard2, ← hci']
    ring
  exact arith (pF ^ kF) k k' H.index (by omega) hdisj hmain

end Work.CORE4.Counting
