import Mathlib
import Submission.Work.PSL2.Card

namespace Work.ASM

/-- For an odd natural number `q`, `4 ∣ q ^ 2 - 1`. -/
private lemma four_dvd_sq_sub_one_of_odd {q : ℕ} (hq : Odd q) : 4 ∣ q ^ 2 - 1 := by
  obtain ⟨m, hm⟩ := hq
  refine ⟨m * (m + 1), ?_⟩
  have h : q ^ 2 = 4 * (m * (m + 1)) + 1 := by rw [hm]; ring
  omega

/-- `|PSL(2, p^k)|` is even for odd prime `p` and `p^k ≥ 5`.

Indeed `2 * |PSL(2, q)| = q * (q ^ 2 - 1)` with `q = p ^ k` odd
(`Work.PSL2.card_PSL2_galoisField`), and `4 ∣ q ^ 2 - 1` for `q` odd,
so `4 ∣ 2 * |PSL(2, q)|` and hence `2 ∣ |PSL(2, q)|`. -/
theorem PSL_even_card (p k : ℕ) [Fact p.Prime] (hp : Odd p) (hq : 5 ≤ p ^ k) :
    Even (Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))) := by
  -- `5 ≤ p ^ k` forces `k ≠ 0`
  have hk : k ≠ 0 := by
    intro h
    rw [h, pow_zero] at hq
    omega
  -- the order formula `2 * |PSL(2, q)| = q * (q ^ 2 - 1)`, `q = p ^ k`
  have hcard := Work.PSL2.card_PSL2_galoisField p k hp hk
  have hodd : Odd (p ^ k) := hp.pow
  have hdvd : 4 ∣ p ^ k * (p ^ (2 * k) - 1) := by
    have hsq : p ^ (2 * k) = (p ^ k) ^ 2 := by
      rw [mul_comm 2 k, pow_mul]
    rw [hsq]
    exact dvd_mul_of_dvd_right (four_dvd_sq_sub_one_of_odd hodd) _
  rw [← hcard] at hdvd
  obtain ⟨c, hc⟩ := hdvd
  refine ⟨c, ?_⟩
  omega

end Work.ASM
