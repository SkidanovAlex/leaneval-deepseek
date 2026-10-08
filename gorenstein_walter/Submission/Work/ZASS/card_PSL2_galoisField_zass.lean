import Mathlib
import Submission.Work.ZASS.Defs
import Submission.Work.PSL2.Card

namespace Work.ZASS

/-- **Z7 arithmetic (blueprint §ZASS).** `|PSL(2,q)| = (q+1) q (q-1)/2` for `q = p^k`,
`k ≥ 1`: from `Work.PSL2.card_PSL2_galoisField`, which gives
`2 * |PSL(2,GF(p,k))| = p^k * (p^(2k) - 1)`, together with
`p^(2k) - 1 = (p^k - 1)(p^k + 1)` and `2 * ((p^k-1)/2) = p^k - 1` (as `p` is odd).  The
notation used is the unfolded `Matrix.ProjectiveSpecialLinearGroup (Fin 2) R`. -/
theorem card_PSL2_galoisField_zass {p k : ℕ} [Fact p.Prime] (hp : Odd p) (hk : k ≠ 0) :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) =
      (p ^ k + 1) * p ^ k * ((p ^ k - 1) / 2) := by
  have h := Work.PSL2.card_PSL2_galoisField p k hp hk
  -- `p ^ (2 * k) = (p ^ k) ^ 2`
  have h2k : p ^ (2 * k) = (p ^ k) ^ 2 := by rw [Nat.mul_comm 2 k, pow_mul]
  rw [h2k] at h
  -- `(p ^ k) ^ 2 - 1 = (p ^ k + 1) * (p ^ k - 1)`
  have hfac : (p ^ k) ^ 2 - 1 = (p ^ k + 1) * (p ^ k - 1) := by
    simpa using Nat.sq_sub_sq (p ^ k) 1
  rw [hfac] at h
  -- `p` odd, hence `p ^ k` odd, hence `2 ∣ p ^ k - 1`
  have hdvd : 2 ∣ p ^ k - 1 := by
    obtain ⟨m, hm⟩ := hp.pow (n := k)
    exact ⟨m, by omega⟩
  have hpk1 : p ^ k - 1 = 2 * ((p ^ k - 1) / 2) := (Nat.mul_div_cancel' hdvd).symm
  -- cancel the common factor `2`
  refine Nat.mul_left_cancel (n := 2) (by norm_num) ?_
  rw [h]
  conv_lhs => rw [hpk1]
  ring

end Work.ZASS
