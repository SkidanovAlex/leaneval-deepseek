import Mathlib
import Submission.Work.PTCert.LetterEval

namespace Work.PTCert

/-- Every letter occurring in the word `letterImg r k i` (the image of the generator `i` under
the letter `b1 r k`, `k < NB1 r`) is a valid free-group letter of rank `r`, i.e. is `< 2 * r`.

Indeed `letterImg` returns either `[2 * i]` (with `i < r`), or a two-letter word built from the
decoded pair `(i₀, j₀) = pairOf r ((k - 1) / 4)`, whose two components are `< r` for
`k < NB1 r`. -/
theorem letterImgLetterLt (r k i : ℕ) (hk : k < Submission.PTCert.NB1 r) (hi : i < r) :
    ∀ c ∈ Submission.PTCert.letterImg r k i, c < 2 * r := by
  intro c hc
  by_cases hk0 : k = 0
  · subst hk0
    rw [Submission.PTCert.letterImg_zero] at hc
    simp only [List.mem_singleton] at hc
    omega
  · by_cases hii : i = (Submission.PTCert.pairOf r ((k - 1) / 4)).1
    · have h1 : 1 ≤ k := by omega
      obtain ⟨hPi, hPj, -⟩ := Work.PTCert.pairOf_bounds (Submission.PTCert.q_lt r k h1 hk)
      have hm : (k - 1) % 4 < 4 := Nat.mod_lt _ (by norm_num)
      rcases (by omega : (k - 1) % 4 = 0 ∨ (k - 1) % 4 = 1 ∨ (k - 1) % 4 = 2 ∨
        (k - 1) % 4 = 3) with h4 | h4 | h4 | h4
      · rw [Submission.PTCert.letterImg_k0 r k i hk0 hii h4] at hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        omega
      · rw [Submission.PTCert.letterImg_k1 r k i hk0 hii h4] at hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        omega
      · rw [Submission.PTCert.letterImg_k2 r k i hk0 hii h4] at hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        omega
      · rw [Submission.PTCert.letterImg_k3 r k i hk0 hii h4] at hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        omega
    · rw [Submission.PTCert.letterImg_ne r k i hii] at hc
      simp only [List.mem_singleton] at hc
      omega

end Work.PTCert
