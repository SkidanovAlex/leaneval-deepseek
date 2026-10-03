import Mathlib
import Submission.Work.FIPiChain.Defs

namespace Work.FIPiChain.P3S3

/-- If `0 ≤ b` and `b ^ 2 ≤ n` (with `n` a natural number), then `b ≤ n`.  Otherwise
`n + 1 ≤ b` forces `(n+1) ^ 2 ≤ b ^ 2 ≤ n`, impossible. -/
private lemma le_of_sq_le {b : ℤ} {n : ℕ} (h : b ^ 2 ≤ (n : ℤ)) : b ≤ (n : ℤ) := by
  by_contra hc
  have h1 : (n : ℤ) + 1 ≤ b := by omega
  have h2 : ((n : ℤ) + 1) * ((n : ℤ) + 1) ≤ b * b := mul_self_le_mul_self (by omega) h1
  nlinarith [sq_nonneg (n : ℤ), Int.natCast_nonneg n]

/-- From `a ^ 2 ≤ n` deduce `|a| ≤ n`. -/
private lemma abs_le_of_sq_le {a : ℤ} {n : ℕ} (h : a ^ 2 ≤ (n : ℤ)) : |a| ≤ (n : ℤ) := by
  have h' : |a| ^ 2 ≤ (n : ℤ) := by rwa [sq_abs]
  exact le_of_sq_le h'

/-- From `a ^ 4 ≤ n` deduce `|a| ≤ n` (reduces to the square case applied to `a ^ 2`). -/
private lemma abs_le_of_pow_four_le {a : ℤ} {n : ℕ} (h : a ^ 4 ≤ (n : ℤ)) : |a| ≤ (n : ℤ) := by
  have h2 : (a ^ 2) ^ 2 ≤ (n : ℤ) := by
    have : (a ^ 2) ^ 2 = a ^ 4 := by ring
    rw [this]; exact h
  have h3 : a ^ 2 ≤ (n : ℤ) := by
    have hh := abs_le_of_sq_le h2
    rwa [abs_of_nonneg (sq_nonneg a)] at hh
  exact abs_le_of_sq_le h3

/-- A crude individual bound for the Friedlander–Iwaniec representation count
`an n = #{(a,c) : ℤ × ℤ | a^2 + c^4 = n}` (`Submission.an`): `an n ≤ (2n+1)^2`.  Indeed every
solution has `|a| ≤ n` (from `a^2 ≤ n`) and `|c| ≤ n` (from `c^4 ≤ n`), so the solution set is
contained in the `(2n+1)^2`-element box `[-n,n] × [-n,n] ⊆ ℤ × ℤ`; conclude with
`Set.ncard_le_ncard` against `(Finset.Icc (-n) n ×ˢ Finset.Icc (-n) n).toSet`. -/
theorem an_le_sq (n : ℕ) : (Submission.an n : ℝ) ≤ (2 * (n : ℝ) + 1) ^ 2 := by
  have hmain : Submission.an n ≤ (2 * n + 1) ^ 2 := by
    unfold Submission.an
    have hsub : {x : ℤ × ℤ | x.1 ^ 2 + x.2 ^ 4 = (n : ℤ)} ⊆
        ((↑(Finset.Icc (-(n : ℤ)) (n : ℤ)) : Set ℤ) ×ˢ
          (↑(Finset.Icc (-(n : ℤ)) (n : ℤ)) : Set ℤ)) := by
      intro x hx
      have hx' : x.1 ^ 2 + x.2 ^ 4 = (n : ℤ) := hx
      simp only [Set.mem_prod, Finset.mem_coe, Finset.mem_Icc]
      have h1 : x.1 ^ 2 ≤ (n : ℤ) := by
        have h2 : (0 : ℤ) ≤ x.2 ^ 4 := by
          have : x.2 ^ 4 = (x.2 ^ 2) ^ 2 := by ring
          rw [this]; exact sq_nonneg _
        linarith
      have h2 : x.2 ^ 4 ≤ (n : ℤ) := by
        have : (0 : ℤ) ≤ x.1 ^ 2 := sq_nonneg _
        linarith
      exact ⟨abs_le.mp (abs_le_of_sq_le h1), abs_le.mp (abs_le_of_pow_four_le h2)⟩
    calc ({x : ℤ × ℤ | x.1 ^ 2 + x.2 ^ 4 = (n : ℤ)}).ncard
        ≤ (((↑(Finset.Icc (-(n : ℤ)) (n : ℤ)) : Set ℤ) ×ˢ
            (↑(Finset.Icc (-(n : ℤ)) (n : ℤ)) : Set ℤ))).ncard :=
          Set.ncard_le_ncard hsub
      _ = (↑(Finset.Icc (-(n : ℤ)) (n : ℤ)) : Set ℤ).ncard *
            (↑(Finset.Icc (-(n : ℤ)) (n : ℤ)) : Set ℤ).ncard := Set.ncard_prod
      _ = (Finset.Icc (-(n : ℤ)) (n : ℤ)).card * (Finset.Icc (-(n : ℤ)) (n : ℤ)).card := by
            rw [Set.ncard_coe_finset]
      _ = (2 * n + 1) ^ 2 := by
          rw [Int.card_Icc]
          rw [show ((n : ℤ) + 1 - (-(n : ℤ))) = ((2 * n + 1 : ℕ) : ℤ) by push_cast; ring,
            Int.toNat_natCast]
          ring
  calc (Submission.an n : ℝ) ≤ (((2 * n + 1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hmain
    _ = (2 * (n : ℝ) + 1) ^ 2 := by push_cast; ring

end Work.FIPiChain.P3S3
