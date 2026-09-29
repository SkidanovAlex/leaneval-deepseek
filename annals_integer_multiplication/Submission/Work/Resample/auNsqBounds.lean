import Mathlib
import Submission.Work.Resample.auDefs
import Submission.Work.Resample.auKClose
import Submission.Work.Resample.auMBound

namespace Work.Resample

/-- `2n+1 ≤ 2^n` for `n ≥ 3` (used to fit the window half-width `2p+1` into `2^p`). -/
theorem two_mul_add_one_le_two_pow (n : ℕ) (hn : 3 ≤ n) : 2 * n + 1 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have h2 : 2 ≤ 2 ^ n := by
        have hn1 : 1 ≤ n := by omega
        calc (2 : ℕ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn1
      rw [pow_succ]
      omega

theorem auNsqBounds (p α s t k i : ℕ) (hs : 2 ≤ s) (hst : s < t) (htp : t < 2 ^ p)
    (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p) (hk : k < t) (hi : i < Work.Resample.auL p α) :
    0 ≤ Work.Resample.auNsq p α s t k i ∧
      Work.Resample.auNsq p α s t k i ≤ (2 : ℤ) ^ (4 * p + 8) := by
  have ht1 : 1 ≤ t := by omega
  have hm : (auM p α : ℤ) ≤ 2 * (p : ℤ) := by
    have h := auMBound p α hp hαp
    exact_mod_cast h
  -- the rounding error of `auK`, as an integer
  set A : ℤ := (t : ℤ) * (auK s t k : ℤ) - (s : ℤ) * (k : ℤ) with hA
  have hAb : |A| ≤ (t : ℤ) := auKClose s t k ht1
  have hAuN : auN p α s t k i = A + (t : ℤ) * ((i : ℤ) - (auM p α : ℤ)) := by
    simp only [hA, auN]; ring
  -- the window offset is bounded by `auM`
  have hi2 : (i : ℤ) ≤ 2 * (auM p α : ℤ) := by
    have h : i ≤ 2 * auM p α := by simp only [auL] at hi ⊢; omega
    exact_mod_cast h
  have hib : |(i : ℤ) - (auM p α : ℤ)| ≤ (auM p α : ℤ) := by
    rw [abs_le]
    constructor
    · have h0 : (0 : ℤ) ≤ (i : ℤ) := by positivity
      linarith
    · linarith
  have ht0 : (0 : ℤ) ≤ (t : ℤ) := by positivity
  have hNle : |auN p α s t k i| ≤ (t : ℤ) * ((auM p α : ℤ) + 1) := by
    rw [hAuN]
    calc |A + (t : ℤ) * ((i : ℤ) - (auM p α : ℤ))|
        ≤ |A| + |(t : ℤ) * ((i : ℤ) - (auM p α : ℤ))| := abs_add_le _ _
      _ = |A| + (t : ℤ) * |(i : ℤ) - (auM p α : ℤ)| := by
            rw [abs_mul, abs_of_nonneg ht0]
      _ ≤ (t : ℤ) + (t : ℤ) * (auM p α : ℤ) := by
            have h := mul_le_mul_of_nonneg_left hib ht0
            linarith
      _ = (t : ℤ) * ((auM p α : ℤ) + 1) := by ring
  have htpow : (t : ℤ) ≤ (2 : ℤ) ^ p := by
    have h : t ≤ 2 ^ p := le_of_lt htp
    exact_mod_cast h
  have hm1pow : (auM p α : ℤ) + 1 ≤ (2 : ℤ) ^ p := by
    have h : auM p α + 1 ≤ 2 ^ p := by
      have h3 : 2 * p + 1 ≤ 2 ^ p := two_mul_add_one_le_two_pow p (by omega)
      have h2 := auMBound p α hp hαp
      omega
    exact_mod_cast h
  have hN2 : |auN p α s t k i| ≤ (2 : ℤ) ^ (2 * p + 2) := by
    have h2p : (2 : ℤ) ^ p * (2 : ℤ) ^ p = (2 : ℤ) ^ (2 * p) := by
      rw [← pow_add]; congr 1; ring
    calc |auN p α s t k i| ≤ (t : ℤ) * ((auM p α : ℤ) + 1) := hNle
      _ ≤ (2 : ℤ) ^ p * (2 : ℤ) ^ p := by
          have hm1 : (0 : ℤ) ≤ (auM p α : ℤ) + 1 := by positivity
          exact mul_le_mul htpow hm1pow hm1 (by positivity)
      _ = (2 : ℤ) ^ (2 * p) := h2p
      _ ≤ (2 : ℤ) ^ (2 * p + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  refine ⟨auNsq_nonneg p α s t k i, ?_⟩
  have hsq : auNsq p α s t k i ≤ ((2 : ℤ) ^ (2 * p + 2)) ^ 2 := by
    rw [auNsq, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hN2 2
  calc auNsq p α s t k i ≤ ((2 : ℤ) ^ (2 * p + 2)) ^ 2 := hsq
    _ = (2 : ℤ) ^ (4 * p + 4) := by rw [← pow_mul]; congr 1; ring
    _ ≤ (2 : ℤ) ^ (4 * p + 8) := pow_le_pow_right₀ (by norm_num) (by omega)

end Work.Resample
