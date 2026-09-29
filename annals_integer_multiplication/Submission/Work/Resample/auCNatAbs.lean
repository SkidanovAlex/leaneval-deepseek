import Mathlib
import Submission.Work.Resample.auDefs
import Submission.Work.Resample.auPrepDefs
import Submission.Work.Resample.auKClose
import Submission.Work.Resample.auMBound

/-!
# Size bound for the window offset `auC` (paper §4, Lemma 4.9)

`auC p α s t k = t·K_k − t·m − s·k` is `t` times the distance of the window centre `K_k` from
`s k / t`, so `|auC| ≤ t·(m+1) ≤ 2^p·2^p = 2^{2p}`: the value fits in `2p+2` bits.
-/

namespace Work.Resample

/-- `2n+1 ≤ 2^n` for `n ≥ 3` (the window half-width `auM p α ≤ 2p` has to fit into `2^p`). -/
theorem au_two_mul_add_one_le_two_pow (n : ℕ) (hn : 3 ≤ n) : 2 * n + 1 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have h2 : 2 ≤ 2 ^ n := by
        have hn1 : 1 ≤ n := by omega
        calc (2 : ℕ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn1
      rw [pow_succ]
      omega

theorem auCNatAbs (p α s t k : ℕ) (hs : 2 ≤ s) (hst : s < t) (htp : t < 2 ^ p)
    (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p) (hk : k < t) :
    (Work.Resample.auC p α s t k).natAbs ≤ 2 ^ (2 * p + 2) := by
  have ht1 : 1 ≤ t := by omega
  -- `t·K_k` is within `t` of `s·k`
  have hKc : |(t : ℤ) * (auK s t k : ℤ) - (s : ℤ) * (k : ℤ)| ≤ (t : ℤ) :=
    auKClose s t k ht1
  -- the window half-width fits into `2^p`
  have hm1 : auM p α + 1 ≤ 2 ^ p := by
    have h := au_two_mul_add_one_le_two_pow p (by omega)
    have h2 := auMBound p α hp hαp
    omega
  have hCeq : auC p α s t k
      = ((t : ℤ) * (auK s t k : ℤ) - (s : ℤ) * (k : ℤ)) - (t : ℤ) * (auM p α : ℤ) := by
    simp only [auC]
    ring
  have ht0 : (0 : ℤ) ≤ (t : ℤ) := by positivity
  have hm0 : (0 : ℤ) ≤ (auM p α : ℤ) := by positivity
  have htm : (0 : ℤ) ≤ (t : ℤ) * (auM p α : ℤ) := mul_nonneg ht0 hm0
  -- the value is bounded by `t·(m+1)`
  have habs : |auC p α s t k| ≤ ((t * (auM p α + 1) : ℕ) : ℤ) := by
    have hstep : |auC p α s t k| ≤ (t : ℤ) * ((auM p α : ℤ) + 1) := by
      rw [hCeq, abs_le]
      obtain ⟨h1, h2⟩ := abs_le.mp hKc
      constructor <;> linarith
    calc |auC p α s t k| ≤ (t : ℤ) * ((auM p α : ℤ) + 1) := hstep
      _ = ((t * (auM p α + 1) : ℕ) : ℤ) := by push_cast; ring
  -- the numerical bound
  have hNle : t * (auM p α + 1) ≤ 2 ^ (2 * p + 2) := by
    calc t * (auM p α + 1) ≤ 2 ^ p * 2 ^ p := Nat.mul_le_mul (le_of_lt htp) hm1
      _ = 2 ^ (2 * p) := by rw [← pow_add]; ring_nf
      _ ≤ 2 ^ (2 * p + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [← Int.ofNat_le, Int.natCast_natAbs]
  calc |auC p α s t k| ≤ ((t * (auM p α + 1) : ℕ) : ℤ) := habs
    _ ≤ ((2 ^ (2 * p + 2) : ℕ) : ℤ) := by exact_mod_cast hNle

end Work.Resample
