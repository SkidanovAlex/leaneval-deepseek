import Mathlib
import Submission.Work.MainP.basic

namespace Work.MainP

/-- The exponent `(kTpar n + D - 1)/D` of `rpar n = 2^(that)` is at least `2` as soon as
`4 ≤ rpar n`. -/
lemma two_le_rpar_exp (n : ℕ) (h : 4 ≤ HvdH.rpar n) :
    2 ≤ (HvdH.kTpar n + HvdH.D - 1) / HvdH.D := by
  have h2 : 2 ^ 2 ≤ 2 ^ ((HvdH.kTpar n + HvdH.D - 1) / HvdH.D) := by
    calc 2 ^ 2 = 4 := by norm_num
      _ ≤ HvdH.rpar n := h
      _ = 2 ^ ((HvdH.kTpar n + HvdH.D - 1) / HvdH.D) := rfl
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2

/-- `rpar n = 2^j` is a power of two in the sense of `HvdH.IsPow2`, for `4 ≤ rpar n`
(so that `j ≥ 2`). -/
lemma isPow2_rpar (n : ℕ) (h : 4 ≤ HvdH.rpar n) : HvdH.IsPow2 (HvdH.rpar n) :=
  ⟨(HvdH.kTpar n + HvdH.D - 1) / HvdH.D, le_trans (by norm_num) (two_le_rpar_exp n h), rfl⟩

/-- Half of a power of two is a power of two, for exponent `≥ 2`. -/
lemma isPow2_two_pow_div_two {k : ℕ} (hk : 2 ≤ k) : HvdH.IsPow2 (2 ^ k / 2) := by
  refine ⟨k - 1, by omega, ?_⟩
  have h1 : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [h1, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]

/-- `rpar n / 2` is a power of two (i.e. the "small" dimension `tᵢ = r/2`). -/
lemma isPow2_rpar_div_two (n : ℕ) (h : 4 ≤ HvdH.rpar n) : HvdH.IsPow2 (HvdH.rpar n / 2) := by
  have h2 : 2 ≤ (HvdH.kTpar n + HvdH.D - 1) / HvdH.D := two_le_rpar_exp n h
  have := isPow2_two_pow_div_two (k := (HvdH.kTpar n + HvdH.D - 1) / HvdH.D) h2
  rwa [show (2 : ℕ) ^ ((HvdH.kTpar n + HvdH.D - 1) / HvdH.D) = HvdH.rpar n from rfl] at this

/-- `ParamOK n ts ss` gives `PowTwoParams (ppar n) ts` (paper Thm 3.1 hypotheses):
each `tᵢ` is `rpar n` or `rpar n / 2`, hence a power of two; `∏ tᵢ = Tpar n < 2^ppar n`. -/
theorem powTwoParams (n : ℕ) (ts ss : List ℕ) (hOK : HvdH.ParamOK n ts ss)
    (h4r : 4 ≤ HvdH.rpar n) (hT : HvdH.Tpar n < 2 ^ HvdH.ppar n)
    (h100 : 100 ≤ HvdH.ppar n) : HvdH.PowTwoParams (HvdH.ppar n) ts := by
  obtain ⟨hlen, -, hpair, hprod, hmem, -⟩ := hOK
  refine ⟨hlen, ?_, hpair, ?_, h100⟩
  · intro t ht
    rcases hmem t ht with h | h
    · exact h ▸ isPow2_rpar n h4r
    · have ht' : t = HvdH.rpar n / 2 := by
        rw [← h, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
      rw [ht']
      exact isPow2_rpar_div_two n h4r
  · rw [hprod]
    exact hT

end Work.MainP
