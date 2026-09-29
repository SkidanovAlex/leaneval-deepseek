import Mathlib
import Submission.Work.Resample.auPrepDefs
import Submission.Work.Resample.auMLe

/-!
# Small sizes for the static parameters of the resampling word (paper Lemma 4.9)

`Work.Resample.auSZ p = 10p + 400` is the uniform bound on `HvdH.isz` for every value occurring in
the table word `Work.Resample.auPrep`.  This module records that bound for the *inputs* of the word
(`p`, `α`, `s`, `t`, the label `k`) and for the *indices* of the inner `mapList`
(`i < auL p α = 2·auM p α + 1`).

The hypotheses are those of `auSizeBounds`/`auPrep`: `2 ≤ s < t < 2^p`, `2 ≤ α`, `100 ≤ p`,
`α^2 < p`, `k < t`.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- A linear quantity is dominated by an exponential one: `4p + 1 < 2^p` for `p ≥ 100`. -/
theorem four_mul_add_one_lt_two_pow : ∀ p : ℕ, 100 ≤ p → 4 * p + 1 < 2 ^ p := by
  intro p
  induction p with
  | zero => omega
  | succ m ih =>
      intro hm
      rcases Nat.lt_or_ge m 100 with hlt | hge
      · have hm1 : m + 1 = 100 := by omega
        rw [hm1]
        norm_num
      · have h1 : 4 * m + 1 < 2 ^ m := ih hge
        have h2 : 4 * (m + 1) + 1 < 2 * (4 * m + 1) := by omega
        have h3 : 2 * (4 * m + 1) ≤ 2 * 2 ^ m := Nat.mul_le_mul_left 2 (le_of_lt h1)
        have h4 : 2 * 2 ^ m = 2 ^ (m + 1) := by rw [pow_succ]; ring
        omega

theorem auSmallSizes (p α s t k : ℕ) (hs : 2 ≤ s) (hst : s < t) (htp : t < 2 ^ p)
    (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p) (hk : k < t) :
    HvdH.isz ((k : ℤ)) ≤ Work.Resample.auSZ p ∧
      HvdH.isz ((s : ℤ)) ≤ Work.Resample.auSZ p ∧
      HvdH.isz ((t : ℤ)) ≤ Work.Resample.auSZ p ∧
      HvdH.isz ((p : ℤ)) ≤ Work.Resample.auSZ p ∧
      HvdH.isz ((α : ℤ)) ≤ Work.Resample.auSZ p ∧
      (∀ i, i < Work.Resample.auL p α → HvdH.isz ((i : ℤ)) ≤ Work.Resample.auSZ p) := by
  -- `α` is small, because `α² < p < 2^p`
  have hαpow : α < 2 ^ p := by
    have h1 : α < α ^ 2 := by nlinarith [hα]
    have h2 : α ^ 2 < 2 ^ p := lt_trans hαp (Nat.lt_two_pow_self)
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isz_le_pow2 (le_of_lt (lt_trans hk htp))
  · exact isz_le_pow2 (le_of_lt (lt_trans hst htp))
  · exact isz_le_pow2 (le_of_lt htp)
  · exact isz_le_pow2 (le_of_lt Nat.lt_two_pow_self)
  · exact isz_le_pow2 (le_of_lt hαpow)
  · intro i hi
    have hL : auL p α ≤ 4 * p + 1 := (auMLe p α hα hαp).2
    have hi' : i ≤ 2 ^ p :=
      le_trans (le_of_lt (lt_of_lt_of_le hi hL)) (le_of_lt (four_mul_add_one_lt_two_pow p hp))
    exact isz_le_pow2 hi'

end Work.Resample
