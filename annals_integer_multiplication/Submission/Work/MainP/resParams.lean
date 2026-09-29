import Mathlib
import Submission.Work.MainP.basic

namespace Work.MainP

/-! ## `ParamOK n ts ss` ⇒ `ResParams (ppar n) (apar n) ss ts` (paper Theorem 4.1 hypotheses)

The two ingredients below are pure arithmetic, independent of `n`:

* `ratioBound`: the window `s ≤ (1 - 1/(4d)) t` together with `4 d p ≤ α⁴` gives
  `p / α⁴ ≤ t/s - 1` (this is the last conjunct of `ResParams`);
* `coprime_of_pow2`: an odd `s` is coprime to any divisor of a power of two
  (the `tᵢ` are `rpar n` or `rpar n / 2`, and `rpar n` is a power of two). -/

/-- If `s ≤ (1 - 1/(4d))·t` with `s > 0`, `α > 0` and `4dp ≤ α⁴`, then
`p/α⁴ ≤ t/s - 1`.  Indeed `s ≤ t - t/(4d)` gives `4d(t-s) ≥ t ≥ s`, so
`t/s - 1 = (t-s)/s ≥ 1/(4d) ≥ p/α⁴`. -/
theorem ratioBound (d s t p α : ℕ) (hd : 1 ≤ d) (hs : 0 < s) (hα : 0 < α)
    (hp : 4 * d * p ≤ α ^ 4)
    (hwin : (s : ℝ) ≤ (1 - 1 / (4 * d : ℝ)) * (t : ℝ)) :
    (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / (s : ℝ) - 1 := by
  have hdR : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have h4d : (0:ℝ) < 4*(d:ℝ) := by linarith
  have hsR : (0:ℝ) < (s:ℝ) := by exact_mod_cast hs
  have hα4 : (0:ℝ) < (α:ℝ)^4 := by positivity
  have hp' : (p:ℝ) * (4*(d:ℝ)) ≤ (α:ℝ)^4 := by
    have h : (4:ℝ)*(d:ℝ)*(p:ℝ) ≤ (α:ℝ)^4 := by exact_mod_cast hp
    linarith
  have h1 : (p:ℝ)/(α:ℝ)^4 ≤ 1/(4*(d:ℝ)) := by
    rw [div_le_div_iff₀ hα4 h4d]
    simpa using hp'
  have htR : (0:ℝ) < (t:ℝ) := by
    have hcoef : (0:ℝ) < 1 - 1/(4*(d:ℝ)) := by
      have hlt : 1/(4*(d:ℝ)) < 1 := by
        rw [div_lt_one h4d]; linarith
      linarith
    nlinarith [hwin, hsR, hcoef]
  have hsub : (t:ℝ)/(s:ℝ) - 1 = ((t:ℝ) - (s:ℝ))/(s:ℝ) := by
    rw [div_sub_one (ne_of_gt hsR)]
  have hcle : 4*(d:ℝ)*(s:ℝ) ≤ (4*(d:ℝ) - 1)*(t:ℝ) := by
    have h := mul_le_mul_of_nonneg_left hwin h4d.le
    rwa [show (4*(d:ℝ))*((1-1/(4*(d:ℝ)))*(t:ℝ)) = (4*(d:ℝ)-1)*(t:ℝ) from by
      field_simp] at h
  have hsle : (s:ℝ) ≤ (t:ℝ) := by
    have hq : (0:ℝ) < 1/(4*(d:ℝ)) := by positivity
    have : (1 - 1/(4*(d:ℝ))) * (t:ℝ) ≤ (t:ℝ) := by nlinarith
    exact le_trans hwin this
  have h2 : 1/(4*(d:ℝ)) ≤ (t:ℝ)/(s:ℝ) - 1 := by
    rw [hsub, div_le_div_iff₀ h4d hsR]
    nlinarith [hcle, hsle, h4d]
  exact le_trans h1 h2

/-- An odd `s` is coprime to `t` when `t = 2^k` or `2t = 2^k` (so `t ∣ 2^k`). -/
theorem coprime_of_pow2 (s t k : ℕ) (hodd : Odd s) (h : t = 2 ^ k ∨ 2 * t = 2 ^ k) :
    Nat.Coprime s t := by
  have ht : t ∣ 2 ^ k := by
    rcases h with h | h
    · exact ⟨1, by rw [h, mul_one]⟩
    · exact ⟨2, by rw [← h]; ring⟩
  have hcs : Nat.Coprime s (2 ^ k) := (Nat.coprime_two_right.mpr hodd).pow_right k
  exact Nat.Coprime.coprime_dvd_right ht hcs

/-- `ParamOK n ts ss` gives `ResParams (ppar n) (apar n) ss ts` (paper Thm 4.1 hypotheses).
From the window `(1-1/(2d))tᵢ < sᵢ ≤ (1-1/(4d))tᵢ`: `2 ≤ sᵢ` (as `rpar ≥ 8` so `tᵢ ≥ 4`),
`sᵢ < tᵢ` and `tᵢ < 2^ppar` (`tᵢ ≤ rpar ≤ Tpar < 2^ppar`); `coprime sᵢ tᵢ` (odd `sᵢ`, `tᵢ` a power
of two); and `p/α⁴ ≤ tᵢ/sᵢ - 1` because `sᵢ ≤ (1-1/(4d))tᵢ` gives `tᵢ/sᵢ - 1 ≥ 1/(4d-1) ≥ 1/(4d)`,
while `4d·p ≤ α⁴` gives `p/α⁴ ≤ 1/(4d)`. -/
theorem resParams (n : ℕ) (ts ss : List ℕ) (hOK : HvdH.ParamOK n ts ss)
    (h100 : 100 ≤ HvdH.ppar n) (h2a : 2 ≤ HvdH.apar n)
    (ha2 : HvdH.apar n ^ 2 < HvdH.ppar n)
    (ha4 : 4 * HvdH.D * HvdH.ppar n ≤ HvdH.apar n ^ 4)
    (h8r : 8 ≤ HvdH.rpar n) (hrT : HvdH.rpar n ≤ HvdH.Tpar n)
    (hT : HvdH.Tpar n < 2 ^ HvdH.ppar n) :
    HvdH.ResParams (HvdH.ppar n) (HvdH.apar n) ss ts := by
  obtain ⟨htlen, hslen, -, -, hmem, hwin, -, hsodd⟩ := hOK
  refine ⟨hslen, htlen, h100, h2a, ha2, ?_⟩
  intro i hi
  have hiT : i < ts.length := by omega
  have hiS : i < ss.length := by omega
  set t := ts.getD i 0 with ht_eq
  set s := ss.getD i 0 with hs_eq
  have htin : t ∈ ts := by
    rw [ht_eq, List.getD_eq_getElem ts 0 hiT]; exact List.getElem_mem hiT
  have hsin : s ∈ ss := by
    rw [hs_eq, List.getD_eq_getElem ss 0 hiS]; exact List.getElem_mem hiS
  obtain ⟨hw1, hw2⟩ := hwin i hi
  rw [← hs_eq, ← ht_eq] at hw1 hw2
  -- `tᵢ ∈ {rpar n/2, rpar n}` and `rpar n ≥ 8`, so `4 ≤ tᵢ ≤ rpar n`
  have ht4 : 4 ≤ t := by rcases hmem t htin with h | h <;> omega
  have htr : t ≤ HvdH.rpar n := by rcases hmem t htin with h | h <;> omega
  have hodd : Odd s := hsodd s hsin
  -- `2 ≤ sᵢ`: the window gives `s > (3/4)·4 = 3`
  have hs2 : 2 ≤ s := by
    have h3 : (3:ℝ) < (s:ℝ) := by
      have hcoef : (3:ℝ)/4 ≤ 1 - 2 / (4 * HvdH.D : ℝ) := by
        rw [show HvdH.D = 1729 from rfl]; norm_num
      have htR : (4:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht4
      have h1 : (3:ℝ)/4 * (t:ℝ) ≤ (1 - 2 / (4 * HvdH.D : ℝ)) * (t:ℝ) :=
        mul_le_mul_of_nonneg_right hcoef (by norm_num)
      nlinarith [hw1, h1, htR]
    have : 3 < s := by exact_mod_cast h3
    omega
  -- `sᵢ < tᵢ`: `s ≤ (1 - 1/(4d))t < t` as `t > 0`
  have hst : s < t := by
    have htR : (0:ℝ) < (t:ℝ) := by exact_mod_cast (by omega : 0 < t)
    have hq : (0:ℝ) < 1 / (4 * HvdH.D : ℝ) := by
      rw [show HvdH.D = 1729 from rfl]; norm_num
    have hlt : (1 - 1 / (4 * HvdH.D : ℝ)) * (t:ℝ) < (t:ℝ) := by nlinarith
    have : (s:ℝ) < (t:ℝ) := lt_of_le_of_lt hw2 hlt
    exact_mod_cast this
  -- `tᵢ ≤ rpar n ≤ Tpar n < 2^ppar n`
  have htt : t < 2 ^ HvdH.ppar n := lt_of_le_of_lt (le_trans htr hrT) hT
  -- `tᵢ` is a power of two (`rpar n = 2^k`) and `sᵢ` is odd
  have hcp : Nat.Coprime s t := by
    refine coprime_of_pow2 s t ((HvdH.kTpar n + HvdH.D - 1) / HvdH.D) hodd ?_
    have hr : HvdH.rpar n = 2 ^ ((HvdH.kTpar n + HvdH.D - 1) / HvdH.D) := rfl
    rcases hmem t htin with h | h
    · exact Or.inl (by rw [h, hr])
    · exact Or.inr (by rw [h, hr])
  have hratio : (HvdH.ppar n : ℝ) / (HvdH.apar n : ℝ) ^ 4 ≤ (t:ℝ)/(s:ℝ) - 1 :=
    ratioBound HvdH.D s t (HvdH.ppar n) (HvdH.apar n)
      (by rw [show HvdH.D = 1729 from rfl]; norm_num) (by omega) (by omega) ha4 hw2
  exact ⟨hs2, hst, htt, hcp, hratio⟩

end Work.MainP
