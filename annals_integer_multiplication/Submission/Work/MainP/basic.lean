import Mathlib
import Submission.HvdH.Interfaces

/-! Core arithmetic facts for the `MainParams` area (paper §5.1, Harvey–van der Hoeven).

This module holds the elementary facts about `bpar n = Nat.clog 2 n` that every conjunct of
`HvdH.MainParamsProp` needs.  The threshold for the area is *never written down*: it is an
astronomical power of two, so we produce it with `Filter.eventually_atTop` (see
`mainParams.lean`); all the lemmas here take hypotheses of the form `2^61 ≤ bpar n`. -/

namespace Work.MainP

theorem one_lt_two : (1 : ℕ) < 2 := by norm_num

/-- For every `C`, all large `n` satisfy `C ≤ bpar n`.  (The witness `2 ^ C` is symbolic, so the
kernel is never asked to evaluate the astronomical `2 ^ (2^61)`.) -/
theorem eventual_bpar_ge (C : ℕ) : ∀ᶠ n in Filter.atTop, C ≤ HvdH.bpar n := by
  refine Filter.eventually_atTop.mpr ⟨2 ^ C, fun n hn => ?_⟩
  have h := Nat.clog_mono_right 2 hn
  rwa [Nat.clog_pow 2 C one_lt_two] at h

/-- `n ≤ 2 ^ bpar n`. -/
theorem le_two_pow_bpar (n : ℕ) : n ≤ 2 ^ HvdH.bpar n := Nat.le_pow_clog one_lt_two n

/-- `2 ^ (bpar n - 1) < n` for `1 < n`. -/
theorem pow_pred_lt_of_bpar (n : ℕ) (h : 1 < n) : 2 ^ (HvdH.bpar n - 1) < n := by
  have := Nat.pow_pred_clog_lt_self one_lt_two h
  simpa [HvdH.bpar, Nat.pred_eq_sub_one] using this

/-- `1 < n` whenever `bpar n ≥ 1`. -/
theorem one_lt_of_bpar_pos (n : ℕ) (h : 1 ≤ HvdH.bpar n) : 1 < n := by
  by_contra hc
  push Not at hc
  have : HvdH.bpar n = 0 := Nat.clog_of_right_le_one hc 2
  omega

/-- `2 ^ j ≤ n` whenever `j < bpar n`. -/
theorem two_pow_le_n (n j : ℕ) (h : j < HvdH.bpar n) : 2 ^ j ≤ n := by
  have h1 : 1 < n := one_lt_of_bpar_pos n (by omega)
  have h2 : 2 ^ j ≤ 2 ^ (HvdH.bpar n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact h2.trans (le_of_lt (pow_pred_lt_of_bpar n h1))

/-- `20 e + 19 ≤ 2 ^ e` for `e ≥ 20`. -/
theorem aux_twenty_mul_add (e : ℕ) (he : 20 ≤ e) : 20 * e + 19 ≤ 2 ^ e := by
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ e he ih =>
    calc 20 * (e + 1) + 19 = 20 * e + 39 := by ring
      _ ≤ 2 * (20 * e + 19) := by omega
      _ ≤ 2 * 2 ^ e := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (e + 1) := by ring

/-- `b ≤ 2 ^ (b / 20)` for `b ≥ 400`. -/
theorem self_le_two_pow_div (b : ℕ) (hb : 400 ≤ b) : b ≤ 2 ^ (b / 20) := by
  have h20 : 20 ≤ b / 20 := by omega
  have h1 := aux_twenty_mul_add (b / 20) h20
  have h2 : b ≤ 20 * (b / 20) + 19 := by omega
  exact h2.trans h1

/-- `b ^ 10 ≤ 2 ^ (b / 2)` for `b ≥ 400`. -/
theorem pow10_le_two_pow (b : ℕ) (hb : 400 ≤ b) : b ^ 10 ≤ 2 ^ (b / 2) := by
  have h1 : b ^ 10 ≤ (2 ^ (b / 20)) ^ 10 := Nat.pow_le_pow_left (self_le_two_pow_div b hb) 10
  have h2 : (2 ^ (b / 20)) ^ 10 = 2 ^ (10 * (b / 20)) := by rw [← pow_mul, Nat.mul_comm]
  have h3 : 10 * (b / 20) ≤ b / 2 := by
    have h : b / 20 * 20 ≤ b := Nat.div_mul_le_self b 20
    exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr (by omega)
  exact h1.trans (h2.trans_le (Nat.pow_le_pow_right (by norm_num) h3))

/-- `bpar n ^ 10 ≤ n` whenever `bpar n` is large. -/
theorem bpow10_le_n (n : ℕ) (h : 400 ≤ HvdH.bpar n) : HvdH.bpar n ^ 10 ≤ n := by
  have h1 : HvdH.bpar n ^ 10 ≤ 2 ^ (HvdH.bpar n / 2) := pow10_le_two_pow _ h
  have h2 : HvdH.bpar n / 2 ≤ HvdH.bpar n - 1 := by omega
  have h3 : 2 ^ (HvdH.bpar n / 2) ≤ 2 ^ (HvdH.bpar n - 1) :=
    Nat.pow_le_pow_right (by norm_num) h2
  have h4 : 1 < n := one_lt_of_bpar_pos n (by omega)
  exact h1.trans (h3.trans (le_of_lt (pow_pred_lt_of_bpar n h4)))

/-- `sqrt b ≤ b / 2^30` for `b ≥ 2^61`. -/
theorem sqrt_le_div (b : ℕ) (hb : 2 ^ 61 ≤ b) : Nat.sqrt b ≤ b / 2 ^ 30 := by
  rw [Nat.le_div_iff_mul_le (by positivity : 0 < 2 ^ 30)]
  have h1 : 2 ^ 30 ≤ Nat.sqrt b := by
    rw [Nat.le_sqrt]
    calc (2 : ℕ) ^ 30 * 2 ^ 30 = 2 ^ 60 := by ring
      _ ≤ 2 ^ 61 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
      _ ≤ b := hb
  calc Nat.sqrt b * 2 ^ 30 ≤ Nat.sqrt b * Nat.sqrt b := Nat.mul_le_mul_left _ h1
    _ = Nat.sqrt b ^ 2 := by ring
    _ ≤ b := Nat.sqrt_le' b

/-- `∏ l = ∏ i < m, l.getD i 0` for a list of length `m`. -/
theorem List.prod_eq_ofFn_getD {l : List ℕ} {m : ℕ} (h : l.length = m) :
    l.prod = (List.ofFn (fun i : Fin m => l.getD i 0)).prod := by
  subst h
  rw [List.prod_ofFn]
  conv_lhs => rw [← List.ofFn_getElem (xs := l)]
  rw [List.prod_ofFn]
  congr 1
  ext i
  rw [List.getD_eq_getElem]

end Work.MainP
