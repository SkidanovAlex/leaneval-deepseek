/-
**AR-SMALL** (`Work.GW2.C16.ArithSmallProp`, BG 1981, §4 end, pp. 214–215).

Pure arithmetic: `1 + a + b + c = 0` with `a, b, c` odd and each either `1` or of modulus `≥ 3`,
together with `N·(abc + bc + ac + ab) = 2k²·abc` (`N` odd), forces `N < 3·(2k²) < 9N`.

Route.  Each of `a, b, c` is non-zero and lies in `{1} ∪ {odd ≥ 3} ∪ {odd ≤ -3}`; hence
`1 ≤ x ∨ x ≤ -3` for each of them.  Clearing denominators in the identity gives
`N · (1 + 1/a + 1/b + 1/c) = 2k²` (in `ℚ`).  The case analysis on the three signs leaves
(in view of `a + b + c = -1`) only the patterns "two positive, one negative" and "one positive,
two negative"; in each, the reciprocal sum `r := 1 + 1/a + 1/b + 1/c` satisfies
`1/3 < r < 3` (estimates `0 < 1/x ≤ 1` for `x ≥ 1`, `1/x < 0` and `-1/3 ≤ 1/x` for `x ≤ -3`).
Since `N > 0` (`N` odd), `2k² = N r` lies strictly between `N/3` and `3N`.
-/
import Mathlib
import Submission.Work.BG.ThmABCDefs

namespace Work.BG

/-- A non-zero integer version of the sign fact: `x = 1` or `|x| ≥ 3` forces `x ≠ 0`. -/
theorem arithSmall_ne_zero_of {x : ℤ} (h : x = 1 ∨ 3 ≤ |x|) : x ≠ 0 := by
  rcases h with h | h
  · omega
  · intro hx; rw [hx] at h; norm_num at h

/-- `x = 1` or `|x| ≥ 3` implies `1 ≤ x` or `x ≤ -3`. -/
theorem arithSmall_one_le_or_le_neg {x : ℤ} (h : x = 1 ∨ 3 ≤ |x|) : 1 ≤ x ∨ x ≤ -3 := by
  rcases h with h | h
  · omega
  · rcases le_or_gt 0 x with hx | hx
    · left; rw [abs_of_nonneg hx] at h; omega
    · right; rw [abs_of_neg hx] at h; omega

/-- For `x ≤ -3` in `ℚ`: the reciprocal is negative but `≥ -1/3`. -/
theorem arithSmall_neg_bound {x : ℚ} (h : x ≤ -3) : (1:ℚ)/x < 0 ∧ -(1/3) ≤ 1/x := by
  have hx : x < 0 := by linarith
  have h3 : (3:ℚ) ≤ -x := by linarith
  refine ⟨one_div_neg.mpr hx, ?_⟩
  have h1 : (1:ℚ) / (-x) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) h3
  have h2 : (1:ℚ) / (-x) = -(1 / x) := div_neg 1
  rw [h2] at h1
  linarith

/-- For `1 ≤ x` in `ℚ`: `0 < 1/x ≤ 1`. -/
theorem arithSmall_pos_bound {x : ℚ} (h : 1 ≤ x) : 0 < 1/x ∧ 1/x ≤ 1 := by
  refine ⟨by positivity, ?_⟩
  have := one_div_le_one_div_of_le (by norm_num : (0:ℚ) < 1) h
  simpa using this

/-- Two positives `≥ 1` and one negative `≤ -3`: the reciprocal sum lies in `(1/3, 3)`. -/
theorem arithSmall_bound_two_pos {p q n : ℚ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hn : n ≤ -3) :
    1/3 < 1 + 1/p + 1/q + 1/n ∧ 1 + 1/p + 1/q + 1/n < 3 := by
  obtain ⟨hp0, hp1⟩ := arithSmall_pos_bound hp
  obtain ⟨hq0, hq1⟩ := arithSmall_pos_bound hq
  obtain ⟨hn0, hn1⟩ := arithSmall_neg_bound hn
  constructor <;> linarith

/-- One positive `≥ 1` and two negatives `≤ -3`: the reciprocal sum lies in `(1/3, 3)`. -/
theorem arithSmall_bound_one_pos {p m n : ℚ} (hp : 1 ≤ p) (hm : m ≤ -3) (hn : n ≤ -3) :
    1/3 < 1 + 1/p + 1/m + 1/n ∧ 1 + 1/p + 1/m + 1/n < 3 := by
  obtain ⟨hp0, hp1⟩ := arithSmall_pos_bound hp
  obtain ⟨hm0, hm1⟩ := arithSmall_neg_bound hm
  obtain ⟨hn0, hn1⟩ := arithSmall_neg_bound hn
  constructor <;> linarith

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem arithSmall : Work.GW2.C16.ArithSmallProp := by
  intro N k a b c hN ha hb hc ha' hb' hc' hsum hid
  have hna : a ≠ 0 := arithSmall_ne_zero_of ha'
  have hnb : b ≠ 0 := arithSmall_ne_zero_of hb'
  have hnc : c ≠ 0 := arithSmall_ne_zero_of hc'
  -- the identity, cast to `ℚ`
  have hQ : (N:ℚ) * ((a:ℚ)*(b:ℚ)*(c:ℚ) + (b:ℚ)*(c:ℚ) + (a:ℚ)*(c:ℚ) + (a:ℚ)*(b:ℚ))
      = 2*(k:ℚ)^2 * ((a:ℚ)*(b:ℚ)*(c:ℚ)) := by
    have h := congrArg (fun z : ℤ => (z:ℚ)) hid
    push_cast at h
    exact h
  -- divided form: `N · r = 2k²` with `r = 1 + 1/a + 1/b + 1/c`
  have hr : (N:ℚ) * (1 + 1/(a:ℚ) + 1/(b:ℚ) + 1/(c:ℚ)) = 2*(k:ℚ)^2 := by
    have ha0 : (a:ℚ) ≠ 0 := by exact_mod_cast hna
    have hb0 : (b:ℚ) ≠ 0 := by exact_mod_cast hnb
    have hc0 : (c:ℚ) ≠ 0 := by exact_mod_cast hnc
    field_simp
    linarith [hQ]
  have haq : (1:ℚ) ≤ (a:ℚ) ∨ (a:ℚ) ≤ -3 := by
    rcases arithSmall_one_le_or_le_neg ha' with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  have hbq : (1:ℚ) ≤ (b:ℚ) ∨ (b:ℚ) ≤ -3 := by
    rcases arithSmall_one_le_or_le_neg hb' with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  have hcq : (1:ℚ) ≤ (c:ℚ) ∨ (c:ℚ) ≤ -3 := by
    rcases arithSmall_one_le_or_le_neg hc' with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  have hsumQ : (a:ℚ) + (b:ℚ) + (c:ℚ) = -1 := by
    have h : ((1 + a + b + c : ℤ) : ℚ) = 0 := by rw [hsum]; norm_num
    push_cast at h
    linarith
  -- the three sign patterns left by `a + b + c = -1`
  have hkey : 1/3 < 1 + 1/(a:ℚ) + 1/(b:ℚ) + 1/(c:ℚ) ∧
      1 + 1/(a:ℚ) + 1/(b:ℚ) + 1/(c:ℚ) < 3 := by
    rcases haq with haq | haq <;> rcases hbq with hbq | hbq <;> rcases hcq with hcq | hcq
    · exfalso; linarith
    · have H := arithSmall_bound_two_pos haq hbq hcq
      exact ⟨by linarith [H.1], by linarith [H.2]⟩
    · have H := arithSmall_bound_two_pos haq hcq hbq
      exact ⟨by linarith [H.1], by linarith [H.2]⟩
    · have H := arithSmall_bound_one_pos haq hbq hcq
      exact ⟨by linarith [H.1], by linarith [H.2]⟩
    · have H := arithSmall_bound_two_pos hbq hcq haq
      exact ⟨by linarith [H.1], by linarith [H.2]⟩
    · have H := arithSmall_bound_one_pos hbq haq hcq
      exact ⟨by linarith [H.1], by linarith [H.2]⟩
    · have H := arithSmall_bound_one_pos hcq haq hbq
      exact ⟨by linarith [H.1], by linarith [H.2]⟩
    · exfalso; linarith
  have hNpos : (0:ℚ) < (N:ℚ) := by
    have hN1 : 0 < N := by rcases hN with ⟨m, hm⟩; omega
    exact_mod_cast hN1
  constructor
  · rw [← Nat.cast_lt (α := ℚ)]
    push_cast
    nlinarith [hr, hkey.1, hNpos]
  · rw [← Nat.cast_lt (α := ℚ)]
    push_cast
    nlinarith [hr, hkey.2, hNpos]

end Work.BG
