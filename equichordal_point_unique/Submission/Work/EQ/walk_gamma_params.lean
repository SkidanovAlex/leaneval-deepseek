import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.charValDefs
import Submission.Work.EQ.charVal_aux

/-!
# Numerical parameters of the fan walk

Auxiliary lemmas for `Work.EQ.walk_gamma_params`: closed forms of the distances `stQ a n` from
the `n`-th fan centre to `O₁ = -a/2` at even and odd states, and the resulting arithmetic of the
step weights `upW a n = λ(1 + 1/q n)`, `dnW a n = λ(1 - 1/q n)` with `λ = eqLam a`.
-/

namespace Work.EQ

/-- `λ = (1-a)/(1+a)` is positive for `0 < a < 1`. -/
lemma wg_eqLam_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 0 < eqLam a := by
  rw [eqLam]
  exact div_pos (by linarith) (by linarith)

/-- `stQ a (2k) = 2k + (1-a)/2`. -/
lemma wg_stQ_even {a : ℝ} (ha1 : a < 1) (k : ℕ) : stQ a (2 * k) = 2 * k + (1 - a) / 2 := by
  have h : stCtr (2 * k) + a / 2 = -(2 * (k : ℝ) + (1 - a) / 2) := by
    rw [stCtr, stIdx_even]
    push_cast
    ring
  have hpos : 0 < 2 * (k : ℝ) + (1 - a) / 2 := by
    have h0 : (0 : ℝ) ≤ 2 * (k : ℝ) := by positivity
    linarith
  rw [stQ, h, abs_neg, abs_of_pos hpos]

/-- `stQ a (2k+1) = 2k + (3+a)/2`. -/
lemma wg_stQ_odd {a : ℝ} (ha0 : 0 < a) (k : ℕ) : stQ a (2 * k + 1) = 2 * k + (3 + a) / 2 := by
  have h : stCtr (2 * k + 1) + a / 2 = 2 * (k : ℝ) + (3 + a) / 2 := by
    rw [stCtr, stIdx_odd]
    push_cast
    ring
  have hpos : 0 < 2 * (k : ℝ) + (3 + a) / 2 := by
    have h0 : (0 : ℝ) ≤ 2 * (k : ℝ) := by positivity
    linarith
  rw [stQ, h, abs_of_pos hpos]

/-- `stQ a n > 0` for every `n`. -/
lemma wg_stQ_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (n : ℕ) : 0 < stQ a n := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hk2 : k + k = 2 * k := by omega
    rw [hk, hk2, wg_stQ_even ha1 k]
    have h0 : (0 : ℝ) ≤ 2 * (k : ℝ) := by positivity
    linarith
  · rw [hk, wg_stQ_odd ha0 k]
    have h0 : (0 : ℝ) ≤ 2 * (k : ℝ) := by positivity
    linarith

/-- `stQ a n > 1` for every `n ≥ 1`. -/
lemma wg_stQ_gt_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {n : ℕ} (hn : 1 ≤ n) :
    1 < stQ a n := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hk2 : k + k = 2 * k := by omega
    have hk1 : 1 ≤ k := by omega
    rw [hk, hk2, wg_stQ_even ha1 k]
    have h2 : (2 : ℝ) ≤ 2 * (k : ℝ) := by
      have h3 : (2 : ℕ) ≤ 2 * k := by omega
      exact_mod_cast h3
    linarith
  · rw [hk, wg_stQ_odd ha0 k]
    have h0 : (0 : ℝ) ≤ 2 * (k : ℝ) := by positivity
    linarith

/-- The "up-then-down" weight identity in the case the two consecutive distances differ by
`1 + a`. -/
lemma wg_up_dn_id_add {lam a q : ℝ} (hq : q ≠ 0) (h : q + 1 + a ≠ 0) :
    (lam * (1 + 1 / q)) * (lam * (1 - 1 / (q + 1 + a))) =
      lam ^ 2 * (1 + a / (q * (q + 1 + a))) := by
  field_simp
  ring

/-- The "up-then-down" weight identity in the case the two consecutive distances differ by
`1 - a`. -/
lemma wg_up_dn_id_sub {lam a q : ℝ} (hq : q ≠ 0) (h : q + 1 - a ≠ 0) :
    (lam * (1 + 1 / q)) * (lam * (1 - 1 / (q + 1 - a))) =
      lam ^ 2 * (1 - a / (q * (q + 1 - a))) := by
  field_simp
  ring

/-- `a/(q*q') ≤ a/(q0*q1)` for positive denominators with `q0 ≤ q`, `q1 ≤ q'`, `0 < a`. -/
lemma wg_div_mul_le {a q q' q0 q1 : ℝ} (ha : 0 < a) (hq0 : 0 < q0) (hq1 : 0 < q1)
    (hq : q0 ≤ q) (hq' : q1 ≤ q') : a / (q * q') ≤ a / (q0 * q1) :=
  div_le_div_of_nonneg_left (le_of_lt ha) (mul_pos hq0 hq1)
    (mul_le_mul hq hq' (le_of_lt hq1) (le_trans (le_of_lt hq0) hq))

/-- The numerical value of the extreme parameter `γ = (3-a)(1-a)/((1+a)(3+a))` lies in `(0,1)`. -/
lemma wg_gamma_arith {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    0 < (3 - a) * (1 - a) / ((1 + a) * (3 + a)) ∧
    (3 - a) * (1 - a) / ((1 + a) * (3 + a)) < 1 := by
  have h1a : 0 < 1 - a := by linarith
  have h1pa : 0 < 1 + a := by linarith
  have h3ma : 0 < 3 - a := by linarith
  have h3pa : 0 < 3 + a := by linarith
  refine ⟨div_pos (mul_pos h3ma h1a) (mul_pos h1pa h3pa), ?_⟩
  rw [div_lt_one (mul_pos h1pa h3pa)]
  nlinarith

/-- The numerical parameters of the fan walk: `γ := upW a 0 * dnW a 1` lies in `(0,1)`, every up
weight is positive, every down weight from state `1` on is positive, `dnW a 0 = -1`, and the
extreme property `upW a n * dnW a (n + 1) ≤ γ` holds for every `n`.  (Here `upW a n = λ(1+1/q n)`,
`dnW a n = λ(1-1/q n)` with `λ = (1-a)/(1+a)` and `q n` the distance from the `n`-th fan centre
to `O₁`; `q` is strictly increasing, `q (2k) = 2k + (1-a)/2`, `q (2k+1) = 2k + (3+a)/2`, and
`upW a n * dnW a (n+1) = λ²(1 ± a/(q n · q (n+1)))`, whence the maximum over `n` is at `n = 0`
and equals `(1-a)(3+2a-a²)/((1+a)²(3+a)) < 1`.) -/
theorem walk_gamma_params {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    0 < upW a 0 * dnW a 1 ∧ upW a 0 * dnW a 1 < 1 ∧
    (∀ n : ℕ, 0 < upW a n) ∧
    (∀ n : ℕ, 1 ≤ n → 0 < dnW a n) ∧
    dnW a 0 = -1 ∧
    ∀ n : ℕ, upW a n * dnW a (n + 1) ≤ upW a 0 * dnW a 1 := by
  have hlam : 0 < eqLam a := wg_eqLam_pos ha0 ha1
  have h1a : 0 < 1 - a := by linarith
  have h1pa : 0 < 1 + a := by linarith
  have h3ma : 0 < 3 - a := by linarith
  have h3pa : 0 < 3 + a := by linarith
  have hq0 : stQ a 0 = (1 - a) / 2 := by simpa using wg_stQ_even ha1 0
  have hq1 : stQ a 1 = (3 + a) / 2 := by simpa using wg_stQ_odd ha0 0
  have hq1' : stQ a 1 = (1 - a) / 2 + 1 + a := by rw [hq1]; ring
  -- the value of `γ`
  have hgamma : upW a 0 * dnW a 1 = (3 - a) * (1 - a) / ((1 + a) * (3 + a)) := by
    simp only [upW, dnW, hq0, hq1, eqLam]
    field_simp
    ring
  obtain ⟨hgpos, hglt⟩ := wg_gamma_arith ha0 ha1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hgamma]; exact hgpos
  · rw [hgamma]; exact hglt
  · intro n
    simp only [upW]
    have hp : 0 < 1 / stQ a n := div_pos one_pos (wg_stQ_pos ha0 ha1 n)
    exact mul_pos hlam (by linarith)
  · intro n hn
    simp only [dnW]
    have hq := wg_stQ_gt_one ha0 ha1 hn
    have hp : 1 / stQ a n < 1 := by
      rw [div_lt_one (by linarith)]
      exact hq
    exact mul_pos hlam (by linarith)
  · exact dnW_zero ha0 ha1
  · intro n
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- `n = k + k`: consecutive distances differ by `1 + a`
      have hk2 : k + k = 2 * k := by omega
      rw [hk, hk2]
      have hq : stQ a (2 * k) = 2 * (k : ℝ) + (1 - a) / 2 := wg_stQ_even ha1 k
      have hq' : stQ a (2 * k + 1) = (2 * (k : ℝ) + (1 - a) / 2) + 1 + a := by
        rw [wg_stQ_odd ha0 k]; ring
      have hqpos : 0 < 2 * (k : ℝ) + (1 - a) / 2 := by
        have h0 : (0 : ℝ) ≤ 2 * (k : ℝ) := by positivity
        linarith
      have hqpos' : 0 < (2 * (k : ℝ) + (1 - a) / 2) + 1 + a := by linarith
      have hL : upW a (2 * k) * dnW a (2 * k + 1) =
          eqLam a ^ 2 * (1 + a / ((2 * (k : ℝ) + (1 - a) / 2) *
            ((2 * (k : ℝ) + (1 - a) / 2) + 1 + a))) := by
        simp only [upW, dnW, hq, hq']
        exact wg_up_dn_id_add (ne_of_gt hqpos) (ne_of_gt hqpos')
      have hR : upW a 0 * dnW a 1 =
          eqLam a ^ 2 * (1 + a / (((1 - a) / 2) * (((1 - a) / 2) + 1 + a))) := by
        simp only [upW, dnW, hq0, hq1']
        exact wg_up_dn_id_add (ne_of_gt (by linarith : (0 : ℝ) < (1 - a) / 2))
          (ne_of_gt (by linarith : (0 : ℝ) < (1 - a) / 2 + 1 + a))
      rw [hL, hR]
      have hle := wg_div_mul_le ha0 (by linarith : (0 : ℝ) < (1 - a) / 2)
        (by linarith : (0 : ℝ) < (1 - a) / 2 + 1 + a)
        (by linarith : (1 - a) / 2 ≤ 2 * (k : ℝ) + (1 - a) / 2)
        (by linarith : (1 - a) / 2 + 1 + a ≤ (2 * (k : ℝ) + (1 - a) / 2) + 1 + a)
      have h2 : (0 : ℝ) ≤ eqLam a ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_left (by linarith) h2
    · -- `n = 2k+1`: consecutive distances differ by `1 - a`
      rw [hk]
      have hq : stQ a (2 * k + 1) = 2 * (k : ℝ) + (3 + a) / 2 := wg_stQ_odd ha0 k
      have hq' : stQ a ((2 * k + 1) + 1) = (2 * (k : ℝ) + (3 + a) / 2) + 1 - a := by
        rw [show (2 * k + 1) + 1 = 2 * (k + 1) from by omega, wg_stQ_even ha1 (k + 1)]
        push_cast
        ring
      have hqpos : 0 < 2 * (k : ℝ) + (3 + a) / 2 := by
        have h0 : (0 : ℝ) ≤ 2 * (k : ℝ) := by positivity
        linarith
      have hqpos' : 0 < (2 * (k : ℝ) + (3 + a) / 2) + 1 - a := by linarith
      have hL : upW a (2 * k + 1) * dnW a ((2 * k + 1) + 1) =
          eqLam a ^ 2 * (1 - a / ((2 * (k : ℝ) + (3 + a) / 2) *
            ((2 * (k : ℝ) + (3 + a) / 2) + 1 - a))) := by
        simp only [upW, dnW, hq, hq']
        exact wg_up_dn_id_sub (ne_of_gt hqpos) (ne_of_gt hqpos')
      have hR : upW a 0 * dnW a 1 =
          eqLam a ^ 2 * (1 + a / (((1 - a) / 2) * (((1 - a) / 2) + 1 + a))) := by
        simp only [upW, dnW, hq0, hq1']
        exact wg_up_dn_id_add (ne_of_gt (by linarith : (0 : ℝ) < (1 - a) / 2))
          (ne_of_gt (by linarith : (0 : ℝ) < (1 - a) / 2 + 1 + a))
      rw [hL, hR]
      have hden : 0 < (2 * (k : ℝ) + (3 + a) / 2) * ((2 * (k : ℝ) + (3 + a) / 2) + 1 - a) :=
        mul_pos hqpos hqpos'
      have hden0 : 0 < ((1 - a) / 2) * (((1 - a) / 2) + 1 + a) :=
        mul_pos (by linarith) (by linarith)
      have hnn : 0 ≤ a / ((2 * (k : ℝ) + (3 + a) / 2) *
          ((2 * (k : ℝ) + (3 + a) / 2) + 1 - a)) :=
        div_nonneg (le_of_lt ha0) (le_of_lt hden)
      have hnn0 : 0 ≤ a / (((1 - a) / 2) * (((1 - a) / 2) + 1 + a)) :=
        div_nonneg (le_of_lt ha0) (le_of_lt hden0)
      have h2 : (0 : ℝ) ≤ eqLam a ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_left (by linarith) h2

end Work.EQ
