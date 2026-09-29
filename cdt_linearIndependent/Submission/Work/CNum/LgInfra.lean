import Mathlib
import Submission.Work.CNum.Fx

/-!
# Rounding lemmas for the `CNum` logarithm certificate

`Work.CNum.Fx` defines the integer-mantissa logarithm `lgUp`/`lgDn` (at scale `SC = 2^30`),
whose soundness is the content of `Work.CNum.LogUpMSpec`.  The raw ingredients it is built from
are the outward-rounded operations `mulU`/`mulD`, `divU`/`divD`, `divUz`/`divDz`, the integer power
`powM` and the artanh variable `lgvUp`/`lgvDn`.  This module collects the *soundness* statements of
those primitives, i.e. the elementary algebraic facts that
`x ∈ [lo, hi]  ⇒  f x ∈ [f lo - ε, f hi + ε]` in mantissa form:

* `le_mulU`, `mulD_le` (multiplication rounded up / down),
* `divU_ge`, `divD_le`, `divUz_ge`, `divDz_le` (division by a positive integer rounded up / down),
* `powM_true_ge`, `powM_false_le` (the rounded power bracketing the true power),
* `lgvUp_ge`, `lgvDn_le` (the artanh variable bracketing `(x-1)/(x+1)`).
-/

namespace Work.CNum

open Work.ANum

/-! ## Casts and basic sign lemmas -/

lemma m2r_two_mul (x : ℤ) : m2r (2 * x) = 2 * m2r x := by
  simp only [m2r]; push_cast; ring

lemma m2r_mul_int (x b : ℤ) : m2r (x * b) = m2r x * (b : ℝ) := by
  simp only [m2r]; push_cast; ring

lemma m2r_mul_SC' (a : ℤ) : m2r (a * SC) = (a : ℝ) := by
  rw [m2r_mul_int]
  simp only [m2r]
  rw [div_mul_cancel₀ _ (ne_of_gt SC_posR)]

lemma m2r_sub_SC (n : ℤ) : m2r ((n - SC) * SC) = (n : ℝ) - SC := by
  rw [m2r_mul_SC']; push_cast; ring

lemma m2r_nonneg_iff (a : ℤ) : 0 ≤ m2r a ↔ 0 ≤ a := by
  constructor
  · intro h
    by_contra hc
    rw [not_le] at hc
    have hlt := m2r_lt hc
    rw [m2r_zero] at hlt
    linarith
  · intro h
    have hle := m2r_le h
    rwa [m2r_zero] at hle

lemma m2r_pos_iff (a : ℤ) : 0 < m2r a ↔ 0 < a := by
  constructor
  · intro h
    by_contra hc
    rw [not_lt] at hc
    have hle := m2r_le hc
    rw [m2r_zero] at hle
    linarith
  · intro h
    have hle := m2r_lt h
    rwa [m2r_zero] at hle

/-! ## Rounded multiplication -/

lemma le_mulU (a b : ℤ) : m2r a * m2r b ≤ m2r (mulU a b) := Iv.le_mulHi a b

lemma mulD_le (a b : ℤ) : m2r (mulD a b) ≤ m2r a * m2r b := Iv.mulLo_le a b

/-! ## Rounded division -/

lemma divU_ge {k : ℕ} (hk : 0 < k) (a : ℤ) : m2r a / (k : ℝ) ≤ m2r (divU a k) := by
  have hkZ : (k : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
  have h : a ≤ divU a k * (k : ℤ) := by
    have h0 : Int.ediv (-a) (k : ℤ) * (k : ℤ) ≤ -a := Int.ediv_mul_le (-a) hkZ
    simp only [divU]
    linarith
  have h2 : m2r a ≤ m2r (divU a k) * (k : ℝ) := by
    have h3 := m2r_le h
    rwa [m2r_mul_int] at h3
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  rw [div_le_iff₀ hkR]
  linarith

lemma divD_le {k : ℕ} (hk : 0 < k) (a : ℤ) : m2r (divD a k) ≤ m2r a / (k : ℝ) := by
  have hkZ : (k : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
  have h : divD a k * (k : ℤ) ≤ a := by
    have h0 : Int.ediv a (k : ℤ) * (k : ℤ) ≤ a := Int.ediv_mul_le a hkZ
    simpa [divD] using h0
  have h2 : m2r (divD a k) * (k : ℝ) ≤ m2r a := by
    have h3 := m2r_le h
    rwa [m2r_mul_int] at h3
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  rw [le_div_iff₀ hkR]
  linarith

lemma divUz_ge {b : ℤ} (hb : 0 < b) (a : ℤ) : m2r a / (b : ℝ) ≤ m2r (divUz a b) := by
  have h : a ≤ divUz a b * b := by
    have h0 : Int.ediv (-a) b * b ≤ -a := Int.ediv_mul_le (-a) (ne_of_gt hb)
    simp only [divUz]
    linarith
  have h2 : m2r a ≤ m2r (divUz a b) * (b : ℝ) := by
    have h3 := m2r_le h
    rwa [m2r_mul_int] at h3
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  rw [div_le_iff₀ hbR]
  linarith

lemma divDz_le {b : ℤ} (hb : 0 < b) (a : ℤ) : m2r (divDz a b) ≤ m2r a / (b : ℝ) := by
  have h : divDz a b * b ≤ a := by
    have h0 : Int.ediv a b * b ≤ a := Int.ediv_mul_le a (ne_of_gt hb)
    simpa [divDz] using h0
  have h2 : m2r (divDz a b) * (b : ℝ) ≤ m2r a := by
    have h3 := m2r_le h
    rwa [m2r_mul_int] at h3
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  rw [le_div_iff₀ hbR]
  linarith

/-! ## The rounded power `powM` -/

lemma powM_true_ge {q : ℤ} (hq : 0 ≤ m2r q) (m : ℕ) :
    (m2r q) ^ m ≤ m2r (powM true q m) := by
  induction m with
  | zero => simp [powM, m2r_SC]
  | succ m ih =>
      have h1 : powM true q (m + 1) = mulU (powM true q m) q := rfl
      rw [h1, pow_succ]
      calc (m2r q) ^ m * m2r q ≤ m2r (powM true q m) * m2r q :=
            mul_le_mul_of_nonneg_right ih hq
        _ ≤ m2r (mulU (powM true q m) q) := le_mulU _ _

lemma powM_false_nonneg {q : ℤ} (hq : 0 ≤ q) (m : ℕ) : 0 ≤ powM false q m := by
  induction m with
  | zero => exact SC_pos.le
  | succ m ih =>
      have h1 : powM false q (m + 1) = mulD (powM false q m) q := rfl
      rw [h1]
      exact Int.ediv_nonneg (mul_nonneg ih hq) (le_of_lt SC_pos)

lemma powM_false_le {q : ℤ} (hq : 0 ≤ m2r q) (m : ℕ) :
    m2r (powM false q m) ≤ (m2r q) ^ m := by
  have hqZ : 0 ≤ q := (m2r_nonneg_iff q).mp hq
  induction m with
  | zero => simp [powM, m2r_SC]
  | succ m ih =>
      have h1 : powM false q (m + 1) = mulD (powM false q m) q := rfl
      rw [h1, pow_succ]
      calc m2r (mulD (powM false q m) q) ≤ m2r (powM false q m) * m2r q := mulD_le _ _
        _ ≤ (m2r q) ^ m * m2r q := mul_le_mul_of_nonneg_right ih hq

/-! ## The artanh variable -/

lemma lgvUp_ge {n : ℤ} (hn : 0 < n + SC) :
    ((n : ℝ) - SC) / ((n : ℝ) + SC) ≤ m2r (lgvUp n) := by
  have h := divUz_ge (b := n + SC) hn ((n - SC) * SC)
  have he : m2r ((n - SC) * SC) / (((n + SC : ℤ)) : ℝ) = ((n : ℝ) - SC) / ((n : ℝ) + SC) := by
    rw [m2r_sub_SC]; push_cast; ring
  rw [he] at h
  exact h

lemma lgvDn_le {n : ℤ} (hn : 0 < n + SC) :
    m2r (lgvDn n) ≤ ((n : ℝ) - SC) / ((n : ℝ) + SC) := by
  have h := divDz_le (b := n + SC) hn ((n - SC) * SC)
  have he : m2r ((n - SC) * SC) / (((n + SC : ℤ)) : ℝ) = ((n : ℝ) - SC) / ((n : ℝ) + SC) := by
    rw [m2r_sub_SC]; push_cast; ring
  rw [he] at h
  exact h


/-! ## The repeated halving of `lgNorm` -/

lemma m2r_mul_int' (c b : ℤ) : m2r (c * b) = (c : ℝ) * m2r b := by
  rw [m2r_mul_int]; simp only [m2r]; ring

lemma halveU_ge : ∀ (k : ℕ) (n : ℤ), 0 ≤ n → m2r n / 2 ^ k ≤ m2r (halveU k n) := by
  intro k
  induction k with
  | zero =>
      intro n hn
      show m2r n / 2 ^ 0 ≤ m2r n
      simp
  | succ k ih =>
      intro n hn
      show m2r n / 2 ^ (k + 1) ≤ m2r (halveU k (divU n 2))
      have hdiv : m2r n / 2 ≤ m2r (divU n 2) := divU_ge (k := 2) (by norm_num) n
      have hnn : 0 ≤ divU n 2 := (m2r_nonneg_iff _).mp (le_trans (div_nonneg ((m2r_nonneg_iff n).mpr hn) (by norm_num)) hdiv)
      have hih := ih (divU n 2) hnn
      have hp : m2r n / 2 ^ (k + 1) = m2r n / 2 / 2 ^ k := by rw [pow_succ]; ring
      rw [hp]
      calc m2r n / 2 / 2 ^ k ≤ m2r (divU n 2) / 2 ^ k :=
            div_le_div_of_nonneg_right hdiv (by positivity : (0:ℝ) ≤ 2 ^ k)
        _ ≤ m2r (halveU k (divU n 2)) := hih

lemma halveD_le : ∀ (k : ℕ) (n : ℤ), 0 ≤ n → m2r (halveD k n) ≤ m2r n / 2 ^ k := by
  intro k
  induction k with
  | zero =>
      intro n hn
      show m2r n ≤ m2r n / 2 ^ 0
      simp
  | succ k ih =>
      intro n hn
      show m2r (halveD k (Int.ediv n 2)) ≤ m2r n / 2 ^ (k + 1)
      have hdiv : m2r (Int.ediv n 2) ≤ m2r n / 2 := divD_le (k := 2) (by norm_num) n
      have hnn : 0 ≤ Int.ediv n 2 := Int.ediv_nonneg hn (by norm_num)
      have hih := ih (Int.ediv n 2) hnn
      have hp : m2r n / 2 ^ (k + 1) = m2r n / 2 / 2 ^ k := by rw [pow_succ]; ring
      rw [hp]
      calc m2r (halveD k (Int.ediv n 2)) ≤ m2r (Int.ediv n 2) / 2 ^ k := hih
        _ ≤ m2r n / 2 / 2 ^ k := div_le_div_of_nonneg_right hdiv (by positivity : (0:ℝ) ≤ 2 ^ k)

/-! ## The constants `LOG2UP`, `LOG2DN` -/

lemma log_two_le_LOG2UP : Real.log 2 ≤ m2r LOG2UP := by
  have h := Real.log_two_lt_d9
  have h2 : (0.6931471808 : ℝ) ≤ m2r LOG2UP := by
    simp only [m2r, LOG2UP, SC]
    norm_num
  linarith

lemma LOG2DN_le_log_two : m2r LOG2DN ≤ Real.log 2 := by
  have h := Real.log_two_gt_d9
  have h2 : m2r LOG2DN ≤ (0.6931471803 : ℝ) := by
    simp only [m2r, LOG2DN, SC]
    norm_num
  linarith

end Work.CNum
