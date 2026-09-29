import Mathlib
import Submission.Work.CNum.LgInfra

/-!
# Normalisation of `lgNorm`

`Work.CNum.lgNorm n` counts how many times the mantissa `n` has to be halved (with `Int.ediv`)
until it lands below `2 * SC`; `lgUp`/`lgDn` then evaluate the artanh series on
`halveU (lgNorm n) n` resp. `halveD (lgNorm n) n`, which must therefore lie in `[SC, 2 * SC]`.

This module provides exactly that.  The two halving sequences are single divisions:

* `halveD k n = n / 2^k`            (`halveD_eq`),
* `halveU k n = -((-n) / 2^k)`      (`halveU_eq`),

and the recursion `lgNormAux` brackets `n` between `2^k * SC` and `2 * SC * 2^k`
(`lgNormAux_lower`, `lgNormAux_lt`).  The bound `n ≤ 2^60` guarantees that the 64 halvings
available in `lgNorm` are more than enough (`lgNormAux_self_ge`), so the recursion never runs
out of steps.
-/

namespace Work.CNum

open Work.ANum

/-! ## Elementary integer division facts -/

lemma two_mul_ediv_two_le (n : ℤ) : 2 * Int.ediv n 2 ≤ n := by
  have h : Int.ediv n 2 * 2 ≤ n := Int.ediv_mul_le n (show (2 : ℤ) ≠ 0 by norm_num)
  rw [mul_comm]
  exact h

lemma le_two_mul_ediv_two_add_one (n : ℤ) : n ≤ 2 * Int.ediv n 2 + 1 := by
  have hlt : Int.ediv n 2 < Int.ediv n 2 + 1 := by omega
  have h := (Int.ediv_lt_iff_lt_mul (show (0 : ℤ) < 2 by norm_num)
      (a := n) (b := Int.ediv n 2 + 1) (c := 2)).mp hlt
  have h2 : n + 1 ≤ (Int.ediv n 2 + 1) * 2 := Int.lt_iff_add_one_le.mp h
  linarith

lemma le_ediv_two_of_two_mul_le {a n : ℤ} (h : 2 * a ≤ n) : a ≤ Int.ediv n 2 :=
  (Int.le_ediv_iff_mul_le (show (0 : ℤ) < 2 by norm_num) (a := a) (b := n) (c := 2)).mpr (by linarith)

/-! ## The halving operators as one division -/

lemma halveD_eq (k : ℕ) (n : ℤ) : halveD k n = n / (2 : ℤ) ^ k := by
  induction k generalizing n with
  | zero => simp [halveD]
  | succ k ih =>
      have h1 : halveD (k + 1) n = halveD k (Int.ediv n 2) := rfl
      rw [h1, ih (Int.ediv n 2)]
      show Int.ediv (Int.ediv n 2) ((2 : ℤ) ^ k) = Int.ediv n ((2 : ℤ) ^ (k + 1))
      rw [show Int.ediv (Int.ediv n 2) ((2 : ℤ) ^ k) = Int.ediv n (2 * (2 : ℤ) ^ k) from
            Int.ediv_ediv_of_nonneg (x := n) (y := 2) (z := (2 : ℤ) ^ k) (by norm_num)]
      have h2 : (2 : ℤ) * 2 ^ k = 2 ^ (k + 1) := by rw [pow_succ]; ring
      rw [h2]

lemma halveU_eq (k : ℕ) (n : ℤ) : halveU k n = - ((-n) / (2 : ℤ) ^ k) := by
  induction k generalizing n with
  | zero => simp [halveU]
  | succ k ih =>
      have h1 : halveU (k + 1) n = halveU k (-(Int.ediv (-n) 2)) := rfl
      rw [h1, ih (-(Int.ediv (-n) 2))]
      simp only [neg_neg]
      show - Int.ediv (Int.ediv (-n) 2) ((2 : ℤ) ^ k) = - Int.ediv (-n) ((2 : ℤ) ^ (k + 1))
      rw [show Int.ediv (Int.ediv (-n) 2) ((2 : ℤ) ^ k) = Int.ediv (-n) (2 * (2 : ℤ) ^ k) from
            Int.ediv_ediv_of_nonneg (x := -n) (y := 2) (z := (2 : ℤ) ^ k) (by norm_num)]
      have h2 : (2 : ℤ) * 2 ^ k = 2 ^ (k + 1) := by rw [pow_succ]; ring
      rw [h2]

/-! ## Bracketing the recursion `lgNormAux` -/

lemma lgNormAux_le : ∀ (j : ℕ) (n : ℤ), lgNormAux j n ≤ j := by
  intro j
  induction j with
  | zero => intro n; simp [lgNormAux]
  | succ j ih =>
      intro n
      have heq : lgNormAux (j + 1) n
          = (if n < 2 * SC then 0 else 1 + lgNormAux j (Int.ediv n 2)) := rfl
      rw [heq]
      split_ifs with h
      · omega
      · have := ih (Int.ediv n 2); omega

/-- The halvings `lgNormAux j n` really are a lower bound for `n`: after `k` halvings the
result is still at least `SC`. -/
lemma lgNormAux_lower : ∀ (j : ℕ) (n : ℤ), SC ≤ n →
    (2 : ℤ) ^ (lgNormAux j n) * SC ≤ n := by
  intro j
  induction j with
  | zero =>
      intro n hn
      simp only [lgNormAux]
      simpa using hn
  | succ j ih =>
      intro n hn
      have heq : lgNormAux (j + 1) n
          = (if n < 2 * SC then 0 else 1 + lgNormAux j (Int.ediv n 2)) := rfl
      rw [heq]
      by_cases hlt : n < 2 * SC
      · rw [if_pos hlt]
        simpa using hn
      · rw [if_neg hlt]
        have h2 : SC ≤ Int.ediv n 2 := le_ediv_two_of_two_mul_le (by linarith)
        have h3 := ih (Int.ediv n 2) h2
        have h4 := two_mul_ediv_two_le n
        have h5 : 2 * ((2 : ℤ) ^ (lgNormAux j (Int.ediv n 2)) * SC) ≤ 2 * Int.ediv n 2 :=
          mul_le_mul_of_nonneg_left h3 (by norm_num)
        have hp : (2 : ℤ) ^ (1 + lgNormAux j (Int.ediv n 2))
            = 2 * ((2 : ℤ) ^ (lgNormAux j (Int.ediv n 2))) := by
          rw [pow_add, pow_one]
        rw [hp]
        linarith

/-- If the recursion has not run out of steps, the remaining value is below `2 * SC`, i.e.
`n < 2 * SC * 2 ^ (lgNormAux j n)`. -/
lemma lgNormAux_lt : ∀ (j : ℕ) (n : ℤ), SC ≤ n → lgNormAux j n < j →
    n < 2 * SC * (2 : ℤ) ^ (lgNormAux j n) := by
  intro j
  induction j with
  | zero =>
      intro n hn h
      simp only [lgNormAux] at h
      omega
  | succ j ih =>
      intro n hn h
      have heq : lgNormAux (j + 1) n
          = (if n < 2 * SC then 0 else 1 + lgNormAux j (Int.ediv n 2)) := rfl
      rw [heq] at h ⊢
      by_cases hlt : n < 2 * SC
      · rw [if_pos hlt] at h ⊢
        simpa using hlt
      · rw [if_neg hlt] at h ⊢
        have h2 : SC ≤ Int.ediv n 2 := le_ediv_two_of_two_mul_le (by linarith)
        have hk : lgNormAux j (Int.ediv n 2) < j := by omega
        have h3 := ih (Int.ediv n 2) h2 hk
        have h3' : Int.ediv n 2 + 1 ≤ 2 * SC * (2 : ℤ) ^ (lgNormAux j (Int.ediv n 2)) :=
          Int.lt_iff_add_one_le.mp h3
        have h4 := le_two_mul_ediv_two_add_one n
        have hp : (2 : ℤ) ^ (1 + lgNormAux j (Int.ediv n 2))
            = 2 * ((2 : ℤ) ^ (lgNormAux j (Int.ediv n 2))) := by
          rw [pow_add, pow_one]
        rw [hp]
        nlinarith [h3', h4]

/-- If the recursion has run out of steps then `n` was still at least `2 * SC` at every stage,
so `n ≥ 2 ^ j * SC`.  With `j = 64` and `n ≤ 2^60` this is impossible. -/
lemma lgNormAux_self_ge : ∀ (j : ℕ) (n : ℤ), SC ≤ n → lgNormAux j n = j →
    (2 : ℤ) ^ j * SC ≤ n := by
  intro j
  induction j with
  | zero =>
      intro n hn h
      simpa using hn
  | succ j ih =>
      intro n hn h
      have heq : lgNormAux (j + 1) n
          = (if n < 2 * SC then 0 else 1 + lgNormAux j (Int.ediv n 2)) := rfl
      rw [heq] at h
      by_cases hlt : n < 2 * SC
      · rw [if_pos hlt] at h
        omega
      · rw [if_neg hlt] at h
        have h2 : SC ≤ Int.ediv n 2 := le_ediv_two_of_two_mul_le (by linarith)
        have hk : lgNormAux j (Int.ediv n 2) = j := by omega
        have h3 := ih (Int.ediv n 2) h2 hk
        have h4 := two_mul_ediv_two_le n
        have hp : (2 : ℤ) ^ (j + 1) = 2 * (2 : ℤ) ^ j := by rw [pow_succ']
        rw [hp]
        linarith

/-- The normalisation fact: for `SC ≤ n ≤ 2^60` the `lgNorm n`-fold halvings of `n` (rounded
up resp. down) both land in `[SC, 2 * SC]`. -/
theorem LgNormSpec {n : ℤ} (h1 : Work.ANum.SC ≤ n) (h2 : n ≤ 2 ^ 60) :
    Work.ANum.SC ≤ Work.CNum.halveU (Work.CNum.lgNorm n) n ∧
    Work.CNum.halveU (Work.CNum.lgNorm n) n ≤ 2 * Work.ANum.SC ∧
    Work.ANum.SC ≤ Work.CNum.halveD (Work.CNum.lgNorm n) n ∧
    Work.CNum.halveD (Work.CNum.lgNorm n) n ≤ 2 * Work.ANum.SC := by
  have hkle : lgNorm n ≤ 64 := lgNormAux_le 64 n
  set p : ℤ := (2 : ℤ) ^ lgNorm n with hp
  have hp_pos : 0 < p := by rw [hp]; positivity
  have hL : p * SC ≤ n := by
    rw [hp]
    exact lgNormAux_lower 64 n h1
  have hk_lt : lgNorm n < 64 := by
    rcases lt_or_eq_of_le hkle with h | h
    · exact h
    · exfalso
      have hge : (2 : ℤ) ^ 64 * SC ≤ n := lgNormAux_self_ge 64 n h1 h
      have hc : (2 : ℤ) ^ 64 * SC ≤ (2 : ℤ) ^ 60 := le_trans hge h2
      exact absurd hc (by norm_num [SC])
  have hU : n < 2 * SC * p := by
    rw [hp]
    exact lgNormAux_lt 64 n h1 hk_lt
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [halveU_eq, ← hp]
    have h : (-n) / p ≤ -SC :=
      (Int.ediv_le_iff_le_mul hp_pos (k := p) (x := -n) (y := -SC)).mpr
        (by nlinarith [hL, hp_pos])
    linarith
  · rw [halveU_eq, ← hp]
    have h : (-2 * SC) ≤ (-n) / p :=
      (Int.le_ediv_iff_mul_le hp_pos (a := -2 * SC) (b := -n) (c := p)).mpr
        (by nlinarith [hU])
    linarith
  · rw [halveD_eq, ← hp]
    exact (Int.le_ediv_iff_mul_le hp_pos (a := SC) (b := n) (c := p)).mpr (by linarith)
  · rw [halveD_eq, ← hp]
    exact (Int.ediv_le_iff_le_mul hp_pos (k := p) (x := n) (y := 2 * SC)).mpr
      (by nlinarith [hU])

end Work.CNum
