import Mathlib
import Submission.Work.PTCert.GlueDefs
import Submission.Work.PTCert.letterAction

/-!
# `ActCSound` — soundness of the kernel action on codes

Proof of `Submission.PTCert.ActCSound` (`GL8` of `NOTES_LEAD_glue.md`).

* `invLk_eq_invL_actCSound`: the kernel form of the inverse letter is `invL`.
* `eltC_mul_add`: a normal code `128 * x + y` (`y < 128`) denotes `b1 5 x * b1 5 y`.
* `normC_unfold`: the three cases of `normC` as ordinary `if`s.
* `normC_eltC`, `normC_bounds`: the two halves of the first conjunct of `ActCSound`.
* the second conjunct follows from `TabOf` and the first part.
-/

namespace Work.PTCert

open Submission.PTCert

/-- The kernel form `invLk` of the inverse letter agrees with `invL`. -/
lemma invLk_eq_invL_actCSound (k : ℕ) : invLk k = invL k := by
  simp only [invLk, invL, cond_eq_ite, Nat.beq_eq]

/-- `eltC 0 = 1`. -/
lemma eltC_zero : eltC 0 = 1 := by
  simp [eltC, Submission.PTCert.b1]

/-- A normal code `128 * x + y` with `y < 128` denotes `b1 5 x * b1 5 y`. -/
lemma eltC_mul_add (x y : ℕ) (hy : y < 128) :
    eltC (128 * x + y) = b1 5 x * b1 5 y := by
  have h1 : (128 * x + y) / 128 = x := by omega
  have h2 : (128 * x + y) % 128 = y := by omega
  simp only [eltC, h1, h2]

/-- The three cases of `normC`, as ordinary `if`s. -/
lemma normC_unfold (cm : NT) (a b : ℕ) :
    normC cm a b = if a = invLk b then 0 else
      if commB cm a b = true then (if a ≤ b then 128 * a + b else 128 * b + a)
      else 128 * a + b := by
  simp only [normC, cond_eq_ite, Nat.beq_eq, Nat.ble_eq]

/-- **First half of the first conjunct**: `normC` computes the product of the two letters. -/
lemma normC_eltC (cm : NT) (hcm : CmSound cm) {a b : ℕ} (ha : a < 81) (hb : b < 81) :
    eltC (normC cm a b) = b1 5 a * b1 5 b := by
  rw [normC_unfold]
  by_cases h1 : a = invLk b
  · rw [if_pos h1, eltC_zero]
    have hb81 : b < NB1 5 := by simp only [NB1]; omega
    have hinv : (b1 5 b)⁻¹ = b1 5 (invL b) := Work.PTCert.b1_inv 5 b hb81
    have hthis : b1 5 a = (b1 5 b)⁻¹ := by rw [h1, invLk_eq_invL_actCSound, ← hinv]
    rw [hthis]
    exact (inv_mul_cancel (b1 5 b)).symm
  · rw [if_neg h1]
    by_cases h2 : commB cm a b = true
    · rw [if_pos h2]
      by_cases h3 : a ≤ b
      · rw [if_pos h3, eltC_mul_add a b (by omega)]
      · rw [if_neg h3, eltC_mul_add b a (by omega)]
        exact (hcm a ha b hb h2).symm
    · rw [if_neg h2, eltC_mul_add a b (by omega)]

/-- **Second half of the first conjunct**: the two components of a normal code stay in range. -/
lemma normC_bounds (cm : NT) {a b : ℕ} (ha : a < 81) (hb : b < 81) :
    normC cm a b / 128 < 81 ∧ normC cm a b % 128 < 81 := by
  rw [normC_unfold]
  by_cases h1 : a = invLk b
  · rw [if_pos h1]; norm_num
  · rw [if_neg h1]
    by_cases h2 : commB cm a b = true
    · rw [if_pos h2]
      by_cases h3 : a ≤ b
      · rw [if_pos h3]; omega
      · rw [if_neg h3]; omega
    · rw [if_neg h2]; omega

/-- The first conjunct of `ActCSound`. -/
lemma normC_spec (cm : NT) (hcm : CmSound cm) {a b : ℕ} (ha : a < 81) (hb : b < 81) :
    eltC (normC cm a b) = b1 5 a * b1 5 b ∧
      normC cm a b / 128 < 81 ∧ normC cm a b % 128 < 81 :=
  ⟨normC_eltC cm hcm ha hb, normC_bounds cm ha hb⟩

theorem actCSound : ActCSound := by
  intro cm hcm
  refine ⟨fun a ha b hb => normC_spec cm hcm ha hb, ?_⟩
  intro σ tab htab htablt c hc1 hc2
  have ha : lk tab (c / 128) < 81 := htablt (c / 128) hc1
  have hb : lk tab (c % 128) < 81 := htablt (c % 128) hc2
  have hspec := normC_spec cm hcm ha hb
  have hact : actC cm tab c = normC cm (lk tab (c / 128)) (lk tab (c % 128)) := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hact, hspec.1]
    have e1 : b1 5 (lk tab (c / 128)) = σ * b1 5 (c / 128) * σ⁻¹ := (htab (c / 128) hc1).symm
    have e2 : b1 5 (lk tab (c % 128)) = σ * b1 5 (c % 128) * σ⁻¹ := (htab (c % 128) hc2).symm
    rw [e1, e2]
    show (σ * b1 5 (c / 128) * σ⁻¹) * (σ * b1 5 (c % 128) * σ⁻¹)
        = σ * (b1 5 (c / 128) * b1 5 (c % 128)) * σ⁻¹
    group
  · rw [hact]; exact hspec.2.1
  · rw [hact]; exact hspec.2.2

end Work.PTCert
