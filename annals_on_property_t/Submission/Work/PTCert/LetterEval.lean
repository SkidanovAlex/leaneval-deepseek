import Mathlib
import Submission.Work.PTCert.WordModel
import Submission.Work.PTCert.LetterAPI

/-!
# `PTCert`: evaluation of the letters `b1 r k` on the free generators

`Checkers.lean` encodes the image of the generator `i` under the letter `b1 r k` as the word
`letterImg r k i`.  This file proves that the encoding is faithful:

* `evalW_two` and friends: evaluation of the two-letter words produced by `letterImg`;
* `letterImg_kind`, `letterImg_ne`, `letterImg_of_ge`: the case analysis of `letterImg`;
* `b1Img` (**the main result**): for `k < NB1 r` and `i : Fin r`,
  `(b1 r k) (FreeGroup.of i) = evalW (letterImg r k i.val)`.
-/

set_option autoImplicit false

namespace Submission.PTCert

open Submission.FreeGroupAut

/-- If `1 ≤ k` and `k < NB1 r` then `2 ≤ r`. -/
theorem two_le_of (r k : ℕ) (h1 : 1 ≤ k) (hk : k < NB1 r) : 2 ≤ r := by
  by_contra h
  have h2 : r ≤ 1 := by omega
  interval_cases r <;> simp [NB1] at hk <;> omega

/-- Evaluation of the one-letter word `[2 * i]`. -/
theorem evalW_single (r i : ℕ) (hi : i < r) :
    evalW (r := r) [2 * i] = FreeGroup.of (⟨i, hi⟩ : Fin r) := by
  rw [evalW_cons, evalW_nil, mul_one, wv_two_mul r i hi]

/-- Evaluation of `[2a, 2b]`. -/
theorem evalW_two (r a b : ℕ) (ha : a < r) (hb : b < r) :
    evalW (r := r) [2 * a, 2 * b]
      = FreeGroup.of (⟨a, ha⟩ : Fin r) * FreeGroup.of (⟨b, hb⟩ : Fin r) := by
  rw [evalW_cons, evalW_cons, evalW_nil, mul_one, wv_two_mul r a ha, wv_two_mul r b hb]

/-- Evaluation of `[2a, 2b+1]`. -/
theorem evalW_two_inv (r a b : ℕ) (ha : a < r) (hb : b < r) :
    evalW (r := r) [2 * a, 2 * b + 1]
      = FreeGroup.of (⟨a, ha⟩ : Fin r) * (FreeGroup.of (⟨b, hb⟩ : Fin r))⁻¹ := by
  rw [evalW_cons, evalW_cons, evalW_nil, mul_one, wv_two_mul r a ha, wv_two_mul_succ r b hb]

/-- Evaluation of `[2b, 2a]`. -/
theorem evalW_two_swap (r a b : ℕ) (ha : a < r) (hb : b < r) :
    evalW (r := r) [2 * b, 2 * a]
      = FreeGroup.of (⟨b, hb⟩ : Fin r) * FreeGroup.of (⟨a, ha⟩ : Fin r) := by
  rw [evalW_cons, evalW_cons, evalW_nil, mul_one, wv_two_mul r b hb, wv_two_mul r a ha]

/-- Evaluation of `[2b+1, 2a]`. -/
theorem evalW_two_inv_swap (r a b : ℕ) (ha : a < r) (hb : b < r) :
    evalW (r := r) [2 * b + 1, 2 * a]
      = (FreeGroup.of (⟨b, hb⟩ : Fin r))⁻¹ * FreeGroup.of (⟨a, ha⟩ : Fin r) := by
  rw [evalW_cons, evalW_cons, evalW_nil, mul_one, wv_two_mul_succ r b hb, wv_two_mul r a ha]

/-- `bif Nat.beq a b` in terms of the propositional equality. -/
theorem cond_natbeq {α : Type} (a b : ℕ) (x y : α) :
    (bif Nat.beq a b then x else y) = if a = b then x else y := by
  by_cases h : a = b
  · rw [if_pos h, show Nat.beq a b = true from by rw [Nat.beq_eq]; exact h, cond_true]
  · rw [if_neg h, show Nat.beq a b = false from by
        rw [Bool.eq_false_iff]; intro hh; exact h (by rwa [Nat.beq_eq] at hh), cond_false]

/-- `letterImg` in the generic "letter matches its first coordinate" case. -/
theorem letterImg_kind (r k i : ℕ) (hk0 : k ≠ 0) (hii : i = (pairOf r ((k - 1) / 4)).1) :
    letterImg r k i =
      (if (k - 1) % 4 = 0 then [2 * (pairOf r ((k - 1) / 4)).1, 2 * (pairOf r ((k - 1) / 4)).2]
       else if (k - 1) % 4 = 1 then [2 * (pairOf r ((k - 1) / 4)).1,
            2 * (pairOf r ((k - 1) / 4)).2 + 1]
       else if (k - 1) % 4 = 2 then [2 * (pairOf r ((k - 1) / 4)).2, 2 * (pairOf r ((k - 1) / 4)).1]
       else [2 * (pairOf r ((k - 1) / 4)).2 + 1, 2 * (pairOf r ((k - 1) / 4)).1]) := by
  dsimp only [letterImg]
  simp only [cond_natbeq]
  rw [if_neg hk0, if_pos hii]

/-- `letterImg` does not move a generator different from its first coordinate. -/
theorem letterImg_ne (r k i : ℕ) (hii : i ≠ (pairOf r ((k - 1) / 4)).1) :
    letterImg r k i = [2 * i] := by
  dsimp only [letterImg]
  by_cases hk0 : k = 0
  · subst hk0; simp only [cond_natbeq]; simp
  · rw [cond_natbeq, cond_natbeq, if_neg hk0, if_neg hii]

/-- `letterImg` of the trivial letter. -/
theorem letterImg_zero (r i : ℕ) : letterImg r 0 i = [2 * i] := by
  dsimp only [letterImg]; simp only [cond_natbeq]; simp

/-- `letterImg` never moves a generator beyond the range of the letter's first coordinate. -/
theorem letterImg_of_ge (r k i : ℕ) (hk : k < NB1 r) (hi : r ≤ i) : letterImg r k i = [2 * i] := by
  by_cases hk0 : k = 0
  · subst hk0; exact letterImg_zero r i
  · have h1 : 1 ≤ k := by omega
    have hPi := (Work.PTCert.pairOf_bounds (q_lt r k h1 hk)).1
    exact letterImg_ne r k i (by omega)

theorem letterImg_k0 (r k i : ℕ) (hk0 : k ≠ 0) (hii : i = (pairOf r ((k - 1) / 4)).1)
    (hk4 : (k - 1) % 4 = 0) :
    letterImg r k i = [2 * (pairOf r ((k - 1) / 4)).1, 2 * (pairOf r ((k - 1) / 4)).2] := by
  rw [letterImg_kind r k i hk0 hii, hk4]; simp

theorem letterImg_k1 (r k i : ℕ) (hk0 : k ≠ 0) (hii : i = (pairOf r ((k - 1) / 4)).1)
    (hk4 : (k - 1) % 4 = 1) :
    letterImg r k i = [2 * (pairOf r ((k - 1) / 4)).1, 2 * (pairOf r ((k - 1) / 4)).2 + 1] := by
  rw [letterImg_kind r k i hk0 hii, hk4]; simp

theorem letterImg_k2 (r k i : ℕ) (hk0 : k ≠ 0) (hii : i = (pairOf r ((k - 1) / 4)).1)
    (hk4 : (k - 1) % 4 = 2) :
    letterImg r k i = [2 * (pairOf r ((k - 1) / 4)).2, 2 * (pairOf r ((k - 1) / 4)).1] := by
  rw [letterImg_kind r k i hk0 hii, hk4]; simp

theorem letterImg_k3 (r k i : ℕ) (hk0 : k ≠ 0) (hii : i = (pairOf r ((k - 1) / 4)).1)
    (hk4 : (k - 1) % 4 = 3) :
    letterImg r k i = [2 * (pairOf r ((k - 1) / 4)).2 + 1, 2 * (pairOf r ((k - 1) / 4)).1] := by
  rw [letterImg_kind r k i hk0 hii, hk4]; simp

/-- **The letter `b1 r k` acts on the generators as `letterImg`.** -/
theorem b1Img (r k : ℕ) (hk : k < NB1 r) (i : Fin r) :
    (b1 r k) (FreeGroup.of i) = evalW (r := r) (letterImg r k i.val) := by
  by_cases hk0 : k = 0
  · subst hk0
    rw [show b1 r 0 = 1 from by simp [b1], letterImg_zero, evalW_single r i.val i.isLt]
    rfl
  · have h1 : 1 ≤ k := by omega
    have hr : 2 ≤ r := two_le_of r k h1 hk
    obtain ⟨hPi, hPj, hPij⟩ := Work.PTCert.pairOf_bounds (q_lt r k h1 hk)
    have hXtr : b1 r k = Xtr ⟨(pairOf r ((k - 1) / 4)).1, hPi⟩
        ⟨(pairOf r ((k - 1) / 4)).2, hPj⟩
        (fun e => hPij (congrArg Fin.val e)) ((k - 1) % 4) := by
      rw [b1_eq_ltr r k hr h1 hk,
          ltr_eq_Xtr r k ⟨hPi, hPj, hPij⟩
            ⟨(pairOf r ((k - 1) / 4)).1, hPi⟩
            ⟨(pairOf r ((k - 1) / 4)).2, hPj⟩
            (fun e => hPij (congrArg Fin.val e)) rfl]
    rw [hXtr]
    by_cases him : i.val = (pairOf r ((k - 1) / 4)).1
    · have hifin : i = (⟨(pairOf r ((k - 1) / 4)).1, hPi⟩ : Fin r) := Fin.ext him
      have hof : FreeGroup.of i
          = FreeGroup.of (⟨(pairOf r ((k - 1) / 4)).1, hPi⟩ : Fin r) := by
        rw [hifin]
      rw [hof]
      rcases (by omega : (k - 1) % 4 = 0 ∨ (k - 1) % 4 = 1 ∨ (k - 1) % 4 = 2
          ∨ (k - 1) % 4 = 3) with h4 | h4 | h4 | h4
      · rw [h4, letterImg_k0 r k i.val hk0 him h4, Xtr_zero, rho_apply_self,
            evalW_two r ((pairOf r ((k - 1) / 4)).1) ((pairOf r ((k - 1) / 4)).2) hPi hPj]
      · rw [h4, letterImg_k1 r k i.val hk0 him h4, Xtr_one, rhoNeg_apply_self,
            evalW_two_inv r ((pairOf r ((k - 1) / 4)).1) ((pairOf r ((k - 1) / 4)).2) hPi hPj]
      · rw [h4, letterImg_k2 r k i.val hk0 him h4, Xtr_two, lam_apply_self,
            evalW_two_swap r ((pairOf r ((k - 1) / 4)).1) ((pairOf r ((k - 1) / 4)).2) hPi hPj]
      · rw [h4, letterImg_k3 r k i.val hk0 him h4, Xtr_three, lamNeg_apply_self,
            evalW_two_inv_swap r ((pairOf r ((k - 1) / 4)).1) ((pairOf r ((k - 1) / 4)).2) hPi hPj]
    · have hne : i ≠ (⟨(pairOf r ((k - 1) / 4)).1, hPi⟩ : Fin r) :=
        fun e => him (congrArg Fin.val e)
      rw [letterImg_ne r k i.val him, evalW_single r i.val i.isLt]
      rcases (by omega : (k - 1) % 4 = 0 ∨ (k - 1) % 4 = 1 ∨ (k - 1) % 4 = 2
          ∨ (k - 1) % 4 = 3) with h4 | h4 | h4 | h4
      · rw [h4, Xtr_zero]; exact rho_apply_other _ hne
      · rw [h4, Xtr_one]; exact rhoNeg_apply_other _ hne
      · rw [h4, Xtr_two]; exact lam_apply_other _ hne
      · rw [h4, Xtr_three]; exact lamNeg_apply_other _ hne

end Submission.PTCert
