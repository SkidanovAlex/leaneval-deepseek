/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Basic algebraic properties of the Hilbert symbol over `ℚ`

Symmetry, multiplicativity in each variable, and the triviality on squares, for the archimedean
place, for the finite places, and assembled at the level of places.
-/
import Submission.Work.HilbertSymbol.Basic
import Submission.Work.HilbertSymbol.hilbertSymbolReal_mul_left
import Submission.Work.HilbertSymbol.hilbertSymbolReal_sq_left
import Submission.Work.HilbertSymbol.hilbertSymbolOdd_mul_left
import Submission.Work.HilbertSymbol.hilbertSymbolOdd_mul_right
import Submission.Work.HilbertSymbol.hilbertSymbolOdd_sq_left
import Submission.Work.HilbertSymbol.hilbertSymbolOdd_sq_right
import Submission.Work.HilbertSymbol.hilbertSymbolTwo_mul_left
import Submission.Work.HilbertSymbol.hilbertSymbolTwo_mul_right
import Submission.Work.HilbertSymbol.hilbertSymbolTwo_sq_left
import Submission.Work.HilbertSymbol.hilbertSymbolTwo_sq_right
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped Classical

namespace Work.HilbertSymbol

/-! ## The archimedean place -/

theorem hilbertSymbolReal_comm (a b : ℚˣ) : hilbertSymbolReal a b = hilbertSymbolReal b a := by
  rw [hilbertSymbolReal, hilbertSymbolReal]
  by_cases h : (a : ℚ) < 0 ∧ (b : ℚ) < 0
  · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
  · rw [if_neg h, if_neg fun h' => h ⟨h'.2, h'.1⟩]

theorem hilbertSymbolReal_mul_right (a b₁ b₂ : ℚˣ) :
    hilbertSymbolReal a (b₁ * b₂) = hilbertSymbolReal a b₁ * hilbertSymbolReal a b₂ := by
  rw [hilbertSymbolReal_comm a (b₁ * b₂), hilbertSymbolReal_mul_left,
    hilbertSymbolReal_comm b₁ a, hilbertSymbolReal_comm b₂ a]

theorem hilbertSymbolReal_sq_right (a b : ℚˣ) : hilbertSymbolReal a (b ^ 2) = 1 := by
  rw [hilbertSymbolReal_eq_one_iff]
  rintro ⟨-, h⟩
  have h2 : ((b ^ 2 : ℚˣ) : ℚ) = (b : ℚ) ^ 2 := by simp
  rw [h2] at h
  nlinarith [sq_nonneg (b : ℚ)]

@[simp] theorem hilbertSymbolReal_one_left (b : ℚˣ) : hilbertSymbolReal 1 b = 1 := by
  simpa using hilbertSymbolReal_sq_left (1 : ℚˣ) b

@[simp] theorem hilbertSymbolReal_one_right (a : ℚˣ) : hilbertSymbolReal a 1 = 1 := by
  simpa using hilbertSymbolReal_sq_right a (1 : ℚˣ)

/-! ## The odd finite places -/

theorem hilbertSymbolOdd_comm (p : ℕ) [Fact p.Prime] (a b : ℚˣ) :
    hilbertSymbolOdd p a b = hilbertSymbolOdd p b a := by
  simp only [hilbertSymbolOdd, mul_comm, mul_assoc]

@[simp] theorem hilbertSymbolOdd_one_left (p : ℕ) [Fact p.Prime] (b : ℚˣ) :
    hilbertSymbolOdd p 1 b = 1 := by
  simpa using hilbertSymbolOdd_sq_left p (1 : ℚˣ) b

@[simp] theorem hilbertSymbolOdd_one_right (p : ℕ) [Fact p.Prime] (a : ℚˣ) :
    hilbertSymbolOdd p a 1 = 1 := by
  simpa using hilbertSymbolOdd_sq_right p a (1 : ℚˣ)

/-! ## The place `2` -/

theorem hilbertSymbolTwo_comm (a b : ℚˣ) :
    hilbertSymbolTwo a b = hilbertSymbolTwo b a := by
  unfold hilbertSymbolTwo
  congr 1
  ring

@[simp] theorem hilbertSymbolTwo_one_left (b : ℚˣ) : hilbertSymbolTwo 1 b = 1 := by
  simpa using hilbertSymbolTwo_sq_left (1 : ℚˣ) b

@[simp] theorem hilbertSymbolTwo_one_right (a : ℚˣ) : hilbertSymbolTwo a 1 = 1 := by
  simpa using hilbertSymbolTwo_sq_right a (1 : ℚˣ)

/-! ## Assembling: finite places and places -/

theorem hilbertSymbolAtPrime_mul_left {p : ℕ} [Fact p.Prime] (a₁ a₂ b : ℚˣ) :
    hilbertSymbolAtPrime p (a₁ * a₂) b
      = hilbertSymbolAtPrime p a₁ b * hilbertSymbolAtPrime p a₂ b := by
  by_cases hp : p = 2
  · subst hp
    simp only [hilbertSymbolAtPrime_two, hilbertSymbolTwo_mul_left]
  · rw [hilbertSymbolAtPrime_eq_odd hp, hilbertSymbolAtPrime_eq_odd hp,
      hilbertSymbolAtPrime_eq_odd hp, hilbertSymbolOdd_mul_left]

theorem hilbertSymbolAtPrime_mul_right {p : ℕ} [Fact p.Prime] (a b₁ b₂ : ℚˣ) :
    hilbertSymbolAtPrime p a (b₁ * b₂)
      = hilbertSymbolAtPrime p a b₁ * hilbertSymbolAtPrime p a b₂ := by
  by_cases hp : p = 2
  · subst hp
    simp only [hilbertSymbolAtPrime_two, hilbertSymbolTwo_mul_right]
  · rw [hilbertSymbolAtPrime_eq_odd hp, hilbertSymbolAtPrime_eq_odd hp,
      hilbertSymbolAtPrime_eq_odd hp, hilbertSymbolOdd_mul_right]

theorem hilbertSymbolAtPrime_comm {p : ℕ} [Fact p.Prime] (a b : ℚˣ) :
    hilbertSymbolAtPrime p a b = hilbertSymbolAtPrime p b a := by
  by_cases hp : p = 2
  · subst hp
    simp only [hilbertSymbolAtPrime_two, hilbertSymbolTwo_comm]
  · rw [hilbertSymbolAtPrime_eq_odd hp, hilbertSymbolAtPrime_eq_odd hp, hilbertSymbolOdd_comm]

@[simp] theorem hilbertSymbolAtPrime_one_left {p : ℕ} [Fact p.Prime] (b : ℚˣ) :
    hilbertSymbolAtPrime p 1 b = 1 := by
  by_cases hp : p = 2
  · subst hp
    simp only [hilbertSymbolAtPrime_two, hilbertSymbolTwo_one_left]
  · rw [hilbertSymbolAtPrime_eq_odd hp, hilbertSymbolOdd_one_left]

@[simp] theorem hilbertSymbolAtPrime_one_right {p : ℕ} [Fact p.Prime] (a : ℚˣ) :
    hilbertSymbolAtPrime p a 1 = 1 := by
  by_cases hp : p = 2
  · subst hp
    simp only [hilbertSymbolAtPrime_two, hilbertSymbolTwo_one_right]
  · rw [hilbertSymbolAtPrime_eq_odd hp, hilbertSymbolOdd_one_right]

theorem hilbertSymbolAtPrime_sq_left {p : ℕ} [Fact p.Prime] (a b : ℚˣ) :
    hilbertSymbolAtPrime p (a ^ 2) b = 1 := by
  by_cases hp : p = 2
  · subst hp
    simp only [hilbertSymbolAtPrime_two, hilbertSymbolTwo_sq_left]
  · rw [hilbertSymbolAtPrime_eq_odd hp, hilbertSymbolOdd_sq_left]

theorem hilbertSymbolAtPrime_sq_right {p : ℕ} [Fact p.Prime] (a b : ℚˣ) :
    hilbertSymbolAtPrime p a (b ^ 2) = 1 := by
  by_cases hp : p = 2
  · subst hp
    simp only [hilbertSymbolAtPrime_two, hilbertSymbolTwo_sq_right]
  · rw [hilbertSymbolAtPrime_eq_odd hp, hilbertSymbolOdd_sq_right]

theorem hilbertSymbol_mul_left (v : Place) (a₁ a₂ b : ℚˣ) :
    hilbertSymbol v (a₁ * a₂) b = hilbertSymbol v a₁ b * hilbertSymbol v a₂ b := by
  match v with
  | none => exact hilbertSymbolReal_mul_left a₁ a₂ b
  | some p =>
    by_cases hp : p.Prime
    · letI : Fact p.Prime := ⟨hp⟩
      rw [hilbertSymbol_some, hilbertSymbol_some, hilbertSymbol_some,
        hilbertSymbolAtPrime_mul_left]
    · simp only [hilbertSymbol, dif_neg hp, mul_one]

theorem hilbertSymbol_mul_right (v : Place) (a b₁ b₂ : ℚˣ) :
    hilbertSymbol v a (b₁ * b₂) = hilbertSymbol v a b₁ * hilbertSymbol v a b₂ := by
  match v with
  | none => exact hilbertSymbolReal_mul_right a b₁ b₂
  | some p =>
    by_cases hp : p.Prime
    · letI : Fact p.Prime := ⟨hp⟩
      rw [hilbertSymbol_some, hilbertSymbol_some, hilbertSymbol_some,
        hilbertSymbolAtPrime_mul_right]
    · simp only [hilbertSymbol, dif_neg hp, mul_one]

theorem hilbertSymbol_comm (v : Place) (a b : ℚˣ) :
    hilbertSymbol v a b = hilbertSymbol v b a := by
  match v with
  | none => exact hilbertSymbolReal_comm a b
  | some p =>
    by_cases hp : p.Prime
    · letI : Fact p.Prime := ⟨hp⟩
      rw [hilbertSymbol_some, hilbertSymbol_some, hilbertSymbolAtPrime_comm]
    · simp only [hilbertSymbol, dif_neg hp]

@[simp] theorem hilbertSymbol_one_left (v : Place) (b : ℚˣ) : hilbertSymbol v 1 b = 1 := by
  match v with
  | none => exact hilbertSymbolReal_one_left b
  | some p =>
    by_cases hp : p.Prime
    · letI : Fact p.Prime := ⟨hp⟩
      rw [hilbertSymbol_some, hilbertSymbolAtPrime_one_left]
    · simp only [hilbertSymbol, dif_neg hp]

@[simp] theorem hilbertSymbol_one_right (v : Place) (a : ℚˣ) : hilbertSymbol v a 1 = 1 := by
  match v with
  | none => exact hilbertSymbolReal_one_right a
  | some p =>
    by_cases hp : p.Prime
    · letI : Fact p.Prime := ⟨hp⟩
      rw [hilbertSymbol_some, hilbertSymbolAtPrime_one_right]
    · simp only [hilbertSymbol, dif_neg hp]

theorem hilbertSymbol_sq_left (v : Place) (a b : ℚˣ) : hilbertSymbol v (a ^ 2) b = 1 := by
  match v with
  | none => exact hilbertSymbolReal_sq_left a b
  | some p =>
    by_cases hp : p.Prime
    · letI : Fact p.Prime := ⟨hp⟩
      rw [hilbertSymbol_some, hilbertSymbolAtPrime_sq_left]
    · simp only [hilbertSymbol, dif_neg hp]

theorem hilbertSymbol_sq_right (v : Place) (a b : ℚˣ) : hilbertSymbol v a (b ^ 2) = 1 := by
  match v with
  | none => exact hilbertSymbolReal_sq_right a b
  | some p =>
    by_cases hp : p.Prime
    · letI : Fact p.Prime := ⟨hp⟩
      rw [hilbertSymbol_some, hilbertSymbolAtPrime_sq_right]
    · simp only [hilbertSymbol, dif_neg hp]

end Work.HilbertSymbol
