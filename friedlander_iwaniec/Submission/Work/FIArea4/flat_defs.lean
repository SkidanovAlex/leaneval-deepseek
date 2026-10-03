import Mathlib
import Submission.Work.FIArea4.box_defs

/-!
# Vocabulary for the flat (`♭`) part of the dyadic dual variance

This module fixes the small vocabulary used by `Submission/Work/FIArea4/flat_part_le.lean` and by
the lemmas delegated for it.

* `suppBox S` is the finite box of natural numbers containing the support of the bump majorant `f`
  of `BumpData S f F C₀`: every `s` with `f s ≠ 0` lies in `suppBox S`.
* `suppCount S R d a` counts the pairs `(r,s)` with `r ∈ (R,2R]`, `s ∈ suppBox S` and
  `s ≡ r a (mod d)`.
* `flatPair d₁ d₂` is the flatness condition `d₁' d₂' = □` on the odd parts (`dᵢ' = oddPart dᵢ`).
-/

namespace Work.FIArea4

open Finset
open scoped BigOperators

noncomputable section

/-- The finite box of naturals containing the support of the bump.  It is an over-approximation of
the integers in `[S/2, 5S/2]`: `Soc (S/2 - 1) (5S/2) = {S/2, S/2+1, …, 5S/2}`. -/
def suppBox (S : ℕ) : Finset ℕ := Finset.Ioc (S / 2 - 1) (5 * S / 2)

/-- The number of pairs `(r,s)`, `r ∈ (R,2R]`, `s ∈ suppBox S`, with `s ≡ r a (mod d)`. -/
def suppCount (S R d a : ℕ) : ℕ :=
  (((Finset.Ioc R (2 * R)).product (suppBox S)).filter
    (fun p : ℕ × ℕ => p.2 % d = (p.1 * a) % d)).card

/-- The flatness condition: the product of the odd parts of `d₁` and `d₂` is a square. -/
def flatPair (d1 d2 : ℕ) : Prop :=
  ∃ m : ℕ, Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2 = m ^ 2

/-- The statement's filter condition is `flatPair`. -/
lemma flatPair_iff_sqrt (d1 d2 : ℕ) :
    flatPair d1 d2 ↔ Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
      = Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2 := by
  constructor
  · rintro ⟨m, hm⟩
    rw [hm]
    simpa using congrArg (fun t => t ^ 2) (Nat.sqrt_eq m)
  · intro h
    exact ⟨Nat.sqrt _, h.symm⟩

/-- Every natural number with `f s ≠ 0` lies in `suppBox S` (for `S ≥ 1`). -/
lemma mem_suppBox_of_support {S : ℕ} {f : ℝ → ℝ} {F : ℝ → ℂ} {C₀ : ℝ} (hS : 1 ≤ S)
    (hM : BumpData S f F C₀) (s : ℕ) (hs : f s ≠ 0) : s ∈ suppBox S := by
  obtain ⟨-, -, hsupp, -, -, -, -⟩ := hM
  obtain ⟨hlo, hhi⟩ := hsupp (s : ℝ) hs
  rw [suppBox, Finset.mem_Ioc]
  have hSR : ((S / 2 : ℕ) : ℝ) ≤ (S : ℝ) / 2 := Nat.cast_div_le (m := S) (n := 2)
  have hlo' : (S / 2 : ℕ) ≤ s := by
    rw [← Nat.cast_le (α := ℝ)]
    exact le_trans hSR hlo
  have hs1 : 1 ≤ s := by
    have hSRpos : (0 : ℝ) < (S : ℝ) / 2 := by
      have : (1 : ℝ) ≤ (S : ℝ) := by exact_mod_cast hS
      linarith
    have : (0 : ℝ) < (s : ℝ) := lt_of_lt_of_le hSRpos hlo
    exact_mod_cast this
  refine ⟨by omega, ?_⟩
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
  have h : (2 : ℝ) * (s : ℝ) ≤ 5 * (S : ℝ) := by linarith [hhi]
  have h2 : 2 * s ≤ 5 * S := by exact_mod_cast h
  calc s * 2 = 2 * s := by ring
    _ ≤ 5 * S := h2

end

end Work.FIArea4
