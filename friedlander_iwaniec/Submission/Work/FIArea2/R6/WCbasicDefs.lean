/-
# `FIArea2/R6/WCbasicDefs` — vocabulary for `WC_basic`

Shared definitions for the elementary per-modulus weighted primitive-pair count
`Work.FIArea2.R6.WC c r X Y` (`R6/WCDefs`):

* `wcSup w` — the sup-norm `max (|w₁|) (|w₂|)` of an integer vector;
* `wcInL c A B w` — the lattice condition `(c : ℤ) ∣ A w₁ - B w₂`;
* `wcDet v w = v₁ w₂ - v₂ w₁` — the determinant pairing;
* `wcG c A B = gcd (gcd c A) B`, `wcI c A B = c / wcG c A B` — the index of the
  lattice `{w : c ∣ A w₁ - B w₂}` of `ℤ²`;
* `wcBox t = [-t,t]²` — the sup-norm box, as a `Finset (ℤ × ℤ)`;
* `wcThStar c r h₁ h₂` — the per-pair weighted primitive count, i.e. the inner double
  sum of `WC`, so that `WC c r X Y = Σ_{h₁,h₂} wcThStar c r h₁ h₂` definitionally.
-/
import Mathlib
import Submission.Work.FIArea2.R6.BSBoxDefs
import Submission.Work.FIArea2.R6.WCDefs

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Sup-norm `max |w₁| |w₂|` of an integer vector. -/
abbrev wcSup (w : ℤ × ℤ) : ℕ := max w.1.natAbs w.2.natAbs

/-- The lattice condition `(c : ℤ) ∣ A w₁ - B w₂` (`A,B ≥ 1` will always be the squares of the
`h`-coordinates; `c` the modulus). -/
abbrev wcInL (c A B : ℕ) (w : ℤ × ℤ) : Prop := (c : ℤ) ∣ (A : ℤ) * w.1 - (B : ℤ) * w.2

/-- The determinant `v₁ w₂ - v₂ w₁` of two integer vectors. -/
abbrev wcDet (v w : ℤ × ℤ) : ℤ := v.1 * w.2 - v.2 * w.1

/-- `gcd(c, A, B)`. -/
abbrev wcG (c A B : ℕ) : ℕ := Nat.gcd (Nat.gcd c A) B

/-- `c / gcd(c,A,B)` — the index of the lattice `{w : c ∣ A w₁ - B w₂}` in `ℤ²`. -/
abbrev wcI (c A B : ℕ) : ℕ := c / wcG c A B

/-- The sup-norm box `[-t,t] × [-t,t]` as a `Finset (ℤ × ℤ)`. -/
abbrev wcBox (t : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(t : ℤ)) (t : ℤ)) ×ˢ (Finset.Icc (-(t : ℤ)) (t : ℤ))

/-- The per-`(h₁,h₂)` weighted primitive count: the inner double sum of `WC`. -/
abbrev wcThStar (c r : ℕ) (h1 h2 : ℤ) : ℝ :=
  ∑ w1 ∈ zPz r, ∑ w2 ∈ zPz r,
    (if Int.gcd w1 w2 = 1 ∧ w1 * h1 ^ 2 - w2 * h2 ^ 2 ≠ 0
        ∧ (c : ℤ) ∣ w1 * h1 ^ 2 - w2 * h2 ^ 2
      then (1 : ℝ) / ((max w1.natAbs w2.natAbs : ℕ) : ℝ) else 0)

/-- `WC` is the double `(h₁,h₂)`-sum of the per-pair counts `wcThStar`. -/
lemma WC_eq_sum_wcThStar (c r X Y : ℕ) :
    WC c r X Y = ∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y, wcThStar c r h1 h2 := rfl

/-- The square of an integer is the cast of the square of its absolute value. -/
lemma sq_eq_cast_natAbs_sq (h : ℤ) : h ^ 2 = (((h.natAbs) ^ 2 : ℕ) : ℤ) := by
  have h1 : ((h ^ 2).natAbs : ℤ) = h ^ 2 := Int.natAbs_of_nonneg (sq_nonneg h)
  rw [← h1, Int.natAbs_pow]

end

end Work.FIArea2.R6
