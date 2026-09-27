import Mathlib
import Submission.Work.EQ.germ_value_defs

/-!
# Invariance of `HasVal` under rescaling of the representing fraction

`HasVal A C w L` (see `germ_value_defs`) says that the rational function `A / C`
takes the value `L` at `w` in the strong "cancellation-free" sense that
`A - L * C` vanishes at `w` to order `ord_w C + 1`.

The point of this file is that the predicate only depends on the rational function
`A / C`, not on the particular choice of numerator and denominator: if
`A * C' = A' * C` (i.e. `A / C = A' / C'`) with `C ≠ 0`, `C' ≠ 0`, and
`HasVal A C w L` holds, then `HasVal A' C' w L` holds.

The proof is a valuation count.  Put `P = X - C w` and
`D = A - L * C`, `D' = A' - L * C'`.  Multiplying `A * C' = A' * C` by `L`
and subtracting gives the key identity

  `D * C' = D' * C`.

`HasVal A C w L` says `P ^ (ord_w C + 1) ∣ D`.  Taking `ord_w` in the identity
`D * C' = D' * C` (from additivity `rootMultiplicity_mul` of `P`-multiplicities)
yields `ord_w D' = ord_w D + ord_w C' - ord_w C ≥ ord_w C' + 1`, which is exactly
`HasVal A' C' w L`.  Everything is phrased with `Polynomial.rootMultiplicity`,
which is the `P`-adic order of a nonzero polynomial (`0` for the zero polynomial,
which is handled separately).
-/

namespace Work.EQ

open Polynomial

-- `hC'` is not needed for the argument (the case `C' = 0` is trivially fine),
-- but the statement is as requested; silence the unused-variable linter.
set_option linter.unusedVariables false

theorem hasVal_congr {A C A' C' : Polynomial ℂ} {w L : ℂ} (hC : C ≠ 0) (hC' : C' ≠ 0)
    (h : A * C' = A' * C) (h1 : Work.EQ.HasVal A C w L) : Work.EQ.HasVal A' C' w L := by
  -- the key algebraic identity `(A - L*C) * C' = (A' - L*C') * C`
  have hid : (A - Polynomial.C L * C) * C' = (A' - Polynomial.C L * C') * C := by
    have hstep : (A - Polynomial.C L * C) * C' - (A' - Polynomial.C L * C') * C
        = A * C' - A' * C := by ring
    rw [← sub_eq_zero, hstep, h, sub_self]
  -- unfold the hypothesis on `A / C`
  have h1' : (Polynomial.X - Polynomial.C w) ^ (C.rootMultiplicity w + 1)
      ∣ (A - Polynomial.C L * C) := h1
  rcases eq_or_ne (A' - Polynomial.C L * C') 0 with hD' | hD'
  · -- the zero polynomial is divisible by everything
    rw [HasVal, hD']
    exact dvd_zero _
  · -- `D' ≠ 0` forces `D ≠ 0`, and we may count `P`-adic orders
    have hne : (A - Polynomial.C L * C) * C' ≠ 0 := by
      rw [hid]
      exact mul_ne_zero hD' hC
    have hD : A - Polynomial.C L * C ≠ 0 := left_ne_zero_of_mul hne
    have hle : C.rootMultiplicity w + 1 ≤ (A - Polynomial.C L * C).rootMultiplicity w :=
      (Polynomial.le_rootMultiplicity_iff hD).mpr h1'
    have hmul : (A - Polynomial.C L * C).rootMultiplicity w + C'.rootMultiplicity w
        = (A' - Polynomial.C L * C').rootMultiplicity w + C.rootMultiplicity w := by
      rw [← Polynomial.rootMultiplicity_mul hne, hid,
        Polynomial.rootMultiplicity_mul (mul_ne_zero hD' hC)]
    have hkey : C'.rootMultiplicity w + 1 ≤ (A' - Polynomial.C L * C').rootMultiplicity w := by
      omega
    exact (Polynomial.le_rootMultiplicity_iff hD').mp hkey

end Work.EQ
