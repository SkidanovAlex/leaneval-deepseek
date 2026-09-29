/-
# Continued-fraction data: definitions

This file sets up the (regular) continued fraction of a real number `β` together with its
convergents' numerators and denominators, in the minimal form needed for the existential
package `exists_cf_data`.

* `cfX β n` is the `n`-th "tail" of the continued fraction of `β`, normalised so that
  `cfX β 0 = β` and `cfX β (n+1) = fract (1 / cfX β n) = 1/(cfX β n) - ⌊1/(cfX β n)⌋ ∈ [0,1)`
  (for irrational `β` this lies in `(0,1)`).
* `cfA β n = ⌊1/(cfX β n)⌋` is the `n`-th partial quotient (a positive integer for irrational
  `β`).
* `cfP β n / cfQ β n` is the `n`-th convergent, with `cfP β 0 = 0`, `cfQ β 0 = 1`,
  `cfP β 1 = 1`, `cfQ β 1 = cfA β 0` and the standard recurrences
  `cfP β (n+2) = cfA β (n+1) * cfP β (n+1) + cfP β n`, `cfQ β (n+2) = cfA β (n+1) * cfQ β (n+1) + cfQ β n`.

The main results about them live in `CFCore`.
-/
import Mathlib
import Submission.Work.TMC16Core.Defs

namespace Work.TMC16Core.Basic

/-- The `n`-th tail of the continued fraction of `β`: `cfX β 0 = β` and
`cfX β (n+1) = fract ((cfX β n)⁻¹)`. -/
noncomputable def cfX (β : ℝ) : ℕ → ℝ
  | 0 => β
  | n + 1 => Int.fract ((cfX β n)⁻¹)

/-- The `n`-th partial quotient `⌊1/(cfX β n)⌋`. -/
noncomputable def cfA (β : ℝ) (n : ℕ) : ℤ := ⌊((cfX β n))⁻¹⌋

/-- Numerators of the convergents of `β`. -/
noncomputable def cfP (β : ℝ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => cfA β (n + 1) * cfP β (n + 1) + cfP β n

/-- Denominators of the convergents of `β`. -/
noncomputable def cfQ (β : ℝ) : ℕ → ℤ
  | 0 => 1
  | 1 => cfA β 0
  | n + 2 => cfA β (n + 1) * cfQ β (n + 1) + cfQ β n

@[simp] theorem cfX_zero (β : ℝ) : cfX β 0 = β := rfl
@[simp] theorem cfX_succ (β : ℝ) (n : ℕ) : cfX β (n + 1) = Int.fract ((cfX β n)⁻¹) := rfl
@[simp] theorem cfA_apply (β : ℝ) (n : ℕ) : cfA β n = ⌊((cfX β n))⁻¹⌋ := rfl
@[simp] theorem cfP_zero (β : ℝ) : cfP β 0 = 0 := rfl
@[simp] theorem cfP_one (β : ℝ) : cfP β 1 = 1 := rfl
theorem cfP_add_two (β : ℝ) (n : ℕ) :
    cfP β (n + 2) = cfA β (n + 1) * cfP β (n + 1) + cfP β n := rfl
@[simp] theorem cfQ_zero (β : ℝ) : cfQ β 0 = 1 := rfl
@[simp] theorem cfQ_one (β : ℝ) : cfQ β 1 = cfA β 0 := rfl
theorem cfQ_add_two (β : ℝ) (n : ℕ) :
    cfQ β (n + 2) = cfA β (n + 1) * cfQ β (n + 1) + cfQ β n := rfl

end Work.TMC16Core.Basic
