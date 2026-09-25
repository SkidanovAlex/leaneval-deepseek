import Mathlib
import Submission.Work.TameArithmetic.Defs

/-!
# `Work.TameArithmetic.VSDefs` -- Koch's group `V_S` over `ℚ`

For a finite set `S` of primes, Shafarevich--Koch's group is

  `V_S = {x ∈ ℚˣ : (x) = I² is a square fractional ideal, and x ∈ ℚ_q^{×2} for all q ∈ S}`.

The `2`-rank of `V_S/ℚ^{×2}` is the number of "extra" relators in the Shafarevich--Koch
presentation of the maximal pro-`2` extension of `ℚ` unramified outside `S`; for our `S` (five
primes `≡ 1 (mod 4)`) it is `1`, so that `r - d ≤ 1` and hence `r ≤ 6` for `d = 5`.

## The elementary content (proved in `VS.lean`)

* over `ℚ` the fractional ideals are principal with unit group `{±1}`, so `(x) = I²` forces
  `x = ±y²` -- this is what makes the whole computation cheap (no genus theory, no Hasse, no
  Kummer two-descent);
* `-1 ∈ ℚ_q^{×2}` for `q ≡ 1 (mod 4)` (Euler's criterion plus Hensel), so the local conditions at
  the primes of `S` are satisfied by both `y²` and `-y²`;
* hence `V_S = {±1}·(ℚˣ)²` and `V_S/ℚ^{×2} ≅ ℤ/2` (as `-1` is not a square in `ℚ`).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open scoped Classical
open scoped NumberField

namespace Work.TameArithmetic

/-- `(x)` is a square fractional ideal of `ℤ` in `ℚ` (the first condition in `V_S`). -/
def IsIdealSquare (x : ℚˣ) : Prop :=
  ∃ I : (FractionalIdeal (nonZeroDivisors ℤ) ℚ)ˣ, I * I = toPrincipalIdeal ℤ ℚ x

/-- `x` is a square in the `q`-adic field `ℚ_q`. -/
def IsLocalSquare (q : ℕ) [Fact q.Prime] (x : ℚˣ) : Prop :=
  ∃ y : ℚ_[q], y * y = ((x : ℚ) : ℚ_[q])

/-- The local conditions of `V_S`: `x ∈ ℚ_q^{×2}` for every `q ∈ S`. -/
def IsLocalSquareAtS (x : ℚˣ) : Prop :=
  ∀ q ∈ primesS, ∃ h : Fact (Nat.Prime q), @IsLocalSquare q h x

/-- **Koch's group `V_S`** for `S = primesS` over `ℚ`. -/
def VS : Subgroup ℚˣ where
  carrier := {x | IsIdealSquare x ∧ IsLocalSquareAtS x}
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨I, hI⟩ := hx1
      obtain ⟨J, hJ⟩ := hy1
      exact ⟨I * J, by rw [mul_mul_mul_comm, hI, hJ, map_mul]⟩
    · intro q hq
      obtain ⟨h, y1, hy⟩ := hx2 q hq
      obtain ⟨h', y2, hy2'⟩ := hy2 q hq
      have hh : h' = h := Subsingleton.elim _ _
      rw [hh] at hy2'
      refine ⟨h, y1 * y2, ?_⟩
      have hcoe : ((((x * y : ℚˣ) : ℚ)) : ℚ_[q])
          = (((x : ℚ)) : ℚ_[q]) * (((y : ℚ)) : ℚ_[q]) := by
        push_cast
        rfl
      rw [hcoe, ← hy, ← hy2']
      ring
  one_mem' := by
    refine ⟨⟨1, by rw [one_mul, map_one]⟩, ?_⟩
    intro q hq
    refine ⟨⟨primesS_prime q hq⟩, 1, ?_⟩
    push_cast
    ring
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨I, hI⟩ := hx1
      exact ⟨I⁻¹, by
        have h := congrArg Inv.inv hI
        simpa [mul_inv] using h⟩
    · intro q hq
      obtain ⟨h, y, hy⟩ := hx2 q hq
      have hy0 : y ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hy
        have hxne : (((x : ℚ)) : ℚ_[q]) ≠ 0 := by
          simp [Rat.cast_eq_zero, Units.ne_zero x]
        exact hxne hy.symm
      refine ⟨h, y⁻¹, ?_⟩
      have hcoe : ((((x⁻¹ : ℚˣ) : ℚ)) : ℚ_[q]) = ((((x : ℚ)) : ℚ_[q]))⁻¹ := by
        push_cast
        rfl
      rw [hcoe, ← hy, mul_inv]

end Work.TameArithmetic
