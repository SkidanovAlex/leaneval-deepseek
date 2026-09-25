import Mathlib
import Submission.Work.TameArithmetic.VSDefs
import Submission.Work.TameArithmetic.exists_pm_square_of_isIdealSquare
import Submission.Work.TameArithmetic.isSquare_neg_one_padic

/-!
# `Work.TameArithmetic.VS_eq_pm_squares`

**The computation of Koch's group `V_S` over `ℚ`:**

  `x ∈ V_S ↔ ∃ y : ℚˣ, x = y * y ∨ x = - (y * y)`,

i.e. `V_S = {±1} · (ℚˣ)²`.

Recall (`Submission/Work/TameArithmetic/VSDefs.lean`)

```
VS          = {x : ℚˣ | IsIdealSquare x ∧ IsLocalSquareAtS x}
IsIdealSquare x   -- ∃ I : (FractionalIdeal ℤ⁰ ℚ)ˣ, I * I = toPrincipalIdeal ℤ ℚ x
IsLocalSquare q x -- x is a square in ℚ_[q];  IsLocalSquareAtS x : ∀ q ∈ primesS, ...
```

The two directions:

* `→`.  Over `ℚ` the fractional ideals are principal and `ℤˣ = {±1}`, so the ideal-square
  condition alone forces `x = ±y²`: this is exactly `exists_pm_square_of_isIdealSquare`.

* `←`.  Both `y²` and `-y²` have square principal ideal: `(y²) = (y)²`, and `-y² = (-1)·y²`
  with `-1 ∈ ℤˣ` a unit, so `(-y²) = (y²)` as fractional ideals.  The local conditions hold
  because `y²` is visibly a local square and, since `q ≡ 1 (mod 4)` for `q ∈ primesS`, `-1` is
  a square in `ℚ_q` too (`isSquare_neg_one_padic`, Euler's criterion plus Hensel); a product of
  local squares is a local square.

Consequently `V_S/ℚ^{×2} ≅ ℤ/2` (with `neg_one_mem_VS`, `neg_one_not_square`), which is the
`dim_{𝔽₂} V_S/ℚ^{×2} = 1` input of the Shafarevich--Koch relation bound `r ≤ 6` of the tame
Golod--Shafarevich route.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open scoped Classical

namespace Work.TameArithmetic

/-! ## The ideal condition -/

/-- `(y²)` is a square fractional ideal: it is `(y)²`, `toPrincipalIdeal` being a monoid
homomorphism. -/
private lemma isIdealSquare_mul_self (y : ℚˣ) : IsIdealSquare (y * y) := by
  refine ⟨toPrincipalIdeal ℤ ℚ y, ?_⟩
  rw [← map_mul]

/-- `(-y²)` is a square fractional ideal: `-y² = (-1)·y²` and `-1 ∈ ℤˣ` is a unit of `ℤ`, so
`-y²` and `y²` generate the same principal fractional ideal
(`FractionalIdeal.spanSingleton_eq_spanSingleton`). -/
private lemma isIdealSquare_neg_mul_self (y : ℚˣ) : IsIdealSquare (-(y * y)) := by
  refine ⟨toPrincipalIdeal ℤ ℚ y, ?_⟩
  rw [← map_mul]
  refine Units.ext ?_
  rw [coe_toPrincipalIdeal, coe_toPrincipalIdeal,
    FractionalIdeal.spanSingleton_eq_spanSingleton]
  refine ⟨-1, ?_⟩
  simp [Units.val_mul, Units.val_neg]

/-! ## The local conditions -/

open scoped NumberField in
/-- `y²` is a square in `ℚ_q` for every prime `q` (the image of `y` is a square root). -/
private lemma isLocalSquareAtS_mul_self (y : ℚˣ) : IsLocalSquareAtS (y * y) := by
  intro q hq
  haveI : Fact (Nat.Prime q) := ⟨primesS_prime q hq⟩
  refine ⟨inferInstance, ((y : ℚ) : ℚ_[q]), ?_⟩
  simp only [Units.val_mul]
  push_cast
  ring

/-- `-y²` is a square in `ℚ_q` for every `q ∈ primesS`: `q ≡ 1 (mod 4)`, so `-1 = z²` in `ℚ_q`
(`isSquare_neg_one_padic`) and `-y² = (z·y)²`. -/
private lemma isLocalSquareAtS_neg_mul_self (y : ℚˣ) : IsLocalSquareAtS (-(y * y)) := by
  intro q hq
  haveI : Fact (Nat.Prime q) := ⟨primesS_prime q hq⟩
  obtain ⟨z, hz⟩ := isSquare_neg_one_padic (primesS_mod_four q hq)
  refine ⟨inferInstance, z * ((y : ℚ) : ℚ_[q]), ?_⟩
  have hsq : (z * ((y : ℚ) : ℚ_[q])) * (z * ((y : ℚ) : ℚ_[q]))
      = (z * z) * (((y : ℚ) : ℚ_[q]) * ((y : ℚ) : ℚ_[q])) := by ring
  rw [hsq, hz]
  simp only [Units.val_neg, Units.val_mul]
  push_cast
  ring

/-! ## The computation of `V_S` -/

theorem VS_eq_pm_squares {x : ℚˣ} :
    x ∈ Work.TameArithmetic.VS ↔ ∃ y : ℚˣ, x = y * y ∨ x = - (y * y) := by
  constructor
  · intro hx
    exact exists_pm_square_of_isIdealSquare hx.1
  · rintro ⟨y, hy | hy⟩
    · rw [hy]
      exact ⟨isIdealSquare_mul_self y, isLocalSquareAtS_mul_self y⟩
    · rw [hy]
      exact ⟨isIdealSquare_neg_mul_self y, isLocalSquareAtS_neg_mul_self y⟩

end Work.TameArithmetic
