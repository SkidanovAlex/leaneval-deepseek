import Mathlib
import Submission.CDT.SympDescent

/-!
# Area CPull — the symmetrised-power polynomials `P_m(y) = x^m + φ(x)^m`

`sympQ m` is the polynomial in the symmetrisation coordinate `y = x²/(x−1)` whose
substitution by `sympY` is the symmetrised power `sympP m = X^m + sympPhi^m`, defined
directly by the recurrence

`P_0 = 2`, `P_1 = y`, `P_{m+2} = y·P_{m+1} − y·P_m`.

`sympRep P` is the candidate for `Sym⁺P`: `Σ_m coeff_m(P) · P_m(y)` (a finite sum at each
coefficient, because `P_m` has `y`-valuation `⌈m/2⌉`).
-/

open scoped BigOperators

namespace Work.CPull

open PowerSeries

/-- The symmetrised powers `P_m(y)`, defined by the recurrence
`P_0 = 2`, `P_1 = X`, `P_{m+2} = X·P_{m+1} − X·P_m`. -/
noncomputable def sympQ : ℕ → PowerSeries ℚ
  | 0 => 2
  | 1 => X
  | n + 2 => X * sympQ (n + 1) - X * sympQ n

@[simp] lemma sympQ_zero : sympQ 0 = 2 := rfl
@[simp] lemma sympQ_one : sympQ 1 = X := rfl
lemma sympQ_succ_succ (n : ℕ) : sympQ (n + 2) = X * sympQ (n + 1) - X * sympQ n := rfl

/-- The explicit symmetrisation of `P` along `y`: `Σ_m coeff_m(P) · P_m(y)`. -/
noncomputable def sympRep (P : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun n =>
    ∑ m ∈ Finset.range (2 * n + 1), PowerSeries.coeff m P * PowerSeries.coeff n (sympQ m)

end Work.CPull
