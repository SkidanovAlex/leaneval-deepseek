import Mathlib
import Submission.Work.WilE3.API.RemDefs

namespace Work.WilE3.API

set_option autoImplicit false
open Classical Topology

noncomputable section

/-!
## Basic vocabulary for the derivative of a Taylor sum

`eTay y S b z = ∑ m ∈ S, b m * eTayMon y m z` where `eTayMon y m` is the monomial
`∏ j, (z j - y j) ^ (m j) / ((m j)!)`.  The lemmas below record the derivative of a single
monomial and the shape of the resulting sum.
-/

/-- The monomial factor of a single Taylor summand. -/
def eTayMon {k : ℕ} (y : Fin k → ℝ) (m : Fin k → ℕ) (x : Fin k → ℝ) : ℝ :=
  ∏ j, (x j - y j) ^ (m j) / ((m j).factorial : ℝ)

/-- The symbolic gradient of `eTayMon y m`. -/
def eTayGrad {k : ℕ} (y : Fin k → ℝ) (m : Fin k → ℕ) (x : Fin k → ℝ) :
    (Fin k → ℝ) →L[ℝ] ℝ :=
  ∑ i : Fin k, (if 0 < m i then eTayMon y (miS m i) x else 0) •
    (ContinuousLinearMap.proj (φ := fun _ : Fin k => ℝ) i)

theorem eTayCoeff_eq {k : ℕ} (y x : Fin k → ℝ) (b : (Fin k → ℕ) → ℝ) (m : Fin k → ℕ) :
    eTayCoeff y b m x = b m * eTayMon y m x := rfl

theorem eTay_eq_sum_mon {k : ℕ} (y : Fin k → ℝ) (S : Finset (Fin k → ℕ))
    (b : (Fin k → ℕ) → ℝ) (x : Fin k → ℝ) :
    eTay y S b x = ∑ m ∈ S, b m * eTayMon y m x := rfl

theorem eDTay_eq {k : ℕ} (y x : Fin k → ℝ) (b : (Fin k → ℕ) → ℝ) (i : Fin k)
    (m : Fin k → ℕ) :
    eDTay y b i m x = b m * eTayMon y (miS m i) x := rfl

end

end Work.WilE3.API
