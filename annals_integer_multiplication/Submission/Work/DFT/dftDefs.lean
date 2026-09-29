import Mathlib
import Submission.HvdH.Interfaces

/-!
# Helper definitions for the multidimensional DFT algebra (`HvdH.DFTMathProp`)

This file is owned by the DFT math area.  It introduces the signed multi-phase

`myPhase ts c k = Σᵢ cᵢ kᵢ / tᵢ`  (`cᵢ : ℤ`, `kᵢ : ℕ`),

which linearises the combinations of `HvdH.phase` appearing when composing two
multidimensional DFTs, together with the componentwise difference operations on
digit lists that produce the coefficient tuples.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.DFT

/-- Signed multi-phase `Σᵢ cᵢ kᵢ / tᵢ` with integer coefficients `cᵢ`. -/
noncomputable def myPhase : List ℕ → List ℤ → List ℕ → ℝ
  | t :: ts, c :: cs, k :: ks => ((c : ℝ) * (k : ℝ)) / (t : ℝ) + myPhase ts cs ks
  | _, _, _ => 0

/-- Componentwise difference of two natural lists, as an integer list. -/
def subN (a b : List ℕ) : List ℤ := List.zipWith (fun x y => (x : ℤ) - y) a b

/-- Componentwise subtraction of a natural list from an integer list. -/
def subNZ (c : List ℤ) (b : List ℕ) : List ℤ := List.zipWith (fun x y => x - (y : ℤ)) c b

/-- The exponential factor `exp(sgn · 2πi · Σᵢ jᵢkᵢ/tᵢ)` of the multidimensional DFT. -/
noncomputable def dftExp (ts : List ℕ) (sgn : ℤ) (j k : ℕ) : ℂ :=
  Complex.exp ((sgn : ℂ) * 2 * (Real.pi : ℂ) * Complex.I *
    (HvdH.phase ts (HvdH.digits ts j) (HvdH.digits ts k) : ℂ))

/-- The exponential `exp(2πi · myPhase ts c (digits ts k))` appearing in the
orthogonality relation for the multidimensional DFT. -/
noncomputable def charExp (ts : List ℕ) (c : List ℤ) (k : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (myPhase ts c (HvdH.digits ts k) : ℂ))

@[simp] theorem subN_cons (a b : ℕ) (as bs : List ℕ) :
    subN (a :: as) (b :: bs) = ((a : ℤ) - b) :: subN as bs := rfl

@[simp] theorem subNZ_cons (c : ℤ) (b : ℕ) (cs : List ℤ) (bs : List ℕ) :
    subNZ (c :: cs) (b :: bs) = (c - b) :: subNZ cs bs := rfl

theorem digits_length (ts : List ℕ) (m : ℕ) : (HvdH.digits ts m).length = ts.length := by
  induction ts generalizing m with
  | nil => simp [HvdH.digits]
  | cons t ts ih => simp [HvdH.digits, ih]

end Work.DFT
