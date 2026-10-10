import Mathlib
import Submission.Work.MotAS.ASRed
import Submission.Work.MotAS.ASData
import Submission.Work.MotK.KleinData

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Base data for the transport of the secant quintic `s` to AS (Artin–Schreier) coordinates

`Work.MotAS.asXi y i` is the coefficient vector of `Σ_j y_j (w+i)^j` in the basis `1,w,w²,w³,w⁴`
of `R[w]/(w⁵-w-g)`.

`Work.MotAS.AsT.Zv k` is the same vector for the five literal indices `k = 0,…,4` (written with
integer coefficients only, so that `simp` can reduce it at literal indices), and
`Work.MotAS.AsT.AX w y i` is the corresponding element `Σ_l (Zv i) l w^l` of `R`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Work.MotAS

variable {R : Type*} [CommRing R]

/-- Coefficients of `Σ_j y_j (w+i)^j` in the basis `1,w,w²,w³,w⁴`. -/
def asXi (y : Fin 5 → R) (i : Fin 5) : Fin 5 → R :=
  ![ y 0 + ((i:ℕ):R)*y 1 + ((i:ℕ):R)^2*y 2 + ((i:ℕ):R)^3*y 3 + ((i:ℕ):R)^4*y 4,
     y 1 + 2*((i:ℕ):R)*y 2 + 3*((i:ℕ):R)^2*y 3 + 4*((i:ℕ):R)^3*y 4,
     y 2 + 3*((i:ℕ):R)*y 3 + 6*((i:ℕ):R)^2*y 4,
     y 3 + 4*((i:ℕ):R)*y 4,
     y 4 ]

/-- `asXi` really are the coefficients of `Σ_j y_j (w+i)^j` in the basis `1,w,…,w⁴`. -/
lemma asXi_spec (w : R) (y : Fin 5 → R) (i : Fin 5) :
    (∑ l : Fin 5, asXi y i l * w ^ (l:ℕ))
      = ∑ j : Fin 5, (w + ((i:ℕ):R)) ^ (j:ℕ) * y j := by
  fin_cases i <;>
    simp only [asXi, Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons] <;>
    norm_num <;> ring

end Work.MotAS

namespace Work.MotAS.AsT

variable {R : Type*} [CommRing R]

/-- Coefficient vector of `Σ_j y_j (w+k)^j` for `k = 0`, with integer coefficients. -/
def Zv0 (y : Fin 5 → R) : Fin 5 → R :=
  ![y 0, y 1, y 2, y 3, y 4]

/-- Coefficient vector of `Σ_j y_j (w+k)^j` for `k = 1`, with integer coefficients. -/
def Zv1 (y : Fin 5 → R) : Fin 5 → R :=
  ![y 0 + y 1 + y 2 + y 3 + y 4, y 1 + 2*y 2 + 3*y 3 + 4*y 4, y 2 + 3*y 3 + 6*y 4, y 3 + 4*y 4, y 4]

/-- Coefficient vector of `Σ_j y_j (w+k)^j` for `k = 2`, with integer coefficients. -/
def Zv2 (y : Fin 5 → R) : Fin 5 → R :=
  ![y 0 + 2*y 1 + 4*y 2 + 8*y 3 + 16*y 4, y 1 + 4*y 2 + 12*y 3 + 32*y 4,
    y 2 + 6*y 3 + 24*y 4, y 3 + 8*y 4, y 4]

/-- Coefficient vector of `Σ_j y_j (w+k)^j` for `k = 3`, with integer coefficients. -/
def Zv3 (y : Fin 5 → R) : Fin 5 → R :=
  ![y 0 + 3*y 1 + 9*y 2 + 27*y 3 + 81*y 4, y 1 + 6*y 2 + 27*y 3 + 108*y 4,
    y 2 + 9*y 3 + 54*y 4, y 3 + 12*y 4, y 4]

/-- Coefficient vector of `Σ_j y_j (w+k)^j` for `k = 4`, with integer coefficients. -/
def Zv4 (y : Fin 5 → R) : Fin 5 → R :=
  ![y 0 + 4*y 1 + 16*y 2 + 64*y 3 + 256*y 4, y 1 + 8*y 2 + 48*y 3 + 256*y 4,
    y 2 + 12*y 3 + 96*y 4, y 3 + 16*y 4, y 4]

lemma pw2 (A : R) : A ^ 2 = A * A := by ring
lemma pw3 (A : R) : A ^ 3 = A * A * A := by ring
lemma pw4 (A : R) : A ^ 4 = A * A * A * A := by ring
lemma pw5 (A : R) : A ^ 5 = A * A * A * A * A := by ring

/-- The element `Σ_l (Zv i) l w^l` of `R[w]`. -/
def AX (w : R) (y : Fin 5 → R) (i : Fin 5) : R :=
  ![ (∑ l : Fin 5, Zv0 y l * w ^ (l:ℕ)), (∑ l : Fin 5, Zv1 y l * w ^ (l:ℕ)),
     (∑ l : Fin 5, Zv2 y l * w ^ (l:ℕ)), (∑ l : Fin 5, Zv3 y l * w ^ (l:ℕ)),
     (∑ l : Fin 5, Zv4 y l * w ^ (l:ℕ)) ] i

end Work.MotAS.AsT
