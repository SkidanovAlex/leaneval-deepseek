import Submission.Ring
import Mathlib.Algebra.MonoidAlgebra.Basic

open UnitConjecture

set_option autoImplicit false
set_option maxRecDepth 10000

noncomputable section

namespace Submission

open scoped Classical
open MonoidAlgebra
open Finset

-- ============================================================
-- monomial sets
-- ============================================================

def Qp : Finset HW := {(m 0 0 0 q0), (m 1 0 0 q0), (m 0 1 0 q0), (m 1 1 0 q0), (m 0 0 (-1) q0), (m 1 0 (-1) q0), (m 0 1 (-1) q0), (m 1 1 (-1) q0)}
def Qq : Finset HW := {(m (-1) (-1) 0 q0), (m 1 0 0 q0), (m 0 (-1) 1 q0), (m 0 0 1 q0)}
def Qr : Finset HW := {(m 0 0 0 q0), (m 1 0 0 q0), (m 0 (-1) 1 q0), (m 1 1 1 q0)}
def Qs : Finset HW := {(m 0 0 0 q0), (m 1 0 (-1) q0), (m (-1) 0 (-1) q0), (m 0 1 (-1) q0), (m 0 (-1) (-1) q0)}
def PqA : Finset HW := {(m (-1) (-1) 0 qA), (m 1 0 0 qA), (m 0 (-1) 1 qA), (m 0 0 1 qA)}
def PrB : Finset HW := {(m 0 0 0 qB), (m 1 0 0 qB), (m 0 (-1) 1 qB), (m 1 1 1 qB)}
def PsAB : Finset HW := {(m 0 0 0 qAB), (m 1 0 (-1) qAB), (m (-1) 0 (-1) qAB), (m 0 1 (-1) qAB), (m 0 (-1) (-1) qAB)}

/-- the 21 monomials of u -/
def sVq0 : Finset HW := {(m (-1) (-1) 0 q0), (m (-1) (-1) 1 q0), (m (-1) 0 0 q0), (m (-1) 0 1 q0), (m 0 (-1) 0 q0), (m 0 (-1) 1 q0), (m 0 0 0 q0), (m 0 0 1 q0)}
def sVqA : Finset HW := {(m (-2) (-1) 0 qA), (m (-1) (-1) 1 qA), (m (-1) 0 1 qA), (m 0 0 0 qA)}
def sVqB : Finset HW := {(m 0 (-2) 1 qB), (m 0 (-1) 0 qB), (m 1 (-1) 0 qB), (m 1 0 1 qB)}
def sVqAB : Finset HW := {(m (-1) 0 0 qAB), (m 0 (-1) 0 qAB), (m 0 0 (-1) qAB), (m 0 1 0 qAB), (m 1 0 0 qAB)}

/-- the transported element u as a sum over its monomials -/
def U0 : MonoidAlgebra (ZMod 2) HW :=
  (((∑ q ∈ Qp, single q (1 : ZMod 2)) + (∑ q ∈ PqA, single q (1 : ZMod 2)))
    + (∑ q ∈ PrB, single q (1 : ZMod 2))) + (∑ q ∈ PsAB, single q (1 : ZMod 2))

/-- the transported element v as a sum over its monomials -/
def V0 : MonoidAlgebra (ZMod 2) HW :=
  (((∑ t ∈ sVq0, single t (1 : ZMod 2)) + (∑ t ∈ sVqA, single t (1 : ZMod 2)))
    + (∑ t ∈ sVqB, single t (1 : ZMod 2))) + (∑ t ∈ sVqAB, single t (1 : ZMod 2))

end Submission
