import Submission.RingMain

open UnitConjecture

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable section

namespace Submission

open scoped Classical
open MonoidAlgebra
open Finset

/-- the 21 monomials of u (union, for membership statements) -/
def SU : Finset HW := Qp ∪ PqA ∪ PrB ∪ PsAB

def r_q0_q0 : Finset HW := {(m (-1) (-1) (-1) q0), (m (-1) (-1) 1 q0), (m (-1) 1 (-1) q0), (m (-1) 1 1 q0), (m 1 (-1) (-1) q0), (m 1 (-1) 1 q0), (m 1 1 (-1) q0), (m 1 1 1 q0)}
def r_q0_qA : Finset HW := {(m (-2) (-1) (-1) qA), (m (-2) (-1) 0 qA), (m (-2) 0 (-1) qA), (m (-2) 0 0 qA), (m (-1) (-1) (-1) qA), (m (-1) (-1) 1 qA), (m (-1) 0 (-1) qA), (m (-1) 0 0 qA), (m (-1) 1 0 qA), (m (-1) 1 1 qA), (m 0 (-1) 0 qA), (m 0 (-1) 1 qA), (m 0 0 (-1) qA), (m 0 0 0 qA), (m 0 1 (-1) qA), (m 0 1 1 qA), (m 1 0 (-1) qA), (m 1 0 0 qA), (m 1 1 (-1) qA), (m 1 1 0 qA)}
def r_q0_qB : Finset HW := {(m 0 (-2) 0 qB), (m 0 (-2) 1 qB), (m 0 (-1) (-1) qB), (m 0 (-1) 1 qB), (m 0 0 (-1) qB), (m 0 0 0 qB), (m 1 (-2) 0 qB), (m 1 (-2) 1 qB), (m 1 (-1) 0 qB), (m 1 (-1) 1 qB), (m 1 0 0 qB), (m 1 0 1 qB), (m 1 1 0 qB), (m 1 1 1 qB), (m 2 (-1) (-1) qB), (m 2 (-1) 0 qB), (m 2 0 (-1) qB), (m 2 0 1 qB), (m 2 1 0 qB), (m 2 1 1 qB)}
def r_q0_qAB : Finset HW := {(m (-1) 0 (-1) qAB), (m (-1) 0 0 qAB), (m (-1) 1 (-1) qAB), (m (-1) 1 0 qAB), (m 0 (-1) (-1) qAB), (m 0 (-1) 0 qAB), (m 0 0 (-2) qAB), (m 0 0 (-1) qAB), (m 0 1 (-2) qAB), (m 0 1 (-1) qAB), (m 0 2 (-1) qAB), (m 0 2 0 qAB), (m 1 (-1) (-1) qAB), (m 1 (-1) 0 qAB), (m 1 0 (-2) qAB), (m 1 0 (-1) qAB), (m 1 1 (-2) qAB), (m 1 1 (-1) qAB), (m 1 2 (-1) qAB), (m 1 2 0 qAB), (m 2 0 (-1) qAB), (m 2 0 0 qAB), (m 2 1 (-1) qAB), (m 2 1 0 qAB)}
def r_qA_q0 : Finset HW := {(m (-2) (-1) (-1) qA), (m (-2) (-1) 0 qA), (m (-2) 0 (-1) qA), (m (-2) 0 0 qA), (m (-1) (-1) (-1) qA), (m (-1) (-1) 1 qA), (m (-1) 0 (-1) qA), (m (-1) 0 0 qA), (m (-1) 1 0 qA), (m (-1) 1 1 qA), (m 0 (-1) 0 qA), (m 0 (-1) 1 qA), (m 0 0 (-1) qA), (m 0 0 0 qA), (m 0 1 (-1) qA), (m 0 1 1 qA), (m 1 0 (-1) qA), (m 1 0 0 qA), (m 1 1 (-1) qA), (m 1 1 0 qA)}
def r_qA_qA : Finset HW := {(m (-2) 0 0 q0), (m (-1) (-1) (-1) q0), (m (-1) 0 (-1) q0), (m (-1) 0 1 q0), (m (-1) 1 1 q0), (m 1 (-1) 1 q0), (m 1 0 (-1) q0), (m 1 0 1 q0), (m 1 1 (-1) q0), (m 2 0 0 q0)}
def r_qA_qB : Finset HW := {(m (-1) 0 0 qAB), (m (-1) 1 (-1) qAB), (m 0 (-1) (-1) qAB), (m 0 0 0 qAB), (m 0 0 1 qAB), (m 0 1 0 qAB), (m 0 1 1 qAB), (m 0 2 0 qAB), (m 1 (-1) 0 qAB), (m 1 0 0 qAB), (m 1 0 1 qAB), (m 1 1 0 qAB), (m 1 1 1 qAB), (m 1 2 (-1) qAB), (m 2 0 (-1) qAB), (m 2 1 0 qAB)}
def r_qA_qAB : Finset HW := {(m (-1) (-1) 0 qB), (m 0 (-2) 0 qB), (m 0 0 0 qB), (m 0 0 1 qB), (m 1 (-2) 1 qB), (m 1 (-1) 0 qB), (m 1 (-1) 1 qB), (m 1 (-1) 2 qB), (m 1 0 0 qB), (m 1 0 1 qB), (m 1 0 2 qB), (m 1 1 1 qB), (m 2 (-1) 0 qB), (m 2 (-1) 1 qB), (m 2 1 0 qB), (m 3 0 0 qB)}
def r_qB_q0 : Finset HW := {(m 0 (-2) 0 qB), (m 0 (-2) 1 qB), (m 0 (-1) (-1) qB), (m 0 (-1) 1 qB), (m 0 0 (-1) qB), (m 0 0 0 qB), (m 1 (-2) 0 qB), (m 1 (-2) 1 qB), (m 1 (-1) 0 qB), (m 1 (-1) 1 qB), (m 1 0 0 qB), (m 1 0 1 qB), (m 1 1 0 qB), (m 1 1 1 qB), (m 2 (-1) (-1) qB), (m 2 (-1) 0 qB), (m 2 0 (-1) qB), (m 2 0 1 qB), (m 2 1 0 qB), (m 2 1 1 qB)}
def r_qB_qA : Finset HW := {(m (-1) 0 0 qAB), (m (-1) 1 (-1) qAB), (m 0 (-1) (-1) qAB), (m 0 0 (-2) qAB), (m 0 0 (-1) qAB), (m 0 1 (-2) qAB), (m 0 1 (-1) qAB), (m 0 2 0 qAB), (m 1 (-1) 0 qAB), (m 1 0 (-2) qAB), (m 1 0 (-1) qAB), (m 1 1 (-2) qAB), (m 1 1 (-1) qAB), (m 1 2 (-1) qAB), (m 2 0 (-1) qAB), (m 2 1 0 qAB)}
def r_qB_qB : Finset HW := {(m (-1) (-1) 1 q0), (m (-1) 1 (-1) q0), (m 0 (-2) 0 q0), (m 0 (-1) (-1) q0), (m 0 (-1) 1 q0), (m 0 1 (-1) q0), (m 0 1 1 q0), (m 0 2 0 q0), (m 1 (-1) (-1) q0), (m 1 1 1 q0)}
def r_qB_qAB : Finset HW := {(m (-2) (-1) 0 qA), (m (-2) 0 (-1) qA), (m (-1) (-2) 0 qA), (m (-1) (-1) (-1) qA), (m (-1) (-1) 1 qA), (m (-1) 0 (-1) qA), (m (-1) 1 (-1) qA), (m (-1) 1 0 qA), (m 0 (-1) (-1) qA), (m 0 (-1) 0 qA), (m 0 0 (-1) qA), (m 0 1 (-1) qA), (m 0 1 1 qA), (m 0 2 0 qA), (m 1 0 (-1) qA), (m 1 1 0 qA)}
def r_qAB_q0 : Finset HW := {(m (-1) 0 (-1) qAB), (m (-1) 0 0 qAB), (m (-1) 1 (-1) qAB), (m (-1) 1 0 qAB), (m 0 (-1) (-1) qAB), (m 0 (-1) 0 qAB), (m 0 0 0 qAB), (m 0 0 1 qAB), (m 0 1 0 qAB), (m 0 1 1 qAB), (m 0 2 (-1) qAB), (m 0 2 0 qAB), (m 1 (-1) (-1) qAB), (m 1 (-1) 0 qAB), (m 1 0 0 qAB), (m 1 0 1 qAB), (m 1 1 0 qAB), (m 1 1 1 qAB), (m 1 2 (-1) qAB), (m 1 2 0 qAB), (m 2 0 (-1) qAB), (m 2 0 0 qAB), (m 2 1 (-1) qAB), (m 2 1 0 qAB)}
def r_qAB_qA : Finset HW := {(m (-1) (-1) 0 qB), (m 0 (-2) 0 qB), (m 0 0 0 qB), (m 0 0 1 qB), (m 1 (-2) 1 qB), (m 1 (-1) 0 qB), (m 1 (-1) 1 qB), (m 1 (-1) 2 qB), (m 1 0 0 qB), (m 1 0 1 qB), (m 1 0 2 qB), (m 1 1 1 qB), (m 2 (-1) 0 qB), (m 2 (-1) 1 qB), (m 2 1 0 qB), (m 3 0 0 qB)}
def r_qAB_qB : Finset HW := {(m (-2) (-1) 0 qA), (m (-2) 0 (-1) qA), (m (-1) (-2) 0 qA), (m (-1) (-1) (-1) qA), (m (-1) (-1) 1 qA), (m (-1) 0 (-1) qA), (m (-1) 1 (-1) qA), (m (-1) 1 0 qA), (m 0 (-1) (-1) qA), (m 0 (-1) 0 qA), (m 0 0 (-1) qA), (m 0 1 (-1) qA), (m 0 1 1 qA), (m 0 2 0 qA), (m 1 0 (-1) qA), (m 1 1 0 qA)}
def r_qAB_qAB : Finset HW := {(m (-2) 0 0 q0), (m (-1) 0 (-1) q0), (m (-1) 0 1 q0), (m 0 (-2) 0 q0), (m 0 (-1) (-1) q0), (m 0 (-1) 1 q0), (m 0 0 0 q0), (m 0 1 (-1) q0), (m 0 1 1 q0), (m 0 2 0 q0), (m 1 0 (-1) q0), (m 1 0 1 q0), (m 2 0 0 q0)}

lemma B_q0_q0 :
    (∑ s ∈ Qp, single s (1 : ZMod 2)) * (∑ t ∈ sVq0, single t (1 : ZMod 2))
      = ∑ r ∈ r_q0_q0, single r (1 : ZMod 2) := by
  rw [prod_sum_single_double]
  exact dbl_sum_single_eq_sum_set_op Qp sVq0 (fun s t => s * t) (r_q0_q0)
    (by decide) (by decide)


lemma B_q0_qA :
    (∑ s ∈ Qp, single s (1 : ZMod 2)) * (∑ t ∈ sVqA, single t (1 : ZMod 2))
      = ∑ r ∈ r_q0_qA, single r (1 : ZMod 2) := by
  rw [prod_sum_single_double]
  exact dbl_sum_single_eq_sum_set_op Qp sVqA (fun s t => s * t) (r_q0_qA)
    (by decide) (by decide)


lemma B_q0_qB :
    (∑ s ∈ Qp, single s (1 : ZMod 2)) * (∑ t ∈ sVqB, single t (1 : ZMod 2))
      = ∑ r ∈ r_q0_qB, single r (1 : ZMod 2) := by
  rw [prod_sum_single_double]
  exact dbl_sum_single_eq_sum_set_op Qp sVqB (fun s t => s * t) (r_q0_qB)
    (by decide) (by decide)


lemma B_q0_qAB :
    (∑ s ∈ Qp, single s (1 : ZMod 2)) * (∑ t ∈ sVqAB, single t (1 : ZMod 2))
      = ∑ r ∈ r_q0_qAB, single r (1 : ZMod 2) := by
  rw [prod_sum_single_double]
  exact dbl_sum_single_eq_sum_set_op Qp sVqAB (fun s t => s * t) (r_q0_qAB)
    (by decide) (by decide)


lemma B_qA_q0 :
    (∑ s ∈ PqA, single s (1 : ZMod 2)) * (∑ t ∈ sVq0, single t (1 : ZMod 2))
      = ∑ r ∈ r_qA_q0, single r (1 : ZMod 2) := by
  rw [prod_sum_single_double]
  exact dbl_sum_single_eq_sum_set_op PqA sVq0 (fun s t => s * t) (r_qA_q0)
    (by decide) (by decide)


lemma B_qA_qA :
    (∑ s ∈ PqA, single s (1 : ZMod 2)) * (∑ t ∈ sVqA, single t (1 : ZMod 2))
      = ∑ r ∈ r_qA_qA, single r (1 : ZMod 2) := by
  rw [prod_sum_single_double]
  exact dbl_sum_single_eq_sum_set_op PqA sVqA (fun s t => s * t) (r_qA_qA)
    (by decide) (by decide)


lemma B_qA_qB :
    (∑ s ∈ PqA, single s (1 : ZMod 2)) * (∑ t ∈ sVqB, single t (1 : ZMod 2))
      = ∑ r ∈ r_qA_qB, single r (1 : ZMod 2) := by
  rw [prod_sum_single_double]
  exact dbl_sum_single_eq_sum_set_op PqA sVqB (fun s t => s * t) (r_qA_qB)
    (by decide) (by decide)


lemma B_qA_qAB :
    (∑ s ∈ PqA, single s (1 : ZMod 2)) * (∑ t ∈ sVqAB, single t (1 : ZMod 2))
      = ∑ r ∈ r_qA_qAB, single r (1 : ZMod 2) := by
  rw [prod_sum_single_double]
  exact dbl_sum_single_eq_sum_set_op PqA sVqAB (fun s t => s * t) (r_qA_qAB)
    (by decide) (by decide)


lemma B_qB_q0 :
    (∑ s ∈ PrB, single s (1 : ZMod 2)) * (∑ t ∈ sVq0, single t (1 : ZMod 2))
      = ∑ r ∈ r_qB_q0, single r (1 : ZMod 2) := by
  rw [prod_sum_single_double]
  exact dbl_sum_single_eq_sum_set_op PrB sVq0 (fun s t => s * t) (r_qB_q0)
    (by decide) (by decide)


lemma B_qB_qA :
    (∑ s ∈ PrB, single s (1 : ZMod 2)) * (∑ t ∈ sVqA, single t (1 : ZMod 2))
      = ∑ r ∈ r_qB_qA, single r (1 : ZMod 2) := by
  rw [prod_sum_single_double]
  exact dbl_sum_single_eq_sum_set_op PrB sVqA (fun s t => s * t) (r_qB_qA)
    (by decide) (by decide)


lemma B_qB_qB :
    (∑ s ∈ PrB, single s (1 : ZMod 2)) * (∑ t ∈ sVqB, single t (1 : ZMod 2))
      = ∑ r ∈ r_qB_qB, single r (1 : ZMod 2) := by
  rw [prod_sum_single_double]
  exact dbl_sum_single_eq_sum_set_op PrB sVqB (fun s t => s * t) (r_qB_qB)
    (by decide) (by decide)


lemma B_qB_qAB :
    (∑ s ∈ PrB, single s (1 : ZMod 2)) * (∑ t ∈ sVqAB, single t (1 : ZMod 2))
      = ∑ r ∈ r_qB_qAB, single r (1 : ZMod 2) := by
  rw [prod_sum_single_double]
  exact dbl_sum_single_eq_sum_set_op PrB sVqAB (fun s t => s * t) (r_qB_qAB)
    (by decide) (by decide)


lemma B_qAB_q0 :
    (∑ s ∈ PsAB, single s (1 : ZMod 2)) * (∑ t ∈ sVq0, single t (1 : ZMod 2))
      = ∑ r ∈ r_qAB_q0, single r (1 : ZMod 2) := by
  rw [prod_sum_single_double]
  exact dbl_sum_single_eq_sum_set_op PsAB sVq0 (fun s t => s * t) (r_qAB_q0)
    (by decide) (by decide)


lemma B_qAB_qA :
    (∑ s ∈ PsAB, single s (1 : ZMod 2)) * (∑ t ∈ sVqA, single t (1 : ZMod 2))
      = ∑ r ∈ r_qAB_qA, single r (1 : ZMod 2) := by
  rw [prod_sum_single_double]
  exact dbl_sum_single_eq_sum_set_op PsAB sVqA (fun s t => s * t) (r_qAB_qA)
    (by decide) (by decide)


lemma B_qAB_qB :
    (∑ s ∈ PsAB, single s (1 : ZMod 2)) * (∑ t ∈ sVqB, single t (1 : ZMod 2))
      = ∑ r ∈ r_qAB_qB, single r (1 : ZMod 2) := by
  rw [prod_sum_single_double]
  exact dbl_sum_single_eq_sum_set_op PsAB sVqB (fun s t => s * t) (r_qAB_qB)
    (by decide) (by decide)


lemma B_qAB_qAB :
    (∑ s ∈ PsAB, single s (1 : ZMod 2)) * (∑ t ∈ sVqAB, single t (1 : ZMod 2))
      = ∑ r ∈ r_qAB_qAB, single r (1 : ZMod 2) := by
  rw [prod_sum_single_double]
  exact dbl_sum_single_eq_sum_set_op PsAB sVqAB (fun s t => s * t) (r_qAB_qAB)
    (by decide) (by decide)

end Submission
