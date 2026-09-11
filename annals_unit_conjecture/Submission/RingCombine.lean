import Submission.RingBlocks

open UnitConjecture

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable section
namespace Submission
open scoped Classical
open MonoidAlgebra
open Finset

def S_q0_q0 : MonoidAlgebra (ZMod 2) HW := ∑ r ∈ r_q0_q0, single r (1 : ZMod 2)

def S_q0_qA : MonoidAlgebra (ZMod 2) HW := ∑ r ∈ r_q0_qA, single r (1 : ZMod 2)

def S_q0_qB : MonoidAlgebra (ZMod 2) HW := ∑ r ∈ r_q0_qB, single r (1 : ZMod 2)

def S_q0_qAB : MonoidAlgebra (ZMod 2) HW := ∑ r ∈ r_q0_qAB, single r (1 : ZMod 2)

def S_qA_q0 : MonoidAlgebra (ZMod 2) HW := ∑ r ∈ r_qA_q0, single r (1 : ZMod 2)

def S_qA_qA : MonoidAlgebra (ZMod 2) HW := ∑ r ∈ r_qA_qA, single r (1 : ZMod 2)

def S_qA_qB : MonoidAlgebra (ZMod 2) HW := ∑ r ∈ r_qA_qB, single r (1 : ZMod 2)

def S_qA_qAB : MonoidAlgebra (ZMod 2) HW := ∑ r ∈ r_qA_qAB, single r (1 : ZMod 2)

def S_qB_q0 : MonoidAlgebra (ZMod 2) HW := ∑ r ∈ r_qB_q0, single r (1 : ZMod 2)

def S_qB_qA : MonoidAlgebra (ZMod 2) HW := ∑ r ∈ r_qB_qA, single r (1 : ZMod 2)

def S_qB_qB : MonoidAlgebra (ZMod 2) HW := ∑ r ∈ r_qB_qB, single r (1 : ZMod 2)

def S_qB_qAB : MonoidAlgebra (ZMod 2) HW := ∑ r ∈ r_qB_qAB, single r (1 : ZMod 2)

def S_qAB_q0 : MonoidAlgebra (ZMod 2) HW := ∑ r ∈ r_qAB_q0, single r (1 : ZMod 2)

def S_qAB_qA : MonoidAlgebra (ZMod 2) HW := ∑ r ∈ r_qAB_qA, single r (1 : ZMod 2)

def S_qAB_qB : MonoidAlgebra (ZMod 2) HW := ∑ r ∈ r_qAB_qB, single r (1 : ZMod 2)

def S_qAB_qAB : MonoidAlgebra (ZMod 2) HW := ∑ r ∈ r_qAB_qAB, single r (1 : ZMod 2)
