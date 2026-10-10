import Mathlib
import Submission.Work.MotAS.Nodes.Fw3Aux
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.Nodes.Fw3FwEq`

The third component of the AS forward chart map `fwVecAS2 a b g` factors as

`fwVecAS2 a b g 3 = C 4 · C (asA a b)² · asH a b g`,

with `asA a b = a² - ab - b²` and `asH` the cubic of `Fw3Aux`.  The identity is established
over an *arbitrary* commutative ring (it is an integral polynomial identity): one unfolds the
explicit data (`kleinPAS3`, the stereographic vector `kleinStereoAS` at `pAS0` and `chart3`, and
`asA, asB, asQ, asH`), pushes `MvPolynomial.C` across the ring operations with `simp`, normalises
the numeric constants `C 2, C 3, C 4` to plain numerals, and closes with `ring`.
-/

set_option maxHeartbeats 1600000

namespace Work.MotAS.Nodes

open MvPolynomial

theorem Fw3FwEq (K : Type) [CommRing K] (a b g : K) :
    Work.MotAS.fwVecAS2 a b g 3
      = MvPolynomial.C 4 * MvPolynomial.C (Work.MotAS.Nodes.Fw3.asA a b) ^ 2
        * Work.MotAS.Nodes.Fw3.asH a b g := by
  simp only [Work.MotAS.fwVecAS2, Work.MotAS.kleinPAS, Work.MotAS.kleinPAS3,
    Work.MotAS.kleinStereoAS, Work.MotAS.kleinBilinAS, Work.MotAS.kleinQAS, Work.MotAS.pAS0,
    Work.MotK.chart3, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Work.MotAS.Nodes.Fw3.asA, Work.MotAS.Nodes.Fw3.asB,
    Work.MotAS.Nodes.Fw3.asQ, Work.MotAS.Nodes.Fw3.asH, Work.MotAS.Nodes.Fw3.asHlo,
    Work.MotAS.Nodes.Fw3.asH3]
  simp
  simp only [map_ofNat MvPolynomial.C]
  first | refl_ring1 | ring

end Work.MotAS.Nodes
