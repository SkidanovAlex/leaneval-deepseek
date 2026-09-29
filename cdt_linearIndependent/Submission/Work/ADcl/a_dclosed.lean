import Mathlib
import Submission.CDTPlan.InterfacesA2
import Submission.Work.ADcl.asym_setup
import Submission.Work.ADcl.ode_H
import Submission.Work.ADcl.ode_Hw
import Submission.Work.ADcl.tfun
import Submission.Work.ADcl.reduce_generic
import Submission.Work.ADcl.x_relation_A
import Submission.Work.ADcl.y_ode_of_xrel
import Submission.Work.ADcl.dclosed_of_yode

/-!
# Area ADcl — the `d/dy`-closure of the 14 functions of Theorem A

`ADClosed` says that for every `a b c : ℤ` the `ℚ(y)`-span of the fourteen functions
`![B₁,…,B₅, G, G', G'', G''', B₆, B₇, ∫G, ∫(G−G(0))/y, ∫(G−G(0)−G'(0)y)/y²]`
(`G = GZ a b c = Sym⁺(a·H_A + b·H_B + c·H_C)`) is closed under `d/dy`.

The proof is the symmetrised-powers route of `Work.CDcl.c_dclosed`, with the x-side ODE being
Zagier's order-two inhomogeneous ODE `x(1−x)(1−9x)H'' + (1−20x+27x²)H' + 3(−1+3x)H = b + c/(1−x)`
(`Submission.CDT.functionsH_ode`):

* `x_relation_A`: a nontrivial `ℚ[x]`-relation among the five pullbacks
  `T k = ((d/dy)^k G) ∘ y`, obtained by reducing `A^k H` and `A^k (H∘φ)` to the four-dimensional
  `ℚ(x)`-span of `H, H', H∘φ, (H∘φ)'` (`reduce_H`, `reduce_Hw`) and applying the linear algebra
  fact `Work.CDcl.xrel_linalg` (five vectors in a four-dimensional span are dependent);
* `y_ode_of_xrel`: symmetrising that relation (adding its `φ`-conjugate) and descending through
  `y = x²/(x−1)` gives an inhomogeneous order-four `y`-ODE for `G` with polynomial coefficients
  and polynomial inhomogeneity (`Work.CDcl.inv_sum_aux`, `Submission.CDT.symp_subst_y_injective`,
  `Work.CDcl.order_raise`);
* `dclosed_of_yode`: the fourteen rows of the coefficient matrix (pure rows from `PureFacts`, the
  `G'''`-row from the ODE with the constant term absorbed into `B₁ = 1`, the integral rows from
  `(∫(G − jet_k G)/y^k)' = (G − jet_k G)/y^k`).
-/

namespace Work.ADcl

open Submission.CDTPlan

theorem a_dclosed (hP : PureFacts) : ADClosed := by
  intro a b c
  refine dclosed_of_yode a b c ?_ hP
  obtain ⟨q, A, cc, hq, hode⟩ :=
    y_ode_of_xrel (a : ℚ) (b : ℚ) (c : ℚ) (x_relation_A (a : ℚ) (b : ℚ) (c : ℚ))
  exact ⟨q, A, cc, hq, hode⟩

end Work.ADcl
