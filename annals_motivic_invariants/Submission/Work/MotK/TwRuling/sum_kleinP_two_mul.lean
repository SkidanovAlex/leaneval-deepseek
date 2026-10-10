import Mathlib
import Submission.Work.MotK.KleinData
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK.TwRuling

theorem sum_kleinP_two_mul {R : Type*} [CommRing R] (a : R) (x : Fin 5 → R) :
    2 * (∑ k : Fin 5, Work.MotK.kleinP a (2 * a) x k)
      = a ^ 2 * (∑ i : Fin 5, x i) ^ 2
        - 5 * a ^ 2 * ((∑ i : Fin 5, (x i) ^ 2) + 2 * ∑ i : Fin 5, x i * x (i + 2)) := by
  simp only [Work.MotK.kleinP, Work.MotK.kleinP0, Work.MotK.kleinP1, Work.MotK.kleinP2,
    Work.MotK.kleinP3, Work.MotK.kleinP4, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  norm_num
  first | refl_ring1 | ring

end Work.MotK.TwRuling
