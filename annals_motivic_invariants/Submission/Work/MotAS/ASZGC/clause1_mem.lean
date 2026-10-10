import Mathlib
import Submission.Work.MotAS.ASZGC.Defs
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotAS.ASZGC.SmallCorr
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Work.MotAS.ASZGC

open MvPolynomial

/-- The `Fin.succ`-rename data expands to the explicit identity
`rename D0 * X 0 + rename R0 = ((C a)^2 + (C b)^2) * zcubAS 3 - ((C a)^2 - C a * C b - (C b)^2) * zcubAS 1`
up to the correction `5 * C1c`. -/
private theorem clause1_key (K : Type) [Field K] [CharP K 5] (a b g : K) :
    MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (D0 a b g) * MvPolynomial.X 0
      + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (R0 a b g)
      - (((MvPolynomial.C a) ^ 2 + (MvPolynomial.C b) ^ 2) * Work.MotAS.zcubAS a b g 3
        - ((MvPolynomial.C a) ^ 2 - MvPolynomial.C a * MvPolynomial.C b
              - (MvPolynomial.C b) ^ 2) * Work.MotAS.zcubAS a b g 1)
      = 5 * C1c a b g := by
  simp only [D0, R0, C1c, C1c_0, Work.MotAS.zcubAS, Work.MotAS.kleinRAS, Work.MotAS.kleinRAS0,
    Work.MotAS.kleinRAS1, Work.MotAS.kleinRAS2, Work.MotAS.kleinRAS3, Work.MotAS.kleinRAS4,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Fin.isValue,
    map_add, map_mul, map_pow, map_ofNat,
    MvPolynomial.rename_C, MvPolynomial.rename_X, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  first | refl_ring1 | ring

theorem clause1_mem (K : Type) [Field K] [CharP K 5] (a b g : K) :
    MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.D0 a b g) * MvPolynomial.X 0
      + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (Work.MotAS.ASZGC.R0 a b g)
    ∈ Work.MotAS.ZIAS a b g := by
  have h5 : (5 : MvPolynomial (Fin 3) K) = 0 := CharP.cast_eq_zero _ 5
  have hkey := clause1_key K a b g
  rw [h5, zero_mul] at hkey
  have hG : MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (D0 a b g) * MvPolynomial.X 0
      + MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3) (R0 a b g)
      = ((MvPolynomial.C a) ^ 2 + (MvPolynomial.C b) ^ 2) * Work.MotAS.zcubAS a b g 3
        - ((MvPolynomial.C a) ^ 2 - MvPolynomial.C a * MvPolynomial.C b
              - (MvPolynomial.C b) ^ 2) * Work.MotAS.zcubAS a b g 1 :=
    sub_eq_zero.mp hkey
  rw [hG]
  exact Ideal.sub_mem _
    (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨3, rfl⟩))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨1, rfl⟩))

end Work.MotAS.ASZGC
