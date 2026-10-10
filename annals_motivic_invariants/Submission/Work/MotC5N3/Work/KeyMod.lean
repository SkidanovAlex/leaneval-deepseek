import Mathlib
import Submission.Work.MotC5N3.Work.KeyDefs
import Submission.Work.MotC5N3.Work.KeyCjA
import Submission.Work.MotC5N3.Work.KeyCjB

import Submission.Work.MotC5N3.RhoGen.gen.Shp0Coeffs
import Submission.Work.MotC5N3.RhoGen.gen.Shp11Coeffs
import Submission.Work.MotC5N3.RhoGen.gen.Shp12Coeffs
import Submission.Work.MotC5N3.RhoGen.gen.Shp13Coeffs
import Submission.Work.MotC5N3.RhoGen.gen.Shp15Coeffs
import Submission.Work.MotC5N3.RhoGen.gen.Shp17Coeffs
import Submission.Work.MotC5N3.RhoGen.gen.Shp20Coeffs
import Submission.Work.MotC5N3.RhoGen.gen.Shp22Coeffs
import Submission.Work.MotC5N3.RhoGen.gen.Shp24Coeffs
import Submission.Work.MotC5N3.RhoGen.gen.Shp27Coeffs
import Submission.Work.MotC5N3.RhoGen.gen.Shp2Coeffs
import Submission.Work.MotC5N3.RhoGen.gen.Shp3Coeffs
import Submission.Work.MotC5N3.RhoGen.gen.Shp5Coeffs
import Submission.Work.MotC5N3.RhoGen.gen.Shp7Coeffs
import Submission.Work.MotC5N3.RhoGen.gen.Shp9Coeffs
import Submission.Work.MotC5N3.RhoGen.gen.Shp0B
import Submission.Work.MotC5N3.RhoGen.gen.Shp11B
import Submission.Work.MotC5N3.RhoGen.gen.Shp12B
import Submission.Work.MotC5N3.RhoGen.gen.Shp13B
import Submission.Work.MotC5N3.RhoGen.gen.Shp15B
import Submission.Work.MotC5N3.RhoGen.gen.Shp17B
import Submission.Work.MotC5N3.RhoGen.gen.Shp20B
import Submission.Work.MotC5N3.RhoGen.gen.Shp22B
import Submission.Work.MotC5N3.RhoGen.gen.Shp24B
import Submission.Work.MotC5N3.RhoGen.gen.Shp27B
import Submission.Work.MotC5N3.RhoGen.gen.Shp2B
import Submission.Work.MotC5N3.RhoGen.gen.Shp3B
import Submission.Work.MotC5N3.RhoGen.gen.Shp5B
import Submission.Work.MotC5N3.RhoGen.gen.Shp7B
import Submission.Work.MotC5N3.RhoGen.gen.Shp9B
import Submission.Work.MotC5N3.Work.RhoSV2.ShpT0
import Submission.Work.MotC5N3.Work.RhoSV2.ShpT1
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Work.MotC5N3.Work

open Polynomial

/-- The expansion of `kleinRAS0` at the witness ruling vector in factored `X`-coefficient form. -/
theorem hL (K : Type) [Field K] [CharP K 5] (a b g : K) :
    Work.MotAS.kleinRAS0 (Polynomial.C a) (Polynomial.C b) (Polynomial.C g)
        (Work.MotV5.ASLocal.WaV a b g)
      = Polynomial.C (AsL0 a b g) * Polynomial.X ^ 0 + Polynomial.C (AsL1 a b g) * Polynomial.X ^ 1 + Polynomial.C (AsL2 a b g) * Polynomial.X ^ 2 + Polynomial.C (AsL3 a b g) * Polynomial.X ^ 3 + Polynomial.C (AsL4 a b g) * Polynomial.X ^ 4 + Polynomial.C (AsL5 a b g) * Polynomial.X ^ 5 + Polynomial.C (AsL6 a b g) * Polynomial.X ^ 6 + Polynomial.C (AsL7 a b g) * Polynomial.X ^ 7 + Polynomial.C (AsL8 a b g) * Polynomial.X ^ 8 + Polynomial.C (AsL9 a b g) * Polynomial.X ^ 9 + Polynomial.C (AsL10 a b g) * Polynomial.X ^ 10 + Polynomial.C (AsL11 a b g) * Polynomial.X ^ 11 + Polynomial.C (AsL12 a b g) * Polynomial.X ^ 12 + Polynomial.C (AsL13 a b g) * Polynomial.X ^ 13 + Polynomial.C (AsL14 a b g) * Polynomial.X ^ 14 + Polynomial.C (AsL15 a b g) * Polynomial.X ^ 15 + Polynomial.C (AsL16 a b g) * Polynomial.X ^ 16 + Polynomial.C (AsL17 a b g) * Polynomial.X ^ 17 + Polynomial.C (AsL18 a b g) * Polynomial.X ^ 18 := by
  simp only [Work.MotAS.kleinRAS0, Work.MotV5.ASLocal.WaV,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val_succ', mul_assoc]
  rw [Work.MotV5.ASLocal.shp_0_bounded, Work.MotV5.ASLocal.shp_2_bounded, Work.MotV5.ASLocal.shp_3_bounded, Work.MotV5.ASLocal.shp_5_bounded, Work.MotV5.ASLocal.shp_7_bounded, Work.MotV5.ASLocal.shp_9_bounded, Work.MotV5.ASLocal.shp_11_bounded, Work.MotV5.ASLocal.shp_12_bounded, Work.MotV5.ASLocal.shp_13_bounded, Work.MotV5.ASLocal.shp_15_bounded, Work.MotV5.ASLocal.shp_17_bounded, Work.MotV5.ASLocal.shp_20_bounded, Work.MotV5.ASLocal.shp_22_bounded, Work.MotV5.ASLocal.shp_24_bounded, Work.MotV5.ASLocal.shp_27_bounded,
  Work.MotV5.ASLocal.shp_1, Work.MotV5.ASLocal.shp_4, Work.MotV5.ASLocal.shp_6, Work.MotV5.ASLocal.shp_8, Work.MotV5.ASLocal.shp_10, Work.MotV5.ASLocal.shp_14, Work.MotV5.ASLocal.shp_16, Work.MotV5.ASLocal.shp_18, Work.MotV5.ASLocal.shp_19, Work.MotV5.ASLocal.shp_21, Work.MotV5.ASLocal.shp_23, Work.MotV5.ASLocal.shp_25, Work.MotV5.ASLocal.shp_26, Work.MotV5.ASLocal.shp_28]
  simp only [Work.MotV5.ASLocal.Shp11R, Work.MotV5.ASLocal.Shp24R, Work.MotV5.ASLocal.Shp22R, Work.MotV5.ASLocal.Shp7R, Work.MotV5.ASLocal.Shp27R, Work.MotV5.ASLocal.Shp20R, Work.MotV5.ASLocal.Shp17R, Work.MotV5.ASLocal.Shp0R, Work.MotV5.ASLocal.Shp12R, Work.MotV5.ASLocal.Shp15R, Work.MotV5.ASLocal.Shp13R, Work.MotV5.ASLocal.Shp3R, Work.MotV5.ASLocal.Shp5R, Work.MotV5.ASLocal.Shp2R, Work.MotV5.ASLocal.Shp9R,
    AsL0, AsL1, AsL2, AsL3, AsL4, AsL5, AsL6, AsL7, AsL8, AsL9, AsL10, AsL11, AsL12, AsL13,
    AsL14, AsL15, AsL16, AsL17, AsL18,
    AsCoef0, AsCoef1, AsCoef2, AsCoef3, AsCoef4, AsCoef5, AsCoef6, AsCoef7, AsCoef8, AsCoef9,
    AsCoef10, AsCoef11, AsCoef12, AsCoef13, AsCoef14,
    Polynomial.C_add, Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_neg,
    Polynomial.C_ofNat, Polynomial.C_eq_natCast]
  refl_ring1

/-- The same expansion on the `QP`/`PhiP` side. -/
theorem hR (K : Type) [Field K] [CharP K 5] (a b g : K) :
    (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g) * Work.MotV5.ASLocal.QP a b g
        + Work.MotV5.ASLocal.PhiP a b g
      = Polynomial.C (AsZ0 a b g) * Polynomial.X ^ 0 + Polynomial.C (AsZ1 a b g) * Polynomial.X ^ 1 + Polynomial.C (AsZ2 a b g) * Polynomial.X ^ 2 + Polynomial.C (AsZ3 a b g) * Polynomial.X ^ 3 + Polynomial.C (AsZ4 a b g) * Polynomial.X ^ 4 + Polynomial.C (AsZ5 a b g) * Polynomial.X ^ 5 + Polynomial.C (AsZ6 a b g) * Polynomial.X ^ 6 + Polynomial.C (AsZ7 a b g) * Polynomial.X ^ 7 + Polynomial.C (AsZ8 a b g) * Polynomial.X ^ 8 + Polynomial.C (AsZ9 a b g) * Polynomial.X ^ 9 + Polynomial.C (AsZ10 a b g) * Polynomial.X ^ 10 + Polynomial.C (AsZ11 a b g) * Polynomial.X ^ 11 + Polynomial.C (AsZ12 a b g) * Polynomial.X ^ 12 + Polynomial.C (AsZ13 a b g) * Polynomial.X ^ 13 + Polynomial.C (AsZ14 a b g) * Polynomial.X ^ 14 + Polynomial.C (AsZ15 a b g) * Polynomial.X ^ 15 + Polynomial.C (AsZ16 a b g) * Polynomial.X ^ 16 + Polynomial.C (AsZ17 a b g) * Polynomial.X ^ 17 + Polynomial.C (AsZ18 a b g) * Polynomial.X ^ 18 := by
  simp only [Work.MotV5.ASLocal.QP, Work.MotV5.ASLocal.PhiP,
    AsZ0, AsZ1, AsZ2, AsZ3, AsZ4, AsZ5, AsZ6, AsZ7, AsZ8, AsZ9, AsZ10, AsZ11, AsZ12, AsZ13,
    AsZ14, AsZ15, AsZ16, AsZ17, AsZ18,
    Polynomial.C_add, Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_neg,
    Polynomial.C_ofNat, Polynomial.C_eq_natCast]
  refl_ring1

theorem keyMod (K : Type) [Field K] [CharP K 5] (a b g : K) :
    (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g) ∣
      (Work.MotAS.kleinRAS0 (Polynomial.C a) (Polynomial.C b) (Polynomial.C g)
        (Work.MotV5.ASLocal.WaV a b g) - Work.MotV5.ASLocal.PhiP a b g) := by
  rw [hL K a b g, cj_0, cj_1, cj_2, cj_3, cj_4, cj_5, cj_6, cj_7, cj_8, cj_9, cj_10, cj_11,
    cj_12, cj_13, cj_14, cj_15, cj_16, cj_17, cj_18, ← hR K a b g]
  exact ⟨ Work.MotV5.ASLocal.QP a b g, by ring ⟩

end Work.MotC5N3.Work
