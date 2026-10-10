import Mathlib
import Submission.Work.MotC5N3.Work.RhoSV2.W
import Submission.Work.MotC5N3.RhoGen.gen.Shp27Coeffs
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Work.MotV5.ASLocal

open Polynomial

noncomputable def Shp27R {K : Type} [CommRing K] (a b g : K) : Polynomial K :=
  Polynomial.C (cshp27_15 a b g) * Polynomial.X ^ 15 + Polynomial.C (cshp27_14 a b g) * Polynomial.X ^ 14 + Polynomial.C (cshp27_13 a b g) * Polynomial.X ^ 13 + Polynomial.C (cshp27_12 a b g) * Polynomial.X ^ 12 + Polynomial.C (cshp27_11 a b g) * Polynomial.X ^ 11 + Polynomial.C (cshp27_10 a b g) * Polynomial.X ^ 10 + Polynomial.C (cshp27_9 a b g) * Polynomial.X ^ 9 + Polynomial.C (cshp27_8 a b g) * Polynomial.X ^ 8 + Polynomial.C (cshp27_7 a b g) * Polynomial.X ^ 7 + Polynomial.C (cshp27_6 a b g) * Polynomial.X ^ 6 + Polynomial.C (cshp27_5 a b g) * Polynomial.X ^ 5 + Polynomial.C (cshp27_4 a b g) * Polynomial.X ^ 4 + Polynomial.C (cshp27_3 a b g) * Polynomial.X ^ 3 + Polynomial.C (cshp27_2 a b g) * Polynomial.X ^ 2 + Polynomial.C (cshp27_1 a b g) * Polynomial.X ^ 1 + Polynomial.C (cshp27_0 a b g)

set_option maxHeartbeats 4000000 in
theorem shp_27_bounded {K : Type} [CommRing K] (a b g : K) :
    (Wa3 a b g)^3 = Shp27R a b g := by
  simp only [Shp27R, Wa0, Wa1, Wa2, Wa3, Wa4, cshp27_0, cshp27_1, cshp27_2, cshp27_3, cshp27_4, cshp27_5, cshp27_6, cshp27_7, cshp27_8, cshp27_9, cshp27_10, cshp27_11, cshp27_12, cshp27_13, cshp27_14, cshp27_15, Polynomial.C_add, Polynomial.C_sub,
    Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_eq_natCast]
  first | refl_ring1 | ring

end Work.MotV5.ASLocal
