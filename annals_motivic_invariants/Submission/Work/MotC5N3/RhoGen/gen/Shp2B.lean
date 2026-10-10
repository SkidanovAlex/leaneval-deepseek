import Mathlib
import Submission.Work.MotC5N3.Work.RhoSV2.W
import Submission.Work.MotC5N3.RhoGen.gen.Shp2Coeffs
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

noncomputable def Shp2R {K : Type} [CommRing K] (a b g : K) : Polynomial K :=
  Polynomial.C (cshp2_18 a b g) * Polynomial.X ^ 18 + Polynomial.C (cshp2_17 a b g) * Polynomial.X ^ 17 + Polynomial.C (cshp2_16 a b g) * Polynomial.X ^ 16 + Polynomial.C (cshp2_15 a b g) * Polynomial.X ^ 15 + Polynomial.C (cshp2_14 a b g) * Polynomial.X ^ 14 + Polynomial.C (cshp2_13 a b g) * Polynomial.X ^ 13 + Polynomial.C (cshp2_12 a b g) * Polynomial.X ^ 12 + Polynomial.C (cshp2_11 a b g) * Polynomial.X ^ 11 + Polynomial.C (cshp2_10 a b g) * Polynomial.X ^ 10 + Polynomial.C (cshp2_9 a b g) * Polynomial.X ^ 9 + Polynomial.C (cshp2_8 a b g) * Polynomial.X ^ 8 + Polynomial.C (cshp2_7 a b g) * Polynomial.X ^ 7 + Polynomial.C (cshp2_6 a b g) * Polynomial.X ^ 6 + Polynomial.C (cshp2_5 a b g) * Polynomial.X ^ 5 + Polynomial.C (cshp2_4 a b g) * Polynomial.X ^ 4 + Polynomial.C (cshp2_3 a b g) * Polynomial.X ^ 3 + Polynomial.C (cshp2_2 a b g) * Polynomial.X ^ 2 + Polynomial.C (cshp2_1 a b g) * Polynomial.X ^ 1 + Polynomial.C (cshp2_0 a b g)

set_option maxHeartbeats 4000000 in
theorem shp_2_bounded {K : Type} [CommRing K] (a b g : K) :
    Wa0 a b g * (Wa1 a b g)^2 = Shp2R a b g := by
  simp only [Shp2R, Wa0, Wa1, Wa2, Wa3, Wa4, cshp2_0, cshp2_1, cshp2_2, cshp2_3, cshp2_4, cshp2_5, cshp2_6, cshp2_7, cshp2_8, cshp2_9, cshp2_10, cshp2_11, cshp2_12, cshp2_13, cshp2_14, cshp2_15, cshp2_16, cshp2_17, cshp2_18, Polynomial.C_add, Polynomial.C_sub,
    Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_eq_natCast]
  refl_ring1

end Work.MotV5.ASLocal
