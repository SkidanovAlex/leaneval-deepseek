import Mathlib
import Submission.Work.MotC5N3.Work.RhoSV2.W
import Submission.Work.MotC5N3.RhoGen.gen.Shp5Coeffs
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

noncomputable def Shp5R {K : Type} [CommRing K] (a b g : K) : Polynomial K :=
  Polynomial.C (cshp5_18 a b g) * Polynomial.X ^ 18 + Polynomial.C (cshp5_17 a b g) * Polynomial.X ^ 17 + Polynomial.C (cshp5_16 a b g) * Polynomial.X ^ 16 + Polynomial.C (cshp5_15 a b g) * Polynomial.X ^ 15 + Polynomial.C (cshp5_14 a b g) * Polynomial.X ^ 14 + Polynomial.C (cshp5_13 a b g) * Polynomial.X ^ 13 + Polynomial.C (cshp5_12 a b g) * Polynomial.X ^ 12 + Polynomial.C (cshp5_11 a b g) * Polynomial.X ^ 11 + Polynomial.C (cshp5_10 a b g) * Polynomial.X ^ 10 + Polynomial.C (cshp5_9 a b g) * Polynomial.X ^ 9 + Polynomial.C (cshp5_8 a b g) * Polynomial.X ^ 8 + Polynomial.C (cshp5_7 a b g) * Polynomial.X ^ 7 + Polynomial.C (cshp5_6 a b g) * Polynomial.X ^ 6 + Polynomial.C (cshp5_5 a b g) * Polynomial.X ^ 5 + Polynomial.C (cshp5_4 a b g) * Polynomial.X ^ 4 + Polynomial.C (cshp5_3 a b g) * Polynomial.X ^ 3 + Polynomial.C (cshp5_2 a b g) * Polynomial.X ^ 2 + Polynomial.C (cshp5_1 a b g) * Polynomial.X ^ 1 + Polynomial.C (cshp5_0 a b g)

set_option maxHeartbeats 4000000 in
theorem shp_5_bounded {K : Type} [CommRing K] (a b g : K) :
    Wa0 a b g * (Wa2 a b g)^2 = Shp5R a b g := by
  simp only [Shp5R, Wa0, Wa1, Wa2, Wa3, Wa4, cshp5_0, cshp5_1, cshp5_2, cshp5_3, cshp5_4, cshp5_5, cshp5_6, cshp5_7, cshp5_8, cshp5_9, cshp5_10, cshp5_11, cshp5_12, cshp5_13, cshp5_14, cshp5_15, cshp5_16, cshp5_17, cshp5_18, Polynomial.C_add, Polynomial.C_sub,
    Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_eq_natCast]
  refl_ring1

end Work.MotV5.ASLocal
