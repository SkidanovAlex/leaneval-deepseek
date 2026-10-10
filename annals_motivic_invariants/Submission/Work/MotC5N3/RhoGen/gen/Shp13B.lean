import Mathlib
import Submission.Work.MotC5N3.Work.RhoSV2.W
import Submission.Work.MotC5N3.RhoGen.gen.Shp13Coeffs
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

noncomputable def Shp13R {K : Type} [CommRing K] (a b g : K) : Polynomial K :=
  Polynomial.C (cshp13_18 a b g) * Polynomial.X ^ 18 + Polynomial.C (cshp13_17 a b g) * Polynomial.X ^ 17 + Polynomial.C (cshp13_16 a b g) * Polynomial.X ^ 16 + Polynomial.C (cshp13_15 a b g) * Polynomial.X ^ 15 + Polynomial.C (cshp13_14 a b g) * Polynomial.X ^ 14 + Polynomial.C (cshp13_13 a b g) * Polynomial.X ^ 13 + Polynomial.C (cshp13_12 a b g) * Polynomial.X ^ 12 + Polynomial.C (cshp13_11 a b g) * Polynomial.X ^ 11 + Polynomial.C (cshp13_10 a b g) * Polynomial.X ^ 10 + Polynomial.C (cshp13_9 a b g) * Polynomial.X ^ 9 + Polynomial.C (cshp13_8 a b g) * Polynomial.X ^ 8 + Polynomial.C (cshp13_7 a b g) * Polynomial.X ^ 7 + Polynomial.C (cshp13_6 a b g) * Polynomial.X ^ 6 + Polynomial.C (cshp13_5 a b g) * Polynomial.X ^ 5 + Polynomial.C (cshp13_4 a b g) * Polynomial.X ^ 4 + Polynomial.C (cshp13_3 a b g) * Polynomial.X ^ 3 + Polynomial.C (cshp13_2 a b g) * Polynomial.X ^ 2 + Polynomial.C (cshp13_1 a b g) * Polynomial.X ^ 1 + Polynomial.C (cshp13_0 a b g)

set_option maxHeartbeats 4000000 in
theorem shp_13_bounded {K : Type} [CommRing K] (a b g : K) :
    Wa1 a b g * (Wa2 a b g)^2 = Shp13R a b g := by
  simp only [Shp13R, Wa0, Wa1, Wa2, Wa3, Wa4, cshp13_0, cshp13_1, cshp13_2, cshp13_3, cshp13_4, cshp13_5, cshp13_6, cshp13_7, cshp13_8, cshp13_9, cshp13_10, cshp13_11, cshp13_12, cshp13_13, cshp13_14, cshp13_15, cshp13_16, cshp13_17, cshp13_18, Polynomial.C_add, Polynomial.C_sub,
    Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_eq_natCast]
  refl_ring1

end Work.MotV5.ASLocal
