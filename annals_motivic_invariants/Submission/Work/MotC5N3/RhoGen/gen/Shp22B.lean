import Mathlib
import Submission.Work.MotC5N3.Work.RhoSV2.W
import Submission.Work.MotC5N3.RhoGen.gen.Shp22Coeffs
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

noncomputable def Shp22R {K : Type} [CommRing K] (a b g : K) : Polynomial K :=
  Polynomial.C (cshp22_17 a b g) * Polynomial.X ^ 17 + Polynomial.C (cshp22_16 a b g) * Polynomial.X ^ 16 + Polynomial.C (cshp22_15 a b g) * Polynomial.X ^ 15 + Polynomial.C (cshp22_14 a b g) * Polynomial.X ^ 14 + Polynomial.C (cshp22_13 a b g) * Polynomial.X ^ 13 + Polynomial.C (cshp22_12 a b g) * Polynomial.X ^ 12 + Polynomial.C (cshp22_11 a b g) * Polynomial.X ^ 11 + Polynomial.C (cshp22_10 a b g) * Polynomial.X ^ 10 + Polynomial.C (cshp22_9 a b g) * Polynomial.X ^ 9 + Polynomial.C (cshp22_8 a b g) * Polynomial.X ^ 8 + Polynomial.C (cshp22_7 a b g) * Polynomial.X ^ 7 + Polynomial.C (cshp22_6 a b g) * Polynomial.X ^ 6 + Polynomial.C (cshp22_5 a b g) * Polynomial.X ^ 5 + Polynomial.C (cshp22_4 a b g) * Polynomial.X ^ 4 + Polynomial.C (cshp22_3 a b g) * Polynomial.X ^ 3 + Polynomial.C (cshp22_2 a b g) * Polynomial.X ^ 2 + Polynomial.C (cshp22_1 a b g) * Polynomial.X ^ 1 + Polynomial.C (cshp22_0 a b g)

set_option maxHeartbeats 4000000 in
theorem shp_22_bounded {K : Type} [CommRing K] (a b g : K) :
    (Wa2 a b g)^2 * Wa3 a b g = Shp22R a b g := by
  simp only [Shp22R, Wa0, Wa1, Wa2, Wa3, Wa4, cshp22_0, cshp22_1, cshp22_2, cshp22_3, cshp22_4, cshp22_5, cshp22_6, cshp22_7, cshp22_8, cshp22_9, cshp22_10, cshp22_11, cshp22_12, cshp22_13, cshp22_14, cshp22_15, cshp22_16, cshp22_17, Polynomial.C_add, Polynomial.C_sub,
    Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_eq_natCast]
  refl_ring1

end Work.MotV5.ASLocal
