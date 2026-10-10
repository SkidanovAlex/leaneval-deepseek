import Mathlib
import Submission.Work.MotC5N3.Work.RhoSV2.W
import Submission.Work.MotC5N3.RhoGen.gen.Shp24Coeffs
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

noncomputable def Shp24R {K : Type} [CommRing K] (a b g : K) : Polynomial K :=
  Polynomial.C (cshp24_18 a b g) * Polynomial.X ^ 18 + Polynomial.C (cshp24_17 a b g) * Polynomial.X ^ 17 + Polynomial.C (cshp24_16 a b g) * Polynomial.X ^ 16 + Polynomial.C (cshp24_15 a b g) * Polynomial.X ^ 15 + Polynomial.C (cshp24_14 a b g) * Polynomial.X ^ 14 + Polynomial.C (cshp24_13 a b g) * Polynomial.X ^ 13 + Polynomial.C (cshp24_12 a b g) * Polynomial.X ^ 12 + Polynomial.C (cshp24_11 a b g) * Polynomial.X ^ 11 + Polynomial.C (cshp24_10 a b g) * Polynomial.X ^ 10 + Polynomial.C (cshp24_9 a b g) * Polynomial.X ^ 9 + Polynomial.C (cshp24_8 a b g) * Polynomial.X ^ 8 + Polynomial.C (cshp24_7 a b g) * Polynomial.X ^ 7 + Polynomial.C (cshp24_6 a b g) * Polynomial.X ^ 6 + Polynomial.C (cshp24_5 a b g) * Polynomial.X ^ 5 + Polynomial.C (cshp24_4 a b g) * Polynomial.X ^ 4 + Polynomial.C (cshp24_3 a b g) * Polynomial.X ^ 3 + Polynomial.C (cshp24_2 a b g) * Polynomial.X ^ 2 + Polynomial.C (cshp24_1 a b g) * Polynomial.X ^ 1 + Polynomial.C (cshp24_0 a b g)

set_option maxHeartbeats 4000000 in
theorem shp_24_bounded {K : Type} [CommRing K] (a b g : K) :
    (Wa2 a b g)^3 = Shp24R a b g := by
  simp only [Shp24R, Wa0, Wa1, Wa2, Wa3, Wa4, cshp24_0, cshp24_1, cshp24_2, cshp24_3, cshp24_4, cshp24_5, cshp24_6, cshp24_7, cshp24_8, cshp24_9, cshp24_10, cshp24_11, cshp24_12, cshp24_13, cshp24_14, cshp24_15, cshp24_16, cshp24_17, cshp24_18, Polynomial.C_add, Polynomial.C_sub,
    Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_eq_natCast]
  refl_ring1

end Work.MotV5.ASLocal
