import Mathlib
import Submission.Work.MotC5N3.Work.RhoSV2.W
import Submission.Work.MotC5N3.RhoGen.gen.Shp20Coeffs
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

noncomputable def Shp20R {K : Type} [CommRing K] (a b g : K) : Polynomial K :=
  Polynomial.C (cshp20_16 a b g) * Polynomial.X ^ 16 + Polynomial.C (cshp20_15 a b g) * Polynomial.X ^ 15 + Polynomial.C (cshp20_14 a b g) * Polynomial.X ^ 14 + Polynomial.C (cshp20_13 a b g) * Polynomial.X ^ 13 + Polynomial.C (cshp20_12 a b g) * Polynomial.X ^ 12 + Polynomial.C (cshp20_11 a b g) * Polynomial.X ^ 11 + Polynomial.C (cshp20_10 a b g) * Polynomial.X ^ 10 + Polynomial.C (cshp20_9 a b g) * Polynomial.X ^ 9 + Polynomial.C (cshp20_8 a b g) * Polynomial.X ^ 8 + Polynomial.C (cshp20_7 a b g) * Polynomial.X ^ 7 + Polynomial.C (cshp20_6 a b g) * Polynomial.X ^ 6 + Polynomial.C (cshp20_5 a b g) * Polynomial.X ^ 5 + Polynomial.C (cshp20_4 a b g) * Polynomial.X ^ 4 + Polynomial.C (cshp20_3 a b g) * Polynomial.X ^ 3 + Polynomial.C (cshp20_2 a b g) * Polynomial.X ^ 2 + Polynomial.C (cshp20_1 a b g) * Polynomial.X ^ 1 + Polynomial.C (cshp20_0 a b g)

set_option maxHeartbeats 4000000 in
theorem shp_20_bounded {K : Type} [CommRing K] (a b g : K) :
    Wa2 a b g * (Wa3 a b g)^2 = Shp20R a b g := by
  simp only [Shp20R, Wa0, Wa1, Wa2, Wa3, Wa4, cshp20_0, cshp20_1, cshp20_2, cshp20_3, cshp20_4, cshp20_5, cshp20_6, cshp20_7, cshp20_8, cshp20_9, cshp20_10, cshp20_11, cshp20_12, cshp20_13, cshp20_14, cshp20_15, cshp20_16, Polynomial.C_add, Polynomial.C_sub,
    Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_eq_natCast]
  first | refl_ring1 | ring

end Work.MotV5.ASLocal
