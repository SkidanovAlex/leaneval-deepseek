import Mathlib
import Submission.Work.MotC5N3.Work.RhoSV2.W
import Submission.Work.MotC5N3.RhoGen.gen.Shp7Coeffs
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

noncomputable def Shp7R {K : Type} [CommRing K] (a b g : K) : Polynomial K :=
  Polynomial.C (cshp7_16 a b g) * Polynomial.X ^ 16 + Polynomial.C (cshp7_15 a b g) * Polynomial.X ^ 15 + Polynomial.C (cshp7_14 a b g) * Polynomial.X ^ 14 + Polynomial.C (cshp7_13 a b g) * Polynomial.X ^ 13 + Polynomial.C (cshp7_12 a b g) * Polynomial.X ^ 12 + Polynomial.C (cshp7_11 a b g) * Polynomial.X ^ 11 + Polynomial.C (cshp7_10 a b g) * Polynomial.X ^ 10 + Polynomial.C (cshp7_9 a b g) * Polynomial.X ^ 9 + Polynomial.C (cshp7_8 a b g) * Polynomial.X ^ 8 + Polynomial.C (cshp7_7 a b g) * Polynomial.X ^ 7 + Polynomial.C (cshp7_6 a b g) * Polynomial.X ^ 6 + Polynomial.C (cshp7_5 a b g) * Polynomial.X ^ 5 + Polynomial.C (cshp7_4 a b g) * Polynomial.X ^ 4 + Polynomial.C (cshp7_3 a b g) * Polynomial.X ^ 3 + Polynomial.C (cshp7_2 a b g) * Polynomial.X ^ 2 + Polynomial.C (cshp7_1 a b g) * Polynomial.X ^ 1 + Polynomial.C (cshp7_0 a b g)

set_option maxHeartbeats 4000000 in
theorem shp_7_bounded {K : Type} [CommRing K] (a b g : K) :
    Wa0 a b g * (Wa3 a b g)^2 = Shp7R a b g := by
  simp only [Shp7R, Wa0, Wa1, Wa2, Wa3, Wa4, cshp7_0, cshp7_1, cshp7_2, cshp7_3, cshp7_4, cshp7_5, cshp7_6, cshp7_7, cshp7_8, cshp7_9, cshp7_10, cshp7_11, cshp7_12, cshp7_13, cshp7_14, cshp7_15, cshp7_16, Polynomial.C_add, Polynomial.C_sub,
    Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_eq_natCast]
  refl_ring1

end Work.MotV5.ASLocal
