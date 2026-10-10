import Mathlib
import Submission.Work.MotC5N3.Work.RhoSV2.W
import Submission.Work.MotC5N3.RhoGen.gen.Shp15Coeffs
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

noncomputable def Shp15R {K : Type} [CommRing K] (a b g : K) : Polynomial K :=
  Polynomial.C (cshp15_16 a b g) * Polynomial.X ^ 16 + Polynomial.C (cshp15_15 a b g) * Polynomial.X ^ 15 + Polynomial.C (cshp15_14 a b g) * Polynomial.X ^ 14 + Polynomial.C (cshp15_13 a b g) * Polynomial.X ^ 13 + Polynomial.C (cshp15_12 a b g) * Polynomial.X ^ 12 + Polynomial.C (cshp15_11 a b g) * Polynomial.X ^ 11 + Polynomial.C (cshp15_10 a b g) * Polynomial.X ^ 10 + Polynomial.C (cshp15_9 a b g) * Polynomial.X ^ 9 + Polynomial.C (cshp15_8 a b g) * Polynomial.X ^ 8 + Polynomial.C (cshp15_7 a b g) * Polynomial.X ^ 7 + Polynomial.C (cshp15_6 a b g) * Polynomial.X ^ 6 + Polynomial.C (cshp15_5 a b g) * Polynomial.X ^ 5 + Polynomial.C (cshp15_4 a b g) * Polynomial.X ^ 4 + Polynomial.C (cshp15_3 a b g) * Polynomial.X ^ 3 + Polynomial.C (cshp15_2 a b g) * Polynomial.X ^ 2 + Polynomial.C (cshp15_1 a b g) * Polynomial.X ^ 1 + Polynomial.C (cshp15_0 a b g)

set_option maxHeartbeats 4000000 in
theorem shp_15_bounded {K : Type} [CommRing K] (a b g : K) :
    Wa1 a b g * (Wa3 a b g)^2 = Shp15R a b g := by
  simp only [Shp15R, Wa0, Wa1, Wa2, Wa3, Wa4, cshp15_0, cshp15_1, cshp15_2, cshp15_3, cshp15_4, cshp15_5, cshp15_6, cshp15_7, cshp15_8, cshp15_9, cshp15_10, cshp15_11, cshp15_12, cshp15_13, cshp15_14, cshp15_15, cshp15_16, Polynomial.C_add, Polynomial.C_sub,
    Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_eq_natCast]
  first | refl_ring1 | ring

end Work.MotV5.ASLocal
