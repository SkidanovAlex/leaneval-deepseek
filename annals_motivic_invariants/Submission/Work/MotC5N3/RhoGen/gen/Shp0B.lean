import Mathlib
import Submission.Work.MotC5N3.Work.RhoSV2.W
import Submission.Work.MotC5N3.RhoGen.gen.Shp0Coeffs
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

noncomputable def Shp0R {K : Type} [CommRing K] (a b g : K) : Polynomial K :=
  Polynomial.C (cshp0_17 a b g) * Polynomial.X ^ 17 + Polynomial.C (cshp0_16 a b g) * Polynomial.X ^ 16 + Polynomial.C (cshp0_15 a b g) * Polynomial.X ^ 15 + Polynomial.C (cshp0_14 a b g) * Polynomial.X ^ 14 + Polynomial.C (cshp0_13 a b g) * Polynomial.X ^ 13 + Polynomial.C (cshp0_12 a b g) * Polynomial.X ^ 12 + Polynomial.C (cshp0_11 a b g) * Polynomial.X ^ 11 + Polynomial.C (cshp0_10 a b g) * Polynomial.X ^ 10 + Polynomial.C (cshp0_9 a b g) * Polynomial.X ^ 9 + Polynomial.C (cshp0_8 a b g) * Polynomial.X ^ 8 + Polynomial.C (cshp0_7 a b g) * Polynomial.X ^ 7 + Polynomial.C (cshp0_6 a b g) * Polynomial.X ^ 6 + Polynomial.C (cshp0_5 a b g) * Polynomial.X ^ 5 + Polynomial.C (cshp0_4 a b g) * Polynomial.X ^ 4 + Polynomial.C (cshp0_3 a b g) * Polynomial.X ^ 3 + Polynomial.C (cshp0_2 a b g) * Polynomial.X ^ 2 + Polynomial.C (cshp0_1 a b g) * Polynomial.X ^ 1 + Polynomial.C (cshp0_0 a b g)

set_option maxHeartbeats 4000000 in
theorem shp_0_bounded {K : Type} [CommRing K] (a b g : K) :
    Wa0 a b g * (Wa1 a b g * Wa3 a b g) = Shp0R a b g := by
  simp only [Shp0R, Wa0, Wa1, Wa2, Wa3, Wa4, cshp0_0, cshp0_1, cshp0_2, cshp0_3, cshp0_4, cshp0_5, cshp0_6, cshp0_7, cshp0_8, cshp0_9, cshp0_10, cshp0_11, cshp0_12, cshp0_13, cshp0_14, cshp0_15, cshp0_16, cshp0_17, Polynomial.C_add, Polynomial.C_sub,
    Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_eq_natCast]
  refl_ring1

end Work.MotV5.ASLocal
