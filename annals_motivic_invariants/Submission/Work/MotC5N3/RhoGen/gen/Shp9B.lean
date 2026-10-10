import Mathlib
import Submission.Work.MotC5N3.Work.RhoSV2.W
import Submission.Work.MotC5N3.RhoGen.gen.Shp9Coeffs
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

noncomputable def Shp9R {K : Type} [CommRing K] (a b g : K) : Polynomial K :=
  Polynomial.C (cshp9_18 a b g) * Polynomial.X ^ 18 + Polynomial.C (cshp9_17 a b g) * Polynomial.X ^ 17 + Polynomial.C (cshp9_16 a b g) * Polynomial.X ^ 16 + Polynomial.C (cshp9_15 a b g) * Polynomial.X ^ 15 + Polynomial.C (cshp9_14 a b g) * Polynomial.X ^ 14 + Polynomial.C (cshp9_13 a b g) * Polynomial.X ^ 13 + Polynomial.C (cshp9_12 a b g) * Polynomial.X ^ 12 + Polynomial.C (cshp9_11 a b g) * Polynomial.X ^ 11 + Polynomial.C (cshp9_10 a b g) * Polynomial.X ^ 10 + Polynomial.C (cshp9_9 a b g) * Polynomial.X ^ 9 + Polynomial.C (cshp9_8 a b g) * Polynomial.X ^ 8 + Polynomial.C (cshp9_7 a b g) * Polynomial.X ^ 7 + Polynomial.C (cshp9_6 a b g) * Polynomial.X ^ 6 + Polynomial.C (cshp9_5 a b g) * Polynomial.X ^ 5 + Polynomial.C (cshp9_4 a b g) * Polynomial.X ^ 4 + Polynomial.C (cshp9_3 a b g) * Polynomial.X ^ 3 + Polynomial.C (cshp9_2 a b g) * Polynomial.X ^ 2 + Polynomial.C (cshp9_1 a b g) * Polynomial.X ^ 1 + Polynomial.C (cshp9_0 a b g)

set_option maxHeartbeats 4000000 in
theorem shp_9_bounded {K : Type} [CommRing K] (a b g : K) :
    (Wa0 a b g)^2 * Wa2 a b g = Shp9R a b g := by
  simp only [Shp9R, Wa0, Wa1, Wa2, Wa3, Wa4, cshp9_0, cshp9_1, cshp9_2, cshp9_3, cshp9_4, cshp9_5, cshp9_6, cshp9_7, cshp9_8, cshp9_9, cshp9_10, cshp9_11, cshp9_12, cshp9_13, cshp9_14, cshp9_15, cshp9_16, cshp9_17, cshp9_18, Polynomial.C_add, Polynomial.C_sub,
    Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_eq_natCast]
  refl_ring1

end Work.MotV5.ASLocal
