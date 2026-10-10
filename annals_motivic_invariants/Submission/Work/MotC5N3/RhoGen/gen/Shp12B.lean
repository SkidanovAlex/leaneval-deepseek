import Mathlib
import Submission.Work.MotC5N3.Work.RhoSV2.W
import Submission.Work.MotC5N3.RhoGen.gen.Shp12Coeffs
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

noncomputable def Shp12R {K : Type} [CommRing K] (a b g : K) : Polynomial K :=
  Polynomial.C (cshp12_17 a b g) * Polynomial.X ^ 17 + Polynomial.C (cshp12_16 a b g) * Polynomial.X ^ 16 + Polynomial.C (cshp12_15 a b g) * Polynomial.X ^ 15 + Polynomial.C (cshp12_14 a b g) * Polynomial.X ^ 14 + Polynomial.C (cshp12_13 a b g) * Polynomial.X ^ 13 + Polynomial.C (cshp12_12 a b g) * Polynomial.X ^ 12 + Polynomial.C (cshp12_11 a b g) * Polynomial.X ^ 11 + Polynomial.C (cshp12_10 a b g) * Polynomial.X ^ 10 + Polynomial.C (cshp12_9 a b g) * Polynomial.X ^ 9 + Polynomial.C (cshp12_8 a b g) * Polynomial.X ^ 8 + Polynomial.C (cshp12_7 a b g) * Polynomial.X ^ 7 + Polynomial.C (cshp12_6 a b g) * Polynomial.X ^ 6 + Polynomial.C (cshp12_5 a b g) * Polynomial.X ^ 5 + Polynomial.C (cshp12_4 a b g) * Polynomial.X ^ 4 + Polynomial.C (cshp12_3 a b g) * Polynomial.X ^ 3 + Polynomial.C (cshp12_2 a b g) * Polynomial.X ^ 2 + Polynomial.C (cshp12_1 a b g) * Polynomial.X ^ 1 + Polynomial.C (cshp12_0 a b g)

set_option maxHeartbeats 4000000 in
theorem shp_12_bounded {K : Type} [CommRing K] (a b g : K) :
    Wa1 a b g * (Wa2 a b g * Wa3 a b g) = Shp12R a b g := by
  simp only [Shp12R, Wa0, Wa1, Wa2, Wa3, Wa4, cshp12_0, cshp12_1, cshp12_2, cshp12_3, cshp12_4, cshp12_5, cshp12_6, cshp12_7, cshp12_8, cshp12_9, cshp12_10, cshp12_11, cshp12_12, cshp12_13, cshp12_14, cshp12_15, cshp12_16, cshp12_17, Polynomial.C_add, Polynomial.C_sub,
    Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_eq_natCast]
  refl_ring1

end Work.MotV5.ASLocal
