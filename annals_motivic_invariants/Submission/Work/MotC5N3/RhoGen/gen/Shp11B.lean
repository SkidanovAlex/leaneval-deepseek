import Mathlib
import Submission.Work.MotC5N3.Work.RhoSV2.W
import Submission.Work.MotC5N3.RhoGen.gen.Shp11Coeffs
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

noncomputable def Shp11R {K : Type} [CommRing K] (a b g : K) : Polynomial K :=
  Polynomial.C (cshp11_18 a b g) * Polynomial.X ^ 18 + Polynomial.C (cshp11_17 a b g) * Polynomial.X ^ 17 + Polynomial.C (cshp11_16 a b g) * Polynomial.X ^ 16 + Polynomial.C (cshp11_15 a b g) * Polynomial.X ^ 15 + Polynomial.C (cshp11_14 a b g) * Polynomial.X ^ 14 + Polynomial.C (cshp11_13 a b g) * Polynomial.X ^ 13 + Polynomial.C (cshp11_12 a b g) * Polynomial.X ^ 12 + Polynomial.C (cshp11_11 a b g) * Polynomial.X ^ 11 + Polynomial.C (cshp11_10 a b g) * Polynomial.X ^ 10 + Polynomial.C (cshp11_9 a b g) * Polynomial.X ^ 9 + Polynomial.C (cshp11_8 a b g) * Polynomial.X ^ 8 + Polynomial.C (cshp11_7 a b g) * Polynomial.X ^ 7 + Polynomial.C (cshp11_6 a b g) * Polynomial.X ^ 6 + Polynomial.C (cshp11_5 a b g) * Polynomial.X ^ 5 + Polynomial.C (cshp11_4 a b g) * Polynomial.X ^ 4 + Polynomial.C (cshp11_3 a b g) * Polynomial.X ^ 3 + Polynomial.C (cshp11_2 a b g) * Polynomial.X ^ 2 + Polynomial.C (cshp11_1 a b g) * Polynomial.X ^ 1 + Polynomial.C (cshp11_0 a b g)

set_option maxHeartbeats 4000000 in
theorem shp_11_bounded {K : Type} [CommRing K] (a b g : K) :
    (Wa0 a b g)^3 = Shp11R a b g := by
  simp only [Shp11R, Wa0, Wa1, Wa2, Wa3, Wa4, cshp11_0, cshp11_1, cshp11_2, cshp11_3, cshp11_4, cshp11_5, cshp11_6, cshp11_7, cshp11_8, cshp11_9, cshp11_10, cshp11_11, cshp11_12, cshp11_13, cshp11_14, cshp11_15, cshp11_16, cshp11_17, cshp11_18, Polynomial.C_add, Polynomial.C_sub,
    Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_neg, Polynomial.C_ofNat, Polynomial.C_eq_natCast]
  refl_ring1

end Work.MotV5.ASLocal
