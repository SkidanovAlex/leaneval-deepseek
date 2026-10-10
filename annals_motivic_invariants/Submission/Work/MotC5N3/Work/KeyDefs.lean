import Mathlib
import Submission.Work.MotV5.ASLocal.asRhoPoly_witPt_data
import Submission.Work.MotC5N3.Work.RhoSV2.W
import Submission.Work.MotAS.WitPt

import Submission.Work.MotC5N3.RhoGen.gen.Shp0Coeffs
import Submission.Work.MotC5N3.RhoGen.gen.Shp11Coeffs
import Submission.Work.MotC5N3.RhoGen.gen.Shp12Coeffs
import Submission.Work.MotC5N3.RhoGen.gen.Shp13Coeffs
import Submission.Work.MotC5N3.RhoGen.gen.Shp15Coeffs
import Submission.Work.MotC5N3.RhoGen.gen.Shp17Coeffs
import Submission.Work.MotC5N3.RhoGen.gen.Shp20Coeffs
import Submission.Work.MotC5N3.RhoGen.gen.Shp22Coeffs
import Submission.Work.MotC5N3.RhoGen.gen.Shp24Coeffs
import Submission.Work.MotC5N3.RhoGen.gen.Shp27Coeffs
import Submission.Work.MotC5N3.RhoGen.gen.Shp2Coeffs
import Submission.Work.MotC5N3.RhoGen.gen.Shp3Coeffs
import Submission.Work.MotC5N3.RhoGen.gen.Shp5Coeffs
import Submission.Work.MotC5N3.RhoGen.gen.Shp7Coeffs
import Submission.Work.MotC5N3.RhoGen.gen.Shp9Coeffs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Work.MotC5N3.Work

open Polynomial


noncomputable def AsCoef0 {K : Type} [CommRing K] (a b g : K) : K :=
  b ^ 4 * g - a * b ^ 3 * g + a ^ 2 * b ^ 2 * g + a ^ 3 * b * g + a ^ 4 * g

noncomputable def AsCoef1 {K : Type} [CommRing K] (a b g : K) : K :=
  -a * b ^ 3 + a ^ 3 * b

noncomputable def AsCoef2 {K : Type} [CommRing K] (a b g : K) : K :=
  b ^ 4 * g + a * b ^ 3 * g + a ^ 3 * b * g - a ^ 4 * g

noncomputable def AsCoef3 {K : Type} [CommRing K] (a b g : K) : K :=
  2 * a * b ^ 3 + 2 * a ^ 3 * b

noncomputable def AsCoef4 {K : Type} [CommRing K] (a b g : K) : K :=
  -2 * b ^ 4 * g - 2 * a * b ^ 3 * g - 2 * a ^ 3 * b * g + 2 * a ^ 4 * g

noncomputable def AsCoef5 {K : Type} [CommRing K] (a b g : K) : K :=
  -a * b ^ 3 - a ^ 3 * b

noncomputable def AsCoef6 {K : Type} [CommRing K] (a b g : K) : K :=
  2 * b ^ 4 * g - a * b ^ 3 * g - 2 * a ^ 2 * b ^ 2 * g + a ^ 3 * b * g + 2 * a ^ 4 * g

noncomputable def AsCoef7 {K : Type} [CommRing K] (a b g : K) : K :=
  2 * b ^ 4 * g - a * b ^ 3 * g - 2 * a ^ 2 * b ^ 2 * g + a ^ 3 * b * g + 2 * a ^ 4 * g

noncomputable def AsCoef8 {K : Type} [CommRing K] (a b g : K) : K :=
  b ^ 4 - a ^ 4

noncomputable def AsCoef9 {K : Type} [CommRing K] (a b g : K) : K :=
  -b ^ 4 * g - 2 * a * b ^ 3 * g + a ^ 2 * b ^ 2 * g + 2 * a ^ 3 * b * g - a ^ 4 * g

noncomputable def AsCoef10 {K : Type} [CommRing K] (a b g : K) : K :=
  -b ^ 4 + 2 * a * b ^ 3 - 2 * a ^ 3 * b - a ^ 4

noncomputable def AsCoef11 {K : Type} [CommRing K] (a b g : K) : K :=
  2 * b ^ 4 + a * b ^ 3 - a ^ 3 * b + 2 * a ^ 4

noncomputable def AsCoef12 {K : Type} [CommRing K] (a b g : K) : K :=
  b ^ 4 + a * b ^ 3 + a ^ 3 * b - a ^ 4

noncomputable def AsCoef13 {K : Type} [CommRing K] (a b g : K) : K :=
  -2 * b ^ 4 - 2 * a * b ^ 3 - 2 * a ^ 3 * b + 2 * a ^ 4

noncomputable def AsCoef14 {K : Type} [CommRing K] (a b g : K) : K :=
  -b ^ 4 - 2 * a * b ^ 3 + a ^ 2 * b ^ 2 + 2 * a ^ 3 * b - a ^ 4

noncomputable def AsL0 {K : Type} [Field K] [CharP K 5] (a b g : K) : K :=
  AsCoef0 a b g * Work.MotV5.ASLocal.cshp27_0 a b g + AsCoef1 a b g * Work.MotV5.ASLocal.cshp20_0 a b g + AsCoef2 a b g * Work.MotV5.ASLocal.cshp22_0 a b g + AsCoef3 a b g * Work.MotV5.ASLocal.cshp24_0 a b g + AsCoef4 a b g * Work.MotV5.ASLocal.cshp15_0 a b g + AsCoef5 a b g * Work.MotV5.ASLocal.cshp12_0 a b g + AsCoef6 a b g * Work.MotV5.ASLocal.cshp13_0 a b g + AsCoef7 a b g * Work.MotV5.ASLocal.cshp17_0 a b g + AsCoef8 a b g * Work.MotV5.ASLocal.cshp7_0 a b g + AsCoef9 a b g * Work.MotV5.ASLocal.cshp3_0 a b g + AsCoef10 a b g * Work.MotV5.ASLocal.cshp5_0 a b g + AsCoef11 a b g * Work.MotV5.ASLocal.cshp0_0 a b g + AsCoef12 a b g * Work.MotV5.ASLocal.cshp2_0 a b g + AsCoef13 a b g * Work.MotV5.ASLocal.cshp9_0 a b g + AsCoef14 a b g * Work.MotV5.ASLocal.cshp11_0 a b g

noncomputable def AsL1 {K : Type} [Field K] [CharP K 5] (a b g : K) : K :=
  AsCoef0 a b g * Work.MotV5.ASLocal.cshp27_1 a b g + AsCoef1 a b g * Work.MotV5.ASLocal.cshp20_1 a b g + AsCoef2 a b g * Work.MotV5.ASLocal.cshp22_1 a b g + AsCoef3 a b g * Work.MotV5.ASLocal.cshp24_1 a b g + AsCoef4 a b g * Work.MotV5.ASLocal.cshp15_1 a b g + AsCoef5 a b g * Work.MotV5.ASLocal.cshp12_1 a b g + AsCoef6 a b g * Work.MotV5.ASLocal.cshp13_1 a b g + AsCoef7 a b g * Work.MotV5.ASLocal.cshp17_1 a b g + AsCoef8 a b g * Work.MotV5.ASLocal.cshp7_1 a b g + AsCoef9 a b g * Work.MotV5.ASLocal.cshp3_1 a b g + AsCoef10 a b g * Work.MotV5.ASLocal.cshp5_1 a b g + AsCoef11 a b g * Work.MotV5.ASLocal.cshp0_1 a b g + AsCoef12 a b g * Work.MotV5.ASLocal.cshp2_1 a b g + AsCoef13 a b g * Work.MotV5.ASLocal.cshp9_1 a b g + AsCoef14 a b g * Work.MotV5.ASLocal.cshp11_1 a b g

noncomputable def AsL2 {K : Type} [Field K] [CharP K 5] (a b g : K) : K :=
  AsCoef0 a b g * Work.MotV5.ASLocal.cshp27_2 a b g + AsCoef1 a b g * Work.MotV5.ASLocal.cshp20_2 a b g + AsCoef2 a b g * Work.MotV5.ASLocal.cshp22_2 a b g + AsCoef3 a b g * Work.MotV5.ASLocal.cshp24_2 a b g + AsCoef4 a b g * Work.MotV5.ASLocal.cshp15_2 a b g + AsCoef5 a b g * Work.MotV5.ASLocal.cshp12_2 a b g + AsCoef6 a b g * Work.MotV5.ASLocal.cshp13_2 a b g + AsCoef7 a b g * Work.MotV5.ASLocal.cshp17_2 a b g + AsCoef8 a b g * Work.MotV5.ASLocal.cshp7_2 a b g + AsCoef9 a b g * Work.MotV5.ASLocal.cshp3_2 a b g + AsCoef10 a b g * Work.MotV5.ASLocal.cshp5_2 a b g + AsCoef11 a b g * Work.MotV5.ASLocal.cshp0_2 a b g + AsCoef12 a b g * Work.MotV5.ASLocal.cshp2_2 a b g + AsCoef13 a b g * Work.MotV5.ASLocal.cshp9_2 a b g + AsCoef14 a b g * Work.MotV5.ASLocal.cshp11_2 a b g

noncomputable def AsL3 {K : Type} [Field K] [CharP K 5] (a b g : K) : K :=
  AsCoef0 a b g * Work.MotV5.ASLocal.cshp27_3 a b g + AsCoef1 a b g * Work.MotV5.ASLocal.cshp20_3 a b g + AsCoef2 a b g * Work.MotV5.ASLocal.cshp22_3 a b g + AsCoef3 a b g * Work.MotV5.ASLocal.cshp24_3 a b g + AsCoef4 a b g * Work.MotV5.ASLocal.cshp15_3 a b g + AsCoef5 a b g * Work.MotV5.ASLocal.cshp12_3 a b g + AsCoef6 a b g * Work.MotV5.ASLocal.cshp13_3 a b g + AsCoef7 a b g * Work.MotV5.ASLocal.cshp17_3 a b g + AsCoef8 a b g * Work.MotV5.ASLocal.cshp7_3 a b g + AsCoef9 a b g * Work.MotV5.ASLocal.cshp3_3 a b g + AsCoef10 a b g * Work.MotV5.ASLocal.cshp5_3 a b g + AsCoef11 a b g * Work.MotV5.ASLocal.cshp0_3 a b g + AsCoef12 a b g * Work.MotV5.ASLocal.cshp2_3 a b g + AsCoef13 a b g * Work.MotV5.ASLocal.cshp9_3 a b g + AsCoef14 a b g * Work.MotV5.ASLocal.cshp11_3 a b g

noncomputable def AsL4 {K : Type} [Field K] [CharP K 5] (a b g : K) : K :=
  AsCoef0 a b g * Work.MotV5.ASLocal.cshp27_4 a b g + AsCoef1 a b g * Work.MotV5.ASLocal.cshp20_4 a b g + AsCoef2 a b g * Work.MotV5.ASLocal.cshp22_4 a b g + AsCoef3 a b g * Work.MotV5.ASLocal.cshp24_4 a b g + AsCoef4 a b g * Work.MotV5.ASLocal.cshp15_4 a b g + AsCoef5 a b g * Work.MotV5.ASLocal.cshp12_4 a b g + AsCoef6 a b g * Work.MotV5.ASLocal.cshp13_4 a b g + AsCoef7 a b g * Work.MotV5.ASLocal.cshp17_4 a b g + AsCoef8 a b g * Work.MotV5.ASLocal.cshp7_4 a b g + AsCoef9 a b g * Work.MotV5.ASLocal.cshp3_4 a b g + AsCoef10 a b g * Work.MotV5.ASLocal.cshp5_4 a b g + AsCoef11 a b g * Work.MotV5.ASLocal.cshp0_4 a b g + AsCoef12 a b g * Work.MotV5.ASLocal.cshp2_4 a b g + AsCoef13 a b g * Work.MotV5.ASLocal.cshp9_4 a b g + AsCoef14 a b g * Work.MotV5.ASLocal.cshp11_4 a b g

noncomputable def AsL5 {K : Type} [Field K] [CharP K 5] (a b g : K) : K :=
  AsCoef0 a b g * Work.MotV5.ASLocal.cshp27_5 a b g + AsCoef1 a b g * Work.MotV5.ASLocal.cshp20_5 a b g + AsCoef2 a b g * Work.MotV5.ASLocal.cshp22_5 a b g + AsCoef3 a b g * Work.MotV5.ASLocal.cshp24_5 a b g + AsCoef4 a b g * Work.MotV5.ASLocal.cshp15_5 a b g + AsCoef5 a b g * Work.MotV5.ASLocal.cshp12_5 a b g + AsCoef6 a b g * Work.MotV5.ASLocal.cshp13_5 a b g + AsCoef7 a b g * Work.MotV5.ASLocal.cshp17_5 a b g + AsCoef8 a b g * Work.MotV5.ASLocal.cshp7_5 a b g + AsCoef9 a b g * Work.MotV5.ASLocal.cshp3_5 a b g + AsCoef10 a b g * Work.MotV5.ASLocal.cshp5_5 a b g + AsCoef11 a b g * Work.MotV5.ASLocal.cshp0_5 a b g + AsCoef12 a b g * Work.MotV5.ASLocal.cshp2_5 a b g + AsCoef13 a b g * Work.MotV5.ASLocal.cshp9_5 a b g + AsCoef14 a b g * Work.MotV5.ASLocal.cshp11_5 a b g

noncomputable def AsL6 {K : Type} [Field K] [CharP K 5] (a b g : K) : K :=
  AsCoef0 a b g * Work.MotV5.ASLocal.cshp27_6 a b g + AsCoef1 a b g * Work.MotV5.ASLocal.cshp20_6 a b g + AsCoef2 a b g * Work.MotV5.ASLocal.cshp22_6 a b g + AsCoef3 a b g * Work.MotV5.ASLocal.cshp24_6 a b g + AsCoef4 a b g * Work.MotV5.ASLocal.cshp15_6 a b g + AsCoef5 a b g * Work.MotV5.ASLocal.cshp12_6 a b g + AsCoef6 a b g * Work.MotV5.ASLocal.cshp13_6 a b g + AsCoef7 a b g * Work.MotV5.ASLocal.cshp17_6 a b g + AsCoef8 a b g * Work.MotV5.ASLocal.cshp7_6 a b g + AsCoef9 a b g * Work.MotV5.ASLocal.cshp3_6 a b g + AsCoef10 a b g * Work.MotV5.ASLocal.cshp5_6 a b g + AsCoef11 a b g * Work.MotV5.ASLocal.cshp0_6 a b g + AsCoef12 a b g * Work.MotV5.ASLocal.cshp2_6 a b g + AsCoef13 a b g * Work.MotV5.ASLocal.cshp9_6 a b g + AsCoef14 a b g * Work.MotV5.ASLocal.cshp11_6 a b g

noncomputable def AsL7 {K : Type} [Field K] [CharP K 5] (a b g : K) : K :=
  AsCoef0 a b g * Work.MotV5.ASLocal.cshp27_7 a b g + AsCoef1 a b g * Work.MotV5.ASLocal.cshp20_7 a b g + AsCoef2 a b g * Work.MotV5.ASLocal.cshp22_7 a b g + AsCoef3 a b g * Work.MotV5.ASLocal.cshp24_7 a b g + AsCoef4 a b g * Work.MotV5.ASLocal.cshp15_7 a b g + AsCoef5 a b g * Work.MotV5.ASLocal.cshp12_7 a b g + AsCoef6 a b g * Work.MotV5.ASLocal.cshp13_7 a b g + AsCoef7 a b g * Work.MotV5.ASLocal.cshp17_7 a b g + AsCoef8 a b g * Work.MotV5.ASLocal.cshp7_7 a b g + AsCoef9 a b g * Work.MotV5.ASLocal.cshp3_7 a b g + AsCoef10 a b g * Work.MotV5.ASLocal.cshp5_7 a b g + AsCoef11 a b g * Work.MotV5.ASLocal.cshp0_7 a b g + AsCoef12 a b g * Work.MotV5.ASLocal.cshp2_7 a b g + AsCoef13 a b g * Work.MotV5.ASLocal.cshp9_7 a b g + AsCoef14 a b g * Work.MotV5.ASLocal.cshp11_7 a b g

noncomputable def AsL8 {K : Type} [Field K] [CharP K 5] (a b g : K) : K :=
  AsCoef0 a b g * Work.MotV5.ASLocal.cshp27_8 a b g + AsCoef1 a b g * Work.MotV5.ASLocal.cshp20_8 a b g + AsCoef2 a b g * Work.MotV5.ASLocal.cshp22_8 a b g + AsCoef3 a b g * Work.MotV5.ASLocal.cshp24_8 a b g + AsCoef4 a b g * Work.MotV5.ASLocal.cshp15_8 a b g + AsCoef5 a b g * Work.MotV5.ASLocal.cshp12_8 a b g + AsCoef6 a b g * Work.MotV5.ASLocal.cshp13_8 a b g + AsCoef7 a b g * Work.MotV5.ASLocal.cshp17_8 a b g + AsCoef8 a b g * Work.MotV5.ASLocal.cshp7_8 a b g + AsCoef9 a b g * Work.MotV5.ASLocal.cshp3_8 a b g + AsCoef10 a b g * Work.MotV5.ASLocal.cshp5_8 a b g + AsCoef11 a b g * Work.MotV5.ASLocal.cshp0_8 a b g + AsCoef12 a b g * Work.MotV5.ASLocal.cshp2_8 a b g + AsCoef13 a b g * Work.MotV5.ASLocal.cshp9_8 a b g + AsCoef14 a b g * Work.MotV5.ASLocal.cshp11_8 a b g

noncomputable def AsL9 {K : Type} [Field K] [CharP K 5] (a b g : K) : K :=
  AsCoef0 a b g * Work.MotV5.ASLocal.cshp27_9 a b g + AsCoef1 a b g * Work.MotV5.ASLocal.cshp20_9 a b g + AsCoef2 a b g * Work.MotV5.ASLocal.cshp22_9 a b g + AsCoef3 a b g * Work.MotV5.ASLocal.cshp24_9 a b g + AsCoef4 a b g * Work.MotV5.ASLocal.cshp15_9 a b g + AsCoef5 a b g * Work.MotV5.ASLocal.cshp12_9 a b g + AsCoef6 a b g * Work.MotV5.ASLocal.cshp13_9 a b g + AsCoef7 a b g * Work.MotV5.ASLocal.cshp17_9 a b g + AsCoef8 a b g * Work.MotV5.ASLocal.cshp7_9 a b g + AsCoef9 a b g * Work.MotV5.ASLocal.cshp3_9 a b g + AsCoef10 a b g * Work.MotV5.ASLocal.cshp5_9 a b g + AsCoef11 a b g * Work.MotV5.ASLocal.cshp0_9 a b g + AsCoef12 a b g * Work.MotV5.ASLocal.cshp2_9 a b g + AsCoef13 a b g * Work.MotV5.ASLocal.cshp9_9 a b g + AsCoef14 a b g * Work.MotV5.ASLocal.cshp11_9 a b g

noncomputable def AsL10 {K : Type} [Field K] [CharP K 5] (a b g : K) : K :=
  AsCoef0 a b g * Work.MotV5.ASLocal.cshp27_10 a b g + AsCoef1 a b g * Work.MotV5.ASLocal.cshp20_10 a b g + AsCoef2 a b g * Work.MotV5.ASLocal.cshp22_10 a b g + AsCoef3 a b g * Work.MotV5.ASLocal.cshp24_10 a b g + AsCoef4 a b g * Work.MotV5.ASLocal.cshp15_10 a b g + AsCoef5 a b g * Work.MotV5.ASLocal.cshp12_10 a b g + AsCoef6 a b g * Work.MotV5.ASLocal.cshp13_10 a b g + AsCoef7 a b g * Work.MotV5.ASLocal.cshp17_10 a b g + AsCoef8 a b g * Work.MotV5.ASLocal.cshp7_10 a b g + AsCoef9 a b g * Work.MotV5.ASLocal.cshp3_10 a b g + AsCoef10 a b g * Work.MotV5.ASLocal.cshp5_10 a b g + AsCoef11 a b g * Work.MotV5.ASLocal.cshp0_10 a b g + AsCoef12 a b g * Work.MotV5.ASLocal.cshp2_10 a b g + AsCoef13 a b g * Work.MotV5.ASLocal.cshp9_10 a b g + AsCoef14 a b g * Work.MotV5.ASLocal.cshp11_10 a b g

noncomputable def AsL11 {K : Type} [Field K] [CharP K 5] (a b g : K) : K :=
  AsCoef0 a b g * Work.MotV5.ASLocal.cshp27_11 a b g + AsCoef1 a b g * Work.MotV5.ASLocal.cshp20_11 a b g + AsCoef2 a b g * Work.MotV5.ASLocal.cshp22_11 a b g + AsCoef3 a b g * Work.MotV5.ASLocal.cshp24_11 a b g + AsCoef4 a b g * Work.MotV5.ASLocal.cshp15_11 a b g + AsCoef5 a b g * Work.MotV5.ASLocal.cshp12_11 a b g + AsCoef6 a b g * Work.MotV5.ASLocal.cshp13_11 a b g + AsCoef7 a b g * Work.MotV5.ASLocal.cshp17_11 a b g + AsCoef8 a b g * Work.MotV5.ASLocal.cshp7_11 a b g + AsCoef9 a b g * Work.MotV5.ASLocal.cshp3_11 a b g + AsCoef10 a b g * Work.MotV5.ASLocal.cshp5_11 a b g + AsCoef11 a b g * Work.MotV5.ASLocal.cshp0_11 a b g + AsCoef12 a b g * Work.MotV5.ASLocal.cshp2_11 a b g + AsCoef13 a b g * Work.MotV5.ASLocal.cshp9_11 a b g + AsCoef14 a b g * Work.MotV5.ASLocal.cshp11_11 a b g

noncomputable def AsL12 {K : Type} [Field K] [CharP K 5] (a b g : K) : K :=
  AsCoef0 a b g * Work.MotV5.ASLocal.cshp27_12 a b g + AsCoef1 a b g * Work.MotV5.ASLocal.cshp20_12 a b g + AsCoef2 a b g * Work.MotV5.ASLocal.cshp22_12 a b g + AsCoef3 a b g * Work.MotV5.ASLocal.cshp24_12 a b g + AsCoef4 a b g * Work.MotV5.ASLocal.cshp15_12 a b g + AsCoef5 a b g * Work.MotV5.ASLocal.cshp12_12 a b g + AsCoef6 a b g * Work.MotV5.ASLocal.cshp13_12 a b g + AsCoef7 a b g * Work.MotV5.ASLocal.cshp17_12 a b g + AsCoef8 a b g * Work.MotV5.ASLocal.cshp7_12 a b g + AsCoef9 a b g * Work.MotV5.ASLocal.cshp3_12 a b g + AsCoef10 a b g * Work.MotV5.ASLocal.cshp5_12 a b g + AsCoef11 a b g * Work.MotV5.ASLocal.cshp0_12 a b g + AsCoef12 a b g * Work.MotV5.ASLocal.cshp2_12 a b g + AsCoef13 a b g * Work.MotV5.ASLocal.cshp9_12 a b g + AsCoef14 a b g * Work.MotV5.ASLocal.cshp11_12 a b g

noncomputable def AsL13 {K : Type} [Field K] [CharP K 5] (a b g : K) : K :=
  AsCoef0 a b g * Work.MotV5.ASLocal.cshp27_13 a b g + AsCoef1 a b g * Work.MotV5.ASLocal.cshp20_13 a b g + AsCoef2 a b g * Work.MotV5.ASLocal.cshp22_13 a b g + AsCoef3 a b g * Work.MotV5.ASLocal.cshp24_13 a b g + AsCoef4 a b g * Work.MotV5.ASLocal.cshp15_13 a b g + AsCoef5 a b g * Work.MotV5.ASLocal.cshp12_13 a b g + AsCoef6 a b g * Work.MotV5.ASLocal.cshp13_13 a b g + AsCoef7 a b g * Work.MotV5.ASLocal.cshp17_13 a b g + AsCoef8 a b g * Work.MotV5.ASLocal.cshp7_13 a b g + AsCoef9 a b g * Work.MotV5.ASLocal.cshp3_13 a b g + AsCoef10 a b g * Work.MotV5.ASLocal.cshp5_13 a b g + AsCoef11 a b g * Work.MotV5.ASLocal.cshp0_13 a b g + AsCoef12 a b g * Work.MotV5.ASLocal.cshp2_13 a b g + AsCoef13 a b g * Work.MotV5.ASLocal.cshp9_13 a b g + AsCoef14 a b g * Work.MotV5.ASLocal.cshp11_13 a b g

noncomputable def AsL14 {K : Type} [Field K] [CharP K 5] (a b g : K) : K :=
  AsCoef0 a b g * Work.MotV5.ASLocal.cshp27_14 a b g + AsCoef1 a b g * Work.MotV5.ASLocal.cshp20_14 a b g + AsCoef2 a b g * Work.MotV5.ASLocal.cshp22_14 a b g + AsCoef3 a b g * Work.MotV5.ASLocal.cshp24_14 a b g + AsCoef4 a b g * Work.MotV5.ASLocal.cshp15_14 a b g + AsCoef5 a b g * Work.MotV5.ASLocal.cshp12_14 a b g + AsCoef6 a b g * Work.MotV5.ASLocal.cshp13_14 a b g + AsCoef7 a b g * Work.MotV5.ASLocal.cshp17_14 a b g + AsCoef8 a b g * Work.MotV5.ASLocal.cshp7_14 a b g + AsCoef9 a b g * Work.MotV5.ASLocal.cshp3_14 a b g + AsCoef10 a b g * Work.MotV5.ASLocal.cshp5_14 a b g + AsCoef11 a b g * Work.MotV5.ASLocal.cshp0_14 a b g + AsCoef12 a b g * Work.MotV5.ASLocal.cshp2_14 a b g + AsCoef13 a b g * Work.MotV5.ASLocal.cshp9_14 a b g + AsCoef14 a b g * Work.MotV5.ASLocal.cshp11_14 a b g

noncomputable def AsL15 {K : Type} [Field K] [CharP K 5] (a b g : K) : K :=
  AsCoef0 a b g * Work.MotV5.ASLocal.cshp27_15 a b g + AsCoef1 a b g * Work.MotV5.ASLocal.cshp20_15 a b g + AsCoef2 a b g * Work.MotV5.ASLocal.cshp22_15 a b g + AsCoef3 a b g * Work.MotV5.ASLocal.cshp24_15 a b g + AsCoef4 a b g * Work.MotV5.ASLocal.cshp15_15 a b g + AsCoef5 a b g * Work.MotV5.ASLocal.cshp12_15 a b g + AsCoef6 a b g * Work.MotV5.ASLocal.cshp13_15 a b g + AsCoef7 a b g * Work.MotV5.ASLocal.cshp17_15 a b g + AsCoef8 a b g * Work.MotV5.ASLocal.cshp7_15 a b g + AsCoef9 a b g * Work.MotV5.ASLocal.cshp3_15 a b g + AsCoef10 a b g * Work.MotV5.ASLocal.cshp5_15 a b g + AsCoef11 a b g * Work.MotV5.ASLocal.cshp0_15 a b g + AsCoef12 a b g * Work.MotV5.ASLocal.cshp2_15 a b g + AsCoef13 a b g * Work.MotV5.ASLocal.cshp9_15 a b g + AsCoef14 a b g * Work.MotV5.ASLocal.cshp11_15 a b g

noncomputable def AsL16 {K : Type} [Field K] [CharP K 5] (a b g : K) : K :=
  AsCoef1 a b g * Work.MotV5.ASLocal.cshp20_16 a b g + AsCoef2 a b g * Work.MotV5.ASLocal.cshp22_16 a b g + AsCoef3 a b g * Work.MotV5.ASLocal.cshp24_16 a b g + AsCoef4 a b g * Work.MotV5.ASLocal.cshp15_16 a b g + AsCoef5 a b g * Work.MotV5.ASLocal.cshp12_16 a b g + AsCoef6 a b g * Work.MotV5.ASLocal.cshp13_16 a b g + AsCoef7 a b g * Work.MotV5.ASLocal.cshp17_16 a b g + AsCoef8 a b g * Work.MotV5.ASLocal.cshp7_16 a b g + AsCoef9 a b g * Work.MotV5.ASLocal.cshp3_16 a b g + AsCoef10 a b g * Work.MotV5.ASLocal.cshp5_16 a b g + AsCoef11 a b g * Work.MotV5.ASLocal.cshp0_16 a b g + AsCoef12 a b g * Work.MotV5.ASLocal.cshp2_16 a b g + AsCoef13 a b g * Work.MotV5.ASLocal.cshp9_16 a b g + AsCoef14 a b g * Work.MotV5.ASLocal.cshp11_16 a b g

noncomputable def AsL17 {K : Type} [Field K] [CharP K 5] (a b g : K) : K :=
  AsCoef2 a b g * Work.MotV5.ASLocal.cshp22_17 a b g + AsCoef3 a b g * Work.MotV5.ASLocal.cshp24_17 a b g + AsCoef5 a b g * Work.MotV5.ASLocal.cshp12_17 a b g + AsCoef6 a b g * Work.MotV5.ASLocal.cshp13_17 a b g + AsCoef7 a b g * Work.MotV5.ASLocal.cshp17_17 a b g + AsCoef9 a b g * Work.MotV5.ASLocal.cshp3_17 a b g + AsCoef10 a b g * Work.MotV5.ASLocal.cshp5_17 a b g + AsCoef11 a b g * Work.MotV5.ASLocal.cshp0_17 a b g + AsCoef12 a b g * Work.MotV5.ASLocal.cshp2_17 a b g + AsCoef13 a b g * Work.MotV5.ASLocal.cshp9_17 a b g + AsCoef14 a b g * Work.MotV5.ASLocal.cshp11_17 a b g

noncomputable def AsL18 {K : Type} [Field K] [CharP K 5] (a b g : K) : K :=
  AsCoef3 a b g * Work.MotV5.ASLocal.cshp24_18 a b g + AsCoef6 a b g * Work.MotV5.ASLocal.cshp13_18 a b g + AsCoef10 a b g * Work.MotV5.ASLocal.cshp5_18 a b g + AsCoef12 a b g * Work.MotV5.ASLocal.cshp2_18 a b g + AsCoef13 a b g * Work.MotV5.ASLocal.cshp9_18 a b g + AsCoef14 a b g * Work.MotV5.ASLocal.cshp11_18 a b g

noncomputable def AsZ0 {K : Type} [Field K] [CharP K 5] (a b g : K) : K :=
  Work.MotV5.ASLocal.asN0 a b g - g * Work.MotV5.ASLocal.asQ0 a b g

noncomputable def AsZ1 {K : Type} [Field K] [CharP K 5] (a b g : K) : K :=
  Work.MotV5.ASLocal.asN1 a b g - Work.MotV5.ASLocal.asQ0 a b g - g * Work.MotV5.ASLocal.asQ1 a b g

noncomputable def AsZ2 {K : Type} [Field K] [CharP K 5] (a b g : K) : K :=
  Work.MotV5.ASLocal.asN2 a b g - Work.MotV5.ASLocal.asQ1 a b g - g * Work.MotV5.ASLocal.asQ2 a b g

noncomputable def AsZ3 {K : Type} [Field K] [CharP K 5] (a b g : K) : K :=
  Work.MotV5.ASLocal.asN3 a b g - Work.MotV5.ASLocal.asQ2 a b g - g * Work.MotV5.ASLocal.asQ3 a b g

noncomputable def AsZ4 {K : Type} [Field K] [CharP K 5] (a b g : K) : K :=
  Work.MotV5.ASLocal.asN4 a b g - Work.MotV5.ASLocal.asQ3 a b g - g * Work.MotV5.ASLocal.asQ4 a b g

noncomputable def AsZ5 {K : Type} [Field K] [CharP K 5] (a b g : K) : K :=
  Work.MotV5.ASLocal.asQ0 a b g - Work.MotV5.ASLocal.asQ4 a b g - g * Work.MotV5.ASLocal.asQ5 a b g

noncomputable def AsZ6 {K : Type} [Field K] [CharP K 5] (a b g : K) : K :=
  Work.MotV5.ASLocal.asQ1 a b g - Work.MotV5.ASLocal.asQ5 a b g - g * Work.MotV5.ASLocal.asQ6 a b g

noncomputable def AsZ7 {K : Type} [Field K] [CharP K 5] (a b g : K) : K :=
  Work.MotV5.ASLocal.asQ2 a b g - Work.MotV5.ASLocal.asQ6 a b g - g * Work.MotV5.ASLocal.asQ7 a b g

noncomputable def AsZ8 {K : Type} [Field K] [CharP K 5] (a b g : K) : K :=
  Work.MotV5.ASLocal.asQ3 a b g - Work.MotV5.ASLocal.asQ7 a b g - g * Work.MotV5.ASLocal.asQ8 a b g

noncomputable def AsZ9 {K : Type} [Field K] [CharP K 5] (a b g : K) : K :=
  Work.MotV5.ASLocal.asQ4 a b g - Work.MotV5.ASLocal.asQ8 a b g - g * Work.MotV5.ASLocal.asQ9 a b g

noncomputable def AsZ10 {K : Type} [Field K] [CharP K 5] (a b g : K) : K :=
  Work.MotV5.ASLocal.asQ5 a b g - Work.MotV5.ASLocal.asQ9 a b g - g * Work.MotV5.ASLocal.asQ10 a b g

noncomputable def AsZ11 {K : Type} [Field K] [CharP K 5] (a b g : K) : K :=
  Work.MotV5.ASLocal.asQ6 a b g - Work.MotV5.ASLocal.asQ10 a b g - g * Work.MotV5.ASLocal.asQ11 a b g

noncomputable def AsZ12 {K : Type} [Field K] [CharP K 5] (a b g : K) : K :=
  Work.MotV5.ASLocal.asQ7 a b g - Work.MotV5.ASLocal.asQ11 a b g - g * Work.MotV5.ASLocal.asQ12 a b g

noncomputable def AsZ13 {K : Type} [Field K] [CharP K 5] (a b g : K) : K :=
  Work.MotV5.ASLocal.asQ8 a b g - Work.MotV5.ASLocal.asQ12 a b g - g * Work.MotV5.ASLocal.asQ13 a b g

noncomputable def AsZ14 {K : Type} [Field K] [CharP K 5] (a b g : K) : K :=
  Work.MotV5.ASLocal.asQ9 a b g - Work.MotV5.ASLocal.asQ13 a b g

noncomputable def AsZ15 {K : Type} [Field K] [CharP K 5] (a b g : K) : K :=
  Work.MotV5.ASLocal.asQ10 a b g

noncomputable def AsZ16 {K : Type} [Field K] [CharP K 5] (a b g : K) : K :=
  Work.MotV5.ASLocal.asQ11 a b g

noncomputable def AsZ17 {K : Type} [Field K] [CharP K 5] (a b g : K) : K :=
  Work.MotV5.ASLocal.asQ12 a b g

noncomputable def AsZ18 {K : Type} [Field K] [CharP K 5] (a b g : K) : K :=
  Work.MotV5.ASLocal.asQ13 a b g

end Work.MotC5N3.Work
