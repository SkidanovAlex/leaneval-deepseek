import Submission.Work.MotC5N3.SatCert2.hB1hB3_c3_a
import Submission.Work.Reflect.PolyId

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false

namespace Work.MotC5N3.CertDemo

open MvPolynomial Work.MotC5N3

variable {K : Type} [Field K] [CharP K 5]

noncomputable def E3_31 (a b g : K) : K :=
  (-5) * cd3_2_3 a b g + (1) * fd30_3 a b g * kD3_1 a b g ^(3:ℕ) + (-1) * kP3_1 a b g * sd3_4 a b g + (-1) * kP3_11 a b g * sd3_1 a b g + (-1) * fd31_1 a b g * kR3_4 a b g * kD3_1 a b g ^(2:ℕ) + (-1) * fd31_2 a b g * kR3_1 a b g * kD3_1 a b g ^(2:ℕ) + (3) * fd30_2 a b g * kD3_2 a b g * kD3_1 a b g ^(2:ℕ) + (-6) * fd33_0 a b g * kR3_0 a b g * kR3_3 a b g * kR3_6 a b g + (-2) * fd31_0 a b g * kD3_0 a b g * kD3_1 a b g * kR3_6 a b g + (-2) * fd31_1 a b g * kD3_0 a b g * kD3_2 a b g * kR3_5 a b g + (-2) * fd31_1 a b g * kD3_0 a b g * kD3_3 a b g * kR3_4 a b g + (-2) * fd31_1 a b g * kD3_1 a b g * kD3_2 a b g * kR3_3 a b g + (-2) * fd31_1 a b g * kD3_1 a b g * kD3_3 a b g * kR3_1 a b g + (-2) * fd31_1 a b g * kD3_2 a b g * kD3_3 a b g * kR3_0 a b g + (-2) * fd31_2 a b g * kD3_0 a b g * kD3_1 a b g * kR3_4 a b g + (-2) * fd31_2 a b g * kD3_0 a b g * kD3_2 a b g * kR3_3 a b g + (-2) * fd31_2 a b g * kD3_0 a b g * kD3_3 a b g * kR3_1 a b g + (-2) * fd31_2 a b g * kD3_1 a b g * kD3_2 a b g * kR3_0 a b g + (2) * fd32_0 a b g * kD3_0 a b g * kR3_3 a b g * kR3_6 a b g + (2) * fd32_0 a b g * kD3_1 a b g * kR3_0 a b g * kR3_6 a b g + (6) * fd30_0 a b g * kD3_1 a b g * kD3_2 a b g * kD3_3 a b g + (6) * fd30_2 a b g * kD3_0 a b g * kD3_2 a b g * kD3_3 a b g + (6) * fd30_3 a b g * kD3_0 a b g * kD3_1 a b g * kD3_3 a b g + (6) * fd30_4 a b g * kD3_0 a b g * kD3_1 a b g * kD3_2 a b g

noncomputable def E3_32 (a b g : K) : K :=
  (-5) * cd3_2_4 a b g + (-1) * kP3_12 a b g * sd3_1 a b g + (-1) * kP3_2 a b g * sd3_4 a b g + (-1) * kP3_4 a b g * sd3_3 a b g + (-1) * kP3_8 a b g * sd3_2 a b g + (1) * fd32_0 a b g * kD3_0 a b g * kR3_5 a b g ^(2:ℕ) + (1) * fd32_0 a b g * kD3_3 a b g * kR3_3 a b g ^(2:ℕ) + (-1) * fd31_0 a b g * kR3_0 a b g * kD3_3 a b g ^(2:ℕ) + (-1) * fd31_0 a b g * kR3_5 a b g * kD3_1 a b g ^(2:ℕ) + (-1) * fd31_1 a b g * kR3_3 a b g * kD3_2 a b g ^(2:ℕ) + (-1) * fd31_2 a b g * kR3_0 a b g * kD3_2 a b g ^(2:ℕ) + (-1) * fd31_2 a b g * kR3_2 a b g * kD3_1 a b g ^(2:ℕ) + (-3) * fd33_0 a b g * kR3_0 a b g * kR3_5 a b g ^(2:ℕ) + (-3) * fd33_0 a b g * kR3_5 a b g * kR3_3 a b g ^(2:ℕ) + (3) * fd30_0 a b g * kD3_3 a b g * kD3_2 a b g ^(2:ℕ) + (3) * fd30_1 a b g * kD3_0 a b g * kD3_3 a b g ^(2:ℕ) + (3) * fd30_1 a b g * kD3_3 a b g * kD3_1 a b g ^(2:ℕ) + (3) * fd30_2 a b g * kD3_1 a b g * kD3_2 a b g ^(2:ℕ) + (3) * fd30_3 a b g * kD3_2 a b g * kD3_1 a b g ^(2:ℕ) + (3) * fd30_4 a b g * kD3_0 a b g * kD3_2 a b g ^(2:ℕ) + (-6) * fd33_0 a b g * kR3_0 a b g * kR3_4 a b g * kR3_6 a b g + (-6) * fd33_0 a b g * kR3_1 a b g * kR3_3 a b g * kR3_6 a b g + (-2) * fd31_0 a b g * kD3_0 a b g * kD3_2 a b g * kR3_6 a b g + (-2) * fd31_0 a b g * kD3_0 a b g * kD3_3 a b g * kR3_5 a b g + (-2) * fd31_0 a b g * kD3_1 a b g * kD3_3 a b g * kR3_3 a b g + (-2) * fd31_1 a b g * kD3_1 a b g * kD3_2 a b g * kR3_4 a b g + (-2) * fd31_1 a b g * kD3_1 a b g * kD3_3 a b g * kR3_2 a b g + (-2) * fd31_1 a b g * kD3_2 a b g * kD3_3 a b g * kR3_1 a b g + (-2) * fd31_2 a b g * kD3_0 a b g * kD3_2 a b g * kR3_4 a b g + (-2) * fd31_2 a b g * kD3_0 a b g * kD3_3 a b g * kR3_2 a b g + (-2) * fd31_2 a b g * kD3_1 a b g * kD3_2 a b g * kR3_1 a b g + (2) * fd32_0 a b g * kD3_0 a b g * kR3_4 a b g * kR3_6 a b g + (2) * fd32_0 a b g * kD3_1 a b g * kR3_1 a b g * kR3_6 a b g + (2) * fd32_0 a b g * kD3_1 a b g * kR3_3 a b g * kR3_5 a b g + (2) * fd32_0 a b g * kD3_2 a b g * kR3_0 a b g * kR3_6 a b g + (2) * fd32_0 a b g * kD3_3 a b g * kR3_0 a b g * kR3_5 a b g + (6) * fd30_3 a b g * kD3_0 a b g * kD3_2 a b g * kD3_3 a b g

noncomputable def E3_33 (a b g : K) : K :=
  (-5) * cd3_2_5 a b g + (1) * fd30_2 a b g * kD3_2 a b g ^(3:ℕ) + (-1) * kP3_5 a b g * sd3_3 a b g + (-1) * kP3_9 a b g * sd3_2 a b g + (-1) * fd31_0 a b g * kR3_1 a b g * kD3_3 a b g ^(2:ℕ) + (-1) * fd31_1 a b g * kR3_4 a b g * kD3_2 a b g ^(2:ℕ) + (-1) * fd31_2 a b g * kR3_1 a b g * kD3_2 a b g ^(2:ℕ) + (-3) * fd33_0 a b g * kR3_1 a b g * kR3_5 a b g ^(2:ℕ) + (3) * fd30_3 a b g * kD3_1 a b g * kD3_2 a b g ^(2:ℕ) + (-6) * fd33_0 a b g * kR3_1 a b g * kR3_4 a b g * kR3_6 a b g + (-6) * fd33_0 a b g * kR3_2 a b g * kR3_3 a b g * kR3_6 a b g + (-6) * fd33_0 a b g * kR3_3 a b g * kR3_4 a b g * kR3_5 a b g + (-2) * fd31_0 a b g * kD3_1 a b g * kD3_2 a b g * kR3_5 a b g + (-2) * fd31_0 a b g * kD3_1 a b g * kD3_3 a b g * kR3_4 a b g + (-2) * fd31_0 a b g * kD3_2 a b g * kD3_3 a b g * kR3_3 a b g + (-2) * fd31_1 a b g * kD3_2 a b g * kD3_3 a b g * kR3_2 a b g + (-2) * fd31_2 a b g * kD3_1 a b g * kD3_2 a b g * kR3_2 a b g + (2) * fd32_0 a b g * kD3_1 a b g * kR3_2 a b g * kR3_6 a b g + (2) * fd32_0 a b g * kD3_1 a b g * kR3_4 a b g * kR3_5 a b g + (2) * fd32_0 a b g * kD3_2 a b g * kR3_1 a b g * kR3_6 a b g + (2) * fd32_0 a b g * kD3_2 a b g * kR3_3 a b g * kR3_5 a b g + (2) * fd32_0 a b g * kD3_3 a b g * kR3_1 a b g * kR3_5 a b g + (2) * fd32_0 a b g * kD3_3 a b g * kR3_3 a b g * kR3_4 a b g + (6) * fd30_1 a b g * kD3_1 a b g * kD3_2 a b g * kD3_3 a b g

noncomputable def E3_34 (a b g : K) : K :=
  (-5) * cd3_2_6 a b g + (1) * fd30_3 a b g * kD3_2 a b g ^(3:ℕ) + (-1) * kP3_3 a b g * sd3_4 a b g + (-1) * kP3_6 a b g * sd3_3 a b g + (1) * fd32_0 a b g * kD3_3 a b g * kR3_4 a b g ^(2:ℕ) + (-1) * fd31_0 a b g * kR3_2 a b g * kD3_3 a b g ^(2:ℕ) + (-1) * fd31_0 a b g * kR3_5 a b g * kD3_2 a b g ^(2:ℕ) + (-1) * fd31_2 a b g * kR3_2 a b g * kD3_2 a b g ^(2:ℕ) + (-3) * fd33_0 a b g * kR3_2 a b g * kR3_5 a b g ^(2:ℕ) + (-3) * fd33_0 a b g * kR3_5 a b g * kR3_4 a b g ^(2:ℕ) + (3) * fd30_1 a b g * kD3_3 a b g * kD3_2 a b g ^(2:ℕ) + (-6) * fd33_0 a b g * kR3_2 a b g * kR3_4 a b g * kR3_6 a b g + (-2) * fd31_0 a b g * kD3_2 a b g * kD3_3 a b g * kR3_4 a b g + (2) * fd32_0 a b g * kD3_2 a b g * kR3_2 a b g * kR3_6 a b g + (2) * fd32_0 a b g * kD3_2 a b g * kR3_4 a b g * kR3_5 a b g + (2) * fd32_0 a b g * kD3_3 a b g * kR3_2 a b g * kR3_5 a b g

noncomputable def E3_35 (a b g : K) : K :=
  (-5) * cd3_2_7 a b g + (-1) * fd31_2 a b g * kR3_6 a b g * kD3_0 a b g ^(2:ℕ) + (-2) * fd31_1 a b g * kD3_0 a b g * kD3_1 a b g * kR3_6 a b g

noncomputable def E3_36 (a b g : K) : K :=
  (-5) * cd3_2_8 a b g + (1) * fd30_4 a b g * kD3_1 a b g ^(3:ℕ) + (-1) * kP3_10 a b g * sd3_2 a b g + (-1) * kP3_13 a b g * sd3_1 a b g + (-1) * kP3_14 a b g * sd3_0 a b g + (-1) * kP3_7 a b g * sd3_3 a b g + (-1) * fd31_1 a b g * kR3_0 a b g * kD3_3 a b g ^(2:ℕ) + (-1) * fd31_1 a b g * kR3_5 a b g * kD3_1 a b g ^(2:ℕ) + (-1) * fd31_2 a b g * kR3_3 a b g * kD3_1 a b g ^(2:ℕ) + (3) * fd30_0 a b g * kD3_1 a b g * kD3_3 a b g ^(2:ℕ) + (3) * fd30_2 a b g * kD3_0 a b g * kD3_3 a b g ^(2:ℕ) + (3) * fd30_2 a b g * kD3_3 a b g * kD3_1 a b g ^(2:ℕ) + (-2) * fd31_1 a b g * kD3_0 a b g * kD3_2 a b g * kR3_6 a b g + (-2) * fd31_1 a b g * kD3_0 a b g * kD3_3 a b g * kR3_5 a b g + (-2) * fd31_1 a b g * kD3_1 a b g * kD3_3 a b g * kR3_3 a b g + (-2) * fd31_2 a b g * kD3_0 a b g * kD3_1 a b g * kR3_5 a b g + (-2) * fd31_2 a b g * kD3_0 a b g * kD3_3 a b g * kR3_3 a b g + (-2) * fd31_2 a b g * kD3_1 a b g * kD3_3 a b g * kR3_0 a b g + (6) * fd30_4 a b g * kD3_0 a b g * kD3_1 a b g * kD3_3 a b g

noncomputable def E3_37 (a b g : K) : K :=
  (-5) * cd3_2_9 a b g + (-1) * kP3_11 a b g * sd3_2 a b g + (-1) * kP3_4 a b g * sd3_4 a b g + (-1) * fd31_0 a b g * kR3_6 a b g * kD3_1 a b g ^(2:ℕ) + (-1) * fd31_1 a b g * kR3_1 a b g * kD3_3 a b g ^(2:ℕ) + (-1) * fd31_2 a b g * kR3_4 a b g * kD3_1 a b g ^(2:ℕ) + (-3) * fd33_0 a b g * kR3_6 a b g * kR3_3 a b g ^(2:ℕ) + (3) * fd30_0 a b g * kD3_2 a b g * kD3_3 a b g ^(2:ℕ) + (3) * fd30_3 a b g * kD3_0 a b g * kD3_3 a b g ^(2:ℕ) + (3) * fd30_3 a b g * kD3_3 a b g * kD3_1 a b g ^(2:ℕ) + (3) * fd30_4 a b g * kD3_2 a b g * kD3_1 a b g ^(2:ℕ) + (-6) * fd33_0 a b g * kR3_0 a b g * kR3_5 a b g * kR3_6 a b g + (-2) * fd31_0 a b g * kD3_0 a b g * kD3_3 a b g * kR3_6 a b g + (-2) * fd31_1 a b g * kD3_1 a b g * kD3_2 a b g * kR3_5 a b g + (-2) * fd31_1 a b g * kD3_1 a b g * kD3_3 a b g * kR3_4 a b g + (-2) * fd31_1 a b g * kD3_2 a b g * kD3_3 a b g * kR3_3 a b g + (-2) * fd31_2 a b g * kD3_0 a b g * kD3_2 a b g * kR3_5 a b g + (-2) * fd31_2 a b g * kD3_0 a b g * kD3_3 a b g * kR3_4 a b g + (-2) * fd31_2 a b g * kD3_1 a b g * kD3_2 a b g * kR3_3 a b g + (-2) * fd31_2 a b g * kD3_1 a b g * kD3_3 a b g * kR3_1 a b g + (-2) * fd31_2 a b g * kD3_2 a b g * kD3_3 a b g * kR3_0 a b g + (2) * fd32_0 a b g * kD3_0 a b g * kR3_5 a b g * kR3_6 a b g + (2) * fd32_0 a b g * kD3_1 a b g * kR3_3 a b g * kR3_6 a b g + (2) * fd32_0 a b g * kD3_3 a b g * kR3_0 a b g * kR3_6 a b g + (6) * fd30_2 a b g * kD3_1 a b g * kD3_2 a b g * kD3_3 a b g + (6) * fd30_4 a b g * kD3_0 a b g * kD3_2 a b g * kD3_3 a b g

noncomputable def E3_38 (a b g : K) : K :=
  (-5) * cd3_2_10 a b g + (-1) * kP3_12 a b g * sd3_2 a b g + (-1) * kP3_5 a b g * sd3_4 a b g + (-1) * kP3_8 a b g * sd3_3 a b g + (1) * fd32_0 a b g * kD3_1 a b g * kR3_5 a b g ^(2:ℕ) + (-1) * fd31_0 a b g * kR3_3 a b g * kD3_3 a b g ^(2:ℕ) + (-1) * fd31_1 a b g * kR3_2 a b g * kD3_3 a b g ^(2:ℕ) + (-1) * fd31_1 a b g * kR3_5 a b g * kD3_2 a b g ^(2:ℕ) + (-1) * fd31_2 a b g * kR3_3 a b g * kD3_2 a b g ^(2:ℕ) + (-3) * fd33_0 a b g * kR3_3 a b g * kR3_5 a b g ^(2:ℕ) + (3) * fd30_1 a b g * kD3_1 a b g * kD3_3 a b g ^(2:ℕ) + (3) * fd30_2 a b g * kD3_3 a b g * kD3_2 a b g ^(2:ℕ) + (3) * fd30_4 a b g * kD3_1 a b g * kD3_2 a b g ^(2:ℕ) + (-6) * fd33_0 a b g * kR3_1 a b g * kR3_5 a b g * kR3_6 a b g + (-6) * fd33_0 a b g * kR3_3 a b g * kR3_4 a b g * kR3_6 a b g + (-2) * fd31_0 a b g * kD3_1 a b g * kD3_2 a b g * kR3_6 a b g + (-2) * fd31_0 a b g * kD3_1 a b g * kD3_3 a b g * kR3_5 a b g + (-2) * fd31_1 a b g * kD3_2 a b g * kD3_3 a b g * kR3_4 a b g + (-2) * fd31_2 a b g * kD3_1 a b g * kD3_2 a b g * kR3_4 a b g + (-2) * fd31_2 a b g * kD3_1 a b g * kD3_3 a b g * kR3_2 a b g + (-2) * fd31_2 a b g * kD3_2 a b g * kD3_3 a b g * kR3_1 a b g + (2) * fd32_0 a b g * kD3_1 a b g * kR3_4 a b g * kR3_6 a b g + (2) * fd32_0 a b g * kD3_2 a b g * kR3_3 a b g * kR3_6 a b g + (2) * fd32_0 a b g * kD3_3 a b g * kR3_1 a b g * kR3_6 a b g + (2) * fd32_0 a b g * kD3_3 a b g * kR3_3 a b g * kR3_5 a b g + (6) * fd30_3 a b g * kD3_1 a b g * kD3_2 a b g * kD3_3 a b g

noncomputable def E3_39 (a b g : K) : K :=
  (-5) * cd3_2_11 a b g + (1) * fd30_4 a b g * kD3_2 a b g ^(3:ℕ) + (-1) * kP3_6 a b g * sd3_4 a b g + (-1) * kP3_9 a b g * sd3_3 a b g + (1) * fd32_0 a b g * kD3_2 a b g * kR3_5 a b g ^(2:ℕ) + (-1) * fd31_0 a b g * kR3_4 a b g * kD3_3 a b g ^(2:ℕ) + (-1) * fd31_0 a b g * kR3_6 a b g * kD3_2 a b g ^(2:ℕ) + (-1) * fd31_2 a b g * kR3_4 a b g * kD3_2 a b g ^(2:ℕ) + (-3) * fd33_0 a b g * kR3_4 a b g * kR3_5 a b g ^(2:ℕ) + (-3) * fd33_0 a b g * kR3_6 a b g * kR3_4 a b g ^(2:ℕ) + (3) * fd30_1 a b g * kD3_2 a b g * kD3_3 a b g ^(2:ℕ) + (3) * fd30_3 a b g * kD3_3 a b g * kD3_2 a b g ^(2:ℕ) + (-6) * fd33_0 a b g * kR3_2 a b g * kR3_5 a b g * kR3_6 a b g + (-2) * fd31_0 a b g * kD3_2 a b g * kD3_3 a b g * kR3_5 a b g + (-2) * fd31_2 a b g * kD3_2 a b g * kD3_3 a b g * kR3_2 a b g + (2) * fd32_0 a b g * kD3_2 a b g * kR3_4 a b g * kR3_6 a b g + (2) * fd32_0 a b g * kD3_3 a b g * kR3_2 a b g * kR3_6 a b g + (2) * fd32_0 a b g * kD3_3 a b g * kR3_4 a b g * kR3_5 a b g

noncomputable def E3_40 (a b g : K) : K :=
  (-5) * cd3_2_12 a b g + (-1) * kP3_7 a b g * sd3_4 a b g + (-1) * fd31_1 a b g * kR3_6 a b g * kD3_1 a b g ^(2:ℕ) + (-2) * fd31_1 a b g * kD3_0 a b g * kD3_3 a b g * kR3_6 a b g + (-2) * fd31_2 a b g * kD3_0 a b g * kD3_1 a b g * kR3_6 a b g

noncomputable def E3_41 (a b g : K) : K :=
  (-5) * cd3_2_13 a b g + (1) * fd30_0 a b g * kD3_3 a b g ^(3:ℕ) + (-1) * kP3_10 a b g * sd3_3 a b g + (-1) * kP3_13 a b g * sd3_2 a b g + (-1) * kP3_14 a b g * sd3_1 a b g + (1) * fd32_0 a b g * kD3_0 a b g * kR3_6 a b g ^(2:ℕ) + (-1) * fd31_1 a b g * kR3_3 a b g * kD3_3 a b g ^(2:ℕ) + (-1) * fd31_2 a b g * kR3_0 a b g * kD3_3 a b g ^(2:ℕ) + (-1) * fd31_2 a b g * kR3_5 a b g * kD3_1 a b g ^(2:ℕ) + (-3) * fd33_0 a b g * kR3_0 a b g * kR3_6 a b g ^(2:ℕ) + (3) * fd30_2 a b g * kD3_1 a b g * kD3_3 a b g ^(2:ℕ) + (3) * fd30_4 a b g * kD3_0 a b g * kD3_3 a b g ^(2:ℕ) + (3) * fd30_4 a b g * kD3_3 a b g * kD3_1 a b g ^(2:ℕ) + (-2) * fd31_1 a b g * kD3_1 a b g * kD3_2 a b g * kR3_6 a b g + (-2) * fd31_1 a b g * kD3_1 a b g * kD3_3 a b g * kR3_5 a b g + (-2) * fd31_2 a b g * kD3_0 a b g * kD3_2 a b g * kR3_6 a b g + (-2) * fd31_2 a b g * kD3_0 a b g * kD3_3 a b g * kR3_5 a b g + (-2) * fd31_2 a b g * kD3_1 a b g * kD3_3 a b g * kR3_3 a b g

noncomputable def E3_42 (a b g : K) : K :=
  (-5) * cd3_3_0 a b g + (-1) * kP3_11 a b g * sd3_3 a b g + (-1) * kP3_8 a b g * sd3_4 a b g + (-1) * fd31_1 a b g * kR3_4 a b g * kD3_3 a b g ^(2:ℕ) + (-1) * fd31_1 a b g * kR3_6 a b g * kD3_2 a b g ^(2:ℕ) + (-1) * fd31_2 a b g * kR3_1 a b g * kD3_3 a b g ^(2:ℕ) + (-3) * fd33_0 a b g * kR3_1 a b g * kR3_6 a b g ^(2:ℕ) + (3) * fd30_2 a b g * kD3_2 a b g * kD3_3 a b g ^(2:ℕ) + (3) * fd30_3 a b g * kD3_1 a b g * kD3_3 a b g ^(2:ℕ) + (-6) * fd33_0 a b g * kR3_3 a b g * kR3_5 a b g * kR3_6 a b g + (-2) * fd31_0 a b g * kD3_1 a b g * kD3_3 a b g * kR3_6 a b g + (-2) * fd31_1 a b g * kD3_2 a b g * kD3_3 a b g * kR3_5 a b g + (-2) * fd31_2 a b g * kD3_1 a b g * kD3_2 a b g * kR3_5 a b g + (-2) * fd31_2 a b g * kD3_1 a b g * kD3_3 a b g * kR3_4 a b g + (-2) * fd31_2 a b g * kD3_2 a b g * kD3_3 a b g * kR3_3 a b g + (2) * fd32_0 a b g * kD3_1 a b g * kR3_5 a b g * kR3_6 a b g + (2) * fd32_0 a b g * kD3_3 a b g * kR3_3 a b g * kR3_6 a b g + (6) * fd30_4 a b g * kD3_1 a b g * kD3_2 a b g * kD3_3 a b g

noncomputable def E3_43 (a b g : K) : K :=
  (-5) * cd3_3_1 a b g + (1) * fd30_1 a b g * kD3_3 a b g ^(3:ℕ) + (-1) * fd33_0 a b g * kR3_5 a b g ^(3:ℕ) + (-1) * kP3_12 a b g * sd3_3 a b g + (-1) * kP3_9 a b g * sd3_4 a b g + (1) * fd32_0 a b g * kD3_3 a b g * kR3_5 a b g ^(2:ℕ) + (-1) * fd31_0 a b g * kR3_5 a b g * kD3_3 a b g ^(2:ℕ) + (-1) * fd31_2 a b g * kR3_2 a b g * kD3_3 a b g ^(2:ℕ) + (-1) * fd31_2 a b g * kR3_5 a b g * kD3_2 a b g ^(2:ℕ) + (-3) * fd33_0 a b g * kR3_2 a b g * kR3_6 a b g ^(2:ℕ) + (3) * fd30_3 a b g * kD3_2 a b g * kD3_3 a b g ^(2:ℕ) + (3) * fd30_4 a b g * kD3_3 a b g * kD3_2 a b g ^(2:ℕ) + (-6) * fd33_0 a b g * kR3_4 a b g * kR3_5 a b g * kR3_6 a b g + (-2) * fd31_0 a b g * kD3_2 a b g * kD3_3 a b g * kR3_6 a b g + (-2) * fd31_2 a b g * kD3_2 a b g * kD3_3 a b g * kR3_4 a b g + (2) * fd32_0 a b g * kD3_2 a b g * kR3_5 a b g * kR3_6 a b g + (2) * fd32_0 a b g * kD3_3 a b g * kR3_4 a b g * kR3_6 a b g

noncomputable def E3_44 (a b g : K) : K :=
  (-5) * cd3_3_2 a b g + (-1) * kP3_10 a b g * sd3_4 a b g + (-1) * fd31_2 a b g * kR3_6 a b g * kD3_1 a b g ^(2:ℕ) + (-2) * fd31_1 a b g * kD3_1 a b g * kD3_3 a b g * kR3_6 a b g + (-2) * fd31_2 a b g * kD3_0 a b g * kD3_3 a b g * kR3_6 a b g

noncomputable def E3_45 (a b g : K) : K :=
  (-5) * cd3_3_3 a b g + (1) * fd30_2 a b g * kD3_3 a b g ^(3:ℕ) + (-1) * kP3_11 a b g * sd3_4 a b g + (-1) * kP3_13 a b g * sd3_3 a b g + (-1) * kP3_14 a b g * sd3_2 a b g + (1) * fd32_0 a b g * kD3_1 a b g * kR3_6 a b g ^(2:ℕ) + (-1) * fd31_1 a b g * kR3_5 a b g * kD3_3 a b g ^(2:ℕ) + (-1) * fd31_2 a b g * kR3_3 a b g * kD3_3 a b g ^(2:ℕ) + (-3) * fd33_0 a b g * kR3_3 a b g * kR3_6 a b g ^(2:ℕ) + (3) * fd30_4 a b g * kD3_1 a b g * kD3_3 a b g ^(2:ℕ) + (-2) * fd31_1 a b g * kD3_2 a b g * kD3_3 a b g * kR3_6 a b g + (-2) * fd31_2 a b g * kD3_1 a b g * kD3_2 a b g * kR3_6 a b g + (-2) * fd31_2 a b g * kD3_1 a b g * kD3_3 a b g * kR3_5 a b g

noncomputable def E3_46 (a b g : K) : K :=
  (-5) * cd3_3_4 a b g + (1) * fd30_3 a b g * kD3_3 a b g ^(3:ℕ) + (-1) * kP3_12 a b g * sd3_4 a b g + (1) * fd32_0 a b g * kD3_2 a b g * kR3_6 a b g ^(2:ℕ) + (-1) * fd31_0 a b g * kR3_6 a b g * kD3_3 a b g ^(2:ℕ) + (-1) * fd31_2 a b g * kR3_4 a b g * kD3_3 a b g ^(2:ℕ) + (-1) * fd31_2 a b g * kR3_6 a b g * kD3_2 a b g ^(2:ℕ) + (-3) * fd33_0 a b g * kR3_4 a b g * kR3_6 a b g ^(2:ℕ) + (-3) * fd33_0 a b g * kR3_6 a b g * kR3_5 a b g ^(2:ℕ) + (3) * fd30_4 a b g * kD3_2 a b g * kD3_3 a b g ^(2:ℕ) + (-2) * fd31_2 a b g * kD3_2 a b g * kD3_3 a b g * kR3_5 a b g + (2) * fd32_0 a b g * kD3_3 a b g * kR3_5 a b g * kR3_6 a b g

noncomputable def E3_47 (a b g : K) : K :=
  (-5) * cd3_3_5 a b g + (-1) * kP3_13 a b g * sd3_4 a b g + (-1) * fd31_1 a b g * kR3_6 a b g * kD3_3 a b g ^(2:ℕ) + (-2) * fd31_2 a b g * kD3_1 a b g * kD3_3 a b g * kR3_6 a b g

noncomputable def E3_48 (a b g : K) : K :=
  (-5) * cd3_3_6 a b g + (1) * fd30_4 a b g * kD3_3 a b g ^(3:ℕ) + (-1) * kP3_14 a b g * sd3_3 a b g + (1) * fd32_0 a b g * kD3_3 a b g * kR3_6 a b g ^(2:ℕ) + (-1) * fd31_2 a b g * kR3_5 a b g * kD3_3 a b g ^(2:ℕ) + (-3) * fd33_0 a b g * kR3_5 a b g * kR3_6 a b g ^(2:ℕ) + (-2) * fd31_2 a b g * kD3_2 a b g * kD3_3 a b g * kR3_6 a b g

noncomputable def E3_49 (a b g : K) : K :=
  (-5) * cd3_3_7 a b g + (-1) * fd33_0 a b g * kR3_6 a b g ^(3:ℕ) + (-1) * kP3_14 a b g * sd3_4 a b g + (-1) * fd31_2 a b g * kR3_6 a b g * kD3_3 a b g ^(2:ℕ)

lemma hD3 (a b g : K) : X2AuxInputs.D a b g =
    C (kD3_0 a b g)
    + C (kD3_1 a b g) * X 1
    + C (kD3_2 a b g) * X 1 * X 2
    + C (kD3_3 a b g) * X 1^(2:ℕ) := by
  simp only [X2AuxInputs.D, kD3_0, kD3_1, kD3_2, kD3_3,
    map_add, map_mul, map_pow, map_neg, map_one, map_ofNat]
  refl_ring1

lemma hR3 (a b g : K) : X2AuxInputs.R a b g =
    C (kR3_0 a b g) * X 2
    + C (kR3_1 a b g) * X 2^(2:ℕ)
    + C (kR3_2 a b g) * X 2^(3:ℕ)
    + C (kR3_3 a b g) * X 1 * X 2
    + C (kR3_4 a b g) * X 1 * X 2^(2:ℕ)
    + C (kR3_5 a b g) * X 1^(2:ℕ) * X 2
    + C (kR3_6 a b g) * X 1^(3:ℕ) := by
  simp only [X2AuxInputs.R, kR3_0, kR3_1, kR3_2, kR3_3, kR3_4, kR3_5, kR3_6,
    map_add, map_mul, map_pow, map_neg, map_one, map_ofNat]
  refl_ring1

lemma hP3 (a b g : K) : X2AuxInputs.Pemb a b g =
    C (kP3_0 a b g)
    + C (kP3_1 a b g) * X 2^(2:ℕ)
    + C (kP3_2 a b g) * X 2^(3:ℕ)
    + C (kP3_3 a b g) * X 2^(5:ℕ)
    + C (kP3_4 a b g) * X 1 * X 2^(2:ℕ)
    + C (kP3_5 a b g) * X 1 * X 2^(3:ℕ)
    + C (kP3_6 a b g) * X 1 * X 2^(4:ℕ)
    + C (kP3_7 a b g) * X 1^(2:ℕ)
    + C (kP3_8 a b g) * X 1^(2:ℕ) * X 2^(2:ℕ)
    + C (kP3_9 a b g) * X 1^(2:ℕ) * X 2^(3:ℕ)
    + C (kP3_10 a b g) * X 1^(3:ℕ)
    + C (kP3_11 a b g) * X 1^(3:ℕ) * X 2
    + C (kP3_12 a b g) * X 1^(3:ℕ) * X 2^(2:ℕ)
    + C (kP3_13 a b g) * X 1^(4:ℕ)
    + C (kP3_14 a b g) * X 1^(5:ℕ) := by
  have h0 : (Fin.succ (0 : Fin 2) : Fin 3) = 1 := by decide
  have h1 : (Fin.succ (1 : Fin 2) : Fin 3) = 2 := by decide
  simp only [X2AuxInputs.Pemb, Work.MotAS.ASZElim.P, map_add, map_mul, map_pow,
    MvPolynomial.rename_C, MvPolynomial.rename_X, h0, h1, kP3_0, kP3_1, kP3_2, kP3_3, kP3_4, kP3_5, kP3_6, kP3_7, kP3_8, kP3_9, kP3_10, kP3_11, kP3_12, kP3_13, kP3_14]
  refl_ring1

lemma struct3 (a b g : K) :
    N3 a b g - X2AuxInputs.Pemb a b g * S3 a b g - 5 * C3 a b g =
    C (E3_0 a b g) * X 2
    + C (E3_1 a b g) * X 2^(3:ℕ)
    + C (E3_2 a b g) * X 2^(4:ℕ)
    + C (E3_3 a b g) * X 2^(5:ℕ)
    + C (E3_4 a b g) * X 2^(6:ℕ)
    + C (E3_5 a b g) * X 2^(7:ℕ)
    + C (E3_6 a b g) * X 2^(8:ℕ)
    + C (E3_7 a b g) * X 2^(9:ℕ)
    + C (E3_8 a b g) * X 1 * X 2
    + C (E3_9 a b g) * X 1 * X 2^(2:ℕ)
    + C (E3_10 a b g) * X 1 * X 2^(3:ℕ)
    + C (E3_11 a b g) * X 1 * X 2^(4:ℕ)
    + C (E3_12 a b g) * X 1 * X 2^(5:ℕ)
    + C (E3_13 a b g) * X 1 * X 2^(6:ℕ)
    + C (E3_14 a b g) * X 1 * X 2^(7:ℕ)
    + C (E3_15 a b g) * X 1 * X 2^(8:ℕ)
    + C (E3_16 a b g) * X 1^(2:ℕ) * X 2
    + C (E3_17 a b g) * X 1^(2:ℕ) * X 2^(2:ℕ)
    + C (E3_18 a b g) * X 1^(2:ℕ) * X 2^(3:ℕ)
    + C (E3_19 a b g) * X 1^(2:ℕ) * X 2^(4:ℕ)
    + C (E3_20 a b g) * X 1^(2:ℕ) * X 2^(5:ℕ)
    + C (E3_21 a b g) * X 1^(2:ℕ) * X 2^(6:ℕ)
    + C (E3_22 a b g) * X 1^(2:ℕ) * X 2^(7:ℕ)
    + C (E3_23 a b g) * X 1^(3:ℕ) * X 2
    + C (E3_24 a b g) * X 1^(3:ℕ) * X 2^(2:ℕ)
    + C (E3_25 a b g) * X 1^(3:ℕ) * X 2^(3:ℕ)
    + C (E3_26 a b g) * X 1^(3:ℕ) * X 2^(4:ℕ)
    + C (E3_27 a b g) * X 1^(3:ℕ) * X 2^(5:ℕ)
    + C (E3_28 a b g) * X 1^(3:ℕ) * X 2^(6:ℕ)
    + C (E3_29 a b g) * X 1^(4:ℕ)
    + C (E3_30 a b g) * X 1^(4:ℕ) * X 2
    + C (E3_31 a b g) * X 1^(4:ℕ) * X 2^(2:ℕ)
    + C (E3_32 a b g) * X 1^(4:ℕ) * X 2^(3:ℕ)
    + C (E3_33 a b g) * X 1^(4:ℕ) * X 2^(4:ℕ)
    + C (E3_34 a b g) * X 1^(4:ℕ) * X 2^(5:ℕ)
    + C (E3_35 a b g) * X 1^(5:ℕ)
    + C (E3_36 a b g) * X 1^(5:ℕ) * X 2
    + C (E3_37 a b g) * X 1^(5:ℕ) * X 2^(2:ℕ)
    + C (E3_38 a b g) * X 1^(5:ℕ) * X 2^(3:ℕ)
    + C (E3_39 a b g) * X 1^(5:ℕ) * X 2^(4:ℕ)
    + C (E3_40 a b g) * X 1^(6:ℕ)
    + C (E3_41 a b g) * X 1^(6:ℕ) * X 2
    + C (E3_42 a b g) * X 1^(6:ℕ) * X 2^(2:ℕ)
    + C (E3_43 a b g) * X 1^(6:ℕ) * X 2^(3:ℕ)
    + C (E3_44 a b g) * X 1^(7:ℕ)
    + C (E3_45 a b g) * X 1^(7:ℕ) * X 2
    + C (E3_46 a b g) * X 1^(7:ℕ) * X 2^(2:ℕ)
    + C (E3_47 a b g) * X 1^(8:ℕ)
    + C (E3_48 a b g) * X 1^(8:ℕ) * X 2
    + C (E3_49 a b g) * X 1^(9:ℕ) := by
  rw [N3, hD3, hR3, hP3]
  simp only [S3, C3, C3_0, C3_1, C3_2, C3_3, f30, f31, f32, f33,
    E3_0, E3_1, E3_2, E3_3, E3_4, E3_5, E3_6, E3_7, E3_8, E3_9, E3_10, E3_11, E3_12, E3_13, E3_14, E3_15, E3_16, E3_17, E3_18, E3_19, E3_20, E3_21, E3_22, E3_23, E3_24, E3_25, E3_26, E3_27, E3_28, E3_29, E3_30, E3_31, E3_32, E3_33, E3_34, E3_35, E3_36, E3_37, E3_38, E3_39, E3_40, E3_41, E3_42, E3_43, E3_44, E3_45, E3_46, E3_47, E3_48, E3_49,
    map_add, map_sub, map_mul, map_pow, map_neg, map_one, map_ofNat]
  refl_ring1

lemma e3_0 (a b g : K) : E3_0 a b g = 0 := by
  simp only [E3_0, cd3_0_0, fd30_0, kD3_0, kP3_0, sd3_0]
  refl_ring1

lemma e3_1 (a b g : K) : E3_1 a b g = 0 := by
  simp only [E3_1, cd3_0_1, fd30_1, fd31_0, fd32_0, fd33_0, kD3_0, kP3_1, kR3_0, sd3_0]
  refl_ring1

lemma e3_2 (a b g : K) : E3_2 a b g = 0 := by
  simp only [E3_2, cd3_0_2, fd31_0, fd32_0, fd33_0, kD3_0, kP3_2, kR3_0, kR3_1, sd3_0]
  refl_ring1

lemma e3_3 (a b g : K) : E3_3 a b g = 0 := by
  simp only [E3_3, cd3_0_3, fd31_0, fd32_0, fd33_0, kD3_0, kR3_0, kR3_1, kR3_2]
  refl_ring1

lemma e3_4 (a b g : K) : E3_4 a b g = 0 := by
  simp only [E3_4, cd3_0_4, fd32_0, fd33_0, kD3_0, kP3_3, kR3_0, kR3_1, kR3_2, sd3_0]
  refl_ring1

lemma e3_5 (a b g : K) : E3_5 a b g = 0 := by
  simp only [E3_5, cd3_0_5, fd32_0, fd33_0, kD3_0, kR3_0, kR3_1, kR3_2]
  refl_ring1

lemma e3_6 (a b g : K) : E3_6 a b g = 0 := by
  simp only [E3_6, cd3_0_6, fd33_0, kR3_1, kR3_2]
  refl_ring1

lemma e3_7 (a b g : K) : E3_7 a b g = 0 := by
  simp only [E3_7, cd3_0_7, fd33_0, kR3_2]
  refl_ring1

lemma e3_8 (a b g : K) : E3_8 a b g = 0 := by
  simp only [E3_8, cd3_0_8, fd30_0, fd30_2, fd31_1, kD3_0, kD3_1, kP3_0, kR3_0, sd3_1]
  refl_ring1

lemma e3_9 (a b g : K) : E3_9 a b g = 0 := by
  simp only [E3_9, cd3_0_9, fd30_0, fd30_3, fd31_1, kD3_0, kD3_2, kR3_1]
  refl_ring1

lemma e3_10 (a b g : K) : E3_10 a b g = 0 := by
  simp only [E3_10, cd3_0_10, fd30_1, fd31_0, fd31_1, fd32_0, fd33_0, kD3_0, kD3_1, kP3_1, kP3_4, kR3_0, kR3_2, kR3_3, sd3_0, sd3_1]
  refl_ring1

end Work.MotC5N3.CertDemo
