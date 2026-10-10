import Submission.Work.MotC5N3.SatCert2.K3_defs

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

noncomputable def kD3_0 (a b g : K) : K :=
  ((-2)*a^(6:ℕ)) + ((1)*a^(5:ℕ)*b) + ((5)*a^(4:ℕ)*b^(2:ℕ)) + ((-5)*a^(2:ℕ)*b^(4:ℕ)) + ((1)*a*b^(5:ℕ)) + ((2)*b^(6:ℕ))

noncomputable def kD3_1 (a b g : K) : K :=
  ((-1)*a^(6:ℕ)) + ((2)*a^(5:ℕ)*b) + ((-2)*a*b^(5:ℕ)) + ((-1)*b^(6:ℕ))

noncomputable def kD3_2 (a b g : K) : K :=
  ((1)*a^(6:ℕ)*g) + ((-3)*a^(5:ℕ)*b*g) + ((5)*a^(3:ℕ)*b^(3:ℕ)*g) + ((-3)*a*b^(5:ℕ)*g) + ((-1)*b^(6:ℕ)*g)

noncomputable def kD3_3 (a b g : K) : K :=
  ((1)*a^(5:ℕ)*b) + ((3)*a^(4:ℕ)*b^(2:ℕ)) + ((-6)*a^(3:ℕ)*b^(3:ℕ)) + ((-3)*a^(2:ℕ)*b^(4:ℕ)) + ((1)*a*b^(5:ℕ))

noncomputable def kR3_0 (a b g : K) : K :=
  ((1)*a^(6:ℕ)) + ((3)*a^(5:ℕ)*b) + ((-3)*a*b^(5:ℕ)) + ((1)*b^(6:ℕ))

noncomputable def kR3_1 (a b g : K) : K :=
  ((-2)*a^(6:ℕ)*g) + ((1)*a^(5:ℕ)*b*g) + ((5)*a^(4:ℕ)*b^(2:ℕ)*g) + ((-5)*a^(2:ℕ)*b^(4:ℕ)*g) + ((1)*a*b^(5:ℕ)*g) + ((2)*b^(6:ℕ)*g)

noncomputable def kR3_2 (a b g : K) : K :=
  ((-5)*a^(3:ℕ)*b^(3:ℕ))

noncomputable def kR3_3 (a b g : K) : K :=
  ((-3)*a^(6:ℕ)) + ((5)*a^(5:ℕ)*b) + ((-2)*a^(4:ℕ)*b^(2:ℕ)) + ((-1)*a^(3:ℕ)*b^(3:ℕ)) + ((2)*a^(2:ℕ)*b^(4:ℕ)) + ((5)*a*b^(5:ℕ)) + ((3)*b^(6:ℕ))

noncomputable def kR3_4 (a b g : K) : K :=
  ((4)*a^(6:ℕ)*g) + ((-3)*a^(5:ℕ)*b*g) + ((3)*a*b^(5:ℕ)*g) + ((4)*b^(6:ℕ)*g)

noncomputable def kR3_5 (a b g : K) : K :=
  ((-3)*a^(5:ℕ)*b) + ((-2)*a^(4:ℕ)*b^(2:ℕ)) + ((-2)*a^(2:ℕ)*b^(4:ℕ)) + ((3)*a*b^(5:ℕ))

noncomputable def kR3_6 (a b g : K) : K :=
  ((1)*a^(6:ℕ)*g) + ((-3)*a^(5:ℕ)*b*g) + ((5)*a^(3:ℕ)*b^(3:ℕ)*g) + ((-3)*a*b^(5:ℕ)*g) + ((-1)*b^(6:ℕ)*g)

noncomputable def kP3_0 (a b g : K) : K :=
  (-1*a^(5:ℕ) + -2*b^(5:ℕ))

noncomputable def kP3_1 (a b g : K) : K :=
  (a^(5:ℕ) + a^(4:ℕ)*b + -2*a^(3:ℕ)*b^(2:ℕ) + -1*a^(2:ℕ)*b^(3:ℕ) + 2*a*b^(4:ℕ) + -2*b^(5:ℕ))

noncomputable def kP3_2 (a b g : K) : K :=
  (-1*a^(5:ℕ)*g + -2*b^(5:ℕ)*g)

noncomputable def kP3_3 (a b g : K) : K :=
  (2*a^(5:ℕ)*g^(3:ℕ) + -1*b^(5:ℕ)*g^(3:ℕ))

noncomputable def kP3_4 (a b g : K) : K :=
  (-1*a^(5:ℕ) + -1*a^(4:ℕ)*b + -1*a^(3:ℕ)*b^(2:ℕ) + -2*a^(2:ℕ)*b^(3:ℕ) + 2*a*b^(4:ℕ) + -2*b^(5:ℕ))

noncomputable def kP3_5 (a b g : K) : K :=
  (-2*a^(5:ℕ)*g + -2*a^(4:ℕ)*b*g + -1*a^(3:ℕ)*b^(2:ℕ)*g + 2*a^(2:ℕ)*b^(3:ℕ)*g + a*b^(4:ℕ)*g + -1*b^(5:ℕ)*g)

noncomputable def kP3_6 (a b g : K) : K :=
  (-1*a^(5:ℕ)*g^(2:ℕ) + -2*b^(5:ℕ)*g^(2:ℕ))

noncomputable def kP3_7 (a b g : K) : K :=
  (2*a^(5:ℕ) + -1*b^(5:ℕ))

noncomputable def kP3_8 (a b g : K) : K :=
  (a^(4:ℕ)*b + 2*a^(3:ℕ)*b^(2:ℕ) + a^(2:ℕ)*b^(3:ℕ) + 2*a*b^(4:ℕ))

noncomputable def kP3_9 (a b g : K) : K :=
  (a^(4:ℕ)*b*g + a^(3:ℕ)*b^(2:ℕ)*g + 2*a^(2:ℕ)*b^(3:ℕ)*g + -2*a*b^(4:ℕ)*g)

noncomputable def kP3_10 (a b g : K) : K :=
  (-1*a^(5:ℕ) + -1*a^(4:ℕ)*b + 2*a^(3:ℕ)*b^(2:ℕ) + a^(2:ℕ)*b^(3:ℕ) + -2*a*b^(4:ℕ) + 2*b^(5:ℕ))

noncomputable def kP3_11 (a b g : K) : K :=
  (-2*a^(5:ℕ)*g + b^(5:ℕ)*g)

noncomputable def kP3_12 (a b g : K) : K :=
  (a^(3:ℕ)*b^(2:ℕ) + 2*a^(2:ℕ)*b^(3:ℕ))

noncomputable def kP3_13 (a b g : K) : K :=
  (2*a^(4:ℕ)*b + 2*a^(3:ℕ)*b^(2:ℕ) + -1*a^(2:ℕ)*b^(3:ℕ) + a*b^(4:ℕ))

noncomputable def kP3_14 (a b g : K) : K :=
  (a^(5:ℕ)*g^(2:ℕ) + -1*a^(3:ℕ)*b^(2:ℕ) + 2*a^(2:ℕ)*b^(3:ℕ) + 2*b^(5:ℕ)*g^(2:ℕ))

noncomputable def E3_0 (a b g : K) : K :=
  (-5) * cd3_0_0 a b g + (1) * fd30_0 a b g * kD3_0 a b g ^(3:ℕ) + (-1) * kP3_0 a b g * sd3_0 a b g

noncomputable def E3_1 (a b g : K) : K :=
  (-5) * cd3_0_1 a b g + (1) * fd30_1 a b g * kD3_0 a b g ^(3:ℕ) + (-1) * fd33_0 a b g * kR3_0 a b g ^(3:ℕ) + (-1) * kP3_1 a b g * sd3_0 a b g + (1) * fd32_0 a b g * kD3_0 a b g * kR3_0 a b g ^(2:ℕ) + (-1) * fd31_0 a b g * kR3_0 a b g * kD3_0 a b g ^(2:ℕ)

noncomputable def E3_2 (a b g : K) : K :=
  (-5) * cd3_0_2 a b g + (-1) * kP3_2 a b g * sd3_0 a b g + (-1) * fd31_0 a b g * kR3_1 a b g * kD3_0 a b g ^(2:ℕ) + (-3) * fd33_0 a b g * kR3_1 a b g * kR3_0 a b g ^(2:ℕ) + (2) * fd32_0 a b g * kD3_0 a b g * kR3_0 a b g * kR3_1 a b g

noncomputable def E3_3 (a b g : K) : K :=
  (-5) * cd3_0_3 a b g + (1) * fd32_0 a b g * kD3_0 a b g * kR3_1 a b g ^(2:ℕ) + (-1) * fd31_0 a b g * kR3_2 a b g * kD3_0 a b g ^(2:ℕ) + (-3) * fd33_0 a b g * kR3_0 a b g * kR3_1 a b g ^(2:ℕ) + (-3) * fd33_0 a b g * kR3_2 a b g * kR3_0 a b g ^(2:ℕ) + (2) * fd32_0 a b g * kD3_0 a b g * kR3_0 a b g * kR3_2 a b g

noncomputable def E3_4 (a b g : K) : K :=
  (-5) * cd3_0_4 a b g + (-1) * fd33_0 a b g * kR3_1 a b g ^(3:ℕ) + (-1) * kP3_3 a b g * sd3_0 a b g + (-6) * fd33_0 a b g * kR3_0 a b g * kR3_1 a b g * kR3_2 a b g + (2) * fd32_0 a b g * kD3_0 a b g * kR3_1 a b g * kR3_2 a b g

noncomputable def E3_5 (a b g : K) : K :=
  (-5) * cd3_0_5 a b g + (1) * fd32_0 a b g * kD3_0 a b g * kR3_2 a b g ^(2:ℕ) + (-3) * fd33_0 a b g * kR3_0 a b g * kR3_2 a b g ^(2:ℕ) + (-3) * fd33_0 a b g * kR3_2 a b g * kR3_1 a b g ^(2:ℕ)

noncomputable def E3_6 (a b g : K) : K :=
  (-5) * cd3_0_6 a b g + (-3) * fd33_0 a b g * kR3_1 a b g * kR3_2 a b g ^(2:ℕ)

noncomputable def E3_7 (a b g : K) : K :=
  (-5) * cd3_0_7 a b g + (-1) * fd33_0 a b g * kR3_2 a b g ^(3:ℕ)

noncomputable def E3_8 (a b g : K) : K :=
  (-5) * cd3_0_8 a b g + (1) * fd30_2 a b g * kD3_0 a b g ^(3:ℕ) + (-1) * kP3_0 a b g * sd3_1 a b g + (-1) * fd31_1 a b g * kR3_0 a b g * kD3_0 a b g ^(2:ℕ) + (3) * fd30_0 a b g * kD3_1 a b g * kD3_0 a b g ^(2:ℕ)

noncomputable def E3_9 (a b g : K) : K :=
  (-5) * cd3_0_9 a b g + (1) * fd30_3 a b g * kD3_0 a b g ^(3:ℕ) + (-1) * fd31_1 a b g * kR3_1 a b g * kD3_0 a b g ^(2:ℕ) + (3) * fd30_0 a b g * kD3_2 a b g * kD3_0 a b g ^(2:ℕ)

noncomputable def E3_10 (a b g : K) : K :=
  (-5) * cd3_0_10 a b g + (-1) * kP3_1 a b g * sd3_1 a b g + (-1) * kP3_4 a b g * sd3_0 a b g + (1) * fd32_0 a b g * kD3_1 a b g * kR3_0 a b g ^(2:ℕ) + (-1) * fd31_0 a b g * kR3_3 a b g * kD3_0 a b g ^(2:ℕ) + (-1) * fd31_1 a b g * kR3_2 a b g * kD3_0 a b g ^(2:ℕ) + (-3) * fd33_0 a b g * kR3_3 a b g * kR3_0 a b g ^(2:ℕ) + (3) * fd30_1 a b g * kD3_1 a b g * kD3_0 a b g ^(2:ℕ) + (-2) * fd31_0 a b g * kD3_0 a b g * kD3_1 a b g * kR3_0 a b g + (2) * fd32_0 a b g * kD3_0 a b g * kR3_0 a b g * kR3_3 a b g

noncomputable def E3_11 (a b g : K) : K :=
  (-5) * cd3_0_11 a b g + (-1) * kP3_2 a b g * sd3_1 a b g + (-1) * kP3_5 a b g * sd3_0 a b g + (1) * fd32_0 a b g * kD3_2 a b g * kR3_0 a b g ^(2:ℕ) + (-1) * fd31_0 a b g * kR3_4 a b g * kD3_0 a b g ^(2:ℕ) + (-3) * fd33_0 a b g * kR3_4 a b g * kR3_0 a b g ^(2:ℕ) + (3) * fd30_1 a b g * kD3_2 a b g * kD3_0 a b g ^(2:ℕ) + (-6) * fd33_0 a b g * kR3_0 a b g * kR3_1 a b g * kR3_3 a b g + (-2) * fd31_0 a b g * kD3_0 a b g * kD3_1 a b g * kR3_1 a b g + (-2) * fd31_0 a b g * kD3_0 a b g * kD3_2 a b g * kR3_0 a b g + (2) * fd32_0 a b g * kD3_0 a b g * kR3_0 a b g * kR3_4 a b g + (2) * fd32_0 a b g * kD3_0 a b g * kR3_1 a b g * kR3_3 a b g + (2) * fd32_0 a b g * kD3_1 a b g * kR3_0 a b g * kR3_1 a b g

noncomputable def E3_12 (a b g : K) : K :=
  (-5) * cd3_0_12 a b g + (-1) * kP3_6 a b g * sd3_0 a b g + (1) * fd32_0 a b g * kD3_1 a b g * kR3_1 a b g ^(2:ℕ) + (-3) * fd33_0 a b g * kR3_3 a b g * kR3_1 a b g ^(2:ℕ) + (-6) * fd33_0 a b g * kR3_0 a b g * kR3_1 a b g * kR3_4 a b g + (-6) * fd33_0 a b g * kR3_0 a b g * kR3_2 a b g * kR3_3 a b g + (-2) * fd31_0 a b g * kD3_0 a b g * kD3_1 a b g * kR3_2 a b g + (-2) * fd31_0 a b g * kD3_0 a b g * kD3_2 a b g * kR3_1 a b g + (2) * fd32_0 a b g * kD3_0 a b g * kR3_1 a b g * kR3_4 a b g + (2) * fd32_0 a b g * kD3_0 a b g * kR3_2 a b g * kR3_3 a b g + (2) * fd32_0 a b g * kD3_1 a b g * kR3_0 a b g * kR3_2 a b g + (2) * fd32_0 a b g * kD3_2 a b g * kR3_0 a b g * kR3_1 a b g

noncomputable def E3_13 (a b g : K) : K :=
  (-5) * cd3_0_13 a b g + (-1) * kP3_3 a b g * sd3_1 a b g + (1) * fd32_0 a b g * kD3_2 a b g * kR3_1 a b g ^(2:ℕ) + (-3) * fd33_0 a b g * kR3_4 a b g * kR3_1 a b g ^(2:ℕ) + (-6) * fd33_0 a b g * kR3_0 a b g * kR3_2 a b g * kR3_4 a b g + (-6) * fd33_0 a b g * kR3_1 a b g * kR3_2 a b g * kR3_3 a b g + (-2) * fd31_0 a b g * kD3_0 a b g * kD3_2 a b g * kR3_2 a b g + (2) * fd32_0 a b g * kD3_0 a b g * kR3_2 a b g * kR3_4 a b g + (2) * fd32_0 a b g * kD3_1 a b g * kR3_1 a b g * kR3_2 a b g + (2) * fd32_0 a b g * kD3_2 a b g * kR3_0 a b g * kR3_2 a b g

noncomputable def E3_14 (a b g : K) : K :=
  (-5) * cd3_1_0 a b g + (1) * fd32_0 a b g * kD3_1 a b g * kR3_2 a b g ^(2:ℕ) + (-3) * fd33_0 a b g * kR3_3 a b g * kR3_2 a b g ^(2:ℕ) + (-6) * fd33_0 a b g * kR3_1 a b g * kR3_2 a b g * kR3_4 a b g + (2) * fd32_0 a b g * kD3_2 a b g * kR3_1 a b g * kR3_2 a b g

noncomputable def E3_15 (a b g : K) : K :=
  (-5) * cd3_1_1 a b g + (1) * fd32_0 a b g * kD3_2 a b g * kR3_2 a b g ^(2:ℕ) + (-3) * fd33_0 a b g * kR3_4 a b g * kR3_2 a b g ^(2:ℕ)

noncomputable def E3_16 (a b g : K) : K :=
  (-5) * cd3_1_2 a b g + (1) * fd30_4 a b g * kD3_0 a b g ^(3:ℕ) + (-1) * kP3_0 a b g * sd3_2 a b g + (-1) * kP3_7 a b g * sd3_0 a b g + (-1) * fd31_1 a b g * kR3_3 a b g * kD3_0 a b g ^(2:ℕ) + (-1) * fd31_2 a b g * kR3_0 a b g * kD3_0 a b g ^(2:ℕ) + (3) * fd30_0 a b g * kD3_0 a b g * kD3_1 a b g ^(2:ℕ) + (3) * fd30_0 a b g * kD3_3 a b g * kD3_0 a b g ^(2:ℕ) + (3) * fd30_2 a b g * kD3_1 a b g * kD3_0 a b g ^(2:ℕ) + (-2) * fd31_1 a b g * kD3_0 a b g * kD3_1 a b g * kR3_0 a b g

noncomputable def E3_17 (a b g : K) : K :=
  (-5) * cd3_1_3 a b g + (-1) * fd31_1 a b g * kR3_4 a b g * kD3_0 a b g ^(2:ℕ) + (-1) * fd31_2 a b g * kR3_1 a b g * kD3_0 a b g ^(2:ℕ) + (3) * fd30_2 a b g * kD3_2 a b g * kD3_0 a b g ^(2:ℕ) + (3) * fd30_3 a b g * kD3_1 a b g * kD3_0 a b g ^(2:ℕ) + (-2) * fd31_1 a b g * kD3_0 a b g * kD3_1 a b g * kR3_1 a b g + (-2) * fd31_1 a b g * kD3_0 a b g * kD3_2 a b g * kR3_0 a b g + (6) * fd30_0 a b g * kD3_0 a b g * kD3_1 a b g * kD3_2 a b g

noncomputable def E3_18 (a b g : K) : K :=
  (-5) * cd3_1_4 a b g + (-1) * kP3_1 a b g * sd3_2 a b g + (-1) * kP3_4 a b g * sd3_1 a b g + (-1) * kP3_8 a b g * sd3_0 a b g + (1) * fd32_0 a b g * kD3_0 a b g * kR3_3 a b g ^(2:ℕ) + (1) * fd32_0 a b g * kD3_3 a b g * kR3_0 a b g ^(2:ℕ) + (-1) * fd31_0 a b g * kR3_0 a b g * kD3_1 a b g ^(2:ℕ) + (-1) * fd31_0 a b g * kR3_5 a b g * kD3_0 a b g ^(2:ℕ) + (-1) * fd31_2 a b g * kR3_2 a b g * kD3_0 a b g ^(2:ℕ) + (-3) * fd33_0 a b g * kR3_0 a b g * kR3_3 a b g ^(2:ℕ) + (-3) * fd33_0 a b g * kR3_5 a b g * kR3_0 a b g ^(2:ℕ) + (3) * fd30_0 a b g * kD3_0 a b g * kD3_2 a b g ^(2:ℕ) + (3) * fd30_1 a b g * kD3_0 a b g * kD3_1 a b g ^(2:ℕ) + (3) * fd30_1 a b g * kD3_3 a b g * kD3_0 a b g ^(2:ℕ) + (3) * fd30_3 a b g * kD3_2 a b g * kD3_0 a b g ^(2:ℕ) + (-2) * fd31_0 a b g * kD3_0 a b g * kD3_1 a b g * kR3_3 a b g + (-2) * fd31_0 a b g * kD3_0 a b g * kD3_3 a b g * kR3_0 a b g + (-2) * fd31_1 a b g * kD3_0 a b g * kD3_1 a b g * kR3_2 a b g + (-2) * fd31_1 a b g * kD3_0 a b g * kD3_2 a b g * kR3_1 a b g + (2) * fd32_0 a b g * kD3_0 a b g * kR3_0 a b g * kR3_5 a b g + (2) * fd32_0 a b g * kD3_1 a b g * kR3_0 a b g * kR3_3 a b g

noncomputable def E3_19 (a b g : K) : K :=
  (-5) * cd3_1_5 a b g + (-1) * kP3_2 a b g * sd3_2 a b g + (-1) * kP3_5 a b g * sd3_1 a b g + (-1) * kP3_9 a b g * sd3_0 a b g + (-1) * fd31_0 a b g * kR3_1 a b g * kD3_1 a b g ^(2:ℕ) + (-3) * fd33_0 a b g * kR3_1 a b g * kR3_3 a b g ^(2:ℕ) + (-6) * fd33_0 a b g * kR3_0 a b g * kR3_1 a b g * kR3_5 a b g + (-6) * fd33_0 a b g * kR3_0 a b g * kR3_3 a b g * kR3_4 a b g + (-2) * fd31_0 a b g * kD3_0 a b g * kD3_1 a b g * kR3_4 a b g + (-2) * fd31_0 a b g * kD3_0 a b g * kD3_2 a b g * kR3_3 a b g + (-2) * fd31_0 a b g * kD3_0 a b g * kD3_3 a b g * kR3_1 a b g + (-2) * fd31_0 a b g * kD3_1 a b g * kD3_2 a b g * kR3_0 a b g + (-2) * fd31_1 a b g * kD3_0 a b g * kD3_2 a b g * kR3_2 a b g + (2) * fd32_0 a b g * kD3_0 a b g * kR3_1 a b g * kR3_5 a b g + (2) * fd32_0 a b g * kD3_0 a b g * kR3_3 a b g * kR3_4 a b g + (2) * fd32_0 a b g * kD3_1 a b g * kR3_0 a b g * kR3_4 a b g + (2) * fd32_0 a b g * kD3_1 a b g * kR3_1 a b g * kR3_3 a b g + (2) * fd32_0 a b g * kD3_2 a b g * kR3_0 a b g * kR3_3 a b g + (2) * fd32_0 a b g * kD3_3 a b g * kR3_0 a b g * kR3_1 a b g + (6) * fd30_1 a b g * kD3_0 a b g * kD3_1 a b g * kD3_2 a b g

noncomputable def E3_20 (a b g : K) : K :=
  (-5) * cd3_1_6 a b g + (-1) * kP3_6 a b g * sd3_1 a b g + (1) * fd32_0 a b g * kD3_0 a b g * kR3_4 a b g ^(2:ℕ) + (1) * fd32_0 a b g * kD3_3 a b g * kR3_1 a b g ^(2:ℕ) + (-1) * fd31_0 a b g * kR3_0 a b g * kD3_2 a b g ^(2:ℕ) + (-1) * fd31_0 a b g * kR3_2 a b g * kD3_1 a b g ^(2:ℕ) + (-3) * fd33_0 a b g * kR3_0 a b g * kR3_4 a b g ^(2:ℕ) + (-3) * fd33_0 a b g * kR3_2 a b g * kR3_3 a b g ^(2:ℕ) + (-3) * fd33_0 a b g * kR3_5 a b g * kR3_1 a b g ^(2:ℕ) + (3) * fd30_1 a b g * kD3_0 a b g * kD3_2 a b g ^(2:ℕ) + (-6) * fd33_0 a b g * kR3_0 a b g * kR3_2 a b g * kR3_5 a b g + (-6) * fd33_0 a b g * kR3_1 a b g * kR3_3 a b g * kR3_4 a b g + (-2) * fd31_0 a b g * kD3_0 a b g * kD3_2 a b g * kR3_4 a b g + (-2) * fd31_0 a b g * kD3_0 a b g * kD3_3 a b g * kR3_2 a b g + (-2) * fd31_0 a b g * kD3_1 a b g * kD3_2 a b g * kR3_1 a b g + (2) * fd32_0 a b g * kD3_0 a b g * kR3_2 a b g * kR3_5 a b g + (2) * fd32_0 a b g * kD3_1 a b g * kR3_1 a b g * kR3_4 a b g + (2) * fd32_0 a b g * kD3_1 a b g * kR3_2 a b g * kR3_3 a b g + (2) * fd32_0 a b g * kD3_2 a b g * kR3_0 a b g * kR3_4 a b g + (2) * fd32_0 a b g * kD3_2 a b g * kR3_1 a b g * kR3_3 a b g + (2) * fd32_0 a b g * kD3_3 a b g * kR3_0 a b g * kR3_2 a b g

noncomputable def E3_21 (a b g : K) : K :=
  (-5) * cd3_1_7 a b g + (-1) * kP3_3 a b g * sd3_2 a b g + (-1) * fd31_0 a b g * kR3_1 a b g * kD3_2 a b g ^(2:ℕ) + (-3) * fd33_0 a b g * kR3_1 a b g * kR3_4 a b g ^(2:ℕ) + (-6) * fd33_0 a b g * kR3_1 a b g * kR3_2 a b g * kR3_5 a b g + (-6) * fd33_0 a b g * kR3_2 a b g * kR3_3 a b g * kR3_4 a b g + (-2) * fd31_0 a b g * kD3_1 a b g * kD3_2 a b g * kR3_2 a b g + (2) * fd32_0 a b g * kD3_1 a b g * kR3_2 a b g * kR3_4 a b g + (2) * fd32_0 a b g * kD3_2 a b g * kR3_1 a b g * kR3_4 a b g + (2) * fd32_0 a b g * kD3_2 a b g * kR3_2 a b g * kR3_3 a b g + (2) * fd32_0 a b g * kD3_3 a b g * kR3_1 a b g * kR3_2 a b g

noncomputable def E3_22 (a b g : K) : K :=
  (-5) * cd3_1_8 a b g + (1) * fd32_0 a b g * kD3_3 a b g * kR3_2 a b g ^(2:ℕ) + (-1) * fd31_0 a b g * kR3_2 a b g * kD3_2 a b g ^(2:ℕ) + (-3) * fd33_0 a b g * kR3_2 a b g * kR3_4 a b g ^(2:ℕ) + (-3) * fd33_0 a b g * kR3_5 a b g * kR3_2 a b g ^(2:ℕ) + (2) * fd32_0 a b g * kD3_2 a b g * kR3_2 a b g * kR3_4 a b g

noncomputable def E3_23 (a b g : K) : K :=
  (-5) * cd3_1_9 a b g + (1) * fd30_0 a b g * kD3_1 a b g ^(3:ℕ) + (-1) * kP3_0 a b g * sd3_3 a b g + (-1) * kP3_10 a b g * sd3_0 a b g + (-1) * kP3_7 a b g * sd3_1 a b g + (-1) * fd31_1 a b g * kR3_0 a b g * kD3_1 a b g ^(2:ℕ) + (-1) * fd31_1 a b g * kR3_5 a b g * kD3_0 a b g ^(2:ℕ) + (-1) * fd31_2 a b g * kR3_3 a b g * kD3_0 a b g ^(2:ℕ) + (3) * fd30_2 a b g * kD3_0 a b g * kD3_1 a b g ^(2:ℕ) + (3) * fd30_2 a b g * kD3_3 a b g * kD3_0 a b g ^(2:ℕ) + (3) * fd30_4 a b g * kD3_1 a b g * kD3_0 a b g ^(2:ℕ) + (-2) * fd31_1 a b g * kD3_0 a b g * kD3_1 a b g * kR3_3 a b g + (-2) * fd31_1 a b g * kD3_0 a b g * kD3_3 a b g * kR3_0 a b g + (-2) * fd31_2 a b g * kD3_0 a b g * kD3_1 a b g * kR3_0 a b g + (6) * fd30_0 a b g * kD3_0 a b g * kD3_1 a b g * kD3_3 a b g

noncomputable def E3_24 (a b g : K) : K :=
  (-5) * cd3_1_10 a b g + (-1) * kP3_11 a b g * sd3_0 a b g + (-1) * fd31_0 a b g * kR3_6 a b g * kD3_0 a b g ^(2:ℕ) + (-1) * fd31_1 a b g * kR3_1 a b g * kD3_1 a b g ^(2:ℕ) + (-1) * fd31_2 a b g * kR3_4 a b g * kD3_0 a b g ^(2:ℕ) + (-3) * fd33_0 a b g * kR3_6 a b g * kR3_0 a b g ^(2:ℕ) + (3) * fd30_0 a b g * kD3_2 a b g * kD3_1 a b g ^(2:ℕ) + (3) * fd30_3 a b g * kD3_0 a b g * kD3_1 a b g ^(2:ℕ) + (3) * fd30_3 a b g * kD3_3 a b g * kD3_0 a b g ^(2:ℕ) + (3) * fd30_4 a b g * kD3_2 a b g * kD3_0 a b g ^(2:ℕ) + (-2) * fd31_1 a b g * kD3_0 a b g * kD3_1 a b g * kR3_4 a b g + (-2) * fd31_1 a b g * kD3_0 a b g * kD3_2 a b g * kR3_3 a b g + (-2) * fd31_1 a b g * kD3_0 a b g * kD3_3 a b g * kR3_1 a b g + (-2) * fd31_1 a b g * kD3_1 a b g * kD3_2 a b g * kR3_0 a b g + (-2) * fd31_2 a b g * kD3_0 a b g * kD3_1 a b g * kR3_1 a b g + (-2) * fd31_2 a b g * kD3_0 a b g * kD3_2 a b g * kR3_0 a b g + (2) * fd32_0 a b g * kD3_0 a b g * kR3_0 a b g * kR3_6 a b g + (6) * fd30_0 a b g * kD3_0 a b g * kD3_2 a b g * kD3_3 a b g + (6) * fd30_2 a b g * kD3_0 a b g * kD3_1 a b g * kD3_2 a b g

noncomputable def E3_25 (a b g : K) : K :=
  (-5) * cd3_1_11 a b g + (1) * fd30_1 a b g * kD3_1 a b g ^(3:ℕ) + (-1) * fd33_0 a b g * kR3_3 a b g ^(3:ℕ) + (-1) * kP3_1 a b g * sd3_3 a b g + (-1) * kP3_12 a b g * sd3_0 a b g + (-1) * kP3_4 a b g * sd3_2 a b g + (-1) * kP3_8 a b g * sd3_1 a b g + (1) * fd32_0 a b g * kD3_1 a b g * kR3_3 a b g ^(2:ℕ) + (-1) * fd31_0 a b g * kR3_3 a b g * kD3_1 a b g ^(2:ℕ) + (-1) * fd31_1 a b g * kR3_0 a b g * kD3_2 a b g ^(2:ℕ) + (-1) * fd31_1 a b g * kR3_2 a b g * kD3_1 a b g ^(2:ℕ) + (3) * fd30_0 a b g * kD3_1 a b g * kD3_2 a b g ^(2:ℕ) + (3) * fd30_2 a b g * kD3_0 a b g * kD3_2 a b g ^(2:ℕ) + (-6) * fd33_0 a b g * kR3_0 a b g * kR3_1 a b g * kR3_6 a b g + (-6) * fd33_0 a b g * kR3_0 a b g * kR3_3 a b g * kR3_5 a b g + (-2) * fd31_0 a b g * kD3_0 a b g * kD3_1 a b g * kR3_5 a b g + (-2) * fd31_0 a b g * kD3_0 a b g * kD3_3 a b g * kR3_3 a b g + (-2) * fd31_0 a b g * kD3_1 a b g * kD3_3 a b g * kR3_0 a b g + (-2) * fd31_1 a b g * kD3_0 a b g * kD3_2 a b g * kR3_4 a b g + (-2) * fd31_1 a b g * kD3_0 a b g * kD3_3 a b g * kR3_2 a b g + (-2) * fd31_1 a b g * kD3_1 a b g * kD3_2 a b g * kR3_1 a b g + (-2) * fd31_2 a b g * kD3_0 a b g * kD3_1 a b g * kR3_2 a b g + (-2) * fd31_2 a b g * kD3_0 a b g * kD3_2 a b g * kR3_1 a b g + (2) * fd32_0 a b g * kD3_0 a b g * kR3_1 a b g * kR3_6 a b g + (2) * fd32_0 a b g * kD3_0 a b g * kR3_3 a b g * kR3_5 a b g + (2) * fd32_0 a b g * kD3_1 a b g * kR3_0 a b g * kR3_5 a b g + (2) * fd32_0 a b g * kD3_3 a b g * kR3_0 a b g * kR3_3 a b g + (6) * fd30_1 a b g * kD3_0 a b g * kD3_1 a b g * kD3_3 a b g + (6) * fd30_3 a b g * kD3_0 a b g * kD3_1 a b g * kD3_2 a b g

noncomputable def E3_26 (a b g : K) : K :=
  (-5) * cd3_1_12 a b g + (1) * fd30_0 a b g * kD3_2 a b g ^(3:ℕ) + (-1) * kP3_2 a b g * sd3_3 a b g + (-1) * kP3_5 a b g * sd3_2 a b g + (-1) * kP3_9 a b g * sd3_1 a b g + (1) * fd32_0 a b g * kD3_2 a b g * kR3_3 a b g ^(2:ℕ) + (-1) * fd31_0 a b g * kR3_4 a b g * kD3_1 a b g ^(2:ℕ) + (-1) * fd31_1 a b g * kR3_1 a b g * kD3_2 a b g ^(2:ℕ) + (-3) * fd33_0 a b g * kR3_4 a b g * kR3_3 a b g ^(2:ℕ) + (-3) * fd33_0 a b g * kR3_6 a b g * kR3_1 a b g ^(2:ℕ) + (3) * fd30_1 a b g * kD3_2 a b g * kD3_1 a b g ^(2:ℕ) + (3) * fd30_3 a b g * kD3_0 a b g * kD3_2 a b g ^(2:ℕ) + (-6) * fd33_0 a b g * kR3_0 a b g * kR3_2 a b g * kR3_6 a b g + (-6) * fd33_0 a b g * kR3_0 a b g * kR3_4 a b g * kR3_5 a b g + (-6) * fd33_0 a b g * kR3_1 a b g * kR3_3 a b g * kR3_5 a b g + (-2) * fd31_0 a b g * kD3_0 a b g * kD3_2 a b g * kR3_5 a b g + (-2) * fd31_0 a b g * kD3_0 a b g * kD3_3 a b g * kR3_4 a b g + (-2) * fd31_0 a b g * kD3_1 a b g * kD3_2 a b g * kR3_3 a b g + (-2) * fd31_0 a b g * kD3_1 a b g * kD3_3 a b g * kR3_1 a b g + (-2) * fd31_0 a b g * kD3_2 a b g * kD3_3 a b g * kR3_0 a b g + (-2) * fd31_1 a b g * kD3_1 a b g * kD3_2 a b g * kR3_2 a b g + (-2) * fd31_2 a b g * kD3_0 a b g * kD3_2 a b g * kR3_2 a b g + (2) * fd32_0 a b g * kD3_0 a b g * kR3_2 a b g * kR3_6 a b g + (2) * fd32_0 a b g * kD3_0 a b g * kR3_4 a b g * kR3_5 a b g + (2) * fd32_0 a b g * kD3_1 a b g * kR3_1 a b g * kR3_5 a b g + (2) * fd32_0 a b g * kD3_1 a b g * kR3_3 a b g * kR3_4 a b g + (2) * fd32_0 a b g * kD3_2 a b g * kR3_0 a b g * kR3_5 a b g + (2) * fd32_0 a b g * kD3_3 a b g * kR3_0 a b g * kR3_4 a b g + (2) * fd32_0 a b g * kD3_3 a b g * kR3_1 a b g * kR3_3 a b g + (6) * fd30_1 a b g * kD3_0 a b g * kD3_2 a b g * kD3_3 a b g

noncomputable def E3_27 (a b g : K) : K :=
  (-5) * cd3_1_13 a b g + (-1) * kP3_6 a b g * sd3_2 a b g + (1) * fd32_0 a b g * kD3_1 a b g * kR3_4 a b g ^(2:ℕ) + (-1) * fd31_0 a b g * kR3_3 a b g * kD3_2 a b g ^(2:ℕ) + (-1) * fd31_1 a b g * kR3_2 a b g * kD3_2 a b g ^(2:ℕ) + (-3) * fd33_0 a b g * kR3_3 a b g * kR3_4 a b g ^(2:ℕ) + (3) * fd30_1 a b g * kD3_1 a b g * kD3_2 a b g ^(2:ℕ) + (-6) * fd33_0 a b g * kR3_1 a b g * kR3_2 a b g * kR3_6 a b g + (-6) * fd33_0 a b g * kR3_1 a b g * kR3_4 a b g * kR3_5 a b g + (-6) * fd33_0 a b g * kR3_2 a b g * kR3_3 a b g * kR3_5 a b g + (-2) * fd31_0 a b g * kD3_1 a b g * kD3_2 a b g * kR3_4 a b g + (-2) * fd31_0 a b g * kD3_1 a b g * kD3_3 a b g * kR3_2 a b g + (-2) * fd31_0 a b g * kD3_2 a b g * kD3_3 a b g * kR3_1 a b g + (2) * fd32_0 a b g * kD3_1 a b g * kR3_2 a b g * kR3_5 a b g + (2) * fd32_0 a b g * kD3_2 a b g * kR3_1 a b g * kR3_5 a b g + (2) * fd32_0 a b g * kD3_2 a b g * kR3_3 a b g * kR3_4 a b g + (2) * fd32_0 a b g * kD3_3 a b g * kR3_1 a b g * kR3_4 a b g + (2) * fd32_0 a b g * kD3_3 a b g * kR3_2 a b g * kR3_3 a b g

noncomputable def E3_28 (a b g : K) : K :=
  (-5) * cd3_2_0 a b g + (1) * fd30_1 a b g * kD3_2 a b g ^(3:ℕ) + (-1) * fd33_0 a b g * kR3_4 a b g ^(3:ℕ) + (-1) * kP3_3 a b g * sd3_3 a b g + (1) * fd32_0 a b g * kD3_2 a b g * kR3_4 a b g ^(2:ℕ) + (-1) * fd31_0 a b g * kR3_4 a b g * kD3_2 a b g ^(2:ℕ) + (-3) * fd33_0 a b g * kR3_6 a b g * kR3_2 a b g ^(2:ℕ) + (-6) * fd33_0 a b g * kR3_2 a b g * kR3_4 a b g * kR3_5 a b g + (-2) * fd31_0 a b g * kD3_2 a b g * kD3_3 a b g * kR3_2 a b g + (2) * fd32_0 a b g * kD3_2 a b g * kR3_2 a b g * kR3_5 a b g + (2) * fd32_0 a b g * kD3_3 a b g * kR3_2 a b g * kR3_4 a b g

noncomputable def E3_29 (a b g : K) : K :=
  (-5) * cd3_2_1 a b g + (-1) * kP3_0 a b g * sd3_4 a b g + (-1) * fd31_1 a b g * kR3_6 a b g * kD3_0 a b g ^(2:ℕ)

noncomputable def E3_30 (a b g : K) : K :=
  (-5) * cd3_2_2 a b g + (1) * fd30_2 a b g * kD3_1 a b g ^(3:ℕ) + (-1) * kP3_10 a b g * sd3_1 a b g + (-1) * kP3_13 a b g * sd3_0 a b g + (-1) * kP3_7 a b g * sd3_2 a b g + (-1) * fd31_1 a b g * kR3_3 a b g * kD3_1 a b g ^(2:ℕ) + (-1) * fd31_2 a b g * kR3_0 a b g * kD3_1 a b g ^(2:ℕ) + (-1) * fd31_2 a b g * kR3_5 a b g * kD3_0 a b g ^(2:ℕ) + (3) * fd30_0 a b g * kD3_0 a b g * kD3_3 a b g ^(2:ℕ) + (3) * fd30_0 a b g * kD3_3 a b g * kD3_1 a b g ^(2:ℕ) + (3) * fd30_4 a b g * kD3_0 a b g * kD3_1 a b g ^(2:ℕ) + (3) * fd30_4 a b g * kD3_3 a b g * kD3_0 a b g ^(2:ℕ) + (-2) * fd31_1 a b g * kD3_0 a b g * kD3_1 a b g * kR3_5 a b g + (-2) * fd31_1 a b g * kD3_0 a b g * kD3_3 a b g * kR3_3 a b g + (-2) * fd31_1 a b g * kD3_1 a b g * kD3_3 a b g * kR3_0 a b g + (-2) * fd31_2 a b g * kD3_0 a b g * kD3_1 a b g * kR3_3 a b g + (-2) * fd31_2 a b g * kD3_0 a b g * kD3_3 a b g * kR3_0 a b g + (6) * fd30_2 a b g * kD3_0 a b g * kD3_1 a b g * kD3_3 a b g

end Work.MotC5N3.CertDemo
