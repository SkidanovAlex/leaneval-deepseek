import Submission.Work.MotC5N3.SatCert2.K1_defs

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

noncomputable def kD1_0 (a b g : K) : K :=
  ((-2)*a^(6:ℕ)) + ((1)*a^(5:ℕ)*b) + ((5)*a^(4:ℕ)*b^(2:ℕ)) + ((-5)*a^(2:ℕ)*b^(4:ℕ)) + ((1)*a*b^(5:ℕ)) + ((2)*b^(6:ℕ))

noncomputable def kD1_1 (a b g : K) : K :=
  ((-1)*a^(6:ℕ)) + ((2)*a^(5:ℕ)*b) + ((-2)*a*b^(5:ℕ)) + ((-1)*b^(6:ℕ))

noncomputable def kD1_2 (a b g : K) : K :=
  ((1)*a^(6:ℕ)*g) + ((-3)*a^(5:ℕ)*b*g) + ((5)*a^(3:ℕ)*b^(3:ℕ)*g) + ((-3)*a*b^(5:ℕ)*g) + ((-1)*b^(6:ℕ)*g)

noncomputable def kD1_3 (a b g : K) : K :=
  ((1)*a^(5:ℕ)*b) + ((3)*a^(4:ℕ)*b^(2:ℕ)) + ((-6)*a^(3:ℕ)*b^(3:ℕ)) + ((-3)*a^(2:ℕ)*b^(4:ℕ)) + ((1)*a*b^(5:ℕ))

noncomputable def kR1_0 (a b g : K) : K :=
  ((1)*a^(6:ℕ)) + ((3)*a^(5:ℕ)*b) + ((-3)*a*b^(5:ℕ)) + ((1)*b^(6:ℕ))

noncomputable def kR1_1 (a b g : K) : K :=
  ((-2)*a^(6:ℕ)*g) + ((1)*a^(5:ℕ)*b*g) + ((5)*a^(4:ℕ)*b^(2:ℕ)*g) + ((-5)*a^(2:ℕ)*b^(4:ℕ)*g) + ((1)*a*b^(5:ℕ)*g) + ((2)*b^(6:ℕ)*g)

noncomputable def kR1_2 (a b g : K) : K :=
  ((-5)*a^(3:ℕ)*b^(3:ℕ))

noncomputable def kR1_3 (a b g : K) : K :=
  ((-3)*a^(6:ℕ)) + ((5)*a^(5:ℕ)*b) + ((-2)*a^(4:ℕ)*b^(2:ℕ)) + ((-1)*a^(3:ℕ)*b^(3:ℕ)) + ((2)*a^(2:ℕ)*b^(4:ℕ)) + ((5)*a*b^(5:ℕ)) + ((3)*b^(6:ℕ))

noncomputable def kR1_4 (a b g : K) : K :=
  ((4)*a^(6:ℕ)*g) + ((-3)*a^(5:ℕ)*b*g) + ((3)*a*b^(5:ℕ)*g) + ((4)*b^(6:ℕ)*g)

noncomputable def kR1_5 (a b g : K) : K :=
  ((-3)*a^(5:ℕ)*b) + ((-2)*a^(4:ℕ)*b^(2:ℕ)) + ((-2)*a^(2:ℕ)*b^(4:ℕ)) + ((3)*a*b^(5:ℕ))

noncomputable def kR1_6 (a b g : K) : K :=
  ((1)*a^(6:ℕ)*g) + ((-3)*a^(5:ℕ)*b*g) + ((5)*a^(3:ℕ)*b^(3:ℕ)*g) + ((-3)*a*b^(5:ℕ)*g) + ((-1)*b^(6:ℕ)*g)

noncomputable def kP1_0 (a b g : K) : K :=
  (-1*a^(5:ℕ) + -2*b^(5:ℕ))

noncomputable def kP1_1 (a b g : K) : K :=
  (a^(5:ℕ) + a^(4:ℕ)*b + -2*a^(3:ℕ)*b^(2:ℕ) + -1*a^(2:ℕ)*b^(3:ℕ) + 2*a*b^(4:ℕ) + -2*b^(5:ℕ))

noncomputable def kP1_2 (a b g : K) : K :=
  (-1*a^(5:ℕ)*g + -2*b^(5:ℕ)*g)

noncomputable def kP1_3 (a b g : K) : K :=
  (2*a^(5:ℕ)*g^(3:ℕ) + -1*b^(5:ℕ)*g^(3:ℕ))

noncomputable def kP1_4 (a b g : K) : K :=
  (-1*a^(5:ℕ) + -1*a^(4:ℕ)*b + -1*a^(3:ℕ)*b^(2:ℕ) + -2*a^(2:ℕ)*b^(3:ℕ) + 2*a*b^(4:ℕ) + -2*b^(5:ℕ))

noncomputable def kP1_5 (a b g : K) : K :=
  (-2*a^(5:ℕ)*g + -2*a^(4:ℕ)*b*g + -1*a^(3:ℕ)*b^(2:ℕ)*g + 2*a^(2:ℕ)*b^(3:ℕ)*g + a*b^(4:ℕ)*g + -1*b^(5:ℕ)*g)

noncomputable def kP1_6 (a b g : K) : K :=
  (-1*a^(5:ℕ)*g^(2:ℕ) + -2*b^(5:ℕ)*g^(2:ℕ))

noncomputable def kP1_7 (a b g : K) : K :=
  (2*a^(5:ℕ) + -1*b^(5:ℕ))

noncomputable def kP1_8 (a b g : K) : K :=
  (a^(4:ℕ)*b + 2*a^(3:ℕ)*b^(2:ℕ) + a^(2:ℕ)*b^(3:ℕ) + 2*a*b^(4:ℕ))

noncomputable def kP1_9 (a b g : K) : K :=
  (a^(4:ℕ)*b*g + a^(3:ℕ)*b^(2:ℕ)*g + 2*a^(2:ℕ)*b^(3:ℕ)*g + -2*a*b^(4:ℕ)*g)

noncomputable def kP1_10 (a b g : K) : K :=
  (-1*a^(5:ℕ) + -1*a^(4:ℕ)*b + 2*a^(3:ℕ)*b^(2:ℕ) + a^(2:ℕ)*b^(3:ℕ) + -2*a*b^(4:ℕ) + 2*b^(5:ℕ))

noncomputable def kP1_11 (a b g : K) : K :=
  (-2*a^(5:ℕ)*g + b^(5:ℕ)*g)

noncomputable def kP1_12 (a b g : K) : K :=
  (a^(3:ℕ)*b^(2:ℕ) + 2*a^(2:ℕ)*b^(3:ℕ))

noncomputable def kP1_13 (a b g : K) : K :=
  (2*a^(4:ℕ)*b + 2*a^(3:ℕ)*b^(2:ℕ) + -1*a^(2:ℕ)*b^(3:ℕ) + a*b^(4:ℕ))

noncomputable def kP1_14 (a b g : K) : K :=
  (a^(5:ℕ)*g^(2:ℕ) + -1*a^(3:ℕ)*b^(2:ℕ) + 2*a^(2:ℕ)*b^(3:ℕ) + 2*b^(5:ℕ)*g^(2:ℕ))

noncomputable def E1_0 (a b g : K) : K :=
  (-5) * cd1_0_0 a b g + (1) * fd10_0 a b g * kD1_0 a b g ^(3:ℕ) + (-1) * kP1_0 a b g * sd1_0 a b g + (-1) * fd11_0 a b g * kR1_0 a b g * kD1_0 a b g ^(2:ℕ)

noncomputable def E1_1 (a b g : K) : K :=
  (1) * fd10_1 a b g * kD1_0 a b g ^(3:ℕ) + (-1) * fd11_0 a b g * kR1_1 a b g * kD1_0 a b g ^(2:ℕ)

noncomputable def E1_2 (a b g : K) : K :=
  (-5) * cd1_0_1 a b g + (1) * fd10_2 a b g * kD1_0 a b g ^(3:ℕ) + (-1) * fd13_0 a b g * kR1_0 a b g ^(3:ℕ) + (-1) * kP1_1 a b g * sd1_0 a b g + (1) * fd12_0 a b g * kD1_0 a b g * kR1_0 a b g ^(2:ℕ) + (-1) * fd11_0 a b g * kR1_2 a b g * kD1_0 a b g ^(2:ℕ) + (-1) * fd11_1 a b g * kR1_0 a b g * kD1_0 a b g ^(2:ℕ)

noncomputable def E1_3 (a b g : K) : K :=
  (-5) * cd1_0_2 a b g + (-1) * kP1_2 a b g * sd1_0 a b g + (-1) * fd11_1 a b g * kR1_1 a b g * kD1_0 a b g ^(2:ℕ) + (-3) * fd13_0 a b g * kR1_1 a b g * kR1_0 a b g ^(2:ℕ) + (2) * fd12_0 a b g * kD1_0 a b g * kR1_0 a b g * kR1_1 a b g

noncomputable def E1_4 (a b g : K) : K :=
  (-5) * cd1_0_3 a b g + (1) * fd12_0 a b g * kD1_0 a b g * kR1_1 a b g ^(2:ℕ) + (-1) * fd11_1 a b g * kR1_2 a b g * kD1_0 a b g ^(2:ℕ) + (-3) * fd13_0 a b g * kR1_0 a b g * kR1_1 a b g ^(2:ℕ) + (-3) * fd13_0 a b g * kR1_2 a b g * kR1_0 a b g ^(2:ℕ) + (2) * fd12_0 a b g * kD1_0 a b g * kR1_0 a b g * kR1_2 a b g

noncomputable def E1_5 (a b g : K) : K :=
  (-5) * cd1_0_4 a b g + (-1) * fd13_0 a b g * kR1_1 a b g ^(3:ℕ) + (-1) * kP1_3 a b g * sd1_0 a b g + (-6) * fd13_0 a b g * kR1_0 a b g * kR1_1 a b g * kR1_2 a b g + (2) * fd12_0 a b g * kD1_0 a b g * kR1_1 a b g * kR1_2 a b g

noncomputable def E1_6 (a b g : K) : K :=
  (-5) * cd1_0_5 a b g + (1) * fd12_0 a b g * kD1_0 a b g * kR1_2 a b g ^(2:ℕ) + (-3) * fd13_0 a b g * kR1_0 a b g * kR1_2 a b g ^(2:ℕ) + (-3) * fd13_0 a b g * kR1_2 a b g * kR1_1 a b g ^(2:ℕ)

noncomputable def E1_7 (a b g : K) : K :=
  (-5) * cd1_0_6 a b g + (-3) * fd13_0 a b g * kR1_1 a b g * kR1_2 a b g ^(2:ℕ)

noncomputable def E1_8 (a b g : K) : K :=
  (-5) * cd1_0_7 a b g + (-1) * fd13_0 a b g * kR1_2 a b g ^(3:ℕ)

noncomputable def E1_9 (a b g : K) : K :=
  (-5) * cd1_0_8 a b g + (1) * fd10_3 a b g * kD1_0 a b g ^(3:ℕ) + (-1) * kP1_0 a b g * sd1_1 a b g + (-1) * fd11_0 a b g * kR1_3 a b g * kD1_0 a b g ^(2:ℕ) + (3) * fd10_0 a b g * kD1_1 a b g * kD1_0 a b g ^(2:ℕ) + (-2) * fd11_0 a b g * kD1_0 a b g * kD1_1 a b g * kR1_0 a b g

noncomputable def E1_10 (a b g : K) : K :=
  (-5) * cd1_0_9 a b g + (1) * fd10_4 a b g * kD1_0 a b g ^(3:ℕ) + (-1) * fd11_0 a b g * kR1_4 a b g * kD1_0 a b g ^(2:ℕ) + (-1) * fd11_2 a b g * kR1_0 a b g * kD1_0 a b g ^(2:ℕ) + (3) * fd10_0 a b g * kD1_2 a b g * kD1_0 a b g ^(2:ℕ) + (3) * fd10_1 a b g * kD1_1 a b g * kD1_0 a b g ^(2:ℕ) + (-2) * fd11_0 a b g * kD1_0 a b g * kD1_1 a b g * kR1_1 a b g + (-2) * fd11_0 a b g * kD1_0 a b g * kD1_2 a b g * kR1_0 a b g

noncomputable def E1_11 (a b g : K) : K :=
  (-5) * cd1_0_10 a b g + (-1) * kP1_1 a b g * sd1_1 a b g + (-1) * kP1_4 a b g * sd1_0 a b g + (1) * fd12_0 a b g * kD1_1 a b g * kR1_0 a b g ^(2:ℕ) + (-1) * fd11_1 a b g * kR1_3 a b g * kD1_0 a b g ^(2:ℕ) + (-1) * fd11_2 a b g * kR1_1 a b g * kD1_0 a b g ^(2:ℕ) + (-3) * fd13_0 a b g * kR1_3 a b g * kR1_0 a b g ^(2:ℕ) + (3) * fd10_1 a b g * kD1_2 a b g * kD1_0 a b g ^(2:ℕ) + (3) * fd10_2 a b g * kD1_1 a b g * kD1_0 a b g ^(2:ℕ) + (-2) * fd11_0 a b g * kD1_0 a b g * kD1_1 a b g * kR1_2 a b g + (-2) * fd11_0 a b g * kD1_0 a b g * kD1_2 a b g * kR1_1 a b g + (-2) * fd11_1 a b g * kD1_0 a b g * kD1_1 a b g * kR1_0 a b g + (2) * fd12_0 a b g * kD1_0 a b g * kR1_0 a b g * kR1_3 a b g

noncomputable def E1_12 (a b g : K) : K :=
  (-5) * cd1_0_11 a b g + (-1) * kP1_2 a b g * sd1_1 a b g + (-1) * kP1_5 a b g * sd1_0 a b g + (1) * fd12_0 a b g * kD1_2 a b g * kR1_0 a b g ^(2:ℕ) + (-1) * fd11_1 a b g * kR1_4 a b g * kD1_0 a b g ^(2:ℕ) + (-1) * fd11_2 a b g * kR1_2 a b g * kD1_0 a b g ^(2:ℕ) + (-3) * fd13_0 a b g * kR1_4 a b g * kR1_0 a b g ^(2:ℕ) + (3) * fd10_2 a b g * kD1_2 a b g * kD1_0 a b g ^(2:ℕ) + (-6) * fd13_0 a b g * kR1_0 a b g * kR1_1 a b g * kR1_3 a b g + (-2) * fd11_0 a b g * kD1_0 a b g * kD1_2 a b g * kR1_2 a b g + (-2) * fd11_1 a b g * kD1_0 a b g * kD1_1 a b g * kR1_1 a b g + (-2) * fd11_1 a b g * kD1_0 a b g * kD1_2 a b g * kR1_0 a b g + (2) * fd12_0 a b g * kD1_0 a b g * kR1_0 a b g * kR1_4 a b g + (2) * fd12_0 a b g * kD1_0 a b g * kR1_1 a b g * kR1_3 a b g + (2) * fd12_0 a b g * kD1_1 a b g * kR1_0 a b g * kR1_1 a b g

noncomputable def E1_13 (a b g : K) : K :=
  (-5) * cd1_0_12 a b g + (-1) * kP1_6 a b g * sd1_0 a b g + (1) * fd12_0 a b g * kD1_1 a b g * kR1_1 a b g ^(2:ℕ) + (-3) * fd13_0 a b g * kR1_3 a b g * kR1_1 a b g ^(2:ℕ) + (-6) * fd13_0 a b g * kR1_0 a b g * kR1_1 a b g * kR1_4 a b g + (-6) * fd13_0 a b g * kR1_0 a b g * kR1_2 a b g * kR1_3 a b g + (-2) * fd11_1 a b g * kD1_0 a b g * kD1_1 a b g * kR1_2 a b g + (-2) * fd11_1 a b g * kD1_0 a b g * kD1_2 a b g * kR1_1 a b g + (2) * fd12_0 a b g * kD1_0 a b g * kR1_1 a b g * kR1_4 a b g + (2) * fd12_0 a b g * kD1_0 a b g * kR1_2 a b g * kR1_3 a b g + (2) * fd12_0 a b g * kD1_1 a b g * kR1_0 a b g * kR1_2 a b g + (2) * fd12_0 a b g * kD1_2 a b g * kR1_0 a b g * kR1_1 a b g

noncomputable def E1_14 (a b g : K) : K :=
  (-5) * cd1_0_13 a b g + (-1) * kP1_3 a b g * sd1_1 a b g + (1) * fd12_0 a b g * kD1_2 a b g * kR1_1 a b g ^(2:ℕ) + (-3) * fd13_0 a b g * kR1_4 a b g * kR1_1 a b g ^(2:ℕ) + (-6) * fd13_0 a b g * kR1_0 a b g * kR1_2 a b g * kR1_4 a b g + (-6) * fd13_0 a b g * kR1_1 a b g * kR1_2 a b g * kR1_3 a b g + (-2) * fd11_1 a b g * kD1_0 a b g * kD1_2 a b g * kR1_2 a b g + (2) * fd12_0 a b g * kD1_0 a b g * kR1_2 a b g * kR1_4 a b g + (2) * fd12_0 a b g * kD1_1 a b g * kR1_1 a b g * kR1_2 a b g + (2) * fd12_0 a b g * kD1_2 a b g * kR1_0 a b g * kR1_2 a b g

noncomputable def E1_15 (a b g : K) : K :=
  (-5) * cd1_1_0 a b g + (1) * fd12_0 a b g * kD1_1 a b g * kR1_2 a b g ^(2:ℕ) + (-3) * fd13_0 a b g * kR1_3 a b g * kR1_2 a b g ^(2:ℕ) + (-6) * fd13_0 a b g * kR1_1 a b g * kR1_2 a b g * kR1_4 a b g + (2) * fd12_0 a b g * kD1_2 a b g * kR1_1 a b g * kR1_2 a b g

noncomputable def E1_16 (a b g : K) : K :=
  (-5) * cd1_1_1 a b g + (1) * fd12_0 a b g * kD1_2 a b g * kR1_2 a b g ^(2:ℕ) + (-3) * fd13_0 a b g * kR1_4 a b g * kR1_2 a b g ^(2:ℕ)

noncomputable def E1_17 (a b g : K) : K :=
  (-5) * cd1_1_2 a b g + (1) * fd10_5 a b g * kD1_0 a b g ^(3:ℕ) + (-1) * kP1_0 a b g * sd1_2 a b g + (-1) * kP1_7 a b g * sd1_0 a b g + (-1) * fd11_0 a b g * kR1_0 a b g * kD1_1 a b g ^(2:ℕ) + (-1) * fd11_0 a b g * kR1_5 a b g * kD1_0 a b g ^(2:ℕ) + (-1) * fd11_3 a b g * kR1_0 a b g * kD1_0 a b g ^(2:ℕ) + (3) * fd10_0 a b g * kD1_0 a b g * kD1_1 a b g ^(2:ℕ) + (3) * fd10_0 a b g * kD1_3 a b g * kD1_0 a b g ^(2:ℕ) + (3) * fd10_3 a b g * kD1_1 a b g * kD1_0 a b g ^(2:ℕ) + (-2) * fd11_0 a b g * kD1_0 a b g * kD1_1 a b g * kR1_3 a b g + (-2) * fd11_0 a b g * kD1_0 a b g * kD1_3 a b g * kR1_0 a b g

noncomputable def E1_18 (a b g : K) : K :=
  (-5) * cd1_1_3 a b g + (-1) * fd11_0 a b g * kR1_1 a b g * kD1_1 a b g ^(2:ℕ) + (-1) * fd11_2 a b g * kR1_3 a b g * kD1_0 a b g ^(2:ℕ) + (-1) * fd11_3 a b g * kR1_1 a b g * kD1_0 a b g ^(2:ℕ) + (3) * fd10_1 a b g * kD1_0 a b g * kD1_1 a b g ^(2:ℕ) + (3) * fd10_1 a b g * kD1_3 a b g * kD1_0 a b g ^(2:ℕ) + (3) * fd10_3 a b g * kD1_2 a b g * kD1_0 a b g ^(2:ℕ) + (3) * fd10_4 a b g * kD1_1 a b g * kD1_0 a b g ^(2:ℕ) + (-2) * fd11_0 a b g * kD1_0 a b g * kD1_1 a b g * kR1_4 a b g + (-2) * fd11_0 a b g * kD1_0 a b g * kD1_2 a b g * kR1_3 a b g + (-2) * fd11_0 a b g * kD1_0 a b g * kD1_3 a b g * kR1_1 a b g + (-2) * fd11_0 a b g * kD1_1 a b g * kD1_2 a b g * kR1_0 a b g + (-2) * fd11_2 a b g * kD1_0 a b g * kD1_1 a b g * kR1_0 a b g + (6) * fd10_0 a b g * kD1_0 a b g * kD1_1 a b g * kD1_2 a b g

noncomputable def E1_19 (a b g : K) : K :=
  (-5) * cd1_1_4 a b g + (-1) * kP1_1 a b g * sd1_2 a b g + (-1) * kP1_4 a b g * sd1_1 a b g + (-1) * kP1_8 a b g * sd1_0 a b g + (1) * fd12_0 a b g * kD1_0 a b g * kR1_3 a b g ^(2:ℕ) + (1) * fd12_0 a b g * kD1_3 a b g * kR1_0 a b g ^(2:ℕ) + (-1) * fd11_0 a b g * kR1_0 a b g * kD1_2 a b g ^(2:ℕ) + (-1) * fd11_0 a b g * kR1_2 a b g * kD1_1 a b g ^(2:ℕ) + (-1) * fd11_1 a b g * kR1_0 a b g * kD1_1 a b g ^(2:ℕ) + (-1) * fd11_1 a b g * kR1_5 a b g * kD1_0 a b g ^(2:ℕ) + (-1) * fd11_2 a b g * kR1_4 a b g * kD1_0 a b g ^(2:ℕ) + (-1) * fd11_3 a b g * kR1_2 a b g * kD1_0 a b g ^(2:ℕ) + (-3) * fd13_0 a b g * kR1_0 a b g * kR1_3 a b g ^(2:ℕ) + (-3) * fd13_0 a b g * kR1_5 a b g * kR1_0 a b g ^(2:ℕ) + (3) * fd10_0 a b g * kD1_0 a b g * kD1_2 a b g ^(2:ℕ) + (3) * fd10_2 a b g * kD1_0 a b g * kD1_1 a b g ^(2:ℕ) + (3) * fd10_2 a b g * kD1_3 a b g * kD1_0 a b g ^(2:ℕ) + (3) * fd10_4 a b g * kD1_2 a b g * kD1_0 a b g ^(2:ℕ) + (-2) * fd11_0 a b g * kD1_0 a b g * kD1_2 a b g * kR1_4 a b g + (-2) * fd11_0 a b g * kD1_0 a b g * kD1_3 a b g * kR1_2 a b g + (-2) * fd11_0 a b g * kD1_1 a b g * kD1_2 a b g * kR1_1 a b g + (-2) * fd11_1 a b g * kD1_0 a b g * kD1_1 a b g * kR1_3 a b g + (-2) * fd11_1 a b g * kD1_0 a b g * kD1_3 a b g * kR1_0 a b g + (-2) * fd11_2 a b g * kD1_0 a b g * kD1_1 a b g * kR1_1 a b g + (-2) * fd11_2 a b g * kD1_0 a b g * kD1_2 a b g * kR1_0 a b g + (2) * fd12_0 a b g * kD1_0 a b g * kR1_0 a b g * kR1_5 a b g + (2) * fd12_0 a b g * kD1_1 a b g * kR1_0 a b g * kR1_3 a b g + (6) * fd10_1 a b g * kD1_0 a b g * kD1_1 a b g * kD1_2 a b g

noncomputable def E1_20 (a b g : K) : K :=
  (-5) * cd1_1_5 a b g + (-1) * kP1_2 a b g * sd1_2 a b g + (-1) * kP1_5 a b g * sd1_1 a b g + (-1) * kP1_9 a b g * sd1_0 a b g + (-1) * fd11_0 a b g * kR1_1 a b g * kD1_2 a b g ^(2:ℕ) + (-1) * fd11_1 a b g * kR1_1 a b g * kD1_1 a b g ^(2:ℕ) + (-3) * fd13_0 a b g * kR1_1 a b g * kR1_3 a b g ^(2:ℕ) + (3) * fd10_1 a b g * kD1_0 a b g * kD1_2 a b g ^(2:ℕ) + (-6) * fd13_0 a b g * kR1_0 a b g * kR1_1 a b g * kR1_5 a b g + (-6) * fd13_0 a b g * kR1_0 a b g * kR1_3 a b g * kR1_4 a b g + (-2) * fd11_0 a b g * kD1_1 a b g * kD1_2 a b g * kR1_2 a b g + (-2) * fd11_1 a b g * kD1_0 a b g * kD1_1 a b g * kR1_4 a b g + (-2) * fd11_1 a b g * kD1_0 a b g * kD1_2 a b g * kR1_3 a b g + (-2) * fd11_1 a b g * kD1_0 a b g * kD1_3 a b g * kR1_1 a b g + (-2) * fd11_1 a b g * kD1_1 a b g * kD1_2 a b g * kR1_0 a b g + (-2) * fd11_2 a b g * kD1_0 a b g * kD1_1 a b g * kR1_2 a b g + (-2) * fd11_2 a b g * kD1_0 a b g * kD1_2 a b g * kR1_1 a b g + (2) * fd12_0 a b g * kD1_0 a b g * kR1_1 a b g * kR1_5 a b g + (2) * fd12_0 a b g * kD1_0 a b g * kR1_3 a b g * kR1_4 a b g + (2) * fd12_0 a b g * kD1_1 a b g * kR1_0 a b g * kR1_4 a b g + (2) * fd12_0 a b g * kD1_1 a b g * kR1_1 a b g * kR1_3 a b g + (2) * fd12_0 a b g * kD1_2 a b g * kR1_0 a b g * kR1_3 a b g + (2) * fd12_0 a b g * kD1_3 a b g * kR1_0 a b g * kR1_1 a b g + (6) * fd10_2 a b g * kD1_0 a b g * kD1_1 a b g * kD1_2 a b g

noncomputable def E1_21 (a b g : K) : K :=
  (-5) * cd1_1_6 a b g + (-1) * kP1_6 a b g * sd1_1 a b g + (1) * fd12_0 a b g * kD1_0 a b g * kR1_4 a b g ^(2:ℕ) + (1) * fd12_0 a b g * kD1_3 a b g * kR1_1 a b g ^(2:ℕ) + (-1) * fd11_0 a b g * kR1_2 a b g * kD1_2 a b g ^(2:ℕ) + (-1) * fd11_1 a b g * kR1_0 a b g * kD1_2 a b g ^(2:ℕ) + (-1) * fd11_1 a b g * kR1_2 a b g * kD1_1 a b g ^(2:ℕ) + (-3) * fd13_0 a b g * kR1_0 a b g * kR1_4 a b g ^(2:ℕ) + (-3) * fd13_0 a b g * kR1_2 a b g * kR1_3 a b g ^(2:ℕ) + (-3) * fd13_0 a b g * kR1_5 a b g * kR1_1 a b g ^(2:ℕ) + (3) * fd10_2 a b g * kD1_0 a b g * kD1_2 a b g ^(2:ℕ) + (-6) * fd13_0 a b g * kR1_0 a b g * kR1_2 a b g * kR1_5 a b g + (-6) * fd13_0 a b g * kR1_1 a b g * kR1_3 a b g * kR1_4 a b g + (-2) * fd11_1 a b g * kD1_0 a b g * kD1_2 a b g * kR1_4 a b g + (-2) * fd11_1 a b g * kD1_0 a b g * kD1_3 a b g * kR1_2 a b g + (-2) * fd11_1 a b g * kD1_1 a b g * kD1_2 a b g * kR1_1 a b g + (-2) * fd11_2 a b g * kD1_0 a b g * kD1_2 a b g * kR1_2 a b g + (2) * fd12_0 a b g * kD1_0 a b g * kR1_2 a b g * kR1_5 a b g + (2) * fd12_0 a b g * kD1_1 a b g * kR1_1 a b g * kR1_4 a b g + (2) * fd12_0 a b g * kD1_1 a b g * kR1_2 a b g * kR1_3 a b g + (2) * fd12_0 a b g * kD1_2 a b g * kR1_0 a b g * kR1_4 a b g + (2) * fd12_0 a b g * kD1_2 a b g * kR1_1 a b g * kR1_3 a b g + (2) * fd12_0 a b g * kD1_3 a b g * kR1_0 a b g * kR1_2 a b g

noncomputable def E1_22 (a b g : K) : K :=
  (-5) * cd1_1_7 a b g + (-1) * kP1_3 a b g * sd1_2 a b g + (-1) * fd11_1 a b g * kR1_1 a b g * kD1_2 a b g ^(2:ℕ) + (-3) * fd13_0 a b g * kR1_1 a b g * kR1_4 a b g ^(2:ℕ) + (-6) * fd13_0 a b g * kR1_1 a b g * kR1_2 a b g * kR1_5 a b g + (-6) * fd13_0 a b g * kR1_2 a b g * kR1_3 a b g * kR1_4 a b g + (-2) * fd11_1 a b g * kD1_1 a b g * kD1_2 a b g * kR1_2 a b g + (2) * fd12_0 a b g * kD1_1 a b g * kR1_2 a b g * kR1_4 a b g + (2) * fd12_0 a b g * kD1_2 a b g * kR1_1 a b g * kR1_4 a b g + (2) * fd12_0 a b g * kD1_2 a b g * kR1_2 a b g * kR1_3 a b g + (2) * fd12_0 a b g * kD1_3 a b g * kR1_1 a b g * kR1_2 a b g

noncomputable def E1_23 (a b g : K) : K :=
  (-5) * cd1_1_8 a b g + (1) * fd12_0 a b g * kD1_3 a b g * kR1_2 a b g ^(2:ℕ) + (-1) * fd11_1 a b g * kR1_2 a b g * kD1_2 a b g ^(2:ℕ) + (-3) * fd13_0 a b g * kR1_2 a b g * kR1_4 a b g ^(2:ℕ) + (-3) * fd13_0 a b g * kR1_5 a b g * kR1_2 a b g ^(2:ℕ) + (2) * fd12_0 a b g * kD1_2 a b g * kR1_2 a b g * kR1_4 a b g

noncomputable def E1_24 (a b g : K) : K :=
  (1) * fd10_6 a b g * kD1_0 a b g ^(3:ℕ) + (-1) * fd11_0 a b g * kR1_6 a b g * kD1_0 a b g ^(2:ℕ)

noncomputable def E1_25 (a b g : K) : K :=
  (-5) * cd1_1_9 a b g + (1) * fd10_0 a b g * kD1_1 a b g ^(3:ℕ) + (-1) * kP1_0 a b g * sd1_3 a b g + (-1) * kP1_10 a b g * sd1_0 a b g + (-1) * kP1_7 a b g * sd1_1 a b g + (-1) * fd11_0 a b g * kR1_3 a b g * kD1_1 a b g ^(2:ℕ) + (-1) * fd11_3 a b g * kR1_3 a b g * kD1_0 a b g ^(2:ℕ) + (3) * fd10_3 a b g * kD1_0 a b g * kD1_1 a b g ^(2:ℕ) + (3) * fd10_3 a b g * kD1_3 a b g * kD1_0 a b g ^(2:ℕ) + (3) * fd10_5 a b g * kD1_1 a b g * kD1_0 a b g ^(2:ℕ) + (-2) * fd11_0 a b g * kD1_0 a b g * kD1_1 a b g * kR1_5 a b g + (-2) * fd11_0 a b g * kD1_0 a b g * kD1_3 a b g * kR1_3 a b g + (-2) * fd11_0 a b g * kD1_1 a b g * kD1_3 a b g * kR1_0 a b g + (-2) * fd11_3 a b g * kD1_0 a b g * kD1_1 a b g * kR1_0 a b g + (6) * fd10_0 a b g * kD1_0 a b g * kD1_1 a b g * kD1_3 a b g

noncomputable def E1_26 (a b g : K) : K :=
  (-5) * cd1_1_10 a b g + (1) * fd10_1 a b g * kD1_1 a b g ^(3:ℕ) + (-1) * kP1_11 a b g * sd1_0 a b g + (-1) * fd11_0 a b g * kR1_4 a b g * kD1_1 a b g ^(2:ℕ) + (-1) * fd11_1 a b g * kR1_6 a b g * kD1_0 a b g ^(2:ℕ) + (-1) * fd11_2 a b g * kR1_0 a b g * kD1_1 a b g ^(2:ℕ) + (-1) * fd11_2 a b g * kR1_5 a b g * kD1_0 a b g ^(2:ℕ) + (-1) * fd11_3 a b g * kR1_4 a b g * kD1_0 a b g ^(2:ℕ) + (-3) * fd13_0 a b g * kR1_6 a b g * kR1_0 a b g ^(2:ℕ) + (3) * fd10_0 a b g * kD1_2 a b g * kD1_1 a b g ^(2:ℕ) + (3) * fd10_4 a b g * kD1_0 a b g * kD1_1 a b g ^(2:ℕ) + (3) * fd10_4 a b g * kD1_3 a b g * kD1_0 a b g ^(2:ℕ) + (3) * fd10_5 a b g * kD1_2 a b g * kD1_0 a b g ^(2:ℕ) + (-2) * fd11_0 a b g * kD1_0 a b g * kD1_2 a b g * kR1_5 a b g + (-2) * fd11_0 a b g * kD1_0 a b g * kD1_3 a b g * kR1_4 a b g + (-2) * fd11_0 a b g * kD1_1 a b g * kD1_2 a b g * kR1_3 a b g + (-2) * fd11_0 a b g * kD1_1 a b g * kD1_3 a b g * kR1_1 a b g + (-2) * fd11_0 a b g * kD1_2 a b g * kD1_3 a b g * kR1_0 a b g + (-2) * fd11_2 a b g * kD1_0 a b g * kD1_1 a b g * kR1_3 a b g + (-2) * fd11_2 a b g * kD1_0 a b g * kD1_3 a b g * kR1_0 a b g + (-2) * fd11_3 a b g * kD1_0 a b g * kD1_1 a b g * kR1_1 a b g + (-2) * fd11_3 a b g * kD1_0 a b g * kD1_2 a b g * kR1_0 a b g + (2) * fd12_0 a b g * kD1_0 a b g * kR1_0 a b g * kR1_6 a b g + (6) * fd10_0 a b g * kD1_0 a b g * kD1_2 a b g * kD1_3 a b g + (6) * fd10_1 a b g * kD1_0 a b g * kD1_1 a b g * kD1_3 a b g + (6) * fd10_3 a b g * kD1_0 a b g * kD1_1 a b g * kD1_2 a b g

noncomputable def E1_27 (a b g : K) : K :=
  (-5) * cd1_1_11 a b g + (1) * fd10_2 a b g * kD1_1 a b g ^(3:ℕ) + (-1) * fd13_0 a b g * kR1_3 a b g ^(3:ℕ) + (-1) * kP1_1 a b g * sd1_3 a b g + (-1) * kP1_12 a b g * sd1_0 a b g + (-1) * kP1_4 a b g * sd1_2 a b g + (-1) * kP1_8 a b g * sd1_1 a b g + (1) * fd12_0 a b g * kD1_1 a b g * kR1_3 a b g ^(2:ℕ) + (-1) * fd11_0 a b g * kR1_3 a b g * kD1_2 a b g ^(2:ℕ) + (-1) * fd11_1 a b g * kR1_3 a b g * kD1_1 a b g ^(2:ℕ) + (-1) * fd11_2 a b g * kR1_1 a b g * kD1_1 a b g ^(2:ℕ) + (3) * fd10_0 a b g * kD1_1 a b g * kD1_2 a b g ^(2:ℕ) + (3) * fd10_1 a b g * kD1_2 a b g * kD1_1 a b g ^(2:ℕ) + (3) * fd10_3 a b g * kD1_0 a b g * kD1_2 a b g ^(2:ℕ) + (-6) * fd13_0 a b g * kR1_0 a b g * kR1_1 a b g * kR1_6 a b g + (-6) * fd13_0 a b g * kR1_0 a b g * kR1_3 a b g * kR1_5 a b g + (-2) * fd11_0 a b g * kD1_1 a b g * kD1_2 a b g * kR1_4 a b g + (-2) * fd11_0 a b g * kD1_1 a b g * kD1_3 a b g * kR1_2 a b g + (-2) * fd11_0 a b g * kD1_2 a b g * kD1_3 a b g * kR1_1 a b g + (-2) * fd11_1 a b g * kD1_0 a b g * kD1_1 a b g * kR1_5 a b g + (-2) * fd11_1 a b g * kD1_0 a b g * kD1_3 a b g * kR1_3 a b g + (-2) * fd11_1 a b g * kD1_1 a b g * kD1_3 a b g * kR1_0 a b g + (-2) * fd11_2 a b g * kD1_0 a b g * kD1_1 a b g * kR1_4 a b g + (-2) * fd11_2 a b g * kD1_0 a b g * kD1_2 a b g * kR1_3 a b g + (-2) * fd11_2 a b g * kD1_0 a b g * kD1_3 a b g * kR1_1 a b g + (-2) * fd11_2 a b g * kD1_1 a b g * kD1_2 a b g * kR1_0 a b g + (-2) * fd11_3 a b g * kD1_0 a b g * kD1_1 a b g * kR1_2 a b g + (-2) * fd11_3 a b g * kD1_0 a b g * kD1_2 a b g * kR1_1 a b g + (2) * fd12_0 a b g * kD1_0 a b g * kR1_1 a b g * kR1_6 a b g + (2) * fd12_0 a b g * kD1_0 a b g * kR1_3 a b g * kR1_5 a b g + (2) * fd12_0 a b g * kD1_1 a b g * kR1_0 a b g * kR1_5 a b g + (2) * fd12_0 a b g * kD1_3 a b g * kR1_0 a b g * kR1_3 a b g + (6) * fd10_1 a b g * kD1_0 a b g * kD1_2 a b g * kD1_3 a b g + (6) * fd10_2 a b g * kD1_0 a b g * kD1_1 a b g * kD1_3 a b g + (6) * fd10_4 a b g * kD1_0 a b g * kD1_1 a b g * kD1_2 a b g

noncomputable def E1_28 (a b g : K) : K :=
  (-5) * cd1_1_12 a b g + (1) * fd10_0 a b g * kD1_2 a b g ^(3:ℕ) + (-1) * kP1_2 a b g * sd1_3 a b g + (-1) * kP1_5 a b g * sd1_2 a b g + (-1) * kP1_9 a b g * sd1_1 a b g + (1) * fd12_0 a b g * kD1_2 a b g * kR1_3 a b g ^(2:ℕ) + (-1) * fd11_0 a b g * kR1_4 a b g * kD1_2 a b g ^(2:ℕ) + (-1) * fd11_1 a b g * kR1_4 a b g * kD1_1 a b g ^(2:ℕ) + (-1) * fd11_2 a b g * kR1_0 a b g * kD1_2 a b g ^(2:ℕ) + (-1) * fd11_2 a b g * kR1_2 a b g * kD1_1 a b g ^(2:ℕ) + (-3) * fd13_0 a b g * kR1_4 a b g * kR1_3 a b g ^(2:ℕ) + (-3) * fd13_0 a b g * kR1_6 a b g * kR1_1 a b g ^(2:ℕ) + (3) * fd10_1 a b g * kD1_1 a b g * kD1_2 a b g ^(2:ℕ) + (3) * fd10_2 a b g * kD1_2 a b g * kD1_1 a b g ^(2:ℕ) + (3) * fd10_4 a b g * kD1_0 a b g * kD1_2 a b g ^(2:ℕ) + (-6) * fd13_0 a b g * kR1_0 a b g * kR1_2 a b g * kR1_6 a b g + (-6) * fd13_0 a b g * kR1_0 a b g * kR1_4 a b g * kR1_5 a b g + (-6) * fd13_0 a b g * kR1_1 a b g * kR1_3 a b g * kR1_5 a b g + (-2) * fd11_0 a b g * kD1_2 a b g * kD1_3 a b g * kR1_2 a b g + (-2) * fd11_1 a b g * kD1_0 a b g * kD1_2 a b g * kR1_5 a b g + (-2) * fd11_1 a b g * kD1_0 a b g * kD1_3 a b g * kR1_4 a b g + (-2) * fd11_1 a b g * kD1_1 a b g * kD1_2 a b g * kR1_3 a b g + (-2) * fd11_1 a b g * kD1_1 a b g * kD1_3 a b g * kR1_1 a b g + (-2) * fd11_1 a b g * kD1_2 a b g * kD1_3 a b g * kR1_0 a b g + (-2) * fd11_2 a b g * kD1_0 a b g * kD1_2 a b g * kR1_4 a b g + (-2) * fd11_2 a b g * kD1_0 a b g * kD1_3 a b g * kR1_2 a b g + (-2) * fd11_2 a b g * kD1_1 a b g * kD1_2 a b g * kR1_1 a b g + (-2) * fd11_3 a b g * kD1_0 a b g * kD1_2 a b g * kR1_2 a b g + (2) * fd12_0 a b g * kD1_0 a b g * kR1_2 a b g * kR1_6 a b g + (2) * fd12_0 a b g * kD1_0 a b g * kR1_4 a b g * kR1_5 a b g + (2) * fd12_0 a b g * kD1_1 a b g * kR1_1 a b g * kR1_5 a b g + (2) * fd12_0 a b g * kD1_1 a b g * kR1_3 a b g * kR1_4 a b g + (2) * fd12_0 a b g * kD1_2 a b g * kR1_0 a b g * kR1_5 a b g + (2) * fd12_0 a b g * kD1_3 a b g * kR1_0 a b g * kR1_4 a b g + (2) * fd12_0 a b g * kD1_3 a b g * kR1_1 a b g * kR1_3 a b g + (6) * fd10_2 a b g * kD1_0 a b g * kD1_2 a b g * kD1_3 a b g

end Work.MotC5N3.CertDemo
