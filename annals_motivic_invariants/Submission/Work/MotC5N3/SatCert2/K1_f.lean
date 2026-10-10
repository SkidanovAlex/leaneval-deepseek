import Mathlib
import Submission.Work.MotC5N3.X2AuxInputs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false

namespace Work.MotC5N3
open MvPolynomial

variable {K : Type} [Field K] [CharP K 5]

noncomputable def fd10_0 (a b g : K) : K :=
  (1)*a^(4:ℕ) + (-1)*a^(3:ℕ)*b^(1:ℕ) + (-1)*a^(1:ℕ)*b^(3:ℕ) + (-1)*b^(4:ℕ)

noncomputable def fd10_1 (a b g : K) : K :=
  (2)*a^(4:ℕ)*g^(1:ℕ) + (1)*a^(3:ℕ)*b^(1:ℕ)*g^(1:ℕ) + (-2)*a^(2:ℕ)*b^(2:ℕ)*g^(1:ℕ) + (-1)*a^(1:ℕ)*b^(3:ℕ)*g^(1:ℕ) + (2)*b^(4:ℕ)*g^(1:ℕ)

noncomputable def fd10_2 (a b g : K) : K :=
  (1)*a^(4:ℕ) + (-1)*a^(3:ℕ)*b^(1:ℕ) + (1)*a^(2:ℕ)*b^(2:ℕ) + (1)*a^(1:ℕ)*b^(3:ℕ) + (1)*b^(4:ℕ)

noncomputable def fd10_3 (a b g : K) : K :=
  (2)*a^(4:ℕ) + (-2)*a^(3:ℕ)*b^(1:ℕ) + (1)*a^(2:ℕ)*b^(2:ℕ) + (2)*a^(1:ℕ)*b^(3:ℕ) + (2)*b^(4:ℕ)

noncomputable def fd10_4 (a b g : K) : K :=
  (-2)*a^(4:ℕ)*g^(1:ℕ) + (2)*a^(3:ℕ)*b^(1:ℕ)*g^(1:ℕ) + (2)*a^(1:ℕ)*b^(3:ℕ)*g^(1:ℕ) + (2)*b^(4:ℕ)*g^(1:ℕ)

noncomputable def fd10_5 (a b g : K) : K :=
  (-1)*a^(4:ℕ) + (2)*a^(3:ℕ)*b^(1:ℕ) + (2)*a^(1:ℕ)*b^(3:ℕ) + (1)*b^(4:ℕ)

noncomputable def fd10_6 (a b g : K) : K :=
  (-1)*a^(4:ℕ)*g^(1:ℕ) + (2)*a^(3:ℕ)*b^(1:ℕ)*g^(1:ℕ) + (1)*a^(2:ℕ)*b^(2:ℕ)*g^(1:ℕ) + (-2)*a^(1:ℕ)*b^(3:ℕ)*g^(1:ℕ) + (-1)*b^(4:ℕ)*g^(1:ℕ)

noncomputable def f10 (a b g : K) : MvPolynomial (Fin 3) K :=
  C (fd10_0 a b g) * X 2
  + C (fd10_1 a b g) * X 2^(2:ℕ)
  + C (fd10_2 a b g) * X 2^(3:ℕ)
  + C (fd10_3 a b g) * X 1 * X 2
  + C (fd10_4 a b g) * X 1 * X 2^(2:ℕ)
  + C (fd10_5 a b g) * X 1^(2:ℕ) * X 2
  + C (fd10_6 a b g) * X 1^(3:ℕ)

noncomputable def fd11_0 (a b g : K) : K :=
  (2)*a^(4:ℕ) + (1)*a^(3:ℕ)*b^(1:ℕ) + (-2)*a^(2:ℕ)*b^(2:ℕ) + (-1)*a^(1:ℕ)*b^(3:ℕ) + (2)*b^(4:ℕ)

noncomputable def fd11_1 (a b g : K) : K :=
  (1)*a^(4:ℕ) + (-1)*b^(4:ℕ)

noncomputable def fd11_2 (a b g : K) : K :=
  (-1)*a^(4:ℕ)*g^(1:ℕ) + (2)*a^(3:ℕ)*b^(1:ℕ)*g^(1:ℕ) + (1)*a^(2:ℕ)*b^(2:ℕ)*g^(1:ℕ) + (-2)*a^(1:ℕ)*b^(3:ℕ)*g^(1:ℕ) + (-1)*b^(4:ℕ)*g^(1:ℕ)

noncomputable def fd11_3 (a b g : K) : K :=
  (1)*a^(4:ℕ) + (-1)*a^(3:ℕ)*b^(1:ℕ) + (-2)*a^(2:ℕ)*b^(2:ℕ) + (1)*a^(1:ℕ)*b^(3:ℕ) + (1)*b^(4:ℕ)

noncomputable def f11 (a b g : K) : MvPolynomial (Fin 3) K :=
  C (fd11_0 a b g)
  + C (fd11_1 a b g) * X 2^(2:ℕ)
  + C (fd11_2 a b g) * X 1 * X 2
  + C (fd11_3 a b g) * X 1^(2:ℕ)

noncomputable def fd12_0 (a b g : K) : K :=
  (-1)*a^(4:ℕ) + (-2)*a^(2:ℕ)*b^(2:ℕ) + (-1)*b^(4:ℕ)

noncomputable def f12 (a b g : K) : MvPolynomial (Fin 3) K :=
  C (fd12_0 a b g) * X 2

noncomputable def fd13_0 (a b g : K) : K :=
  (-1)*a^(4:ℕ) + (1)*a^(3:ℕ)*b^(1:ℕ) + (1)*a^(1:ℕ)*b^(3:ℕ) + (1)*b^(4:ℕ)

noncomputable def f13 (a b g : K) : MvPolynomial (Fin 3) K :=
  C (fd13_0 a b g)

noncomputable def sd1_0 (a b g : K) : K :=
  (1)*a^(17:ℕ) + (1)*a^(15:ℕ)*b^(2:ℕ) + (1)*a^(12:ℕ)*b^(5:ℕ) + (1)*a^(10:ℕ)*b^(7:ℕ) + (2)*a^(7:ℕ)*b^(10:ℕ) + (2)*a^(5:ℕ)*b^(12:ℕ) + (-2)*a^(2:ℕ)*b^(15:ℕ) + (-2)*b^(17:ℕ)

noncomputable def sd1_1 (a b g : K) : K :=
  (2)*a^(17:ℕ) + (2)*a^(16:ℕ)*b^(1:ℕ) + (-2)*a^(15:ℕ)*b^(2:ℕ) + (2)*a^(12:ℕ)*b^(5:ℕ) + (2)*a^(11:ℕ)*b^(6:ℕ) + (-2)*a^(10:ℕ)*b^(7:ℕ) + (-1)*a^(7:ℕ)*b^(10:ℕ) + (-1)*a^(6:ℕ)*b^(11:ℕ) + (1)*a^(5:ℕ)*b^(12:ℕ) + (1)*a^(2:ℕ)*b^(15:ℕ) + (1)*a^(1:ℕ)*b^(16:ℕ) + (-1)*b^(17:ℕ)

noncomputable def sd1_2 (a b g : K) : K :=
  (1)*a^(17:ℕ) + (1)*a^(16:ℕ)*b^(1:ℕ) + (2)*a^(15:ℕ)*b^(2:ℕ) + (-2)*a^(14:ℕ)*b^(3:ℕ) + (-1)*a^(13:ℕ)*b^(4:ℕ) + (-2)*a^(12:ℕ)*b^(5:ℕ) + (2)*a^(11:ℕ)*b^(6:ℕ) + (2)*a^(9:ℕ)*b^(8:ℕ) + (1)*a^(8:ℕ)*b^(9:ℕ) + (1)*a^(6:ℕ)*b^(11:ℕ) + (1)*a^(5:ℕ)*b^(12:ℕ) + (2)*a^(4:ℕ)*b^(13:ℕ) + (1)*a^(3:ℕ)*b^(14:ℕ) + (1)*a^(2:ℕ)*b^(15:ℕ) + (2)*a^(1:ℕ)*b^(16:ℕ) + (-2)*b^(17:ℕ)

noncomputable def sd1_3 (a b g : K) : K :=
  (-2)*a^(16:ℕ)*b^(1:ℕ) + (1)*a^(15:ℕ)*b^(2:ℕ) + (1)*a^(14:ℕ)*b^(3:ℕ) + (2)*a^(13:ℕ)*b^(4:ℕ) + (-2)*a^(12:ℕ)*b^(5:ℕ) + (-2)*a^(11:ℕ)*b^(6:ℕ) + (-1)*a^(10:ℕ)*b^(7:ℕ) + (-1)*a^(9:ℕ)*b^(8:ℕ) + (-2)*a^(8:ℕ)*b^(9:ℕ) + (2)*a^(7:ℕ)*b^(10:ℕ) + (1)*a^(6:ℕ)*b^(11:ℕ) + (-1)*a^(5:ℕ)*b^(12:ℕ) + (-1)*a^(4:ℕ)*b^(13:ℕ) + (-2)*a^(3:ℕ)*b^(14:ℕ) + (2)*a^(2:ℕ)*b^(15:ℕ) + (-1)*a^(1:ℕ)*b^(16:ℕ)

noncomputable def sd1_4 (a b g : K) : K :=
  (1)*a^(17:ℕ)*g^(1:ℕ) + (1)*a^(15:ℕ)*b^(2:ℕ)*g^(1:ℕ) + (1)*a^(12:ℕ)*b^(5:ℕ)*g^(1:ℕ) + (1)*a^(10:ℕ)*b^(7:ℕ)*g^(1:ℕ) + (2)*a^(7:ℕ)*b^(10:ℕ)*g^(1:ℕ) + (2)*a^(5:ℕ)*b^(12:ℕ)*g^(1:ℕ) + (-2)*a^(2:ℕ)*b^(15:ℕ)*g^(1:ℕ) + (-2)*b^(17:ℕ)*g^(1:ℕ)

noncomputable def S1 (a b g : K) : MvPolynomial (Fin 3) K :=
  C (sd1_0 a b g) * X 2
  + C (sd1_1 a b g) * X 1 * X 2
  + C (sd1_2 a b g) * X 1^(2:ℕ) * X 2
  + C (sd1_3 a b g) * X 1^(3:ℕ) * X 2
  + C (sd1_4 a b g) * X 1^(4:ℕ)

end Work.MotC5N3
