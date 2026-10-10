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

noncomputable def fd30_0 (a b g : K) : K :=
  (2)*a^(4:ℕ) + (1)*a^(3:ℕ)*b^(1:ℕ) + (-2)*a^(2:ℕ)*b^(2:ℕ) + (-1)*a^(1:ℕ)*b^(3:ℕ) + (2)*b^(4:ℕ)

noncomputable def fd30_1 (a b g : K) : K :=
  (1)*a^(4:ℕ) + (-2)*a^(3:ℕ)*b^(1:ℕ) + (-2)*a^(1:ℕ)*b^(3:ℕ) + (-1)*b^(4:ℕ)

noncomputable def fd30_2 (a b g : K) : K :=
  (-1)*a^(4:ℕ) + (1)*a^(3:ℕ)*b^(1:ℕ) + (1)*a^(1:ℕ)*b^(3:ℕ) + (1)*b^(4:ℕ)

noncomputable def fd30_3 (a b g : K) : K :=
  (2)*a^(4:ℕ)*g^(1:ℕ) + (1)*a^(3:ℕ)*b^(1:ℕ)*g^(1:ℕ) + (-2)*a^(2:ℕ)*b^(2:ℕ)*g^(1:ℕ) + (-1)*a^(1:ℕ)*b^(3:ℕ)*g^(1:ℕ) + (2)*b^(4:ℕ)*g^(1:ℕ)

noncomputable def fd30_4 (a b g : K) : K :=
  (-1)*a^(4:ℕ) + (-2)*a^(2:ℕ)*b^(2:ℕ) + (-1)*b^(4:ℕ)

noncomputable def f30 (a b g : K) : MvPolynomial (Fin 3) K :=
  C (fd30_0 a b g) * X 2
  + C (fd30_1 a b g) * X 2^(3:ℕ)
  + C (fd30_2 a b g) * X 1 * X 2
  + C (fd30_3 a b g) * X 1 * X 2^(2:ℕ)
  + C (fd30_4 a b g) * X 1^(2:ℕ) * X 2

noncomputable def fd31_0 (a b g : K) : K :=
  (1)*a^(4:ℕ) + (-1)*a^(3:ℕ)*b^(1:ℕ) + (-2)*a^(2:ℕ)*b^(2:ℕ) + (1)*a^(1:ℕ)*b^(3:ℕ) + (1)*b^(4:ℕ)

noncomputable def fd31_1 (a b g : K) : K :=
  (-1)*a^(4:ℕ) + (2)*a^(3:ℕ)*b^(1:ℕ) + (1)*a^(2:ℕ)*b^(2:ℕ) + (-2)*a^(1:ℕ)*b^(3:ℕ) + (-1)*b^(4:ℕ)

noncomputable def fd31_2 (a b g : K) : K :=
  (1)*a^(4:ℕ) + (-1)*a^(3:ℕ)*b^(1:ℕ) + (-1)*a^(1:ℕ)*b^(3:ℕ) + (-1)*b^(4:ℕ)

noncomputable def f31 (a b g : K) : MvPolynomial (Fin 3) K :=
  C (fd31_0 a b g) * X 2^(2:ℕ)
  + C (fd31_1 a b g) * X 1
  + C (fd31_2 a b g) * X 1^(2:ℕ)

noncomputable def fd32_0 (a b g : K) : K :=
  (-1)*a^(4:ℕ) + (1)*a^(3:ℕ)*b^(1:ℕ) + (1)*a^(1:ℕ)*b^(3:ℕ) + (1)*b^(4:ℕ)

noncomputable def f32 (a b g : K) : MvPolynomial (Fin 3) K :=
  C (fd32_0 a b g) * X 2

noncomputable def fd33_0 (a b g : K) : K :=
  (-1)*a^(4:ℕ) + (2)*a^(3:ℕ)*b^(1:ℕ) + (1)*a^(2:ℕ)*b^(2:ℕ) + (-2)*a^(1:ℕ)*b^(3:ℕ) + (-1)*b^(4:ℕ)

noncomputable def f33 (a b g : K) : MvPolynomial (Fin 3) K :=
  C (fd33_0 a b g)

noncomputable def sd3_0 (a b g : K) : K :=
  (1)*a^(17:ℕ) + (-1)*a^(16:ℕ)*b^(1:ℕ) + (-1)*a^(15:ℕ)*b^(2:ℕ) + (1)*a^(12:ℕ)*b^(5:ℕ) + (-1)*a^(11:ℕ)*b^(6:ℕ) + (-1)*a^(10:ℕ)*b^(7:ℕ) + (2)*a^(7:ℕ)*b^(10:ℕ) + (-2)*a^(6:ℕ)*b^(11:ℕ) + (-2)*a^(5:ℕ)*b^(12:ℕ) + (-2)*a^(2:ℕ)*b^(15:ℕ) + (2)*a^(1:ℕ)*b^(16:ℕ) + (2)*b^(17:ℕ)

noncomputable def sd3_1 (a b g : K) : K :=
  (2)*a^(17:ℕ) + (2)*a^(15:ℕ)*b^(2:ℕ) + (2)*a^(12:ℕ)*b^(5:ℕ) + (2)*a^(10:ℕ)*b^(7:ℕ) + (-1)*a^(7:ℕ)*b^(10:ℕ) + (-1)*a^(5:ℕ)*b^(12:ℕ) + (1)*a^(2:ℕ)*b^(15:ℕ) + (1)*b^(17:ℕ)

noncomputable def sd3_2 (a b g : K) : K :=
  (1)*a^(17:ℕ) + (-1)*a^(15:ℕ)*b^(2:ℕ) + (1)*a^(12:ℕ)*b^(5:ℕ) + (-1)*a^(10:ℕ)*b^(7:ℕ) + (2)*a^(7:ℕ)*b^(10:ℕ) + (-2)*a^(5:ℕ)*b^(12:ℕ) + (-2)*a^(2:ℕ)*b^(15:ℕ) + (2)*b^(17:ℕ)

noncomputable def sd3_3 (a b g : K) : K :=
  (-2)*a^(16:ℕ)*b^(1:ℕ) + (-2)*a^(15:ℕ)*b^(2:ℕ) + (-1)*a^(14:ℕ)*b^(3:ℕ) + (2)*a^(13:ℕ)*b^(4:ℕ) + (1)*a^(12:ℕ)*b^(5:ℕ) + (1)*a^(11:ℕ)*b^(6:ℕ) + (2)*a^(10:ℕ)*b^(7:ℕ) + (1)*a^(9:ℕ)*b^(8:ℕ) + (-2)*a^(8:ℕ)*b^(9:ℕ) + (-1)*a^(7:ℕ)*b^(10:ℕ) + (-2)*a^(6:ℕ)*b^(11:ℕ) + (2)*a^(5:ℕ)*b^(12:ℕ) + (1)*a^(4:ℕ)*b^(13:ℕ) + (-2)*a^(3:ℕ)*b^(14:ℕ) + (-1)*a^(2:ℕ)*b^(15:ℕ) + (1)*a^(1:ℕ)*b^(16:ℕ)

noncomputable def sd3_4 (a b g : K) : K :=
  (1)*a^(17:ℕ)*g^(1:ℕ) + (-1)*a^(16:ℕ)*b^(1:ℕ)*g^(1:ℕ) + (-1)*a^(15:ℕ)*b^(2:ℕ)*g^(1:ℕ) + (1)*a^(12:ℕ)*b^(5:ℕ)*g^(1:ℕ) + (-1)*a^(11:ℕ)*b^(6:ℕ)*g^(1:ℕ) + (-1)*a^(10:ℕ)*b^(7:ℕ)*g^(1:ℕ) + (2)*a^(7:ℕ)*b^(10:ℕ)*g^(1:ℕ) + (-2)*a^(6:ℕ)*b^(11:ℕ)*g^(1:ℕ) + (-2)*a^(5:ℕ)*b^(12:ℕ)*g^(1:ℕ) + (-2)*a^(2:ℕ)*b^(15:ℕ)*g^(1:ℕ) + (2)*a^(1:ℕ)*b^(16:ℕ)*g^(1:ℕ) + (2)*b^(17:ℕ)*g^(1:ℕ)

noncomputable def S3 (a b g : K) : MvPolynomial (Fin 3) K :=
  C (sd3_0 a b g) * X 2
  + C (sd3_1 a b g) * X 1 * X 2
  + C (sd3_2 a b g) * X 1^(2:ℕ) * X 2
  + C (sd3_3 a b g) * X 1^(3:ℕ) * X 2
  + C (sd3_4 a b g) * X 1^(4:ℕ)

end Work.MotC5N3
