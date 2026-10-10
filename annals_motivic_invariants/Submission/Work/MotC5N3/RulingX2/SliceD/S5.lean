import Mathlib

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

namespace Work.MotC5N3.RulingX2.Slice

open MvPolynomial

variable {K : Type*} [Field K] [CharP K 5]

noncomputable def What4_p0 (a b g : K) : MvPolynomial (Fin 2) K :=
  C ((2 : K) * a ^(10:ℕ) * g) * X 0 * X 1 ^(2:ℕ) + C ((3 : K) * a ^(10:ℕ) * g) * X 1 ^(4:ℕ) + C (a ^(10:ℕ) * g) * X 1 ^(2:ℕ) + C ((3 : K) * a ^(10:ℕ) * g) * X 1 + C ((3 : K) * a ^(10:ℕ)) * X 0 * X 1 ^(2:ℕ) + C (a ^(10:ℕ)) * X 0 * X 1 + C ((2 : K) * a ^(10:ℕ)) * X 1 ^(2:ℕ) + C (a ^(10:ℕ)) * X 1 + C ((2 : K) * a ^(10:ℕ)) + C (a ^(9:ℕ) * b * g) * X 1 ^(2:ℕ) + C ((2 : K) * a ^(9:ℕ) * b) * X 0 * X 1 ^(3:ℕ) + C ((3 : K) * a ^(9:ℕ) * b) * X 0 * X 1 ^(2:ℕ) + C ((4 : K) * a ^(9:ℕ) * b) * X 1 ^(2:ℕ) + C (a ^(9:ℕ) * b) * X 1 + C ((3 : K) * a ^(8:ℕ) * b ^(2:ℕ) * g) * X 1 ^(2:ℕ) + C ((2 : K) * a ^(8:ℕ) * b ^(2:ℕ)) * X 0 * X 1 ^(3:ℕ) + C ((4 : K) * a ^(8:ℕ) * b ^(2:ℕ)) * X 0 * X 1 ^(2:ℕ) + C ((4 : K) * a ^(8:ℕ) * b ^(2:ℕ)) * X 1 ^(2:ℕ) + C ((3 : K) * a ^(8:ℕ) * b ^(2:ℕ)) * X 1 + C ((4 : K) * a ^(7:ℕ) * b ^(3:ℕ) * g) * X 1 ^(2:ℕ) + C ((4 : K) * a ^(7:ℕ) * b ^(3:ℕ)) * X 0 * X 1 ^(3:ℕ) + C ((2 : K) * a ^(7:ℕ) * b ^(3:ℕ)) * X 0 * X 1 ^(2:ℕ) + C ((3 : K) * a ^(7:ℕ) * b ^(3:ℕ)) * X 1 ^(2:ℕ) + C ((4 : K) * a ^(7:ℕ) * b ^(3:ℕ)) * X 1 + C ((2 : K) * a ^(6:ℕ) * b ^(4:ℕ) * g) * X 1 ^(2:ℕ) + C (a ^(6:ℕ) * b ^(4:ℕ)) * X 0 * X 1 ^(3:ℕ) + C (a ^(6:ℕ) * b ^(4:ℕ)) * X 0 * X 1 ^(2:ℕ) + C ((2 : K) * a ^(6:ℕ) * b ^(4:ℕ)) * X 1 ^(2:ℕ) + C ((2 : K) * a ^(6:ℕ) * b ^(4:ℕ)) * X 1 + C ((3 : K) * a ^(5:ℕ) * b ^(5:ℕ) * g) * X 0 * X 1 ^(2:ℕ) + C ((2 : K) * a ^(5:ℕ) * b ^(5:ℕ) * g) * X 1 ^(4:ℕ) + C ((2 : K) * a ^(5:ℕ) * b ^(5:ℕ) * g) * X 1 + C ((4 : K) * a ^(5:ℕ) * b ^(5:ℕ)) * X 0 * X 1 + C ((3 : K) * a ^(5:ℕ) * b ^(5:ℕ)) * X 1 ^(2:ℕ) + C ((3 : K) * a ^(5:ℕ) * b ^(5:ℕ)) + C ((2 : K) * a ^(4:ℕ) * b ^(6:ℕ) * g) * X 1 ^(2:ℕ) + C ((4 : K) * a ^(4:ℕ) * b ^(6:ℕ)) * X 0 * X 1 ^(3:ℕ) + C (a ^(4:ℕ) * b ^(6:ℕ)) * X 0 * X 1 ^(2:ℕ) + C ((3 : K) * a ^(4:ℕ) * b ^(6:ℕ)) * X 1 ^(2:ℕ) + C ((2 : K) * a ^(4:ℕ) * b ^(6:ℕ)) * X 1
noncomputable def What4_p1 (a b g : K) : MvPolynomial (Fin 2) K :=
  C (a ^(3:ℕ) * b ^(7:ℕ) * g) * X 1 ^(2:ℕ) + C ((4 : K) * a ^(3:ℕ) * b ^(7:ℕ)) * X 0 * X 1 ^(3:ℕ) + C ((3 : K) * a ^(3:ℕ) * b ^(7:ℕ)) * X 0 * X 1 ^(2:ℕ) + C ((3 : K) * a ^(3:ℕ) * b ^(7:ℕ)) * X 1 ^(2:ℕ) + C (a ^(3:ℕ) * b ^(7:ℕ)) * X 1 + C ((3 : K) * a ^(2:ℕ) * b ^(8:ℕ) * g) * X 1 ^(2:ℕ) + C ((3 : K) * a ^(2:ℕ) * b ^(8:ℕ)) * X 0 * X 1 ^(3:ℕ) + C ((4 : K) * a ^(2:ℕ) * b ^(8:ℕ)) * X 0 * X 1 ^(2:ℕ) + C (a ^(2:ℕ) * b ^(8:ℕ)) * X 1 ^(2:ℕ) + C ((3 : K) * a ^(2:ℕ) * b ^(8:ℕ)) * X 1 + C ((4 : K) * a * b ^(9:ℕ) * g) * X 1 ^(2:ℕ) + C ((2 : K) * a * b ^(9:ℕ)) * X 0 * X 1 ^(3:ℕ) + C ((2 : K) * a * b ^(9:ℕ)) * X 0 * X 1 ^(2:ℕ) + C ((4 : K) * a * b ^(9:ℕ)) * X 1 ^(2:ℕ) + C ((4 : K) * a * b ^(9:ℕ)) * X 1 + C ((3 : K) * b ^(10:ℕ) * g) * X 0 * X 1 ^(2:ℕ) + C ((2 : K) * b ^(10:ℕ) * g) * X 1 ^(4:ℕ) + C (b ^(10:ℕ) * g) * X 1 ^(2:ℕ) + C ((2 : K) * b ^(10:ℕ) * g) * X 1 + C ((3 : K) * b ^(10:ℕ)) * X 0 * X 1 ^(2:ℕ) + C ((4 : K) * b ^(10:ℕ)) * X 0 * X 1 + C ((3 : K) * b ^(10:ℕ)) * X 1 ^(2:ℕ) + C (b ^(10:ℕ)) * X 1 + C ((3 : K) * b ^(10:ℕ))
noncomputable def What4 (a b g : K) : MvPolynomial (Fin 2) K :=
  What4_p0 a b g + What4_p1 a b g

end Work.MotC5N3.RulingX2.Slice
