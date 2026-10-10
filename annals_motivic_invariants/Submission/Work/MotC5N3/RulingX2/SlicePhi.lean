import Submission.Work.MotC5N3.RulingX2.SliceD.All

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

/-- The monic quadratic `Phi = X0^2 + alpha X0 + beta` in `J_1` (from the AS `zE` relation). -/
noncomputable def PhiAlpha (a b g : K) : MvPolynomial (Fin 2) K :=
  C ((2 : K) * a ^(5:ℕ) * g * (2 * (a - 3 * b) ^(5:ℕ))⁻¹) + C ((2 : K) * a ^(5:ℕ) * (2 * (a - 3 * b) ^(5:ℕ))⁻¹) + C ((2 : K) * a ^(4:ℕ) * b * (2 * (a - 3 * b) ^(5:ℕ))⁻¹) * X 1 ^(1:ℕ) + C ((2 : K) * a ^(4:ℕ) * b * (2 * (a - 3 * b) ^(5:ℕ))⁻¹) + C ((2 : K) * a ^(3:ℕ) * b ^(2:ℕ) * (2 * (a - 3 * b) ^(5:ℕ))⁻¹) * X 1 ^(1:ℕ) + C (a ^(3:ℕ) * b ^(2:ℕ) * (2 * (a - 3 * b) ^(5:ℕ))⁻¹) + C ((4 : K) * a ^(2:ℕ) * b ^(3:ℕ) * (2 * (a - 3 * b) ^(5:ℕ))⁻¹) * X 1 ^(1:ℕ) + C ((3 : K) * a ^(2:ℕ) * b ^(3:ℕ) * (2 * (a - 3 * b) ^(5:ℕ))⁻¹) + C (a * b ^(4:ℕ) * (2 * (a - 3 * b) ^(5:ℕ))⁻¹) * X 1 ^(1:ℕ) + C ((4 : K) * a * b ^(4:ℕ) * (2 * (a - 3 * b) ^(5:ℕ))⁻¹) + C ((4 : K) * b ^(5:ℕ) * g * (2 * (a - 3 * b) ^(5:ℕ))⁻¹) + C (b ^(5:ℕ) * (2 * (a - 3 * b) ^(5:ℕ))⁻¹)

noncomputable def PhiBeta (a b g : K) : MvPolynomial (Fin 2) K :=
  C ((2 : K) * a ^(5:ℕ) * g * (2 * (a - 3 * b) ^(5:ℕ))⁻¹) * X 1 ^(2:ℕ) + C ((3 : K) * a ^(5:ℕ) * g * (2 * (a - 3 * b) ^(5:ℕ))⁻¹) + C ((3 : K) * a ^(5:ℕ) * (2 * (a - 3 * b) ^(5:ℕ))⁻¹) * X 1 ^(2:ℕ) + C ((2 : K) * a ^(5:ℕ) * (2 * (a - 3 * b) ^(5:ℕ))⁻¹) * X 1 ^(1:ℕ) + C (a ^(5:ℕ) * (2 * (a - 3 * b) ^(5:ℕ))⁻¹) + C ((3 : K) * a ^(4:ℕ) * b * g * (2 * (a - 3 * b) ^(5:ℕ))⁻¹) + C ((3 : K) * a ^(4:ℕ) * b * (2 * (a - 3 * b) ^(5:ℕ))⁻¹) * X 1 ^(2:ℕ) + C ((4 : K) * a ^(4:ℕ) * b * (2 * (a - 3 * b) ^(5:ℕ))⁻¹) * X 1 ^(1:ℕ) + C ((2 : K) * a ^(4:ℕ) * b * (2 * (a - 3 * b) ^(5:ℕ))⁻¹) + C ((4 : K) * a ^(3:ℕ) * b ^(2:ℕ) * g * (2 * (a - 3 * b) ^(5:ℕ))⁻¹) + C ((4 : K) * a ^(3:ℕ) * b ^(2:ℕ) * (2 * (a - 3 * b) ^(5:ℕ))⁻¹) * X 1 ^(2:ℕ) + C ((3 : K) * a ^(3:ℕ) * b ^(2:ℕ) * (2 * (a - 3 * b) ^(5:ℕ))⁻¹) * X 1 ^(1:ℕ) + C ((2 : K) * a ^(3:ℕ) * b ^(2:ℕ) * (2 * (a - 3 * b) ^(5:ℕ))⁻¹) + C ((2 : K) * a ^(2:ℕ) * b ^(3:ℕ) * g * (2 * (a - 3 * b) ^(5:ℕ))⁻¹) + C ((2 : K) * a ^(2:ℕ) * b ^(3:ℕ) * (2 * (a - 3 * b) ^(5:ℕ))⁻¹) * X 1 ^(2:ℕ) + C ((4 : K) * a ^(2:ℕ) * b ^(3:ℕ) * (2 * (a - 3 * b) ^(5:ℕ))⁻¹) * X 1 ^(1:ℕ) + C ((4 : K) * a ^(2:ℕ) * b ^(3:ℕ) * (2 * (a - 3 * b) ^(5:ℕ))⁻¹) + C (a * b ^(4:ℕ) * g * (2 * (a - 3 * b) ^(5:ℕ))⁻¹) + C (a * b ^(4:ℕ) * (2 * (a - 3 * b) ^(5:ℕ))⁻¹) * X 1 ^(2:ℕ) + C ((3 : K) * a * b ^(4:ℕ) * (2 * (a - 3 * b) ^(5:ℕ))⁻¹) * X 1 ^(1:ℕ) + C (a * b ^(4:ℕ) * (2 * (a - 3 * b) ^(5:ℕ))⁻¹) + C ((4 : K) * b ^(5:ℕ) * g * (2 * (a - 3 * b) ^(5:ℕ))⁻¹) * X 1 ^(2:ℕ) + C ((4 : K) * b ^(5:ℕ) * g * (2 * (a - 3 * b) ^(5:ℕ))⁻¹) + C ((4 : K) * b ^(5:ℕ) * (2 * (a - 3 * b) ^(5:ℕ))⁻¹) * X 1 ^(2:ℕ) + C ((4 : K) * b ^(5:ℕ) * (2 * (a - 3 * b) ^(5:ℕ))⁻¹) * X 1 ^(1:ℕ) + C ((2 : K) * b ^(5:ℕ) * (2 * (a - 3 * b) ^(5:ℕ))⁻¹)

/-- `Phi` itself, monic in `X 0`. -/
noncomputable def Phisq (a b g : K) : MvPolynomial (Fin 2) K :=
  X 0 ^(2:ℕ) + PhiAlpha a b g * X 0 + PhiBeta a b g

/-- The graph element `Gamma = Dhat * X 0 + Rhat`. -/
noncomputable def Gam (a b g : K) : MvPolynomial (Fin 2) K :=
  Dhat a b g * X 0 + Rhat a b g

/-- `Phat` as a polynomial (same as `Slice.Phat`). -/
noncomputable def PhatPoly (a b g : K) : MvPolynomial (Fin 2) K := Phat a b g

/-- The five slice cubics as a `Fin 5`-indexed family. -/
noncomputable def fhatF (a b g : K) : Fin 5 → MvPolynomial (Fin 2) K :=
  ![fhat0 a b g, fhat1 a b g, fhat2 a b g, fhat3 a b g, fhat4 a b g]


end Work.MotC5N3.RulingX2.Slice
