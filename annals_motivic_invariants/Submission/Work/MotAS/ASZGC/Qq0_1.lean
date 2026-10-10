import Mathlib

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
open MvPolynomial
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Work.MotAS.ASZGC
variable {K : Type*} [Field K] [CharP K 5]
noncomputable def Qq0_1 (a b g : K) : MvPolynomial (Fin 2) K :=
  2 * C a ^ (15 : ℕ) * C b ^ (11 : ℕ) * C g ^ (6 : ℕ) * X 0 ^ (2 : ℕ)
  + 4 * C a ^ (16 : ℕ) * C b ^ (10 : ℕ)
  + 4 * C a ^ (16 : ℕ) * C b ^ (10 : ℕ) * X 0 ^ (1 : ℕ)
  + 2 * C a ^ (16 : ℕ) * C b ^ (10 : ℕ) * X 0 ^ (2 : ℕ)
  + C a ^ (16 : ℕ) * C b ^ (10 : ℕ) * C g ^ (2 : ℕ)
  + 2 * C a ^ (16 : ℕ) * C b ^ (10 : ℕ) * C g ^ (2 : ℕ) * X 0 ^ (1 : ℕ)
  + 2 * C a ^ (16 : ℕ) * C b ^ (10 : ℕ) * C g ^ (2 : ℕ) * X 0 ^ (2 : ℕ)
  + 3 * C a ^ (16 : ℕ) * C b ^ (10 : ℕ) * C g ^ (4 : ℕ) * X 0 ^ (2 : ℕ)
  + 4 * C a ^ (16 : ℕ) * C b ^ (10 : ℕ) * C g ^ (6 : ℕ) * X 0 ^ (2 : ℕ)
  + C a ^ (17 : ℕ) * C b ^ (9 : ℕ)
  + 2 * C a ^ (17 : ℕ) * C b ^ (9 : ℕ) * X 0 ^ (1 : ℕ)
  + C a ^ (17 : ℕ) * C b ^ (9 : ℕ) * X 0 ^ (2 : ℕ)
  + 2 * C a ^ (17 : ℕ) * C b ^ (9 : ℕ) * C g ^ (2 : ℕ)
  + 3 * C a ^ (17 : ℕ) * C b ^ (9 : ℕ) * C g ^ (2 : ℕ) * X 0 ^ (1 : ℕ)
  + C a ^ (17 : ℕ) * C b ^ (9 : ℕ) * C g ^ (2 : ℕ) * X 0 ^ (2 : ℕ)
  + 4 * C a ^ (17 : ℕ) * C b ^ (9 : ℕ) * C g ^ (4 : ℕ)
  + 4 * C a ^ (17 : ℕ) * C b ^ (9 : ℕ) * C g ^ (4 : ℕ) * X 0 ^ (1 : ℕ)
  + C a ^ (17 : ℕ) * C b ^ (9 : ℕ) * C g ^ (4 : ℕ) * X 0 ^ (2 : ℕ)
  + 3 * C a ^ (17 : ℕ) * C b ^ (9 : ℕ) * C g ^ (6 : ℕ) * X 0 ^ (2 : ℕ)
  + C a ^ (18 : ℕ) * C b ^ (8 : ℕ) * X 0 ^ (1 : ℕ)
  + 4 * C a ^ (18 : ℕ) * C b ^ (8 : ℕ) * X 0 ^ (2 : ℕ)
  + 2 * C a ^ (18 : ℕ) * C b ^ (8 : ℕ) * C g ^ (2 : ℕ) * X 0 ^ (2 : ℕ)
  + C a ^ (18 : ℕ) * C b ^ (8 : ℕ) * C g ^ (4 : ℕ) * X 0 ^ (1 : ℕ)
  + 4 * C a ^ (18 : ℕ) * C b ^ (8 : ℕ) * C g ^ (4 : ℕ) * X 0 ^ (2 : ℕ)
  + C a ^ (18 : ℕ) * C b ^ (8 : ℕ) * C g ^ (6 : ℕ) * X 0 ^ (2 : ℕ)
  + C a ^ (19 : ℕ) * C b ^ (7 : ℕ)
  + 3 * C a ^ (19 : ℕ) * C b ^ (7 : ℕ) * X 0 ^ (1 : ℕ)
  + 2 * C a ^ (19 : ℕ) * C b ^ (7 : ℕ) * X 0 ^ (2 : ℕ)
  + C a ^ (19 : ℕ) * C b ^ (7 : ℕ) * C g ^ (2 : ℕ)
  + C a ^ (19 : ℕ) * C b ^ (7 : ℕ) * C g ^ (2 : ℕ) * X 0 ^ (1 : ℕ)
  + 4 * C a ^ (19 : ℕ) * C b ^ (7 : ℕ) * C g ^ (2 : ℕ) * X 0 ^ (2 : ℕ)
  + 4 * C a ^ (19 : ℕ) * C b ^ (7 : ℕ) * C g ^ (4 : ℕ)
  + C a ^ (19 : ℕ) * C b ^ (7 : ℕ) * C g ^ (4 : ℕ) * X 0 ^ (1 : ℕ)
  + 2 * C a ^ (19 : ℕ) * C b ^ (7 : ℕ) * C g ^ (4 : ℕ) * X 0 ^ (2 : ℕ)
  + 2 * C a ^ (19 : ℕ) * C b ^ (7 : ℕ) * C g ^ (6 : ℕ) * X 0 ^ (2 : ℕ)
  + C a ^ (20 : ℕ) * C b ^ (6 : ℕ)
  + 4 * C a ^ (20 : ℕ) * C b ^ (6 : ℕ) * X 0 ^ (1 : ℕ)
  + 2 * C a ^ (20 : ℕ) * C b ^ (6 : ℕ) * C g ^ (2 : ℕ)
  + C a ^ (20 : ℕ) * C b ^ (6 : ℕ) * C g ^ (2 : ℕ) * X 0 ^ (1 : ℕ)
  + C a ^ (20 : ℕ) * C b ^ (6 : ℕ) * C g ^ (2 : ℕ) * X 0 ^ (2 : ℕ)
  + 4 * C a ^ (20 : ℕ) * C b ^ (6 : ℕ) * C g ^ (4 : ℕ) * X 0 ^ (2 : ℕ)
  + 4 * C a ^ (20 : ℕ) * C b ^ (6 : ℕ) * C g ^ (6 : ℕ) * X 0 ^ (2 : ℕ)
  + C a ^ (21 : ℕ) * C b ^ (5 : ℕ) * C g ^ (2 : ℕ)
  + 2 * C a ^ (21 : ℕ) * C b ^ (5 : ℕ) * C g ^ (2 : ℕ) * X 0 ^ (1 : ℕ)
  + 4 * C a ^ (21 : ℕ) * C b ^ (5 : ℕ) * C g ^ (2 : ℕ) * X 0 ^ (2 : ℕ)
  + 3 * C a ^ (21 : ℕ) * C b ^ (5 : ℕ) * C g ^ (4 : ℕ) * X 0 ^ (2 : ℕ)
  + 3 * C a ^ (21 : ℕ) * C b ^ (5 : ℕ) * C g ^ (6 : ℕ) * X 0 ^ (2 : ℕ)
  + 2 * C a ^ (22 : ℕ) * C b ^ (4 : ℕ) * C g ^ (2 : ℕ)
  + 3 * C a ^ (22 : ℕ) * C b ^ (4 : ℕ) * C g ^ (2 : ℕ) * X 0 ^ (1 : ℕ)
  + 3 * C a ^ (22 : ℕ) * C b ^ (4 : ℕ) * C g ^ (4 : ℕ)
  + 3 * C a ^ (22 : ℕ) * C b ^ (4 : ℕ) * C g ^ (4 : ℕ) * X 0 ^ (1 : ℕ)
  + C a ^ (22 : ℕ) * C b ^ (4 : ℕ) * C g ^ (4 : ℕ) * X 0 ^ (2 : ℕ)
  + C a ^ (22 : ℕ) * C b ^ (4 : ℕ) * C g ^ (6 : ℕ) * X 0 ^ (2 : ℕ)
  + 2 * C a ^ (23 : ℕ) * C b ^ (3 : ℕ) * C g ^ (4 : ℕ) * X 0 ^ (1 : ℕ)
  + C a ^ (23 : ℕ) * C b ^ (3 : ℕ) * C g ^ (4 : ℕ) * X 0 ^ (2 : ℕ)
  + 2 * C a ^ (23 : ℕ) * C b ^ (3 : ℕ) * C g ^ (6 : ℕ) * X 0 ^ (2 : ℕ)
  + 3 * C a ^ (24 : ℕ) * C b ^ (2 : ℕ) * C g ^ (4 : ℕ)
  + 2 * C a ^ (24 : ℕ) * C b ^ (2 : ℕ) * C g ^ (4 : ℕ) * X 0 ^ (1 : ℕ)
  + 4 * C a ^ (24 : ℕ) * C b ^ (2 : ℕ) * C g ^ (6 : ℕ) * X 0 ^ (2 : ℕ)
  + 3 * C a ^ (25 : ℕ) * C b ^ (1 : ℕ) * C g ^ (6 : ℕ)
  + 3 * C a ^ (25 : ℕ) * C b ^ (1 : ℕ) * C g ^ (6 : ℕ) * X 0 ^ (1 : ℕ)
  + 3 * C a ^ (25 : ℕ) * C b ^ (1 : ℕ) * C g ^ (6 : ℕ) * X 0 ^ (2 : ℕ)
  + 4 * C a ^ (26 : ℕ) * C g ^ (6 : ℕ)
  + C a ^ (26 : ℕ) * C g ^ (6 : ℕ) * X 0 ^ (1 : ℕ)
end Work.MotAS.ASZGC
