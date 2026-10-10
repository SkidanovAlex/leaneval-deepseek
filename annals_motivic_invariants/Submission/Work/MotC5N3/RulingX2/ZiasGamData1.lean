import Submission.Work.MotC5N3.RulingX2.SlicePhi

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.MotC5N3.RulingX2

variable {K : Type} [Field K] [CharP K 5]
noncomputable def A0mv_0 (a b g : K) : MvPolynomial (Fin 2) K :=
  MvPolynomial.C (2 * a^4 * b) * MvPolynomial.X 1 ^ 1
    + MvPolynomial.C (2 * a^3 * b^2) * MvPolynomial.X 1 ^ 1
    + MvPolynomial.C (4 * a^2 * b^3) * MvPolynomial.X 1 ^ 1
    + MvPolynomial.C (a * b^4) * MvPolynomial.X 1 ^ 1
    + MvPolynomial.C (2 * a^5 * g)
    + MvPolynomial.C (2 * a^5)
    + MvPolynomial.C (2 * a^4 * b)
    + MvPolynomial.C (a^3 * b^2)
    + MvPolynomial.C (3 * a^2 * b^3)
    + MvPolynomial.C (4 * a * b^4)
    + MvPolynomial.C (4 * b^5 * g)
    + MvPolynomial.C (b^5)

noncomputable def A0mv (a b g : K) : MvPolynomial (Fin 2) K :=
  A0mv_0 a b g

noncomputable def B0mv_0 (a b g : K) : MvPolynomial (Fin 2) K :=
  MvPolynomial.C (2 * a^5 * g) * MvPolynomial.X 1 ^ 2
    + MvPolynomial.C (3 * a^5) * MvPolynomial.X 1 ^ 2
    + MvPolynomial.C (3 * a^4 * b) * MvPolynomial.X 1 ^ 2
    + MvPolynomial.C (4 * a^3 * b^2) * MvPolynomial.X 1 ^ 2
    + MvPolynomial.C (2 * a^2 * b^3) * MvPolynomial.X 1 ^ 2
    + MvPolynomial.C (a * b^4) * MvPolynomial.X 1 ^ 2
    + MvPolynomial.C (4 * b^5 * g) * MvPolynomial.X 1 ^ 2
    + MvPolynomial.C (4 * b^5) * MvPolynomial.X 1 ^ 2
    + MvPolynomial.C (2 * a^5) * MvPolynomial.X 1 ^ 1
    + MvPolynomial.C (4 * a^4 * b) * MvPolynomial.X 1 ^ 1
    + MvPolynomial.C (3 * a^3 * b^2) * MvPolynomial.X 1 ^ 1
    + MvPolynomial.C (4 * a^2 * b^3) * MvPolynomial.X 1 ^ 1
    + MvPolynomial.C (3 * a * b^4) * MvPolynomial.X 1 ^ 1
    + MvPolynomial.C (4 * b^5) * MvPolynomial.X 1 ^ 1
    + MvPolynomial.C (3 * a^5 * g)
    + MvPolynomial.C (a^5)
    + MvPolynomial.C (3 * a^4 * b * g)
    + MvPolynomial.C (2 * a^4 * b)
    + MvPolynomial.C (4 * a^3 * b^2 * g)
    + MvPolynomial.C (2 * a^3 * b^2)

noncomputable def B0mv_1 (a b g : K) : MvPolynomial (Fin 2) K :=
  MvPolynomial.C (2 * a^2 * b^3 * g)
    + MvPolynomial.C (4 * a^2 * b^3)
    + MvPolynomial.C (a * b^4 * g)
    + MvPolynomial.C (a * b^4)
    + MvPolynomial.C (4 * b^5 * g)
    + MvPolynomial.C (2 * b^5)

noncomputable def B0mv (a b g : K) : MvPolynomial (Fin 2) K :=
  B0mv_0 a b g
    + B0mv_1 a b g


noncomputable def N5v (a b g : K) : K := 4 * a^16 * b + 4 * a^11 * b^6 + 3 * a^6 * b^11 + 2 * a * b^16

noncomputable def P4v (a b g : K) : K := 2 * a^4 * b + 2 * a^3 * b^2 + 4 * a^2 * b^3 + a * b^4

end Work.MotC5N3.RulingX2
