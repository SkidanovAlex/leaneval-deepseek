import Mathlib
import Submission.Work.CrauderKatz.BlowUp.fractionRing_algEquiv_of_algEquiv
import Submission.Work.MotV5.fractionRing_mvPoly_fractionRing

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.MotV

open MvPolynomial

/-- **Iterated rational function fields** (own copy, used by `SpreadClasses`): `F(x₁,…,x_{a+b})`,
i.e. the fraction field of `MvPolynomial (Fin (a+b)) F`, is the rational function field in `a`
variables over the rational function field in `b` variables over `F`. -/
theorem fracMvPoly_fin_add {𝕜 F : Type} [Field 𝕜] [Field F] [Algebra 𝕜 F] (a b : ℕ) :
    Nonempty (FractionRing (MvPolynomial (Fin (a + b)) F) ≃ₐ[𝕜]
      FractionRing (MvPolynomial (Fin a) (FractionRing (MvPolynomial (Fin b) F)))) := by
  have hAB : MvPolynomial (Fin (a + b)) F ≃ₐ[𝕜]
      MvPolynomial (Fin a) (MvPolynomial (Fin b) F) :=
    ((MvPolynomial.renameEquiv F (finSumFinEquiv.symm)).trans
      (MvPolynomial.sumAlgEquiv F (Fin a) (Fin b))).restrictScalars 𝕜
  obtain ⟨e1⟩ := Work.CrauderKatz.BlowUp.fractionRing_algEquiv_of_algEquiv (𝕜 := 𝕜) hAB
  obtain ⟨e2⟩ := Work.MotV5.fractionRing_mvPoly_fractionRing (𝕜 := 𝕜)
    (R := MvPolynomial (Fin b) F) (Fin a)
  exact ⟨e1.trans e2.symm⟩

end Work.MotV
