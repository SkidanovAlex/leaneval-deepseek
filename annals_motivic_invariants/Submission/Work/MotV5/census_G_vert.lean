import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotA.SpreadAux
import Submission.Work.MotA.prime_aeval_X0
import Submission.Work.MotA.quotient_vertical
import Submission.Work.MotV5.fractionRing_mvPoly_fin_add
import Submission.Work.MotV5.fractionRing_mvPoly_one
import Submission.Work.CrauderKatz.BlowUp.fractionRing_algEquiv_of_algEquiv
import Submission.Work.MotV5.SpreadLoc.census_G_vert

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5

/-- Vertical (principal-in-`t`) case of the `G`-side census: if a height-one prime `p` of
`𝕜[Fin 4]` contains the image of a nonzero `t`-polynomial, then `κ(p)` is junk.  Here
`M := (nonZeroDivisors 𝕜[t]).map (tPoly 𝕜 3) ⊆ 𝕜[Fin 4]` is the submonoid of "vertical"
elements.

The proof lives in `Submission/Work/MotV5/SpreadLoc/census_G_vert.lean`
(`Work.MotV5.SpreadLoc.census_G_vert`), which is the live copy of this node (see also
`cf_census_vert` for the `F`-side wording of the same statement). -/
theorem census_G_vert {𝕜 : Type} [Field 𝕜]
    (p : Ideal (MvPolynomial (Fin 4) 𝕜)) [p.IsPrime] (hp1 : p.height = 1)
    (h : ¬ Disjoint ((nonZeroDivisors (Polynomial 𝕜)).map (Work.MotA.tPoly 𝕜 3) :
        Set (MvPolynomial (Fin 4) 𝕜)) (p : Set (MvPolynomial (Fin 4) 𝕜))) :
    ∃ (F₀ : Type) (_ : Field F₀) (_ : Algebra 𝕜 F₀), ¬ Work.MotV.ConstantsOnly 𝕜 F₀ ∧
      Nonempty (FractionRing (MvPolynomial (Fin 4) 𝕜 ⧸ p) ≃ₐ[𝕜] RatFunc F₀) :=
  Work.MotV5.SpreadLoc.census_G_vert p hp1 h

end Work.MotV5
