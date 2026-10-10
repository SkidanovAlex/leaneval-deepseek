import Mathlib
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotC5N3.AK
import Submission.Work.MotC5N3.ASZTwistDivPlaneGeom
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotAS.ASZTwistDefs
import Submission.Work.MotC5N3.ASZPhiMemGen

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC5N3

/-!
# `Work.MotC5N3.ASZTwistDivPlaneGeomGen` — explicit inverse parametrisation of the AS residual

## The route (established and verified numerically this session)

`Res_g = V(ZIAS a b g)` — the residual curve of the AS Crauder–Katz link of class `g` — is the
image of the AS-twisted Klein curve `C_{3g} = V(kleinPAS a b (3g))` under the *linear* map
`phiAS a b` (`Work.MotAS.phiAS`): in the charts (`z₀ = 1, z₄ = 0` on `Res_g`, `Y₀ = 1` on `C_{3g}`)
the map is `Xᵢ = Z_{i+1}/Z₀` with `Z_k = Σ_j phiAS a b k j · Y_j`.  Over `𝔽₅` and `𝔽₂₅` this map is a
bijection between the two point sets and every residual point has a preimage; hence `Res_g ≅ C_{3g}`
and, since `3g = -2g` and `c ≅ -c` for the AS twist (`Work.MotAS.kleinPAS_neg_apply`), also
`Res_g ≅ C_{2g}` — the statement.

## The inverse, explicitly

`ker (phiAS a b) = ⟨e₀⟩`, so the preimage of `[1 : X₀ : X₁ : X₂ : 0]` is the line
`{[S : f₁ : f₂ : f₃ : f₄]}` with the `f_j` independent of `S`:

  `f₁ = (1 - (3a+4b)X₁/(a+2b))/(3a+b)`, `f₂ = (X₀ - (a+3b)X₂/(4a+3b))/(3a+b)`,
  `f₃ = X₁/(a+2b)`, `f₄ = X₂/(4a+3b)`,

cleared as `f_j = Pb_j/D1`, `D1 = (3a+b)(a+2b)(4a+3b) ≠ 0` (each factor vanishes only where
`a² - ab - b² = 0`, excluded by `ASGood`).  With `y = (D1·S, t·Pb₁, …, t·Pb₄)` (homogeneous of
degree `2` in `(S,t)`),

  `kleinPAS k (3g) y = A k·S² + B k·S·t + C k·t²`,

and `A k = 0` for `k ≥ 1`, so the four linear equations `B k·S + C k·t = 0` determine `S/t`: the
consistent solution is `S := -C 1 / B 1`, and the certificate is that it satisfies all five, i.e.
`A k·C₁² - B k·C₁·B₁ + C k·B₁² ∈ √(ZIAS a b g)`.  The chart map
`Θ : K[Y] →ₐ[K] Frac(K[X]/√(ZIAS a b g))`, `Y₀ ↦ 1`, `Y_j ↦ f_j/S` then satisfies
`Xᵢ = Θ(Z_{i+1})/Θ(Z₀)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open MvPolynomial

theorem ASZTwistDivPlaneGeomGen (K : Type) [Field K] [CharP K 5] {𝕜 : Type} [Field 𝕜]
    [CharP 𝕜 5] [Algebra 𝕜 K] (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D)
    (g : K) (hg : ¬ ∃ u : K, u ^ 5 - u = g) :
    Nonempty (FractionRing (MvPolynomial (Fin 3) K ⧸
        Ideal.radical (Work.MotAS.ZIAS (Work.MotC5N3.aK K D) (Work.MotC5N3.bK K D) g)) ≃ₐ[K]
      FractionRing (MvPolynomial (Fin 5) K ⧸
        Work.MotAS.asChartIdeal (Work.MotC5N3.aK K D) (Work.MotC5N3.bK K D) (2 • g))) :=
  Work.MotC5N3.ASZTwistDivPlaneGeom K D hD g hg

end Work.MotC5N3
