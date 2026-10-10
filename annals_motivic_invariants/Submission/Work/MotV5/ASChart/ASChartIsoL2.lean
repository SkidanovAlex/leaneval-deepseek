import Mathlib
import Submission.Work.MotV5.ASChart.ASChartIsoL

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotV5.ASChart.ASChartIsoL2` — the chart isomorphism (local form, final assembly)

The composites computed in `Submission/Work/MotV5/ASChart/ASChartIsoL.lean` are upgraded to the
`K`-algebra equivalence of the two chart localisations: the two composites are the identity on the
generators `X_j`, hence on the whole chart ring by `IsLocalization.algHom_ext` and
`MvPolynomial.algHom_ext`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

namespace Work.MotV5.ASChart

open MvPolynomial

/-- **The composite `Φ ∘ Ψ` is the identity.** -/
theorem PhiLA_PsiLA_comp {K : Type*} [Field K] (a b g : K)
    (h5 : (5 : MvPolynomial (Fin 3) K) = 0) (hlin : IsUnit (linAS2L a b)) :
    (PhiLA a b g h5 hlin).comp (PsiLA a b g h5 hlin)
      = AlgHom.id K (Localization.Away (GdivAS2L a b g)) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (GdivAS2L a b g))
  apply MvPolynomial.algHom_ext
  intro j
  exact PhiLA_PsiLA_X a b g h5 hlin j

/-- **The composite `Ψ ∘ Φ` is the identity.** -/
theorem PsiLA_PhiLA_comp {K : Type*} [Field K] (a b g : K)
    (h5 : (5 : MvPolynomial (Fin 3) K) = 0) (hlin : IsUnit (linAS2L a b)) :
    (PsiLA a b g h5 hlin).comp (PhiLA a b g h5 hlin)
      = AlgHom.id K (Localization.Away (FdivAS2L a b g)) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (FdivAS2L a b g))
  apply MvPolynomial.algHom_ext
  intro j
  exact PsiLA_PhiLA_X a b g h5 hlin j

/-- **The AS chart isomorphism (local form).** -/
theorem chartIsoL {K : Type*} [Field K] (h5 : (5 : MvPolynomial (Fin 3) K) = 0) (a b g : K)
    (hlin : IsUnit (linAS2L a b)) :
    Nonempty (Localization.Away (FdivAS2L a b g) ≃ₐ[K] Localization.Away (GdivAS2L a b g)) :=
  ⟨AlgEquiv.ofAlgHom (PhiLA a b g h5 hlin) (PsiLA a b g h5 hlin)
    (PhiLA_PsiLA_comp a b g h5 hlin) (PsiLA_PhiLA_comp a b g h5 hlin)⟩

end Work.MotV5.ASChart
