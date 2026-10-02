import Mathlib
import Submission.Work.LerayHirsch.FibreIso
import Submission.Work.Thom.pontryaginClass_comap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The restriction of `ζ` to a fibre

`Work.LerayHirsch.nonempty_bundleIso_tautLine_fibre` identifies the restriction of the tautological
line bundle of `P(E)` to a fibre with the tautological line bundle of the fibre.  This module reads
off the cohomological consequence

`Work.LerayHirsch.CohMap_fibreIncl_zeta : ζ|_fibre = ζ(ℂP^{m-1})`,

where `ζ = c₁(ℓ(E))` and `ζ(ℂP^{m-1}) = Work.LerayHirsch.zetaP m`.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}

/-- **The pullback of the hyperplane class of `ℂP^{m-1}`**: the first Chern class of the pullback of
the tautological line bundle. -/
theorem zetaP_comap {B' : Type} [TopologicalSpace B']
    (g : C(B', ℙ ℂ (EuclideanSpace ℂ (Fin m)))) :
    (CohMap g ℤ 2).hom (zetaP m)
      = cohTransport (rfl : 2 * 1 = 2) (chernClass 1 1 (bundleComap (tautLineP m) g)) := by
  rw [zetaP, cohTransport_CohMap]
  rw [← chernClass_comap]

/-- **The first Chern class of the two tautological bundles on a fibre coincide.** -/
theorem chernClass_fibreIncl_tautLine
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι] (b : B) :
    chernClass 1 1 (bundleComap (tautLine Z) (fibreIncl Z b))
      = chernClass 1 1 (bundleComap (tautLineP m) (projClassFibre Z b)) :=
  chernClass_BundleIso _ _ (Classical.choice (nonempty_bundleIso_tautLine_fibre Z b))

/-- **The restriction of `ζ` to a fibre is the hyperplane class of the fibre**:
`(fibreIncl Z b)^* ζ(E) = (projClassFibre Z b)^* ζ(ℂP^{m-1})`. -/
theorem CohMap_fibreIncl_zeta (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι]
    (b : B) :
    (CohMap (fibreIncl Z b) ℤ 2).hom (zeta Z)
      = (CohMap (projClassFibre Z b) ℤ 2).hom (zetaP m) := by
  rw [zeta_comap Z (fibreIncl Z b), zetaP_comap (m := m) (projClassFibre Z b)]
  exact congrArg (fun x => cohTransport (rfl : 2 * 1 = 2) x) (chernClass_fibreIncl_tautLine Z b)

end

end Work.LerayHirsch
