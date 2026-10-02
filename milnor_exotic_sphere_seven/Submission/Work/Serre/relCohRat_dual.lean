import Mathlib
import Submission.Work.Thom.Cohomology
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.StemsB.WangCohRat

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Relative cohomology over `ℚ` is the `ℤ`-dual of integral relative homology

The universal coefficient theorem over the field `ℚ` identifies the relative cohomology
`H^n(P,Q;ℚ)` with the rational dual of the rational relative homology.  The relative homology
*over `ℚ`* is the base change `ℚ ⊗[ℤ] H_n(P,Q;ℤ)` of the integral relative homology, and over a
field the base change is invisible to the dual:

  `Hom_ℚ(ℚ ⊗[ℤ] M, ℚ) ≃ₗ[ℚ] Hom_ℤ(M, ℚ)`   (tensor–hom adjunction).

Combining the two gives the statement needed by subproject SERRE, that `H^n(P,Q;ℚ)` is the
`ℤ`-dual of the *integral* relative homology `H_n(P,Q;ℤ)`.

* `Work.Serre.intDual_baseChange` — the tensor–hom adjunction
  `Hom_ℚ(ℚ ⊗[ℤ] M, ℚ) ≃ₗ[ℚ] Hom_ℤ(M, ℚ)` for a `ℤ`-module `M`;
* `Work.Serre.relCohRat_dual` — the target statement, from
  `Work.StemsB.ratRelCohTensorDual`
  (`H^n(P,Q;ℚ) ≅ Hom_ℚ(ℚ ⊗[ℤ] H_n(P,Q;ℤ), ℚ)`).
-/

set_option backward.isDefEq.respectTransparency false

namespace Work.Serre

noncomputable section

open CategoryTheory CategoryTheory.Limits

/-- **Tensor–hom adjunction.**  For a `ℤ`-module `M`, the `ℚ`-dual of the base change
`ℚ ⊗[ℤ] M = M ⊗[ℤ] ℚ` is the `ℤ`-dual of `M`:

  `Hom_ℚ(ℚ ⊗[ℤ] M, ℚ) ≃ₗ[ℚ] Hom_ℤ(M, ℚ)`.

Both sides are the space of `ℤ`-linear functionals `M → ℚ`, the left one presented through the
adjunction `Hom_ℚ(ℚ ⊗[ℤ] M, ℚ) ≅ Hom_ℤ(M, Hom_ℚ(ℚ,ℚ)) ≅ Hom_ℤ(M,ℚ)`
(`TensorProduct.AlgebraTensorModule.lift.equiv` followed by `LinearMap.ringLmapEquivSelf`). -/
noncomputable def intDual_baseChange (M : ModuleCat.{0, 0} ℤ) :
    (↥(Work.StemsB.IntRatF.obj M) →ₗ[ℚ] ℚ) ≃ₗ[ℚ] (↥M →ₗ[ℤ] ℚ) :=
  (TensorProduct.AlgebraTensorModule.lift.equiv ℤ ℚ ℚ ℚ M ℚ).symm.trans
    (LinearMap.ringLmapEquivSelf ℚ ℚ (↥M →ₗ[ℤ] ℚ))

theorem relCohRat_dual (P : Type) [TopologicalSpace P] (Q : Set P) (n : ℕ) :
    Nonempty (Work.Thom.RelCoh ℚ n P Q ≅ ModuleCat.of ℚ
      (↥((Work.Cohomology.relChains (TopCat.of P) Q).homology n) →ₗ[ℤ] ℚ)) :=
  ⟨Work.StemsB.ratRelCohTensorDual (TopCat.of P) Q n ≪≫
    LinearEquiv.toModuleIso
      (intDual_baseChange ((Work.Cohomology.relChains (TopCat.of P) Q).homology n))⟩

end

end Work.Serre
