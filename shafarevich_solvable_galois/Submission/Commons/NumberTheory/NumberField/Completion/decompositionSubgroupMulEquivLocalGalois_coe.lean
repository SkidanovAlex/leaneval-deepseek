import Mathlib
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_algEquiv_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.NumberField.Completion

/-- The group isomorphism `D_w ≃* Gal(L_w / K_p)` between the decomposition group and the local
Galois group is, on underlying maps, the canonical action homomorphism
`decompositionToLocalGalois`: it is `MulEquiv.ofBijective` applied to that
homomorphism, so evaluation at `σ` is `decompositionToLocalGalois p w h σ`.

This is the `AlgEquiv`-valued form of the compatibility `decompositionSubgroupMulEquivLocalGalois`
with the canonical map `decompositionToLocalGalois`. -/
theorem decompositionSubgroupMulEquivLocalGalois_coe {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (h : w.asIdeal.LiesOver p.asIdeal)
    (σ : Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) w) :
    letI : Algebra (p.adicCompletion K) (w.adicCompletion L) :=
      Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra p w h
    ((Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois p w h σ :
        w.adicCompletion L ≃ₐ[p.adicCompletion K] w.adicCompletion L)) =
      Commons.NumberTheory.NumberField.Completion.decompositionToLocalGalois p w h σ := by
  -- `decompositionSubgroupMulEquivLocalGalois` is `MulEquiv.ofBijective` applied to
  -- `decompositionToLocalGalois`, and `MulEquiv.ofBijective_apply` records that this operation
  -- does not change the underlying function.
  simp only [decompositionSubgroupMulEquivLocalGalois, MulEquiv.ofBijective_apply]

end Commons.NumberTheory.NumberField.Completion
