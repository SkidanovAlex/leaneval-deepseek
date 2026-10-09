import Mathlib
import Submission.Work.SSGRoute.ZDataMup.AbelianOnePlaceAux
import Submission.Work.SSGRoute.ZDataMup.AbelianOnePlaceAux2
import Submission.Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois_coe
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.SSGRoute.ZDataMup

/-- **A decomposition-group element is detected by its action on the completion image.**

Let `Q` be a finite place of `K`, `q | Q` a place of `L`, `M ≤ L` an intermediate field normal over
`K`, and `σ` an element of the decomposition group of `q` in `Gal(L/K)`; via
`decompositionSubgroupMulEquivLocalGalois` it extends canonically to an element of `Gal(L_q/K_Q)`.
If that extension fixes pointwise the image of the completion `(M)_{q|M}` inside `L_q` — this image
is `Work.SSGRoute.ZDataMup.localFieldImage Q q hq M` — then `σ` fixes `M` pointwise.

Route: `Submission.NeukirchUchida.Local.localRestrict_adicCompletionMap` says that the restriction
of the extended automorphism to the image of `(M)_{q|M}` is the extension of the restriction of `σ`
to `M`; combined with injectivity of `Commons.RingTheory.Henselian.adicCompletionMap`
(`Commons.NumberTheory.NumberField.Completion.adicCompletionMap_injective`) this forces the
restriction of `σ` to `M` to be `1`, i.e. `σ.1 ∈ M.fixingSubgroup`. -/
theorem mem_fixingSubgroup_of_mem_localFieldImage
    {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (M : IntermediateField K L) [Normal K ↥M]
    (σ : ↥(Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) (L := L) q))
    (hσ : (Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois
        Q q hq σ) ∈ (Work.SSGRoute.ZDataMup.localFieldImage Q q hq M).fixingSubgroup) :
    σ.1 ∈ M.fixingSubgroup := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra Q q hq
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  -- the image of `x` in the completion of `L` lies in the image of the completion of `M`
  have hmem : algebraMap L (q.adicCompletion L) x ∈
      Work.SSGRoute.ZDataMup.localFieldImage Q q hq M :=
    Work.SSGRoute.ZDataMup.image_mem_localFieldImage Q q hq M ⟨x, hx⟩
  -- the extended automorphism fixes it
  have hfix : (Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois
        Q q hq σ) (algebraMap L (q.adicCompletion L) x) = algebraMap L (q.adicCompletion L) x :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ _ hmem
  -- on the image of `L` the extended automorphism is the action of `σ`
  have hcoe : (Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois
        Q q hq σ) (algebraMap L (q.adicCompletion L) x) = (σ.1 x : q.adicCompletion L) := by
    have h1 := congrArg
      (fun e : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L =>
        e (algebraMap L (q.adicCompletion L) x))
      (Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois_coe
        Q q hq σ)
    rw [h1]
    exact Commons.NumberTheory.NumberField.Completion.decompositionToAdicCompletion_coe q σ x
  have hEq : (σ.1 x : q.adicCompletion L) = (x : q.adicCompletion L) := by
    rw [← hcoe]
    exact hfix
  exact Commons.NumberTheory.NumberField.Completion.injective_algebraMap_adicCompletion q hEq

end Work.SSGRoute.ZDataMup
