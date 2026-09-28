import Mathlib
import Submission.Work.Thom.localThom_union

set_option autoImplicit false
open Work.TangentClasses CategoryTheory CategoryTheory.Limits
open Work.Cohomology

namespace Work.Thom

variable {X : TopCat}

/-- **Functoriality of the restrictions `pdCohMap`**: restricting relative cohomology from `W` to
`V` is the same as restricting from `W` to `U` and then from `U` to `V`.  This is
`Work.Cohomology.pdIU_pdCohMap_comp` with the excluded set written as `A` instead of `Kᶜ`
(`pdIU_pdCohMap_comp` is stated for `Kᶜ` and cannot be instantiated directly because
`(Kᶜ)ᶜ` is only propositionally, not definitionally, equal to `K`).

Proof: rewrite the three `pdCohMap`s with `Work.Cohomology.pdCohMap_eq_relCohMap`, then use
`← HomologicalComplex.homologyMap_comp` and
`Work.Cohomology.capRel_relComplexMap_comp ℤ {y : V | (y : X) ∈ A} {y : U | (y : X) ∈ A}
{y : W | (y : X) ∈ A} (pdIncl U V hVU) (pdIncl W U hUW)` (the `Kᶜ`-version of the same proof is
`Work.Cohomology.pdIU_pdCohMap_comp` in `Submission/Work/Cohomology/pd_good_iUnion.lean` and
transcribes verbatim once `pdRelSub V K` is read as `{y : V | (y : X) ∈ A}`), finishing with
`congrArg (fun m => HomologicalComplex.homologyMap m k)`. -/
theorem pdCohMap_comp (X : TopCat) (A : Set X) {V U W : Set X} (hVU : V ⊆ U) (hUW : U ⊆ W)
    (k : ℕ) :
    Work.Cohomology.pdCohMap X A W V (hVU.trans hUW) k
      = Work.Cohomology.pdCohMap X A W U hUW k ≫ Work.Cohomology.pdCohMap X A U V hVU k := by
  have hkey : Work.Cohomology.relComplexMap ℤ (X₁ := TopCat.of V) (X₂ := TopCat.of W)
        {y : V | (y : X) ∈ A} {y : W | (y : X) ∈ A}
        (Work.Cohomology.pdIncl W V (hVU.trans hUW)) (fun y hy => hy)
      = Work.Cohomology.relComplexMap ℤ (X₁ := TopCat.of U) (X₂ := TopCat.of W)
          {y : U | (y : X) ∈ A} {y : W | (y : X) ∈ A}
          (Work.Cohomology.pdIncl W U hUW) (fun y hy => hy)
        ≫ Work.Cohomology.relComplexMap ℤ (X₁ := TopCat.of V) (X₂ := TopCat.of U)
            {y : V | (y : X) ∈ A} {y : U | (y : X) ∈ A}
            (Work.Cohomology.pdIncl U V hVU) (fun y hy => hy) := by
    rw [← Work.Cohomology.capRel_relComplexMap_comp ℤ
      ({y : V | (y : X) ∈ A}) ({y : U | (y : X) ∈ A}) ({y : W | (y : X) ∈ A})
      (Work.Cohomology.pdIncl U V hVU) (Work.Cohomology.pdIncl W U hUW)
      (fun x hx => hx) (fun x hx => hx)]
    exact Work.Thom.relComplexMap_congrA _ _ rfl _ _ ℤ
  rw [Work.Cohomology.pdCohMap, Work.Cohomology.pdCohMap, Work.Cohomology.pdCohMap,
    ← HomologicalComplex.homologyMap_comp, hkey]

end Work.Thom
