/-
Area DSCOH (curric-46) — the geometric alternating Čech complex, as a cochain complex.

`Work.DSCOH.altCech` is the alternating Čech complex of a family of opens with coefficients in a
presheaf of `A`-modules (terms `∏_{|S| = q+1} P (⋂_{i∈S} U i)`, alternating differential
`Work.DSCOH.altCechDiff`).  It is the geometric counterpart of the chart Čech complex
`Work.DSCOH.chartCech`, and the two are identified chartwise by the bridge; this file exists so
that the comparison with Mathlib's unnormalized `cechComplexFunctor` (which is what the frozen
`DSMap.cech` uses) can be stated as a quasi-isomorphism.
-/
import Submission.Work.DSCOH.AltCech
import Submission.Work.DSCOH.altCechDiff_comp

open CategoryTheory

namespace Work.DSCOH

variable {X : Type*} [TopologicalSpace X] {A : Type*} [CommRing A] {ι : Type*}
  [Fintype ι] [DecidableEq ι] [LinearOrder ι]

/-- **The geometric alternating Čech complex** of a family of opens `U` with coefficients in a
presheaf `P` of `A`-modules. -/
noncomputable def altCech (P : (TopologicalSpace.Opens X)ᵒᵖ ⥤ ModuleCat A)
    (U : ι → TopologicalSpace.Opens X) : CochainComplex (ModuleCat A) ℕ :=
  CochainComplex.of (fun q => ModuleCat.of A (AltCechTerm P U q))
    (fun q => ModuleCat.ofHom (altCechDiff P U q))
    (fun q => by
      rw [← ModuleCat.ofHom_comp, altCechDiff_comp X A ι P U q]
      exact ModuleCat.ofHom_zero)

end Work.DSCOH
