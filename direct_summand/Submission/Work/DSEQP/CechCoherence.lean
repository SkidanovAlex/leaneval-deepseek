/-
# Coherence of the Čech complex of the chart cover, via the algebraic bridge

This file records the *plumbing* that turns the two ingredients of the algebraic bridge

* **(1b)** the chartwise identification `Work.DSEQP.chartCechTerm_iso`
  (`Submission/Work/DSEQP/gf_bridge.lean`, proved in this area), and
* **(1c)** the normalization quasi-isomorphism
  `Work.DSCOH.cechComplexFunctor_homology_iso` (subproject `DSCOH`),
  stated here as an explicit hypothesis `h1c`,

into the Čech-level coherence statement for the chart cover of a closed subscheme
`i : X ⊆ ℙᴺ_A`:

  `∃ N, ∀ j, Module.Finite A ((cechZ A X f (chartCover i)).homology j) ∧ (N < j → IsZero …)`.

This is the Čech-level form of the frozen area `DSMap.area_COH` — it needs *no* area `F1` and no
`area_COH`, only `(1b)`, `(1c)` and the graded finiteness theorem
`Work.DSCOH.chartCech_finite_vanishing` (subproject `DSCOH`).  It is what `Submission/Work/DSEQP/F1COHWire.lean`
uses (or will use) in order to make `DSMap.area_EQP_proved` independent of the frozen `DSMap.area_COH`.

All DSCOH lemmas cited here are proved and axiom-clean; the only input is `h1c`.
-/
import Mathlib
import Submission.Work.DSMap.Gaps
import Submission.Work.DSCOH.cechZ_homology_iso_chartCech
import Submission.Work.DSCOH.cechZ_coherence_of_homology_iso
import Submission.Work.DSCOH.chartCechZ_finite_vanishing

open CategoryTheory AlgebraicGeometry Limits

namespace Work.DSEQP

universe u

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-- **Čech coherence of the chart cover from the bridge `(1b)+(1c)`.**

`h1c` is the normalization comparison of subproject `DSCOH`
(`Work.DSCOH.cechComplexFunctor_homology_iso`); the rest is proved. -/
theorem cechZ_homology_finite_chartCover (A : Type u) [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} (N : ℕ) (i : X ⟶ DSMap.PSpace A N) (hi : IsClosedImmersion i)
    (f : X ⟶ Spec (.of A)) (hif : i ≫ DSMap.PSpace.toSpec A N = f)
    (h1c : ∀ q : ℕ, Nonempty ((DSMap.cech A X f (DSMap.Mix2.chartCover i)).homology q ≅
      (Work.DSCOH.altCech (DSMap.cechPresheaf A X f) (DSMap.Mix2.chartCover i)).homology q)) :
    ∃ N' : ℤ, ∀ j : ℤ,
      Module.Finite A ((DSMap.cechZ A X f (DSMap.Mix2.chartCover i)).homology j) ∧
      (N' < j → CategoryTheory.Limits.IsZero
        ((DSMap.cechZ A X f (DSMap.Mix2.chartCover i)).homology j)) := by
  haveI : DirectSum.Decomposition (Work.DSEQP.Mg i) := Work.DSEQP.MgDecomposition i
  have hK := Work.DSCOH.cechZ_homology_iso_chartCech A N i hi f hif h1c
  refine Work.DSCOH.cechZ_coherence_of_homology_iso A X f (DSMap.Mix2.chartCover i)
    (Work.DSCOH.chartCech (A := A) (n := N + 1) (M := Work.DSEQP.Mmod i)
      (Work.DSEQP.Mg i)) (fun q => ?_)
    (Work.DSCOH.chartCechZ_finite_vanishing (A := A) (n := N + 1) (M := Work.DSEQP.Mmod i)
      (ℳ := Work.DSEQP.Mg i))
  exact ⟨(HomologicalComplex.extendHomologyIso (DSMap.cech A X f (DSMap.Mix2.chartCover i))
      ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f q)).symm.trans
    (Classical.choice (hK q))⟩

end Work.DSEQP
