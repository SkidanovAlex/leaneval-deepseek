import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_RegExport.RXT.C2Assemble
import Submission.Work.FTS_RegExport.RXT.contDiffOn_succ_integral_Ioi

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.C2Radial` — `L₁₂(F)` is `C³` as soon as `𝔽K(F)` is `C²`

`L₁₂(F)(z) = ∫_{r>z} 𝔽K(F)(r)/r dr` (`L12_eq_integral_FK`, from the definition of `L₁₂`), so
the primitive lemma `contDiffOn_succ_integral_Ioi` applies with `h = 𝔽K(F)/·`: a `C²`
`𝔽K(F)` gives a `C³` `L₁₂(F)` on `(0,∞)` — which is exactly what `Θ` and `Vz7`/`cs7` need.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- `L₁₂(F)(z) = ∫_{r>z} 𝔽K(F)(r)/r dr`: the definition of `L₁₂` with the angular integral
factored through the angular moment `𝔽K`. -/
theorem L12_eq_integral_FK (F : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Construction.L12 F z
      = ∫ r in Set.Ioi z, Work.Construction.FK F r / r := by
  simp only [Work.Construction.L12, Work.FM.L12, Work.FM.L12dens, Work.Construction.FK,
    Work.Spaces.Iθ]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
  rw [MeasureTheory.integral_div]
  refine congrArg (fun t : ℝ => t / r) ?_
  exact MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun θ => by ring)

/-- **`L₁₂(F)` is `C³` on `(0,∞)` when `𝔽K(F)` is `C²`.** -/
theorem contDiffOn_three_L12 {F : ℝ → ℝ → ℝ}
    (hFK : ContDiffOn ℝ 2 (Work.Construction.FK F) (Set.Ioi 0)) :
    ContDiffOn ℝ 3 (Work.Construction.L12 F) (Set.Ioi 0) := by
  have h : ContDiffOn ℝ 2 (fun r : ℝ => Work.Construction.FK F r / r) (Set.Ioi 0) :=
    hFK.div contDiffOn_id (fun r hr => ne_of_gt hr)
  have hprim := contDiffOn_succ_integral_Ioi (n := 2) h
  refine hprim.congr (fun z _ => ?_)
  exact L12_eq_integral_FK F z

end Work.FTS_RegExport.RXT
