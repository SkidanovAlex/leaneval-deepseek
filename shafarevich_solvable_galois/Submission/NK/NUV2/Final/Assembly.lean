import Mathlib
import Submission.NK.NUV2.Final.Wiring
import Submission.NK.NUV2.Final.Koenig
import Submission.NK.NUV2.Final.levelSymbol_ker_alt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local reciprocity law at every completion

The final assembly: the coherent family of fundamental classes (L3,
`NK.NUV2.RouteE.exists_compatible_fundamentalClasses`) together with L7
(`NK.NUV2.Final.levelSymbol_ker_alt`, the kernel/surjectivity of the level symbol at every finite
abelian level) gives `Nonempty (NK.LocalArtin.KernelCondition (Q.adicCompletion K) _)`, via the
proved wiring `NK.NUV2.Final.nonempty_kernelCondition_of_family`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory

namespace NK.NUV2.Final

/-- **The local reciprocity law in kernel form at every completion.** -/
theorem nonempty_kernelCondition_of_L7 {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Nonempty (NK.LocalArtin.KernelCondition (Q.adicCompletion K)
      (SeparableClosure (Q.adicCompletion K))) := by
  refine nonempty_kernelCondition_of_family Q
    (NK.NUV2.FinalKoenig.exists_compatible_fundamentalClasses Q) ?_
  intro L hfd hnorm hfin hcomm u hu
  haveI : IsGalois (Q.adicCompletion K) ↥L := NK.NUV2.RouteE.isGalois_level Q L
  exact levelSymbol_ker_alt (K := K) Q hcomm u hu

end NK.NUV2.Final
