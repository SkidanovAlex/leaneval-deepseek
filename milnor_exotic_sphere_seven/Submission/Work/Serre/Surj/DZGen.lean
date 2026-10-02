import Submission.Work.Serre.crossProduct_defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The generator of the coefficient complex `ℤ[r+1]`, as a cycle
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct

namespace Work.Serre.Surj

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- The generator of the coefficient complex `ℤ[r+1]`, as a cycle of degree `r+1`. -/
noncomputable def dzGenCycle (r : ℕ) : ↥((Work.Serre.dzComplex r).cycles (r + 1)) :=
  Work.Kunneth.cycleOf (Work.Serre.dzComplex r) (r + 1)
    ⟨(Work.Serre.dzIso r).inv (1 : ℤ), by
      show (ModuleCat.Hom.hom ((Work.Serre.dzComplex r).d (r + 1) r)) ((Work.Serre.dzIso r).inv (1 : ℤ)) = 0
      rw [Work.Serre.dzComplex_d_succ, ModuleCat.hom_zero, LinearMap.zero_apply]⟩

/-- The underlying chain of `dzGenCycle` is the generator of `ℤ`. -/
theorem iCycles_dzGenCycle (r : ℕ) :
    (ModuleCat.Hom.hom ((Work.Serre.dzComplex r).iCycles (r + 1))) (dzGenCycle r)
      = (Work.Serre.dzIso r).inv (1 : ℤ) :=
  Work.Kunneth.iCycles_cycleOf (Work.Serre.dzComplex r) (r + 1) _

end

end Work.Serre.Surj
