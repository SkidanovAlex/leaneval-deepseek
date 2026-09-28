import Mathlib
import Submission.Work.SSS.E2Zero.Defs
import Submission.Work.SSS.E2Zero.ker_chi_map
import Submission.Work.SSS.LESFacts

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

namespace Work.SSS.E2Zero

attribute [-instance] AddCommGroup.toIntModule

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {C : ChainComplex (ModuleCat ℤ) ℕ}

/-- Transport of `ker_chi_map` along the linear equivalence `hT ξ t`: the kernel of `chi ξ t`
pulled back along `hT ξ t` is the range of the connecting map `kF ξ 0 t`.  The pullback adds
`ker (hT.symm) = ⊥` to `ker (chi ξ t)`, which is why the statement mentions `hT`. -/
theorem ker_comap_hT (ξ : Filtration C) (t : ℕ) :
    Submodule.comap ((hT ξ t).symm).toLinearMap (LinearMap.range (kF ξ 0 t).hom)
      = LinearMap.ker (chi ξ t) := by
  have hbot : LinearMap.ker ((hT ξ t).symm).toLinearMap = ⊥ :=
    LinearMap.ker_eq_bot.mpr (hT ξ t).symm.injective
  rw [← ker_chi_map ξ t, Submodule.comap_map_eq, hbot, sup_bot_eq]

end

end Work.SSS.E2Zero
