import Mathlib
import Submission.Work.Thom.sumStableDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# The `E`-part of the transition functions of `sumEps`

For a complex vector bundle `Z` of rank `m` over `B`, the sum `Z ⊕ ε¹` with the trivial complex line
bundle is presented in the standard fibre `ℂ^{m+1}` by `Work.Thom.sumEps ι₀ Z`, whose transition
functions are obtained from those of the Whitney sum by conjugating with the standard identification
`Work.Thom.prodFinEquiv m` of the product fibre (`Work.Thom.sumEps_coordChange`).

Since `Work.Thom.EpartCLM m` is the projection `ℂ^{m+1} → ℂ^m` onto the first factor of that
identification, and `prodFinEquiv m` is a two-sided inverse of it on the nose, the `E`-part of a
transition function of `sumEps` is the transition function of `Z`:

  `EpartCLM m ((sumEps ι₀ Z).coordChange i j b w) = Z.coordChange i.1 j.1 b (EpartCLM m w)`.

In other words the `E`-summand of `Z ⊕ ε¹` transforms by exactly the transition functions of `Z`:
the fibrewise maps `Work.Thom.sumToZ`/`Work.Thom.sumToQ` that identify `s^*(Q_{Z⊕ε¹})` with `Z` are
compatible with the transition functions, which is what makes them a bundle isomorphism.
-/

namespace Work.Thom

open Work.TangentClasses

noncomputable section

/-- **The `E`-part of a transition function of `sumEps` is the transition function of `Z`.** -/
theorem sumEps_coordChange_Epart {m : ℕ} {B : Type} [TopologicalSpace B] {ι : Type}
    {ι₀ : Type} [Inhabited ι₀] (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (i j : ι × ι₀) (b : B) (w : EuclideanSpace ℂ (Fin (m + 1))) :
    EpartCLM m ((sumEps ι₀ Z).coordChange i j b w) = Z.coordChange i.1 j.1 b (EpartCLM m w) := by
  rw [sumEps_coordChange, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    bundleSum_coordChange]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', EpartCLM,
    ContinuousLinearEquiv.coe_coe]
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rfl

end

end Work.Thom
