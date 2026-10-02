import Mathlib
import Submission.Work.Agree.whitneySumRCongr
import Submission.Work.Whitney.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# Congruence of the direct sum in its second argument

The direct sum `Work.Whitney.whitneySum Z₁ Z₂` is `Work.Whitney.sumCore (sumFibreC m₁ m₂) Z₁ Z₂`,
so the congruence of the sum (`Work.Agree.nonempty_bundleIso_sumCore_congr`) applies with the
identity on the first summand: an isomorphism `Z₂ ≅ Z₂'` induces
`Z₁ ⊕ Z₂ ≅ Z₁ ⊕ Z₂'`.  (A copy of `Work.Gen.nonempty_bundleIso_whitneySum_snd` inside the
Leray–Hirsch area, whose import closure stays inside the areas that build.)
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

noncomputable section

/-- **Congruence of the complex direct sum in its second argument.** -/
theorem nonempty_bundleIso_whitneySum_snd {m₁ m₂ m₂' : ℕ} {ι₁ ι₂ ι₂' : Type}
    {B : Type} [TopologicalSpace B]
    (Z₁ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₁)) ι₁)
    (Z₂ : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂)) ι₂)
    (Z₂' : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m₂')) ι₂')
    (e : Work.Thom.BundleIso Z₂ Z₂') :
    Nonempty (Work.Thom.BundleIso (Work.Whitney.whitneySum Z₁ Z₂)
      (Work.Whitney.whitneySum Z₁ Z₂')) := by
  obtain ⟨φ⟩ := Work.Agree.nonempty_bundleIso_sumCore_congr (𝕜 := ℂ)
    (Work.Whitney.sumFibreC m₁ m₂) (Work.Whitney.sumFibreC m₁ m₂') Z₁ Z₁ Z₂ Z₂'
    (Work.Thom.BundleIso.refl Z₁) e
  exact ⟨φ⟩

end

end Work.LerayHirsch
