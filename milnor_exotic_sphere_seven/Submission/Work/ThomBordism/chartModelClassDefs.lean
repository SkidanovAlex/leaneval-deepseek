import Mathlib
import Submission.Work.ThomBordism.ambientClassDefs
import Submission.Work.ThomBordism.ambientLocalDefs
import Submission.Work.ThomBordism.ambientLocalDefs2
import Submission.Work.ThomBordism.tubeInvMap_pullback_chart

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# The chart model class on the normal bundle

`Work.ThomBordism.chartModelClass E C x hcont` is the ν-side avatar of the determinate ambient
class `Work.ThomBordism.ambientStandardClass E C x`: the pull-back of the model class
`Work.ThomBordism.stdModelGen (8+k)` along the capped ambient chart map
`p ↦ chartAffine E x (cap E ε p)`, which is a map of pairs `(ν, ν∖0) → (ℝ^{8+k}, {0}ᶜ)` by
`Work.ThomBordism.chartAffine_cap_ne_zero`.

The main identity of this file, `ambientStandardClass_eq_chartModelClass`, is the tube inverse of
that statement: `C.inv` pulls `chartModelClass` back to `ambientStandardClass`, because the capping
is the identity on the image of `C.inv` and `chartAffine E x ∘ C.inv` is the translation
`y ↦ y - E.e x`.
-/

open CategoryTheory

namespace Work.ThomBordism

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- **The chart-model class on the normal bundle.** -/
noncomputable def chartModelClass (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (x : V.pt)
    (hcont : Continuous fun p : Work.Tubular.NormalTotal E =>
      Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε p)) :
    Work.Thom.RelCoh ℤ (8 + k) (TopCat.of (Work.Tubular.NormalTotal E))
      (Work.Tubular.normalNonzero E) :=
  (Work.Thom.relCohMap
    ⟨fun p : Work.Tubular.NormalTotal E =>
      Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε p), hcont⟩
    (Work.Tubular.normalNonzero E) ({0}ᶜ : Set (Work.Tubular.Euc (8 + k)))
    (fun p hp => Set.mem_compl_singleton_iff.mpr
      (Work.ThomBordism.chartAffine_cap_ne_zero E C x hp)) ℤ (8 + k)).hom
    (Work.ThomBordism.stdModelGen (8 + k))

/-- The tube inverse of the chart model class is the ambient standard class. -/
theorem ambientStandardClass_eq_chartModelClass
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (x : V.pt)
    (hcont : Continuous fun p : Work.Tubular.NormalTotal E =>
      Work.ThomBordism.chartAffine E x (Work.ThomBordism.cap E ε p)) :
    (Work.Thom.relCohMap (Work.ThomBordism.tubeInvMap E C) (Work.ThomBordism.tubeInvPunct E C)
        (Work.Tubular.normalNonzero E) (fun y hy => hy) ℤ (8 + k)).hom
      (chartModelClass E C x hcont : Work.Thom.RelCoh ℤ (8 + k)
        (↑(TopCat.of (Work.Tubular.NormalTotal E))) (Work.Tubular.normalNonzero E))
      = Work.ThomBordism.ambientStandardClass E C x := by
  have h := Work.ThomBordism.tubeInvMap_pullback_chart V k E C x hcont
  rw [chartModelClass]
  exact h

end

end Work.ThomBordism
