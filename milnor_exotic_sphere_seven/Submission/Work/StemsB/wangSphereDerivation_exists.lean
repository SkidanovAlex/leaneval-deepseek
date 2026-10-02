import Mathlib
import Submission.Work.StemsB.wangThetaTw
import Submission.Work.StemsB.wangThetaTw_derivation
import Submission.Work.StemsB.wangGammaExplicit
import Submission.Work.StemsB.WangDerivation

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Wang transgression over a sphere is a derivation

The main statement of D2: for a Hurewicz fibration `p : E → Sᵇ` with the two fibrewise
trivialisations over the outer piece and the inner cube, there are identifications `γ` of the
source and `τS` of the target of the Wang transgression with which the transgression is a
derivation of degree `-(b-1)`.

The witnesses are `γ = wangGammaExplicit` (the pullback along `π₂ ∘ Φ_O`) and
`τS = wangTauSTw` (excision followed by the trivialisation, the degree transport, the inverse
Thom isomorphism of the collar and the clutching identification `ρ`, twisted by the sign
`c_n = (-1)^{b n}`); `wangCohShiftθ_tw_apply` computes the resulting transgression as
`ω = c • θ`, and `wangThetaTw_derivation` is the derivation property of `ω`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace Work.StemsB

noncomputable section

theorem wangSphereDerivation_exists (b : ℕ) (hb : 2 ≤ b) (E : Type) [TopologicalSpace E]
    (p : ContinuousMap E (Work.StemsB.SphModel b)) (hp : Work.StemsB.IsHurewiczFibration p)
    (hT_O : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopOuter b) (Work.StemsB.dOuter b))
    (d_G : ↥(Work.StemsB.sphLoopBig b))
    (hT_G : Work.StemsB.FibrewiseTrivial p (Work.StemsB.sphLoopBig b) d_G) :
    ∃ (γ : ∀ k : ℕ,
        Work.Cohomology.singularCohomology ℤ k (TopCat.of (p ⁻¹' Work.StemsB.sphLoopOuter b)) ≅
        Work.Cohomology.singularCohomology ℤ k (Work.StemsB.wangCohFsp b p))
      (τS : ∀ n : ℕ,
        (Work.Cohomology.relComplex ℤ (TopCat.of E) (p ⁻¹' Work.StemsB.sphLoopOuter b)).homology
            (n + b + 1) ≅
        Work.Cohomology.singularCohomology ℤ (n + 1) (Work.StemsB.wangCohFsp b p)),
      Work.StemsB.WangCohShiftDerivation (TopCat.of E) (p ⁻¹' Work.StemsB.sphLoopOuter b)
        (Work.StemsB.wangCohFsp b p) b γ τS := by
  refine ⟨wangGammaExplicit b p hT_O, fun n => wangTauSTw b hb E p hT_O d_G hT_G n, ?_⟩
  unfold WangCohShiftDerivation
  intro n n' a b'
  rw [wangCohShiftθ_tw_apply b hb E p hT_O d_G hT_G (n + n' + b),
    wangCohShiftθ_tw_apply b hb E p hT_O d_G hT_G n,
    wangCohShiftθ_tw_apply b hb E p hT_O d_G hT_G n']
  exact wangThetaTw_derivation b hb E p d_G hT_G hT_O n n' a b'

end

end Work.StemsB
