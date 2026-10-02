/-
Work.MRMT.Found — the principal solution `principal μ` of the Beltrami equation.

`principal μ` is the homeomorphism of `ℂ` produced by the limit construction
(`principalData_exists`) when `μ` is admissible, and the identity otherwise.  Its defining
properties are `principal_decay` (the normalisation `φ z = z + O(1/‖z‖)`) and the Beltrami
equation `principalData_beltrami`; the approximating sequence is available as
`principalData μ hμ`.
-/
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.principalData_exists

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Filter Topology Complex Function Classical
open scoped ENNReal

namespace Work.MRMT.Found

/-- The `PrincipalData` record realising the principal solution for an admissible
coefficient. -/
noncomputable def principalData (μ : ℂ → ℂ) (hμ : Admissible μ) : PrincipalData μ :=
  Classical.choice (principalData_exists hμ)

/-- The **principal solution** of the Beltrami equation for `μ`: the homeomorphism of `ℂ`
produced by the limit construction for admissible `μ`, and the identity otherwise. -/
noncomputable def principal (μ : ℂ → ℂ) : ℂ ≃ₜ ℂ :=
  if h : Admissible μ then (principalData μ h).φ else Homeomorph.refl ℂ

theorem principal_eq_principalData {μ : ℂ → ℂ} (hμ : Admissible μ) :
    principal μ = (principalData μ hμ).φ := by
  simp [principal, hμ]

/-- **M1.** The normalisation of the principal solution: `principal μ z = z + O(1/‖z‖)`. -/
theorem principal_decay {μ : ℂ → ℂ} (hμ : Admissible μ) :
    ∃ C R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖principal μ z - z‖ ≤ C / ‖z‖ := by
  refine ⟨(principalData μ hμ).C, (principalData μ hμ).R, fun z hz => ?_⟩
  rw [principal_eq_principalData hμ]
  exact (principalData μ hμ).decay z hz

/-- The principal solution is the locally uniform limit of the C¹ approximants. -/
theorem tendsto_principalData_Fn {μ : ℂ → ℂ} (hμ : Admissible μ) :
    TendstoLocallyUniformly (fun n => (((principalData μ hμ).Fn n : ℂ ≃ₜ ℂ) : ℂ → ℂ))
      (principal μ : ℂ → ℂ) Filter.atTop := by
  rw [principal_eq_principalData hμ]
  exact (principalData μ hμ).tendsto_Fn

end Work.MRMT.Found
