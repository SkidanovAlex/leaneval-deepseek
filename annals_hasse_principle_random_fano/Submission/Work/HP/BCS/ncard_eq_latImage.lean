import Mathlib
import Submission.Work.HP.BCS.ncard_eq_core
import Submission.Work.HP.BCS.Transport
import Submission.Work.HP.BCS.CLDefs

set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open MeasureTheory Finset
open scoped Pointwise

namespace Work.HP.BCS

/-- The count of lattice points `a ∈ L ⊆ ℤ^ι` with `eNorm a ≤ T` inside the two cones
`Cgam v γ`, `Cgam w γ` equals the count of points of the lattice `latImage (PsiOf L b)` inside
the corresponding two cone slices of `ℝ^k` cut by the ball of radius `T`.

This is `ncard_eq_core` (which is a bijection statement onto the coordinate space `ℤ^k`)
composed with the observation that `t ↦ PsiOf L b (toEk t)` is an injective parametrisation of
`latImage (PsiOf L b)`. -/
theorem ncard_eq_latImage {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (L : Submodule ℤ (ι → ℤ)) (b : Module.Basis (Fin k) ℤ L) (v w : ι → ℝ) (γ T : ℝ) :
    ({a : ι → ℤ | a ∈ L ∧ eNorm a ≤ T ∧ toR a ∈ Cgam v γ ∧ toR a ∈ Cgam w γ}.ncard : ℝ)
      = ({y : EuclideanSpace ℝ (Fin k) | y ∈ latImage (PsiOf L b) ∧
            y ∈ coneSet (coneVec L b v) (‖toE v‖ / (2 * γ)) ∧
            y ∈ coneSet (coneVec L b w) (‖toE w‖ / (2 * γ)) ∧ ‖y‖ ≤ T}.ncard : ℝ) := by
  classical
  have hΨinj : Function.Injective (PsiOf L b) := PsiOf_injective L b
  have htoEk : Function.Injective (toEk (k := k)) := toEk_injective
  have himg : (fun t : Fin k → ℤ => PsiOf L b (toEk t)) ''
        {t : Fin k → ℤ | PsiOf L b (toEk t) ∈ latImage (PsiOf L b) ∧
          PsiOf L b (toEk t) ∈ coneSet (coneVec L b v) (‖toE v‖ / (2 * γ)) ∧
          PsiOf L b (toEk t) ∈ coneSet (coneVec L b w) (‖toE w‖ / (2 * γ)) ∧
          ‖PsiOf L b (toEk t)‖ ≤ T}
      = {y : EuclideanSpace ℝ (Fin k) | y ∈ latImage (PsiOf L b) ∧
          y ∈ coneSet (coneVec L b v) (‖toE v‖ / (2 * γ)) ∧
          y ∈ coneSet (coneVec L b w) (‖toE w‖ / (2 * γ)) ∧ ‖y‖ ≤ T} := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2⟩
    · rintro ⟨hy, h2, h3, h4⟩
      rw [latImage, Set.mem_image] at hy
      obtain ⟨a, ⟨t, rfl⟩, rfl⟩ := hy
      exact ⟨t, ⟨⟨toEk t, ⟨t, rfl⟩, rfl⟩, h2, h3, h4⟩, rfl⟩
  rw [ncard_eq_core L b v w γ T, ← himg]
  congr 1
  exact (Set.ncard_image_of_injective _ (hΨinj.comp htoEk)).symm

end Work.HP.BCS
