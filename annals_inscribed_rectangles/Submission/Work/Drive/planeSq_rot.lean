import Mathlib
import Submission.Work.Drive.planeSquare
import Submission.Work.Drive.rotLens_rotCapping_isAction

/-!
# The plane sweep is equivariant under the rotation of the capping space

The disk presentation `Work.Drive.diskPt` of the capped plane `P_u` depends on the rotation parameter
`u` only through the rotation of the capping space: the cap chart carries the cap angle `θ + u` and
the strip chart is `rotCapping u` applied to the un-rotated strip point.  Consequently the plane sweep
`Work.Drive.planeSq` satisfies

> `planeSq (u + v) = rotCapping v ∘ planeSq u`,

the *parametrised* form of the equivariance used in `Submission/Work/Drive/orderSplit_model.lean`
("`rotCapping v ∘ sweepChain a ha P = sweepChain a ha (rotCapping v ∘ P)`"): rotating the plane by `v`
is the same as rotating the sweep of the plane.

The file proves the two chart computations

* `Work.Drive.capDiskPt_rot` — the cap chart,
* `Work.Drive.stripDiskPt_rot` — the strip chart,

glues them along `‖z‖ = 1/2` into `Work.Drive.diskPt_rot`, and finally unfolds `planeSq`.
-/

set_option autoImplicit false

namespace Work.Drive

open scoped Topology ContDiff
open Manifold

noncomputable section

open Submission.Configuration (muOrd)

/-- **The rotation action law, additive form.**  `rotCapping` is a right action
(`Work.Drive.rotCapping_add`), so `rotCapping (u + v) = rotCapping v ∘ rotCapping u` — the direction in
which a rotation of the plane's parameter is applied to an already rotated plane. -/
lemma rotCapping_add_apply (u v : UnitAddCircle) (x : CappingSpace) :
    rotCapping (u + v) x = rotCapping v (rotCapping u x) := by
  rw [add_comm u v, rotCapping_add]
  rfl

/-! ## The cap chart -/

/-- **The cap chart is equivariant.**  The only occurrence of the rotation parameter `u` in the cap
cone point `Work.Drive.capConePt` is the added cap angle `θ + u`, which is exactly what `rotCap`
changes; so rotating the plane by `v` is the same as `u ↦ u + v`. -/
lemma capDiskPt_rot {r₀ : ℝ} {ρ Ψ Θ : ℝ → ℝ} (hr₀ : 0 < r₀) (hρ : ∀ t : ℝ, 0 < ρ t)
    (u v : UnitAddCircle) (z : ℂ) (hz : ‖z‖ < 1 / 2) :
    capDiskPt r₀ ρ Ψ Θ (u + v) hr₀ hρ z hz
      = rotCapping v (capDiskPt r₀ ρ Ψ Θ u hr₀ hρ z hz) := by
  rw [capDiskPt_def, capDiskPt_def, capPtClass_def, capPtClass_def, rotCapping_mk, rotSum_inr]
  refine congrArg (fun Q : CapPiece =>
    (Quotient.mk'' (Sum.inr Q) : CappingSpace)) ?_
  refine Subtype.ext ?_
  simp only [rotCap_val, capConePt_fst, capConePt_snd, capConePt_thd]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [capConePt_fst]
  · simp only [capConePt_snd]
    abel
  · simp only [capConePt_thd]

/-! ## The strip chart -/

/-- **The strip chart is equivariant.**  The strip chart through which `stripDiskPt` is defined is
already `rotCapping u` applied to the un-rotated configuration point, so this is the action law. -/
lemma stripDiskPt_rot {γ : Circle → ℝ × ℝ}
    {μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ}
    (hγne : ∀ x : Circle, γ x ≠ 0) (hγinj : Function.Injective γ)
    (hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = muOrd γ (x, y))
    (hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0))
    (u v : UnitAddCircle) (z : ℂ) (hz : 1 / 2 ≤ ‖z‖) (hz1 : ‖z‖ ≤ 1) :
    stripDiskPt μ (u + v) hγne hγinj hμne hμdiag z hz hz1
      = rotCapping v (stripDiskPt μ u hγne hγinj hμne hμdiag z hz hz1) := by
  unfold stripDiskPt
  rw [stripPt_def, stripPt_def]
  exact rotCapping_add_apply u v _

/-! ## The disk presentation and the plane sweep -/

/-- **The disk presentation of the capped plane is equivariant.**  The two charts agree on the
overlap, so the equivariance of each of them (`Work.Drive.capDiskPt_rot`,
`Work.Drive.stripDiskPt_rot`) gives it for `Work.Drive.diskPt`. -/
lemma diskPt_rot {γ : Circle → ℝ × ℝ}
    {μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ} {ρ Ψ Θ : ℝ → ℝ} {r₀ : ℝ}
    (hr₀ : 0 < r₀) (hρ : ∀ t : ℝ, 0 < ρ t)
    (hγne : ∀ x : Circle, γ x ≠ 0) (hγinj : Function.Injective γ)
    (hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = muOrd γ (x, y))
    (hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0))
    (u v : UnitAddCircle) (z : ℂ) (hz1 : ‖z‖ ≤ 1) :
    diskPt μ ρ Ψ Θ r₀ (u + v) hr₀ hρ hγne hγinj hμne hμdiag z hz1
      = rotCapping v (diskPt μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag z hz1) := by
  by_cases h : ‖z‖ < 1 / 2
  · rw [diskPt_of_lt h, diskPt_of_lt h]
    exact capDiskPt_rot hr₀ hρ u v z h
  · rw [diskPt_of_ge (le_of_not_gt h), diskPt_of_ge (le_of_not_gt h)]
    exact stripDiskPt_rot hγne hγinj hμne hμdiag u v z (le_of_not_gt h) hz1

theorem planeSq_rot {γ : Circle → ℝ × ℝ}
    {μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ} {ρ Ψ Θ : ℝ → ℝ} {r₀ : ℝ}
    (hr₀ : 0 < r₀) (hρ : ∀ t : ℝ, 0 < ρ t)
    (hγne : ∀ x : Circle, γ x ≠ 0) (hγinj : Function.Injective γ)
    (hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = Submission.Configuration.muOrd γ (x, y))
    (hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0))
    (u v : UnitAddCircle) :
    planeSq μ ρ Ψ Θ r₀ (u + v) hr₀ hρ hγne hγinj hμne hμdiag
      = rotCapping v ∘ planeSq μ ρ Ψ Θ r₀ u hr₀ hρ hγne hγinj hμne hμdiag := by
  funext y
  rw [Function.comp_apply, planeSq, planeSq]
  exact diskPt_rot hr₀ hρ hγne hγinj hμne hμdiag u v (sqDisk (clampBox y)) _

end

end Work.Drive
