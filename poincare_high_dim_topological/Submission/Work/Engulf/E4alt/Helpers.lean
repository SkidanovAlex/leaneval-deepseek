import Mathlib
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.Auxi.SimplexCover
import Submission.Work.Engulf.Auxi.face_subset_of_subset_union
import Submission.Work.Engulf.Auxi.exists_subdiv_affine
import Submission.Work.Geo.Radial.ChartImage
import Submission.Work.Geo.Radial.isOpen_image_of_subset

/-!
# `Work.Engulf.Alt.Helpers` — elementary helpers for the `E4a` normalisation

* `exists_bump` : the continuous bump `b : M → ℝ` with `b = 1` on `ψ '' closedCube ρ` and
  `b = 0` off `ψ '' openCube ρ'` (`ρ < ρ' < 1`), used to glue the perturbed chart map with `f`;
* `exists_margin_isCompact` : the positive distance between a compact set and a disjoint
  nonempty closed set (used for the margins `μ_K`, `μ_ψ` of the normalisation).
-/

open Set Metric PL

namespace Work.Engulf.Alt

variable {n : ℕ} {M : Type*} [MetricSpace M]

/-- **The bump.**  For `ρ < ρ' < 1` there is a continuous `b : M → ℝ` with `0 ≤ b ≤ 1`,
`b = 1` on `ψ '' closedCube ρ` and `b = 0` off `ψ '' openCube ρ'`. -/
theorem exists_bump (ψ : PL.CubeChart n M) {ρ ρ' : ℝ} (hρ : ρ < 1) (hρ' : ρ < ρ')
    (hρ'1 : ρ' < 1) :
    ∃ b : M → ℝ, Continuous b ∧ (∀ x, 0 ≤ b x ∧ b x ≤ 1) ∧
      (∀ x ∈ ψ.toFun '' PL.closedCube ρ, b x = 1) ∧
      (∀ x, x ∉ ψ.toFun '' PL.openCube ρ' → b x = 0) := by
  classical
  have hclosed : IsClosed (ψ.toFun '' PL.closedCube ρ) :=
    (Work.Geo.Radial.isCompact_image_closedCube ψ ρ hρ).isClosed
  have hopen : IsOpen (ψ.toFun '' PL.openCube ρ') :=
    Work.Geo.Radial.isOpen_image_of_subset ψ
      (Work.Engulf.isOpen_openCube ρ') (Work.Engulf.openCube_mono (le_of_lt hρ'1))
  have hdisj : Disjoint ((ψ.toFun '' PL.openCube ρ')ᶜ) (ψ.toFun '' PL.closedCube ρ) := by
    rw [Set.disjoint_left]
    intro y hy hyc
    exact hy (Set.image_mono (Work.Engulf.closedCube_subset_openCube hρ') hyc)
  obtain ⟨b, hb0, hb1, hb01⟩ :=
    exists_continuous_zero_one_of_isClosed hopen.isClosed_compl hclosed hdisj
  exact ⟨b, b.continuous, fun x => ⟨(hb01 x).1, (hb01 x).2⟩, fun x hx => hb1 hx,
    fun x hx => hb0 hx⟩

end Work.Engulf.Alt
