/-
Local germ structure of the dynamic rays at their common landing point.

This module sets up the vocabulary for the "germ order" of the dynamic rays that land at a
repelling periodic point `y` of the tricorn `T_c`: the tail of a ray inside a small ball about
`y`, the picture of a co-landing pair inside that ball, and the two sectors cut out by the two
rays of the pair.
-/
import Mathlib
import Submission.Work.LandLeaves.TypeGeometry
import Submission.Work.LandLeaves.ccBet_v2_defs
import Submission.Work.LandLeaves.ray_tail_trap
import Submission.Work.LandLeaves.dynRay_local_subset
import Submission.Work.ELTop.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Classical Set
open scoped Topology

namespace Work.LandLeaves

variable {c : ℂ} {φ : ℂ → ℂ}

/-- The **tail** of the dynamic ray at angle `θ` inside the open disc of radius `ε` about `y`. -/
def rayTail (c : ℂ) (φ : ℂ → ℂ) (θ : ℝ) (y : ℂ) (ε : ℝ) : Set ℂ :=
  {z : ℂ | z ∈ Work.Landing.dynRay c φ θ ∧ ‖z - y‖ < ε}

theorem mem_rayTail {θ : ℝ} {y z : ℂ} {ε : ℝ} :
    z ∈ rayTail c φ θ y ε ↔ z ∈ Work.Landing.dynRay c φ θ ∧ ‖z - y‖ < ε := Iff.rfl

theorem rayTail_subset_dynRay {θ : ℝ} {y : ℂ} {ε : ℝ} :
    rayTail c φ θ y ε ⊆ Work.Landing.dynRay c φ θ := fun _ h => h.1

theorem rayTail_subset_ball {θ : ℝ} {y : ℂ} {ε : ℝ} :
    rayTail c φ θ y ε ⊆ Metric.ball y ε := fun z h => by
  rw [Metric.mem_ball, dist_eq_norm]; exact h.2

theorem rayTail_mono {θ : ℝ} {y : ℂ} {ε ε' : ℝ} (h : ε ≤ ε') :
    rayTail c φ θ y ε ⊆ rayTail c φ θ y ε' := fun _ hz => ⟨hz.1, lt_of_lt_of_le hz.2 h⟩

/-- The **picture** of the co-landing pair `(u,v)` at `y`: the disc of radius `ε` about `y` with
the point `y` and the two ray tails removed.  For small `ε` it has exactly two components, the two
*sectors* cut out by the germs of the rays at `y`. -/
def pairPicture (c : ℂ) (φ : ℂ → ℂ) (u v : ℝ) (y : ℂ) (ε : ℝ) : Set ℂ :=
  Metric.ball y ε \ ({y} ∪ rayTail c φ u y ε ∪ rayTail c φ v y ε)

theorem mem_pairPicture {u v : ℝ} {y z : ℂ} {ε : ℝ} :
    z ∈ pairPicture c φ u v y ε ↔
      z ∈ Metric.ball y ε ∧ z ≠ y ∧ z ∉ rayTail c φ u y ε ∧ z ∉ rayTail c φ v y ε := by
  simp only [pairPicture, Set.mem_sdiff, Metric.mem_ball, mem_union, mem_singleton_iff]
  tauto

theorem pairPicture_subset_ball {u v : ℝ} {y : ℂ} {ε : ℝ} :
    pairPicture c φ u v y ε ⊆ Metric.ball y ε := fun _ h => (mem_pairPicture.mp h).1

/-- The **sector** of the pair picture at `y` through a point `z`. -/
def sector (c : ℂ) (φ : ℂ → ℂ) (u v : ℝ) (y : ℂ) (ε : ℝ) (z : ℂ) : Set ℂ :=
  connectedComponentIn (pairPicture c φ u v y ε) z

theorem sector_subset {u v : ℝ} {y z : ℂ} {ε : ℝ} :
    sector c φ u v y ε z ⊆ pairPicture c φ u v y ε := connectedComponentIn_subset _ _

theorem mem_sector_self {u v : ℝ} {y z : ℂ} {ε : ℝ} (hz : z ∈ pairPicture c φ u v y ε) :
    z ∈ sector c φ u v y ε z := mem_connectedComponentIn hz

end Work.LandLeaves
