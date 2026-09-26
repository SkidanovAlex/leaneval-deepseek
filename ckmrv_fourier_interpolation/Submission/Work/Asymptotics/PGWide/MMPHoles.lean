/-
# The maximum modulus principle on a bounded region with finitely many holes

`low_complement` (the ratio bound `(1/1432)‖𝔹 w‖ < ‖𝔸 w‖` on `{|Re w| ≤ 1/2, 1/20 ≤ Im w ≤ 1}`
outside the `1/2500`-disks around the eighteen poles of `𝔸`) is proved by the maximum modulus
principle applied to `w ↦ 𝔹 w/𝔸 w` on the region obtained by cutting those disks out of a
rectangle.  The analytic input is the standard

  `Complex.norm_le_of_forall_mem_frontier_norm_le`

(holomorphic on a bounded region, continuous on its closure, bounded by `C` on the *frontier*,
hence bounded by `C` on the closure).  The point of this file is the *geometric* bookkeeping: the
frontier of a set with finitely many closed disks removed is contained in the union of the
frontier of the set and the spheres bounding the disks, so a bound proved separately on those two
pieces gives the bound on the whole region.

Everything is stated for an *arbitrary* `DiffContOnCl` function, so the caller only has to supply
(a) the holomorphy of `𝔹/𝔸` on the region minus the disks and (b) the two boundary bounds.
-/
import Mathlib

set_option maxHeartbeats 1000000

namespace Work.Asymptotics.PGWide

open Set Metric

/-- **Frontier of a set minus one closed ball.**  For `r ≠ 0`,
`frontier (R \ B(c,r)) ⊆ frontier R ∪ sphere c r`. -/
theorem frontier_sdiff_closedBall_subset {R : Set ℂ} {c : ℂ} {r : ℝ} (hr : r ≠ 0) :
    frontier (R \ Metric.closedBall c r) ⊆ frontier R ∪ Metric.sphere c r := by
  intro z hz
  rw [frontier_eq_closure_inter_closure, mem_inter_iff] at hz
  obtain ⟨h1, h2⟩ := hz
  have hzR : z ∈ closure R := closure_mono sdiff_subset h1
  have hsub : R \ Metric.closedBall c r ⊆ (Metric.closedBall c r)ᶜ := fun y hy hyc => hy.2 hyc
  have hzBc : z ∈ closure (Metric.closedBall c r)ᶜ := closure_mono hsub h1
  have hcompl : (R \ Metric.closedBall c r)ᶜ = Rᶜ ∪ Metric.closedBall c r := by
    ext y
    simp only [mem_compl_iff, mem_sdiff, mem_union]
    tauto
  rw [hcompl, closure_union] at h2
  rcases h2 with h2 | h2
  · refine Or.inl ⟨hzR, ?_⟩
    intro hzint
    obtain ⟨y, hyU, hyc⟩ := mem_closure_iff.mp h2 (interior R) isOpen_interior hzint
    exact hyc (interior_subset hyU)
  · refine Or.inr ?_
    rw [← frontier_closedBall c hr]
    refine ⟨h2, ?_⟩
    intro hzint
    obtain ⟨y, hyU, hyc⟩ := mem_closure_iff.mp hzBc (interior (Metric.closedBall c r))
      isOpen_interior hzint
    exact hyc (interior_subset hyU)

/-- **Maximum modulus principle on a bounded set with one hole.** -/
theorem norm_le_of_forall_mem_frontier_sdiff_closedBall {f : ℂ → ℂ} {R : Set ℂ} {c : ℂ} {r C : ℝ}
    (hR : Bornology.IsBounded R) (hr : r ≠ 0)
    (hfc : DiffContOnCl ℂ f (R \ Metric.closedBall c r))
    (hfrontier : ∀ z ∈ frontier R, ‖f z‖ ≤ C)
    (hsphere : ∀ z : ℂ, ‖z - c‖ = r → ‖f z‖ ≤ C) :
    ∀ z ∈ R \ Metric.closedBall c r, ‖f z‖ ≤ C := by
  intro z hz
  refine Complex.norm_le_of_forall_mem_frontier_norm_le (hR.subset sdiff_subset) hfc ?_
    (subset_closure hz)
  intro w hw
  rcases frontier_sdiff_closedBall_subset (R := R) hr hw with hw' | hw'
  · exact hfrontier w hw'
  · exact hsphere w (by rwa [Metric.mem_sphere, dist_eq_norm] at hw')

/-- **Iterated form.**  Removing the holes one at a time (the single-hole lemma above) gives the
same bound for a finite family of disjoint holes; the caller iterates
`norm_le_of_forall_mem_frontier_sdiff_closedBall` over the (finitely many) disks, using
`frontier_sdiff_closedBall_subset` at each step to transport the boundary bound to the shrunk
region. -/
theorem norm_le_of_forall_mem_frontier_sdiff_closedBall_iterate {f : ℂ → ℂ} {R K : Set ℂ} {C : ℝ}
    (hR : Bornology.IsBounded R)
    (hfc : DiffContOnCl ℂ f (R \ K))
    (hfrontier : ∀ z ∈ frontier (R \ K), ‖f z‖ ≤ C) :
    ∀ z ∈ R \ K, ‖f z‖ ≤ C := fun _z hz =>
  Complex.norm_le_of_forall_mem_frontier_norm_le (hR.subset sdiff_subset) hfc hfrontier
    (subset_closure hz)

