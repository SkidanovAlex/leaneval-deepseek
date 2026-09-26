import Submission.Work.Smooth.Schoenflies.PlaneJordanDataRel
import Submission.Work.Smooth.Plane.Defs

/-!
# The convexity form of the corrected Jordan datum

The sibling chapter `Submission/Work/Smooth/Plane` proves, from its classical input
`Work.Smooth.Plane.PlaneJordanInput` (which is false as stated, `not_planeJordanInput`), the
*convexity form of planar Jordan–Schoenflies*: a simple closed curve lying in a convex set bounds an
embedded disc contained in that set.  The only place where the datum is used in that argument is the
"hard direction of the Jordan curve theorem"
(`Work.Smooth.Plane.PlaneJordanData.inside_not_nullHomotopic`), and the straight-line homotopy that
provides the contradiction is a homotopy of loops *based at `c 0`* whenever the curve is
`2π`-periodic — so the argument works verbatim with the corrected predicate `NullHomotopicRel`.

This file records the corrected forms:

* `nullHomotopicRel_of_convex` — the straight-line homotopy, in the corrected predicate;
* `PlaneJordanDataRel.e_mem_of_convex` — the convexity form of the corrected Jordan datum;
* `planeJordanInputRel_of_smooth` — the corrected input holds for every `C¹` simple closed curve.

## Main results

* `nullHomotopicRel_of_convex : Convex ℝ D → x ∉ D → Continuous c → Periodic c (2π) →
  (∀ t, c t ∈ D) → NullHomotopicRel c x`;
* `PlaneJordanDataRel.e_mem_of_convex : PlaneJordanDataRel c → Convex ℝ D → … → ∀ z, ‖z‖ ≤ 1 →
  h.e z ∈ D`;
* `planeJordanInputRel_of_smooth`.
-/

open Set

namespace Work.Smooth.Schoenflies

noncomputable section

/-- **A loop with trace in a convex set is null-homotopic away from any point outside it**, in the
*corrected* (based) sense: the straight-line homotopy
`H (s, t) = (1 - s) • c (2π t) + s • c 0` stays in the convex set `D`, contracts the loop to the
constant loop, and is relative to the endpoints of the interval precisely because `c` is
`2π`-periodic (`H (s, 0) = H (s, 1) = c 0`). -/
theorem nullHomotopicRel_of_convex {D : Set ℂ} (hD : Convex ℝ D) {x : ℂ} (hx : x ∉ D)
    {c : ℝ → ℂ} (hc : Continuous c) (hper : Function.Periodic c (2 * Real.pi))
    (hmem : ∀ t : ℝ, c t ∈ D) : NullHomotopicRel c x := by
  have haux : ∀ p : Work.Smooth.Plane.ArcInterval × Work.Smooth.Plane.ArcInterval,
      (1 - (p.1 : ℝ)) • c (2 * Real.pi * (p.2 : ℝ)) + (p.1 : ℝ) • c 0 ∈ D := by
    intro p
    refine hD (hmem _) (hmem 0) ?_ ?_ ?_
    · exact sub_nonneg.mpr p.1.2.2
    · exact p.1.2.1
    · ring
  refine ⟨⟨fun p : Work.Smooth.Plane.ArcInterval × Work.Smooth.Plane.ArcInterval =>
      (1 - (p.1 : ℝ)) • c (2 * Real.pi * (p.2 : ℝ)) + (p.1 : ℝ) • c 0, ?_⟩,
    fun p hpx => hx (hpx ▸ haux p), ?_, ?_, ?_⟩
  · fun_prop
  · intro t; simp
  · intro t; simp
  · intro s
    have h2pi : c (2 * Real.pi) = c 0 := by simpa using hper 0
    show (1 - (s : ℝ)) • c (2 * Real.pi * ((0 : Work.Smooth.Plane.ArcInterval) : ℝ))
        + (s : ℝ) • c 0
      = (1 - (s : ℝ)) • c (2 * Real.pi * ((1 : Work.Smooth.Plane.ArcInterval) : ℝ))
        + (s : ℝ) • c 0
    rw [show (2 * Real.pi * ((0 : Work.Smooth.Plane.ArcInterval) : ℝ)) = 0 from by simp,
      show (2 * Real.pi * ((1 : Work.Smooth.Plane.ArcInterval) : ℝ)) = 2 * Real.pi from by simp,
      h2pi]

/-- **The convexity form of planar Jordan–Schoenflies for the corrected datum.**  If `c` is a
`2π`-periodic loop with trace in a convex set `D ⊆ ℂ` and `h : PlaneJordanDataRel c`, then the whole
image of the spanning disc lies in `D`: points outside `D` would be contracted away by the
straight-line homotopy, contradicting `h.inside_not_nullHomotopic`. -/
theorem PlaneJordanDataRel.e_mem_of_convex {c : ℝ → ℂ} (h : PlaneJordanDataRel c) {D : Set ℂ}
    (hD : Convex ℝ D) (hc : Continuous c) (hper : Function.Periodic c (2 * Real.pi))
    (hmem : ∀ t : ℝ, c t ∈ D) (z : Work.InnermostDisk.Disc) : h.e z ∈ D := by
  rcases lt_or_eq_of_le (by simpa using Metric.mem_closedBall.mp z.2 : ‖(z : ℂ)‖ ≤ 1) with hz | hz
  · by_contra hxD
    exact h.inside_not_nullHomotopic z hz (nullHomotopicRel_of_convex hD hxD hc hper hmem)
  · obtain ⟨θ, hθ⟩ := Work.Smooth.Plane.exists_circlePoint_eq_of_norm_eq_one hz
    rw [← hθ, h.boundary θ]
    exact hmem θ

/-- **The corrected classical input holds for every `C¹` simple closed curve** — the input form of
`nonempty_planeJordanDataRel_of_smooth`. -/
theorem planeJordanInputRel_of_smooth (c : ℝ → ℂ) (hdiff : ContDiff ℝ 1 c) (hc : Continuous c)
    (hper : Function.Periodic c (2 * Real.pi)) (hinj : Set.InjOn c (Set.Ico 0 (2 * Real.pi))) :
    Nonempty (PlaneJordanDataRel c) :=
  nonempty_planeJordanDataRel_of_smooth hc hper hinj hdiff

end

end Work.Smooth.Schoenflies
