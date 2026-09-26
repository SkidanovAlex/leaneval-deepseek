import Mathlib
import Submission.Work.Drive.arcChamferCorner

/-!
# The mirror corner: the second chamfer against the retained arc

`Submission/Work/Drive/arcChamferCorner.lean` settles the corner where the retained arc meets
the *first* chamfer (at the arc's last retained point `r (b - lam (b - a))`).  The sweep loop has a
second such corner, where the *second* chamfer meets the retained arc at its first retained point
`r (a + lam (b - a))`; there the two adjacent branch directions are the chamfer direction
`(r a + lam • (r b - r a)) - r (a + lam (b - a))` and the tangent `velocity r (a + lam (b - a))`, and
the `π`-corner would be `∃ c > 0` with the first equal to `c •` the second.

This is the *mirror* of the first corner under the reversal of the knot, `x ↦ r (a + b - x)` (again
a smooth knot, `Work.Drive.mirror_isSmoothKnot`), so it follows from the first corner by pure
bookkeeping: the reversal swaps the two ends of the retained arc, hence the two corners, and
negates the velocity.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology

/-- **The reversal of a smooth knot is a smooth knot.** -/
lemma mirror_isSmoothKnot {r : ℝ → Space} (hr : IsSmoothKnot r) (c : ℝ) :
    IsSmoothKnot (fun x : ℝ => r (c - x)) where
  smooth := hr.smooth.comp (contDiff_const.sub contDiff_id)
  periodic := by
    intro t
    show r (c - (t + period)) = r (c - t)
    rw [show c - (t + period) = (c - t) - period by ring,
      ← hr.periodic (c - t - period)]
    congr 1
    ring
  injective_on_period := by
    intro x hx y hy hxy
    have hmod : ((c - x : ℝ) : AddCircle period) = ((c - y : ℝ) : AddCircle period) :=
      knotMap_injective hr (by
        rw [knotMap_coe' hr.periodic, knotMap_coe' hr.periodic]
        exact hxy)
    have hx' : c - x ∈ Set.Ioc (c - period) (c - period + period) :=
      ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have hy' : c - y ∈ Set.Ioc (c - period) (c - period + period) :=
      ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have h : c - x = c - y := (AddCircle.coe_eq_coe_iff_of_mem_Ioc hx' hy').mp hmod
    linarith
  regular := by
    intro t
    have h2 : HasDerivAt r (velocity r (c - t)) (c - t) :=
      ((hr.smooth.differentiable (by simp)) (c - t)).hasDerivAt
    have h1 : HasDerivAt (fun x : ℝ => c - x) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub c
    have h : HasDerivAt (fun y : ℝ => r (c - y)) ((-1 : ℝ) • velocity r (c - t)) t :=
      HasDerivAt.scomp (x := t) (h := fun y : ℝ => c - y) (g₁ := r)
        (g₁' := velocity r (c - t)) (by simpa using h2) h1
    have h3 : (-1 : ℝ) • velocity r (c - t) = - velocity r (c - t) := by simp
    rw [h3] at h
    intro hzero
    have hzero' : deriv (fun y : ℝ => r (c - y)) t = 0 := by simpa [velocity] using hzero
    have hd := h.deriv
    rw [hzero'] at hd
    exact hr.regular (c - t) (neg_eq_zero.mp hd.symm)

/-- **The velocity of the reversed knot.** -/
lemma mirror_velocity {r : ℝ → Space} (hr : ContDiff ℝ ⊤ r) (c x : ℝ) :
    velocity (fun y : ℝ => r (c - y)) x = - velocity r (c - x) := by
  have h2 : HasDerivAt r (velocity r (c - x)) (c - x) :=
    ((hr.differentiable (by simp)) (c - x)).hasDerivAt
  have h1 : HasDerivAt (fun y : ℝ => c - y) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub c
  have h : HasDerivAt (fun y : ℝ => r (c - y)) ((-1 : ℝ) • velocity r (c - x)) x :=
    HasDerivAt.scomp (x := x) (h := fun y : ℝ => c - y) (g₁ := r)
      (g₁' := velocity r (c - x)) (by simpa using h2) h1
  have h3 : (-1 : ℝ) • velocity r (c - x) = - velocity r (c - x) := by simp
  rw [h3] at h
  simpa [velocity] using h.deriv

/-- **The arc/second-chamfer corner is not a `π`-corner.** -/
theorem arcChamfer_no_piCorner_mirror {r : ℝ → Space} (hr : IsSmoothKnot r) {a b : ℝ}
    (hab : a < b) :
    ∃ L : ℝ, 0 < L ∧ ∀ lam : ℝ, 0 < lam → lam ≤ L →
      ¬ ∃ c : ℝ, 0 < c ∧
        (r a + lam • (r b - r a)) - r (a + lam * (b - a))
          = c • velocity r (a + lam * (b - a)) := by
  obtain ⟨L, hL, hmain⟩ :=
    arcChamferCorner_noOpposite (r := fun x : ℝ => r (a + b - x)) (mirror_isSmoothKnot hr (a + b)) hab
  refine ⟨L, hL, fun lam hlam hlamL => ?_⟩
  rintro ⟨c, hc, heq⟩
  refine hmain lam hlam hlamL ⟨c, hc, ?_⟩
  have hrv : velocity (fun y : ℝ => r (a + b - y)) (b - lam * (b - a))
      = - velocity r (a + lam * (b - a)) := by
    have h := mirror_velocity hr.smooth (a + b) (b - lam * (b - a))
    rw [show a + b - (b - lam * (b - a)) = a + lam * (b - a) from by ring] at h
    exact h
  show (r (a + b - b) - lam • (r (a + b - b) - r (a + b - a)))
      - r (a + b - (b - lam * (b - a)))
      = -c • velocity (fun y : ℝ => r (a + b - y)) (b - lam * (b - a))
  rw [hrv, show a + b - b = a from by ring, show a + b - a = b from by ring,
    show a + b - (b - lam * (b - a)) = a + lam * (b - a) from by ring]
  rw [show -c • -velocity r (a + lam * (b - a)) = c • velocity r (a + lam * (b - a)) from by
    rw [smul_neg, neg_smul, neg_neg]]
  rw [show r a - lam • (r a - r b) = r a + lam • (r b - r a) from by
    rw [smul_sub, smul_sub]; abel]
  exact heq

end Work.Drive
