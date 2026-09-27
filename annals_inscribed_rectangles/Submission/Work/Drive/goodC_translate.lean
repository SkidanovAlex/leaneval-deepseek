import Mathlib
import Submission.Work.Drive.OrderBase
import Submission.Work.Drive.Interfaces

/-!
# Translation invariance of the collision set

The configuration map `muOrd γ (x,y) = ((γx + γy)/2, dirC (γx - γy), ‖γx - γy‖)` transforms under a
translation of the curve by shifting only the *midpoint* coordinate, and the rotation `actC u` only
changes the direction coordinate; so the collision set `GoodC γ` (and hence `Zc γ`) is unchanged when
`γ` is translated.

This matters for the order-theory route to `ParityCore`: the capping of the configuration Möbius
strip uses polar coordinates about the origin and so implicitly assumes that the curve avoids the
origin (otherwise the strip meets the axis `{0} × S¹ × {0}` of the configuration space).  Since the
target statements are translation invariant, that assumption can be arranged by translating `γ`
first and transferring the result back.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

/-- Translation of the midpoint coordinate of a configuration. -/
def Ttrans (c : ℝ × ℝ) (q : (ℝ × ℝ) × UnitAddCircle × ℝ) : (ℝ × ℝ) × UnitAddCircle × ℝ :=
  (q.1 + c, q.2)

lemma Ttrans_actC (c : ℝ × ℝ) (u : UnitAddCircle) (q : (ℝ × ℝ) × UnitAddCircle × ℝ) :
    Ttrans c (Submission.Configuration.actC u q) = Submission.Configuration.actC u (Ttrans c q) :=
  rfl

lemma Ttrans_injective (c : ℝ × ℝ) : Function.Injective (Ttrans c) := by
  intro q q' h
  have h1 : q.1 + c = q'.1 + c := by
    have := congrArg (fun z => z.1) h
    simpa [Ttrans] using this
  have h2 : q.2 = q'.2 := by
    have := congrArg (fun z => z.2) h
    simpa [Ttrans] using this
  exact Prod.ext (add_right_cancel h1) h2

/-- The configuration map of a translated curve is the translated configuration map. -/
lemma muOrd_translate (γ : Circle → ℝ × ℝ) (c : ℝ × ℝ) (p : Circle × Circle) :
    Submission.Configuration.muOrd (fun t => γ t + c) p
      = Ttrans c (Submission.Configuration.muOrd γ p) := by
  have hvec : γ p.1 + c - (γ p.2 + c) = γ p.1 - γ p.2 := by abel
  refine Prod.ext ?_ ?_
  · show (γ p.1 + c + (γ p.2 + c)) / 2 = (γ p.1 + γ p.2) / 2 + c
    refine Prod.ext ?_ ?_
    · show ((γ p.1).1 + c.1 + ((γ p.2).1 + c.1)) / 2 = ((γ p.1).1 + (γ p.2).1) / 2 + c.1
      ring
    · show ((γ p.1).2 + c.2 + ((γ p.2).2 + c.2)) / 2 = ((γ p.1).2 + (γ p.2).2) / 2 + c.2
      ring
  · show (Submission.Collision.dirC (γ p.1 + c - (γ p.2 + c)),
      Submission.Geometry.eucNorm (γ p.1 + c - (γ p.2 + c)))
      = (Submission.Collision.dirC (γ p.1 - γ p.2),
        Submission.Geometry.eucNorm (γ p.1 - γ p.2))
    rw [hvec]

/-- **The collision set is translation invariant.** -/
theorem goodC_translate (γ : Circle → ℝ × ℝ) (c : ℝ × ℝ) :
    Submission.Configuration.GoodC (fun t => γ t + c) = Submission.Configuration.GoodC γ := by
  ext u
  constructor
  · rintro ⟨x, y, x', y', hxy, hx'y', h⟩
    refine ⟨x, y, x', y', hxy, hx'y', ?_⟩
    rw [muOrd_translate γ c (x, y), muOrd_translate γ c (x', y'), ← Ttrans_actC] at h
    exact Ttrans_injective c h
  · rintro ⟨x, y, x', y', hxy, hx'y', h⟩
    refine ⟨x, y, x', y', hxy, hx'y', ?_⟩
    rw [muOrd_translate γ c (x, y), muOrd_translate γ c (x', y'), ← Ttrans_actC]
    exact congrArg (Ttrans c) h

/-- **The non-collision set is translation invariant.** -/
theorem Zc_translate (γ : Circle → ℝ × ℝ) (c : ℝ × ℝ) :
    Zc (fun t => γ t + c) = Zc γ := by
  simp only [Zc, goodC_translate γ c]

end Work.Drive
