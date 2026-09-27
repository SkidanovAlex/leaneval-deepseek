import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation
import Submission.Work.Noncompact.CompressionTube.radial_ball_facts

/-!
# The parameter-space shrinking map

For the construction of a "shrunk tube" out of a given tube `Ψ : ℝ^{n-1} × ℝ → M` we compose `Ψ`
on the right with a self-map of the parameter space which

* keeps the `s`-coordinate,
* replaces the transverse coordinate `u` by `R s • b u`, where `b u = (√(1+‖u‖²))⁻¹ • u` is the
  radial compression of `ℝ^{n-1}` onto the open unit ball and `R : ℝ → ℝ` is a smooth positive
  function.

The image of `shrinkMap n R` is thus contained in the "tube" `{(u,s) | ‖u‖ < R s}`, which allows
one to force the image into any prescribed open neighbourhood of the axis (and to avoid any
prescribed closed set disjoint from the axis) by choosing `R` small enough.
-/

namespace Work.Noncompact.CompressionTube

open scoped Manifold ContDiff
open Topology Set Function

noncomputable section

/-- The shrinking self-map `(u,s) ↦ (R s • b u, s)` of the parameter space, where
`b = OpenPartialHomeomorph.univUnitBall` is the radial compression of `ℝ^{n-1}` onto the open unit
ball. -/
def shrinkMap (n : ℕ) (R : ℝ → ℝ) :
    EuclideanSpace ℝ (Fin (n - 1)) × ℝ → EuclideanSpace ℝ (Fin (n - 1)) × ℝ :=
  fun p => (R p.2 • OpenPartialHomeomorph.univUnitBall p.1, p.2)

@[simp] lemma shrinkMap_fst (n : ℕ) (R : ℝ → ℝ)
    (p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ) :
    (shrinkMap n R p).1 = R p.2 • OpenPartialHomeomorph.univUnitBall p.1 := rfl

@[simp] lemma shrinkMap_snd (n : ℕ) (R : ℝ → ℝ)
    (p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ) :
    (shrinkMap n R p).2 = p.2 := rfl

/-- The transverse norm of the image of `shrinkMap n R` is strictly less than `R s`. -/
lemma shrinkMap_fst_norm_lt (n : ℕ) (R : ℝ → ℝ) (hpos : ∀ s, 0 < R s)
    (p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ) :
    ‖(shrinkMap n R p).1‖ < R p.2 := by
  rw [shrinkMap_fst]
  have hb : ‖OpenPartialHomeomorph.univUnitBall p.1‖ < 1 := by
    have h := OpenPartialHomeomorph.map_source OpenPartialHomeomorph.univUnitBall
      (x := p.1) (by trivial)
    rw [OpenPartialHomeomorph.univUnitBall_target] at h
    exact mem_ball_zero_iff.mp h
  rw [norm_smul, Real.norm_eq_abs]
  rw [abs_of_pos (hpos _)]
  calc R p.2 * ‖OpenPartialHomeomorph.univUnitBall p.1‖ < R p.2 * 1 :=
        mul_lt_mul_of_pos_left hb (hpos _)
    _ = R p.2 := mul_one _

end

end Work.Noncompact.CompressionTube
