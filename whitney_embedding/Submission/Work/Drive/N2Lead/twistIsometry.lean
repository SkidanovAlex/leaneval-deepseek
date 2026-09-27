import Mathlib
import Submission.Work.Drive.N2Lead.twistDefs

open scoped Manifold ContDiff

/-!
# D2d.1 (continued): the slab twists are isometries, and the relaxed off-row is automatic

The slab twists `twistY a s` and `twistX ε s` rotate each circle orbit rigidly, so they preserve the
norm of `ℝ³`.  Consequences used by the Möbius saddle certificate:

* the *bridge* values of the polar picture keep their distance from the origin, so the relaxed
  off-row `hAoff` of `D2d.3` (`(A x) 2 ≠ 0 ∨ c₀ + 2η < ‖A x‖²`, asked only off the pinned set) reduces
  to the *norm* row `c₀ + 2η < (r φ)²` of the polar profile `mobius_lowerProfile` — the second
  disjunct holds automatically, whatever the twist does to the height;
* the same row for `twistX` is what makes the vertical untwist of the upper picture harmless for the
  off-row as well.
-/

namespace Work.Drive.N2Lead

open Set Function

noncomputable section

/-- The rotation of the `(x, z)`-plane preserves the norm of `ℝ³`. -/
theorem norm_rot02 (t : ℝ) (v : E3) : ‖rot02 t v‖ = ‖v‖ := by
  have h : ‖rot02 t v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    simp only [rot02, Fin.sum_univ_three, WithLp.ofLp_toLp]
    simp
    ring_nf
    nlinarith [Real.sin_sq_add_cos_sq t]
  have h2 := congrArg Real.sqrt h
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h2

/-- The rotation of the `(y, z)`-plane preserves the norm of `ℝ³`. -/
theorem norm_rot12 (t : ℝ) (v : E3) : ‖rot12 t v‖ = ‖v‖ := by
  have h : ‖rot12 t v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    simp only [rot12, Fin.sum_univ_three, WithLp.ofLp_toLp]
    simp
    ring_nf
    nlinarith [Real.sin_sq_add_cos_sq t]
  have h2 := congrArg Real.sqrt h
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h2

/-- The horizontal slab twist preserves the norm of `ℝ³`. -/
theorem norm_twistY (a s : ℝ) (v : E3) : ‖twistY a s v‖ = ‖v‖ :=
  norm_rot02 _ v

/-- The vertical slab twist preserves the norm of `ℝ³`. -/
theorem norm_twistX (ε s : ℝ) (v : E3) : ‖twistX ε s v‖ = ‖v‖ :=
  norm_rot12 _ v

/-- **The relaxed off-row is automatic for a twisted planar point of large norm.**  If `b` is below
`‖v‖²`, then after a slab twist the *second* disjunct of the off-row holds — the rotated point still
has norm squared `> b`. -/
theorem twistY_off_row (a b : ℝ) (v : E3) (hv : b < ‖v‖ ^ 2) :
    (twistY a 1 v) 2 ≠ 0 ∨ b < ‖twistY a 1 v‖ ^ 2 :=
  Or.inr (by rw [norm_twistY]; exact hv)

/-- The same row for the vertical twist (the upper picture). -/
theorem twistX_off_row (ε b : ℝ) (v : E3) (hv : b < ‖v‖ ^ 2) :
    (twistX ε (-1) v) 2 ≠ 0 ∨ b < ‖twistX ε (-1) v‖ ^ 2 :=
  Or.inr (by rw [norm_twistX]; exact hv)

end

end Work.Drive.N2Lead
