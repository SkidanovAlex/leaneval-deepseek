import Mathlib.Analysis.InnerProductSpace.PiL2
import ChallengeDeps
import Submission.BoxEnergy
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
Facts about potentials with compact support contained in a ball.

Throughout the project `v : ℝ³ → ℝ` is a non-negative radial potential in L¹
whose (topological) support lies in an open ball `ball 0 R`.  The lemmas below
record the only property of that assumption that is used over and over: `v`
vanishes at every point at distance `≥ R` from the origin, in particular at
every relative coordinate `x i - x j` of norm `≥ R`.
-/

namespace Submission

open _root_.BoseGases
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- A point of norm `≥ R` lies outside the open ball `ball 0 R`. -/
lemma not_mem_ball_of_norm_ge {R : ℝ} {x : ℝ³} (hx : R ≤ ‖x‖) : x ∉ ball (0 : ℝ³) R := by
  intro hb
  have hlt : ‖x‖ < R := by
    simpa [Metric.mem_ball, dist_eq_norm, sub_zero] using hb
  linarith

/-- If the support of `v` is contained in `ball 0 R` then `v x = 0` for `‖x‖ ≥ R`. -/
lemma v_eq_zero_of_norm_ge {v : ℝ³ → ℝ} {R : ℝ} (h : tsupport v ⊆ ball (0 : ℝ³) R)
    {x : ℝ³} (hx : R ≤ ‖x‖) : v x = 0 := by
  by_contra hvx
  have hxsupp : x ∈ Function.support v := by simpa [Function.support] using hvx
  have hxt : x ∈ tsupport v := subset_tsupport v hxsupp
  exact not_mem_ball_of_norm_ge hx (h hxt)

/-- Consequence for relative coordinates: `v (x i - x j) = 0` whenever the two
particles are at distance `≥ R`. -/
lemma v_sub_eq_zero_of_norm_ge {N : ℕ} {v : ℝ³ → ℝ} {R : ℝ}
    (h : tsupport v ⊆ ball (0 : ℝ³) R) (i j : Fin N) {x : X N}
    (hx : R ≤ ‖x i - x j‖) : v (x i - x j) = 0 :=
  v_eq_zero_of_norm_ge h hx

/-- If `0 ≤ v` and its support is inside `ball 0 R`, then each two-body term
`v (x i - x j)` is nonnegative everywhere. -/
lemma v_sub_nonneg {N : ℕ} {v : ℝ³ → ℝ} (hv : 0 ≤ v) (i j : Fin N) (x : X N) :
    0 ≤ v (x i - x j) := hv (x i - x j)

end BoseGases

end Submission
