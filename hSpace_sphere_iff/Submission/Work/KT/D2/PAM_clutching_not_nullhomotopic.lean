import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.D2.Basic
import Submission.Work.KT.Dim2.circle_log_facts
import Submission.Work.KT.diskQuot
import Submission.Work.KT.D2.PAMDefs
import Submission.Work.KT.D2.PAMMain

namespace Work.KT.D2

/-- **The Hopf idempotent of the disc model is non-trivial.**  Let
`u : D² → M₂(ℂ)` be a continuous family of invertible matrices carrying the constant rank-one
projection `e₀ = diag(1,0)` to the disc-model Hopf idempotent `Work.KT.D2.PAM`
(`u y * e₀ = PAM(y) * u y` for all `y`).  Then the `(0,0)`-entry of `u`, restricted to the
boundary circle, is a loop in `ℂˣ` which is not null-homotopic; equivalently its winding number is
non-zero.

Route.  Write `w(z) ∈ ℂ²` for the unit vector `(1 + x₂, x₀ + i x₁)/‖(1 + x₂, x₀ + i x₁)‖` where
`x = Work.KT.qc 2 z ∈ S²` (so `im PAM(z) = ℂ·w(z)`) and `u_c(z) := [[w₁, -w̄₂],[w₂, w̄₁]]`.  The
map `u_c` is unitary-valued and satisfies `u_c e₀ = PAM u_c` on the punctured disc, but is *not*
continuous at `0` (the direction of `w` winds by `1` there while the line `ℂ·w` is continuous).
Set `c := u_c^* u`, so `c y * e₀ = e₀ * c y`, i.e. `c` is block diagonal on the punctured disc.
Then `c 0 0 = w̄₁ u 0 0 + w̄₂ u 1 0`.  Near the centre `w̄₁ → 0` while
`w̄₂ = cos(π‖z‖/2) · e^{-iθ}` on `|z| = ‖z‖` (from the explicit formula `qMap 2 z =
(sfun ‖z‖ • z, -cos (π ‖z‖))` of `Submission.Work.KT.DiskAux`), and `u 1 0 (0) ≠ 0` because
`u(0) e₀ u(0)^{-1} = PAM(0) = diag(0,1)` forces the first column of `u(0)` to lie in `ℂ e₂`.  So on
small circles `c 0 0` is homotopic through non-vanishing functions to `w̄₂ · u 1 0`, whose winding
is `-1` (a continuous non-vanishing `u 1 0` on a disc has winding `0`, and `w̄₂` has winding `-1`),
while on the boundary circle `c 0 0 = u 0 0`.  Since the winding of a non-vanishing loop equals the
winding on every concentric circle, the boundary loop `u 0 0` has winding `-1`, in particular it is
not null-homotopic (`Work.KT.Dim2.circle_log_facts`). -/
lemma PAMA_eq_PAM : PAMA = PAM := rfl

lemma PyA_eq_PAM_map (y : Dc) : PyA y = PAM.map (Work.KT.augPair E2 y) := by
  show PAMA.map (Work.KT.augPair E2 y) = PAM.map (Work.KT.augPair E2 y)
  rw [PAMA_eq_PAM]

lemma inBallA_eq_inBall (x : Sc) : inBallA x = Work.KT.D2.inBall x := rfl

theorem PAM_clutching_not_nullhomotopic
    (u : C(Work.KT.Ball (EuclideanSpace ℝ (Fin 2)), Matrix (Fin 2) (Fin 2) ℂ))
    (hunit : ∀ y, IsUnit (u y))
    (hconj : ∀ y, u y * !![(1 : ℂ), 0; 0, 0]
      = (Work.KT.D2.PAM.map (Work.KT.augPair (EuclideanSpace ℝ (Fin 2)) y)) * u y)
    (f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, ℂˣ))
    (hf : ∀ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
      ((f x : ℂˣ) : ℂ) = (u (Work.KT.D2.inBall x)) 0 0) :
    ¬ ContinuousMap.Homotopic f
        (ContinuousMap.const (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) 1) := by
  refine Work.KT.D2.PAMA_clutching_not_nullhomotopic u hunit ?_ f ?_
  · intro y
    rw [Work.KT.D2.PyA_eq_PAM_map y]
    exact hconj y
  · intro x
    rw [Work.KT.D2.inBallA_eq_inBall x]
    exact hf x

end Work.KT.D2
