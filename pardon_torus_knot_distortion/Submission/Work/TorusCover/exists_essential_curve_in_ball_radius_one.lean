import Mathlib
import Submission.Work.TorusCover.Basic
import Submission.Work.TorusCover.exists_torusParam_torusMap
import Submission.Work.TorusCover.Lifting

/-!
# Pardon's Lemma 4, existence half: an essential curve inside a ball of radius one

Pardon's proof of the torus-knot distortion bound needs a *positive* lower bound for the
radius of a closed ball of `ℝ³` containing an essential loop of the torus: no ball of radius
`< 1` contains one.  The complementary file `Work.CoreTopology.positive_scale` (and
`Work.CoreTopology.essential_diameter_ge_two`) establishes the inequality `1 ≤ r`.

This file supplies the model witness making that lower bound *sharp*: the meridian circle

  `γ φ = torusMap 0 φ = (2 + cos φ, 0, sin φ)`

of the standard torus of revolution (major radius `2`, minor radius `1`) is an essential
closed curve on the torus, and it is entirely contained in the closed ball of radius `1`
centred at `x = (2, 0, 0)`.  Indeed `γ φ - x = (cos φ, 0, sin φ)` has norm `1`.

Essentiality is witnessed by the winding vector `(0, 1) ≠ 0`, whose periodic lift is the
straight line `t ↦ (0, t)` in the parameter plane: `Λ (t + 2π) = Λ t + periodShift (0,1)`.

The parametrised torus is `Work.TorusCover.torusParamModel`, the standard torus of revolution
bundled as a `TorusParam` with the sharp constant `c = 1`
(`Work.TorusCover.exists_torusParam_torusMap`).
-/

open LeanEval.KnotTheory.PardonDistortion

namespace Work.TorusCover

noncomputable section

/-- The centre `(2, 0, 0)` of the meridian disc of the standard torus of revolution, as a
point of `ℝ³`. -/
def ballCenterR1 : R3 :=
  WithLp.toLp 2 (fun i : Fin 3 => if i.val = 0 then (2 : ℝ) else 0)

/-- The meridian circle `{θ = 0}` of the standard torus: `φ ↦ torusMap 0 φ`. -/
def meridianCircle0 : ℝ → R3 := fun φ => Work.Core.torusMap 0 φ

@[simp] lemma ballCenterR1_apply (i : Fin 3) :
    ballCenterR1 i = (if i.val = 0 then (2 : ℝ) else 0) := by
  simp [ballCenterR1]

@[simp] lemma meridianCircle0_apply (φ : ℝ) :
    meridianCircle0 φ = Work.Core.torusMap 0 φ := rfl

/-- The squared distance from the meridian circle `{θ = 0}` to the centre `(2,0,0)` is `1`. -/
lemma norm_sq_meridianCircle0_sub_center (φ : ℝ) :
    ‖meridianCircle0 φ - ballCenterR1‖ ^ 2 = 1 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs, PiLp.sub_apply, meridianCircle0_apply,
    ballCenterR1_apply]
  rw [Work.Core.torusMap_apply_zero, Work.Core.torusMap_apply_one,
    Work.Core.torusMap_apply_two]
  norm_num [Real.sin_zero, Real.cos_zero]

/-- The meridian circle `{θ = 0}` lies in the closed ball of radius `1` about `(2,0,0)`. -/
lemma meridianCircle0_mem_closedBall (φ : ℝ) :
    meridianCircle0 φ ∈ Metric.closedBall ballCenterR1 1 := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  nlinarith [norm_nonneg (meridianCircle0 φ - ballCenterR1),
    norm_sq_meridianCircle0_sub_center φ]

/-- The meridian circle `{θ = 0}` is `2π`-periodic. -/
lemma meridianCircle0_periodic (φ : ℝ) :
    meridianCircle0 (φ + 2 * Real.pi) = meridianCircle0 φ :=
  Work.Core.torusMap_add_two_pi_right 0 φ

/-- The straight line `t ↦ (0, t)` in the parameter plane is a periodic lift of the meridian
circle `{θ = 0}` with winding vector `(0, 1)`. -/
lemma isPeriodicLift_meridianCircle0 :
    IsPeriodicLift Work.Core.torusMap meridianCircle0 ((0, 1) : ℤ × ℤ)
      (fun t => ((0 : ℝ), t)) := by
  refine ⟨⟨continuous_const.prodMk continuous_id, fun t => rfl⟩, fun t => ?_⟩
  ext <;> simp [periodShift]

/-- The meridian circle `{θ = 0}` is essential: it winds once around the meridian. -/
lemma isEssential_meridianCircle0 :
    IsEssential Work.Core.torusMap meridianCircle0 :=
  ⟨((0, 1) : ℤ × ℤ), by decide, ⟨fun t => ((0 : ℝ), t), isPeriodicLift_meridianCircle0⟩⟩

/-- **Pardon's Lemma 4, existence half.**  There is an essential closed curve on the standard
torus of revolution, of winding vector `(0, 1)`, entirely contained in a closed ball of radius
`1` of `ℝ³`.  Together with the lower bound `1 ≤ r` for *every* ball containing an essential
loop (`Work.CoreTopology.positive_scale`), this identifies `1` as the exact critical radius.

The curve is the meridian circle `{θ = 0}`, and the ball is the one centred at `(2, 0, 0)`;
the parametrised torus is the standard one, with the sharp derivative constant `c = 1`. -/
theorem exists_essential_curve_in_ball_radius_one :
    ∃ (P : Work.TorusCover.TorusParam) (γ : ℝ → LeanEval.KnotTheory.PardonDistortion.R3)
      (x : LeanEval.KnotTheory.PardonDistortion.R3),
      P.psi = Work.Core.torusMap ∧ P.c = 1 ∧
      Work.TorusCover.IsEssential P.psi γ ∧
      (∀ φ : ℝ, γ φ ∈ Metric.closedBall x 1) ∧
      (∀ φ : ℝ, γ (φ + 2 * Real.pi) = γ φ) := by
  refine ⟨torusParamModel, meridianCircle0, ballCenterR1, rfl, rfl, ?_, ?_, ?_⟩
  · exact isEssential_meridianCircle0
  · exact meridianCircle0_mem_closedBall
  · exact meridianCircle0_periodic

end

end Work.TorusCover
