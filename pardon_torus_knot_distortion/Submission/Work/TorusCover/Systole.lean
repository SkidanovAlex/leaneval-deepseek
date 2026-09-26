import Submission.Work.TorusCover.Basic
import Submission.Work.TorusCover.exists_dist_lower_bound
import Submission.Work.TorusCover.ofReal_two_pi_mul_c_le_curveLength
import Submission.Work.TorusCover.curveLength_le_integral_deriv
import Submission.Work.TorusCover.Lifting

/-!
# The extrinsic systole of a parametrised torus

Pardon's proof rests on the following quantitative fact, the *extrinsic systole bound*: an
essential closed curve in `range psi` (one whose winding vector is nonzero, i.e. which is not
null-homotopic in the torus) has extrinsic length at least `2π c`, where `c > 0` is the uniform
lower bound for `‖d psi‖` from hypothesis (iii).

The proof is a lift-and-count argument: let `Λ` be the periodic lift of `γ` with winding vector
`v ≠ 0`, so that `Λ (2π) - Λ 0 = periodShift v` has norm `≥ 2π`.  Given `ε > 0`, choose `δ`
with `(c - ε)‖x - y‖ ≤ ‖psi x - psi y‖` for `‖x - y‖ ≤ δ` (this is
`Work.TorusCover.exists_dist_lower_bound`), and subdivide `[0, 2π]` so finely that consecutive
lift points are `≤ δ` apart.  Then

`length γ ≥ Σ ‖γ t_{i+1} - γ t_i‖ = Σ ‖psi (Λ t_{i+1}) - psi (Λ t_i)‖ ≥ (c - ε) Σ ‖Λ t_{i+1} - Λ t_i‖
  ≥ (c - ε) ‖Λ (2π) - Λ 0‖ ≥ 2π (c - ε)`,

and `ε → 0` gives the bound.

Main results:

* `Work.TorusCover.TorusParam.ofReal_two_pi_mul_c_le_curveLength`: in the extended nonnegative
  reals, `ofReal (2π c) ≤ curveLength γ 0 (2π)` for continuous curves;
* `Work.TorusCover.TorusParam.two_pi_mul_c_le_integral_deriv`: for a `C¹` closed curve,
  `2π c ≤ ∫ t in 0..2π, ‖γ' t‖`.
-/

open LeanEval.KnotTheory.PardonDistortion Set
open scoped ENNReal

namespace Work.TorusCover

noncomputable section

variable {P : TorusParam}

/-- **Extrinsic systole bound.**  A closed curve with nonzero winding vector has extrinsic
length at least `2π c`. -/
theorem TorusParam.systole_bound (P : TorusParam) {γ : ℝ → R3}
    {v : ℤ × ℤ} {Λ : ℝ → ℝ × ℝ} (hΛ : IsPeriodicLift P.psi γ v Λ) (hv : v ≠ 0) :
    ENNReal.ofReal (2 * Real.pi * P.c) ≤ curveLength γ 0 (2 * Real.pi) :=
  _root_.Work.TorusCover.ofReal_two_pi_mul_c_le_curveLength P hΛ hv
    fun _ hε => _root_.Work.TorusCover.exists_dist_lower_bound P hε

/-- **Extrinsic systole bound, in terms of the arclength integral.**  A `C¹` closed curve in the
range of `psi` whose winding vector is nonzero has arclength at least `2π c` over one period. -/
theorem TorusParam.systole_bound_integral (P : TorusParam) {γ : ℝ → R3}
    (hγ : ContDiff ℝ (1 : ℕ∞) γ) (hper : ∀ t, γ (t + 2 * Real.pi) = γ t)
    (himg : ∀ t, γ t ∈ Set.range (psiMap P.psi)) {v : ℤ × ℤ}
    (hv : HasWinding P.psi γ v) (hv0 : v ≠ 0) :
    2 * Real.pi * P.c ≤ ∫ t in (0 : ℝ)..(2 * Real.pi), ‖deriv γ t‖ := by
  obtain ⟨Λ, hΛ⟩ := hv
  have h1 : ENNReal.ofReal (2 * Real.pi * P.c) ≤
      ENNReal.ofReal (∫ t in (0 : ℝ)..(2 * Real.pi), ‖deriv γ t‖) :=
    le_trans (P.systole_bound hΛ hv0)
      (curveLength_le_integral_deriv γ hγ (le_of_lt (by positivity : (0 : ℝ) < 2 * Real.pi)))
  have hint : (0 : ℝ) ≤ ∫ t in (0 : ℝ)..(2 * Real.pi), ‖deriv γ t‖ :=
    intervalIntegral.integral_nonneg (by positivity) fun t _ => norm_nonneg _
  exact (ENNReal.ofReal_le_ofReal_iff hint).mp h1

/-- **Extrinsic systole bound in the vocabulary of `Knot`.**  If a smooth knot curve lies in the
range of `psi` and has nonzero winding vector, then its total arclength (in the sense of
`totalArcLength`) is at least `2π c`. -/
theorem TorusParam.two_pi_mul_c_le_totalArcLength (P : TorusParam) {v : ℤ × ℤ} (K : Knot)
    (himg : ∀ t, K.curve t ∈ Set.range (psiMap P.psi))
    (hv : HasWinding P.psi K.curve v) (hv0 : v ≠ 0) :
    2 * Real.pi * P.c ≤ totalArcLength K := by
  have h1 : ContDiff ℝ (1 : ℕ∞) K.curve := K.smooth.of_le (by simp)
  have h2 := P.systole_bound_integral h1 K.periodic himg hv hv0
  have hnn : 0 ≤ ∫ u in (0 : ℝ)..(2 * Real.pi), speed K u :=
    intervalIntegral.integral_nonneg (by positivity) fun u _ => by
      simp only [speed]; positivity
  rw [totalArcLength, parameterArcLength, abs_of_nonneg hnn]
  exact h2

/-- **Systole bound for the shortest essential curve, contrapositive form.**  If a closed curve
in the range of `psi` is shorter than `2π c`, then it is inessential: the winding vector is
`(0,0)`. -/
theorem hasWinding_eq_zero_of_curveLength_lt (P : TorusParam) {γ : ℝ → R3}
    {v : ℤ × ℤ} {Λ : ℝ → ℝ × ℝ} (hΛ : IsPeriodicLift P.psi γ v Λ)
    (h : curveLength γ 0 (2 * Real.pi) < ENNReal.ofReal (2 * Real.pi * P.c)) : v = 0 := by
  by_contra hv
  exact absurd (P.systole_bound hΛ hv) (not_le_of_gt h)

/-- **From a diameter bound to a ball bound.**  If every pair of points of the curve `γ` is at
distance at least `D`, then `γ` is not contained in any closed ball of radius `< D / 2`.

The extrinsic diameter of an essential curve is *not* bounded below by a function of the
immersion constant `c` alone: for the standard torus (`c = 1`) the meridian circle is essential,
has length `2π = 2π c`, and is contained in a closed ball of radius `1 < π/2 = π c / 2`.  A lower
bound for the diameter is part of the *embedding* data; see
`Work.CoreTopology.essential_diameter_ge_two` and `Work.CoreTopology.positive_scale` for the
standard torus, where the bound `D = 2` holds. -/
theorem le_two_mul_radius_of_diam_le {γ : ℝ → R3} {D r : ℝ} {x : R3}
    (hdiam : ∀ t t', D ≤ dist (γ t) (γ t'))
    (hball : ∀ t, γ t ∈ Metric.closedBall x r) : D ≤ 2 * r := by
  have hr : 0 ≤ r := by
    have h1 : dist (γ 0) x ≤ r := by simpa [Metric.mem_closedBall] using hball 0
    linarith [dist_nonneg (x := γ 0) (y := x)]
  have h0 : D ≤ dist (γ 0) (γ 0) := hdiam 0 0
  simp only [dist_self] at h0
  linarith

/-! ### Systole bounds in terms of `windingVector` -/

/-- **Extrinsic systole bound** for a closed curve in the range of `psi` with nonzero winding
vector. -/
theorem TorusParam.systole_bound_windingVector (P : TorusParam) {γ : ℝ → R3}
    (hγ : Continuous γ) (hper : ∀ t, γ (t + 2 * Real.pi) = γ t)
    (himg : ∀ t, γ t ∈ Set.range (psiMap P.psi))
    (hv : windingVector P γ hγ hper himg ≠ 0) :
    ENNReal.ofReal (2 * Real.pi * P.c) ≤ curveLength γ 0 (2 * Real.pi) := by
  obtain ⟨Λ, hΛ⟩ := windingVector_spec P hγ hper himg
  exact P.systole_bound hΛ hv

/-- **Extrinsic systole bound, arclength form**, for a closed curve in the range of `psi` with
nonzero winding vector. -/
theorem TorusParam.systole_bound_windingVector_integral (P : TorusParam) {γ : ℝ → R3}
    (hγ : ContDiff ℝ (1 : ℕ∞) γ) (hperp : ∀ t, γ (t + 2 * Real.pi) = γ t)
    (himg : ∀ t, γ t ∈ Set.range (psiMap P.psi))
    (hv : windingVector P γ hγ.continuous hperp himg ≠ 0) :
    2 * Real.pi * P.c ≤ ∫ t in (0 : ℝ)..(2 * Real.pi), ‖deriv γ t‖ :=
  P.systole_bound_integral hγ hperp himg (windingVector_spec P hγ.continuous hperp himg) hv

/-- **Extrinsic systole bound** for an essential closed curve (one whose winding vector is
nonzero). -/
theorem TorusParam.systole_bound_essential (P : TorusParam) {γ : ℝ → R3}
    (hγ : Continuous γ) (hper : ∀ t, γ (t + 2 * Real.pi) = γ t)
    (himg : ∀ t, γ t ∈ Set.range (psiMap P.psi)) (hess : IsEssential P.psi γ) :
    ENNReal.ofReal (2 * Real.pi * P.c) ≤ curveLength γ 0 (2 * Real.pi) :=
  P.systole_bound_windingVector hγ hper himg
    ((isEssential_iff_windingVector_ne_zero P hγ hper himg).mp hess)

end

end Work.TorusCover
