import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Submission.Work.SmallBoxBridge.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.W1momentAux` — the fixed smooth replacement for `1/(χ⋆χ)(·/ℓ)`

This file provides the two *fixed* (parameter-independent) objects used in
`Submission/Work/BoseBogFS/W1funDecay_momentsAbs.lean`:

* `Work.BoseBogFS.theta : ℝ → ℝ` — a globally `C^∞` function which agrees with
  `t ↦ t⁻¹` on `[1/4, ∞)`.  Since `(χ⋆χ)(x/ℓ) ≥ 1/2` whenever `‖x‖ ≤ R` and
  `R ≤ ℓ·chiR0` (`Submission.BoseGases.convScale_ge_half_ball`), the composition
  `y ↦ theta ((χ⋆χ)(y/ℓ))` equals `(χ⋆χ)(y/ℓ)⁻¹` on `ball 0 R`; being a
  composition of two globally smooth functions it is smooth *everywhere* — the
  point of introducing `theta` is precisely that the totalised `x ↦ (χ⋆χ)(x/ℓ)⁻¹`
  is not smooth at the boundary of the support of `χ⋆χ`.

* `Work.BoseBogFS.beta : ℝ³ → ℝ` — a fixed smooth bump which is `1` on the
  closed unit ball (a `ContDiffBump` with `rIn = 1`, `rOut = 2`).

Both are used in the *scaled* picture: after the substitution `y = R • z` the
weight `ψg₀(‖y‖)` becomes `ψg₀(R‖z‖)` (supported in `ball 0 1`) and the
remaining factor becomes `z ↦ z_j^m · theta ((χ⋆χ)(ε•z)) · beta z` with
`ε = R/ℓ ≤ chiR0`.
-/

noncomputable section

open MeasureTheory Metric
open scoped Real Topology

namespace Work.BoseBogFS

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The denominator of `theta`: `t + (1/2 - t)·smoothTransition (1 - 4t)`, a smooth
function equal to `t` for `t ≥ 1/4` and equal to `1/2` for `t ≤ 0`, positive
everywhere. -/
noncomputable def thetaDenom : ℝ → ℝ :=
  fun t => t + (1 / 2 - t) * Real.smoothTransition (1 - 4 * t)

/-- A fixed smooth function equal to `t ↦ t⁻¹` on `[1/4, ∞)`. -/
noncomputable def theta : ℝ → ℝ := fun t => (thetaDenom t)⁻¹

lemma thetaDenom_eq (t : ℝ) :
    thetaDenom t = (1 - Real.smoothTransition (1 - 4 * t)) * t
      + Real.smoothTransition (1 - 4 * t) * (1 / 2) := by
  show t + (1 / 2 - t) * Real.smoothTransition (1 - 4 * t) = _
  ring

lemma thetaDenom_contDiff (n : ℕ) : ContDiff ℝ n thetaDenom := by
  show ContDiff ℝ n fun t : ℝ => t + (1 / 2 - t) * Real.smoothTransition (1 - 4 * t)
  fun_prop

/-- The denominator of `theta` is strictly positive. -/
lemma thetaDenom_pos (t : ℝ) : 0 < thetaDenom t := by
  rw [thetaDenom_eq]
  set σ := Real.smoothTransition (1 - 4 * t) with hσ
  have h0 : 0 ≤ σ := Real.smoothTransition.nonneg _
  have h1 : σ ≤ 1 := Real.smoothTransition.le_one _
  rcases le_or_gt (1 / 4 : ℝ) t with ht | ht
  · -- `σ = 0`, so the denominator is `t ≥ 1/4`
    have hz : σ = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
    rw [hz]; simp only [sub_zero, zero_mul, mul_zero, add_zero]; linarith
  · rcases le_or_gt t 0 with ht0 | ht0
    · -- `σ = 1`, so the denominator is `1/2`
      have ho : σ = 1 := Real.smoothTransition.one_of_one_le (by linarith)
      rw [ho]; simp only [sub_self, zero_mul, one_mul]; norm_num
    · -- `0 < t < 1/4`: `σ > 0` and the first term is nonnegative
      have hpos : 0 < σ := Real.smoothTransition.pos_of_pos (by linarith)
      have hlt : 0 ≤ 1 - σ := by linarith
      nlinarith [mul_nonneg hlt ht0.le, mul_pos hpos (by norm_num : (0:ℝ) < 1/2)]

lemma theta_contDiff (n : ℕ) : ContDiff ℝ n theta := by
  show ContDiff ℝ n fun t : ℝ => (thetaDenom t)⁻¹
  exact (thetaDenom_contDiff n).inv fun t => ne_of_gt (thetaDenom_pos t)

/-- `theta` agrees with `t ↦ t⁻¹` for `t ≥ 1/4`. -/
lemma theta_eq_inv {t : ℝ} (ht : 1 / 4 ≤ t) : theta t = 1 / t := by
  have hz : Real.smoothTransition (1 - 4 * t) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  have hD : thetaDenom t = t := by
    show t + (1 / 2 - t) * Real.smoothTransition (1 - 4 * t) = t
    rw [hz, mul_zero, add_zero]
  show (thetaDenom t)⁻¹ = 1 / t
  rw [hD, inv_eq_one_div]

/-- A bound for `theta` on a half-line `[t₀, ∞)`, `t₀ > 0`. -/
lemma abs_theta_le {t₀ t : ℝ} (ht₀ : 0 < t₀) (ht : t₀ ≤ t) :
    |theta t| ≤ (min t₀ (1 / 2))⁻¹ := by
  have hpos : 0 < thetaDenom t := thetaDenom_pos t
  have hge : min t₀ (1 / 2) ≤ thetaDenom t := by
    rw [thetaDenom_eq]
    set σ := Real.smoothTransition (1 - 4 * t) with hσ
    have h0 : 0 ≤ σ := Real.smoothTransition.nonneg _
    have h1 : σ ≤ 1 := Real.smoothTransition.le_one _
    have hmin : min t₀ (1 / 2) ≤ (1 - σ) * t + σ * (1 / 2) := by
      rcases le_total (1 / 2) t₀ with h | h
      · -- `min = 1/2`
        rw [min_eq_right h]
        nlinarith [mul_nonneg h0 ht₀.le, mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ) ≤ 1 / 2)]
      · -- `min = t₀`
        rw [min_eq_left h]
        nlinarith [mul_le_mul_of_nonneg_left ht h0, mul_nonneg (by linarith : (0:ℝ) ≤ 1 - σ)
          (by norm_num : (0:ℝ) ≤ 1 / 2)]
    linarith
  have hminpos : 0 < min t₀ (1 / 2) := lt_min ht₀ (by norm_num)
  show |(thetaDenom t)⁻¹| ≤ (min t₀ (1 / 2))⁻¹
  rw [abs_of_pos (inv_pos.mpr hpos)]
  exact (inv_le_inv₀ hpos hminpos).mpr hge

/-- A fixed smooth bump equal to `1` on the closed unit ball, with `rIn = 1`, `rOut = 2`. -/
noncomputable def betaBump : ContDiffBump (0 : E3) :=
  ⟨1, 2, one_pos, one_lt_two⟩

/-- The fixed bump function `beta : ℝ³ → ℝ`, equal to `1` on `closedBall 0 1`. -/
noncomputable def beta : E3 → ℝ := fun z => (betaBump : E3 → ℝ) z

lemma beta_one {z : E3} (hz : ‖z‖ ≤ 1) : beta z = 1 := by
  show (betaBump : E3 → ℝ) z = 1
  exact ContDiffBump.one_of_mem_closedBall betaBump
    (by simpa [betaBump, mem_closedBall, dist_eq_norm] using hz)

lemma beta_contDiff (n : ℕ) : ContDiff ℝ n beta := by
  show ContDiff ℝ n fun z : E3 => (betaBump : E3 → ℝ) z
  exact (betaBump.contDiff (n := ⊤)).of_le (WithTop.coe_le_coe.mpr le_top)

lemma beta_hasCompactSupport : HasCompactSupport beta := by
  show HasCompactSupport fun z : E3 => (betaBump : E3 → ℝ) z
  exact betaBump.hasCompactSupport

lemma beta_bounded (z : E3) : |beta z| ≤ 1 := by
  show |(betaBump : E3 → ℝ) z| ≤ 1
  exact abs_le.mpr ⟨by linarith [betaBump.nonneg (x := z)], betaBump.le_one (x := z)⟩

end Work.BoseBogFS
