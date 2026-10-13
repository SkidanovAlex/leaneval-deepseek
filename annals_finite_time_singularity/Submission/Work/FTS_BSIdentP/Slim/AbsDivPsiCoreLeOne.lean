import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_BSIdentP.Slim.DecayTwoDefs
import Submission.Work.FTS_BSIdentP.Slim.RhoMulRpowWeightLeTwo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdentP.Levels

open Work.FTS.BSIdent

theorem abs_div_psiCore_le_one {G : ℝ → ℝ → ℝ} {p c b C₀ lam r z : ℝ}
    (hC₀ : 0 ≤ C₀) (hlam : 0 < lam) (hp : 0 < p) (hb : 0 < b)
    (hr : 0 < r) (hz : 0 < z) (hpl : 2 ≤ p * lam)
    (hval : |G (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z)|
      ≤ C₀ * (Real.pi / 2 - Work.Cyl.thetaP r z)
        * (1 + Work.Cyl.rhoP r z ^ p / b) ^ (-lam)) :
    |Work.FTS.BSIdent.Cyl.psiCore p c b G r z / r|
      ≤ Work.FTS.BSIdentP.Levels.decayKqOne c C₀ lam b / (1 + Work.Cyl.rhoP r z) := by
  -- Unfold the core `ψ = ρ² c G(w, θ)` and abbreviate the four recurring quantities.
  simp only [Work.FTS.BSIdent.Cyl.psiCore]
  set ρ := Work.Cyl.rhoP r z with hρ
  set θ := Work.Cyl.thetaP r z with hθ
  set w := ρ ^ p / b with hw
  set R := (1 + w) ^ (-lam) with hR
  have hρpos : 0 < ρ := by rw [hρ]; exact Work.Cyl.rhoP_pos hr z
  have hρnn : 0 ≤ ρ := hρpos.le
  have hθpos : 0 < θ := by rw [hθ]; exact Work.FTS.BSIdent.Cyl.thetaP_pos_of_pos hr hz
  have hwpos : 0 < w := by rw [hw]; exact div_pos (Real.rpow_pos_of_pos hρpos p) hb
  have hRnn : 0 ≤ R := by
    rw [hR]; exact (Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < 1 + w) _).le
  -- `cos θ = r/ρ` is the sharp form of the distance of `θ` to `π/2`.
  have hcos : Real.cos θ = r / ρ := by rw [hθ, hρ]; exact Work.Cyl.cos_thetaP hr z
  -- The rate hypothesis, in the abbreviations.
  have hG : |G w θ| ≤ C₀ * (Real.pi / 2 - θ) * R := hval
  -- Jordan's inequality turns the profile rate `(π/2 - θ)` into `(π/2) cos θ = (π/2) r/ρ`.
  have hSle : Real.pi / 2 - θ ≤ Real.pi / 2 * Real.cos θ := by
    have hθabs : |θ| ≤ Real.pi / 2 :=
      le_of_lt (by rw [hθ]; exact Work.FTS.BSIdent.Cyl.abs_thetaP_lt r z)
    have h := Work.FTS.BSIdent.Cyl.DecayAux.pi_div_two_sub_abs_le_cos hθabs
    rw [abs_of_nonneg hθpos.le] at h
    exact h
  -- … so that `ρ² (π/2 - θ)/r ≤ (π/2) ρ`.
  have hSbound : ρ ^ 2 * (Real.pi / 2 - θ) / r ≤ Real.pi / 2 * ρ := by
    have h1 : ρ ^ 2 * (Real.pi / 2 - θ) ≤ ρ ^ 2 * (Real.pi / 2 * Real.cos θ) :=
      mul_le_mul_of_nonneg_left hSle (sq_nonneg ρ)
    have h2 : ρ ^ 2 * (Real.pi / 2 * Real.cos θ) = Real.pi / 2 * ρ * r := by
      rw [hcos]; field_simp
    rw [h2] at h1
    rw [div_le_iff₀ hr]
    exact h1
  have step1 : |ρ ^ 2 * c * G w θ / r|
      ≤ |c| * C₀ * (ρ ^ 2 * (Real.pi / 2 - θ) / r) * R := by
    have h1 : (0 : ℝ) ≤ ρ ^ 2 * |c| := mul_nonneg (sq_nonneg ρ) (abs_nonneg c)
    have h2 : ρ ^ 2 * |c| * |G w θ| / r
        ≤ ρ ^ 2 * |c| * (C₀ * (Real.pi / 2 - θ) * R) / r :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hG h1) hr.le
    calc |ρ ^ 2 * c * G w θ / r|
        = ρ ^ 2 * |c| * |G w θ| / r := by
          rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg ρ), abs_of_nonneg hr.le]
      _ ≤ ρ ^ 2 * |c| * (C₀ * (Real.pi / 2 - θ) * R) / r := h2
      _ = |c| * C₀ * (ρ ^ 2 * (Real.pi / 2 - θ) / r) * R := by ring
  have step2 : |c| * C₀ * (ρ ^ 2 * (Real.pi / 2 - θ) / r) * R
      ≤ |c| * C₀ * (Real.pi / 2) * ρ * R := by
    have h4 : (0 : ℝ) ≤ |c| * C₀ * R :=
      mul_nonneg (mul_nonneg (abs_nonneg c) hC₀) hRnn
    have h5 := mul_le_mul_of_nonneg_left hSbound h4
    calc |c| * C₀ * (ρ ^ 2 * (Real.pi / 2 - θ) / r) * R
        = (|c| * C₀ * R) * (ρ ^ 2 * (Real.pi / 2 - θ) / r) := by ring
      _ ≤ (|c| * C₀ * R) * (Real.pi / 2 * ρ) := h5
      _ = |c| * C₀ * (Real.pi / 2) * ρ * R := by ring
  have step3 : |c| * C₀ * (Real.pi / 2) * ρ * R
      ≤ decayKqOne c C₀ lam b / (1 + ρ) := by
    have hρR : ρ * R ≤ 2 * max 1 (b ^ lam) / (1 + ρ) := by
      have h := rho_mul_rpow_weight_le_two hp hlam hb hρnn hpl
      rw [← hw, ← hR] at h
      exact h
    have h4 : (0 : ℝ) ≤ |c| * C₀ * (Real.pi / 2) :=
      mul_nonneg (mul_nonneg (abs_nonneg c) hC₀) (by linarith [Real.pi_pos])
    calc |c| * C₀ * (Real.pi / 2) * ρ * R
        = (|c| * C₀ * (Real.pi / 2)) * (ρ * R) := by ring
      _ ≤ (|c| * C₀ * (Real.pi / 2)) * (2 * max 1 (b ^ lam) / (1 + ρ)) :=
          mul_le_mul_of_nonneg_left hρR h4
      _ = decayKqOne c C₀ lam b / (1 + ρ) := by rw [decayKqOne]; ring
  calc |ρ ^ 2 * c * G w θ / r|
      ≤ |c| * C₀ * (ρ ^ 2 * (Real.pi / 2 - θ) / r) * R := step1
    _ ≤ |c| * C₀ * (Real.pi / 2) * ρ * R := step2
    _ ≤ decayKqOne c C₀ lam b / (1 + ρ) := step3

end Work.FTS.BSIdentP.Levels
