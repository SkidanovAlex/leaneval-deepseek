import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.H2.T1Q

theorem SliceLimit {φ : ℝ → ℝ} {chi : ℕ → ℝ → ℝ} {M : ℝ} {err : ℕ → ℝ}
    (herr : Filter.Tendsto err Filter.atTop (nhds 0))
    (hφint : MeasureTheory.IntegrableOn φ Work.Spaces.Iθ)
    (hchi_meas : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable (chi n)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hchi_le : ∀ (n : ℕ) (θ : ℝ), |chi n θ| ≤ 1)
    (hchi_lim : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Filter.Tendsto (fun n : ℕ => chi n θ) Filter.atTop (nhds 1))
    (hbd : ∀ n : ℕ, |∫ θ in Work.Spaces.Iθ, chi n θ * φ θ| ≤ M + err n) :
    |∫ θ in Work.Spaces.Iθ, φ θ| ≤ M := by
  -- `chi n → 1` a.e. and `|chi n| ≤ 1`, so `∫ chi n · φ → ∫ φ` by dominated
  -- convergence with dominating function `|φ|`.
  have hbound_int : MeasureTheory.Integrable (fun θ => |φ θ|)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hφint.abs
  have hFmeas : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable
      (fun θ => chi n θ * φ θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    fun n => (hchi_meas n).mul hφint.aestronglyMeasurable
  have hb : ∀ n : ℕ, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖chi n θ * φ θ‖ ≤ |φ θ| := by
    intro n
    filter_upwards with θ
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (hchi_le n θ)
  have hlim_aesm : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Filter.Tendsto (fun n : ℕ => chi n θ * φ θ) Filter.atTop (nhds (φ θ)) := by
    filter_upwards [hchi_lim] with θ hθ
    simpa using hθ.mul_const (φ θ)
  have hconv := MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun θ => |φ θ|) hFmeas hbound_int hb hlim_aesm
  -- Pass to the limit in the bound `|∫ chi n · φ| ≤ M + err n`.
  have h1 : Filter.Tendsto (fun n : ℕ => |∫ θ in Work.Spaces.Iθ, chi n θ * φ θ|) Filter.atTop
      (nhds |∫ θ in Work.Spaces.Iθ, φ θ|) := hconv.abs
  have h2 : Filter.Tendsto (fun n : ℕ => M + err n) Filter.atTop (nhds M) := by
    simpa using (tendsto_const_nhds.add herr)
  exact le_of_tendsto_of_tendsto' h1 h2 (fun n => hbd n)

end Work.H2.T1Q
