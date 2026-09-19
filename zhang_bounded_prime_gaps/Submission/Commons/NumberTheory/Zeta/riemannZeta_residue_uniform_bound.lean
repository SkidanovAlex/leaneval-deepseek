import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Submission.Commons.NumberTheory.Zeta.riemannZeta_norm_antitone_re

open Complex Filter Metric Asymptotics
open scoped Topology

noncomputable section

namespace Commons.NumberTheory.Zeta

/-- `s ↦ riemannZeta₁ (1 + s)` is complex-differentiable at `0`. -/
private lemma differentiable_riemannZeta₁_shift (z₀ : ℂ) :
    DifferentiableAt ℂ (fun z : ℂ => riemannZeta₁ (1 + z)) z₀ := by
  have hlin : DifferentiableAt ℂ (fun z : ℂ => 1 + z) z₀ := by fun_prop
  have hg : DifferentiableAt ℂ riemannZeta₁ ((fun z : ℂ => 1 + z) z₀) :=
    differentiable_riemannZeta₁.differentiableAt
  exact DifferentiableAt.fun_comp' (f := fun z : ℂ => 1 + z) (g := riemannZeta₁)
    (x := z₀) hg hlin

/-- The residue of the Riemann zeta function at `s = 1` is `1`, uniformly on a
small disc: `z * ζ (1 + z) = 1 + O(z)` as `z → 0`. -/
theorem riemannZeta_residue_uniform_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖z‖ ≤ r → z ≠ 0 →
      ‖z * riemannZeta (1 + z) - 1‖ ≤ C * ‖z‖ := by
  -- `z ↦ riemannZeta₁ (1 + z)` is differentiable at `0`, with value `1` at `0`.
  have hdiff : DifferentiableAt ℂ (fun z : ℂ => riemannZeta₁ (1 + z)) 0 :=
    differentiable_riemannZeta₁_shift 0
  have hbigO := hdiff.isBigO_sub
  -- hbigO : (fun x => riemannZeta₁ (1 + x) - riemannZeta₁ (1 + 0)) =O[𝓝 0] fun x => x - 0
  rcases Asymptotics.isBigO_iff.mp hbigO with ⟨c, hc⟩
  -- hc : ∀ᶠ (x : ℂ) in 𝓝 0, ‖riemannZeta₁ (1 + x) - riemannZeta₁ (1 + 0)‖ ≤ c * ‖x - 0‖
  let K : ℝ := max c 0 + 1
  have hKpos : 0 < K := by
    dsimp [K]
    linarith [le_max_right c 0]
  have hcK : ∀ᶠ y in 𝓝 (0 : ℂ), ‖riemannZeta₁ (1 + y) - 1‖ ≤ K * ‖y‖ := by
    filter_upwards [hc] with y hy
    have hy1 : ‖riemannZeta₁ (1 + y) - 1‖ ≤ c * ‖y‖ := by
      simpa [riemannZeta₁_one] using hy
    calc
      ‖riemannZeta₁ (1 + y) - 1‖ ≤ c * ‖y‖ := hy1
      _ ≤ max c 0 * ‖y‖ := mul_le_mul_of_nonneg_right (le_max_left c 0) (norm_nonneg y)
      _ ≤ K * ‖y‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg y)
        dsimp [K]
        linarith
  rcases Metric.eventually_nhds_iff.mp hcK with ⟨ρ, hρpos, hρ⟩
  refine ⟨K, hKpos, ρ / 2, half_pos hρpos, ?_⟩
  intro z hz hz0
  have hzlt : ‖z‖ < ρ := lt_of_le_of_lt hz (half_lt_self hρpos)
  have hdist : dist z 0 < ρ := by
    simpa [dist_eq_norm] using hzlt
  have hb := hρ hdist
  -- hb : ‖riemannZeta₁ (1 + z) - 1‖ ≤ K * ‖z‖
  have hs : (1 + z : ℂ) ≠ 1 := by
    intro h1
    apply hz0
    have hz' : z = (1 : ℂ) - 1 := by
      calc
        z = ((1 : ℂ) + z) - 1 := by ring
        _ = (1 : ℂ) - 1 := by rw [h1]
    simpa using hz'
  have hmul : z * riemannZeta (1 + z) = riemannZeta₁ (1 + z) := by
    have hzstep : ((1 + z : ℂ) - 1) = z := by ring
    rw [riemannZeta_eq_inv_sub_mul hs, hzstep]
    rw [← mul_assoc, mul_inv_cancel₀ hz0]
    simp
  simpa [hmul] using hb

end Commons.NumberTheory.Zeta