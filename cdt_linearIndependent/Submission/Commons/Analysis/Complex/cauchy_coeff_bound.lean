import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Liouville

open Metric

noncomputable section

-- The project harness elaborates `(ρ : ENNReal)` for `ρ : ℝ` through `ENNReal.ofReal`.
local instance : Coe ℝ ENNReal := ⟨ENNReal.ofReal⟩

namespace Commons.Analysis.Complex

theorem cauchy_coeff_bound {f : ℂ → ℂ} {ρ M : ℝ} (hρ : 0 < ρ)
    (hM : ∀ z : ℂ, z ∈ Metric.sphere (0 : ℂ) ρ → ‖f z‖ ≤ M)
    (hd : DifferentiableOn ℂ f (closedBall (0 : ℂ) ρ))
    {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : HasFPowerSeriesOnBall f p (0 : ℂ) (ρ : ENNReal)) (n : ℕ) :
    ‖p n (fun _ : Fin n => (1 : ℂ))‖ ≤ M / ρ ^ n := by
  have hc_eq : (n.factorial : ℂ) *
      p n (fun _ : Fin n => (1 : ℂ)) = iteratedDeriv n f (0 : ℂ) := by
    have hfs := hp.factorial_smul (1 : ℂ) n
    rw [nsmul_eq_mul] at hfs
    exact hfs.trans (by
      rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Finset.prod_const_one, one_smul])
  have hb : DiffContOnCl ℂ f (ball (0 : ℂ) ρ) := by
    exact DiffContOnCl.mk_ball (hd.mono ball_subset_closedBall) hd.continuousOn
  have hcau : ‖iteratedDeriv n f (0 : ℂ)‖ ≤ (n.factorial : ℝ) * M / ρ ^ n := by
    exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hρ hb hM
  have hnorm : (n.factorial : ℝ) *
      ‖p n (fun _ : Fin n => (1 : ℂ))‖ = ‖iteratedDeriv n f (0 : ℂ)‖ := by
    rw [← hc_eq]
    rw [norm_mul]
    simp
  have hnorm_le : (n.factorial : ℝ) *
      ‖p n (fun _ : Fin n => (1 : ℂ))‖ ≤ (n.factorial : ℝ) * (M / ρ ^ n) := by
    rw [hnorm]
    calc
      ‖iteratedDeriv n f (0 : ℂ)‖ ≤ (n.factorial : ℝ) * M / ρ ^ n := hcau
      _ = (n.factorial : ℝ) * (M / ρ ^ n) := by rw [mul_div_assoc]
  exact le_of_mul_le_mul_left hnorm_le (by positivity : (0 : ℝ) < (n.factorial : ℝ))

end Commons.Analysis.Complex