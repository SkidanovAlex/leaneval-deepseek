import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.sigma_alpha_close
import Submission.Work.Pert.tauC_add_inv_le

namespace Work.PertCrux

/-- Comparison of the perturbed chart `τ_f = Work.Pert.tauC σ α` with the unperturbed chart
`τ₀ = MandelDim.tau0` at the *same* point `w`, in the regime of Shishikura (A.1.7)(ii):

  `‖τ_f(w) - τ₀(w)‖ ≤ 4π‖α‖ + (8π²‖α‖ + 4π‖u₀-1‖)/(π m)`,

for `0 < m ≤ ‖w‖`, `2π‖α‖‖w‖ ≤ 1/2`, the normalisation `1 - σ u₀ = exp(2πiα)` with
`‖α‖ ≤ 1/(2π)`, `‖u₀ - 1‖ ≤ 1/2`.

This is the combination of the Laurent estimate `Work.Pert.tauC_add_inv_le`
(`τ_f(w) + 1/w = O(1/|w|) + O(‖α‖)`) with the perturbation bound `Work.Pert.sigma_alpha_close`
(`‖σ/α + 2πi‖ ≤ 8π²‖α‖ + 4π‖u₀-1‖`), using `τ₀ w = -1/w`. -/
theorem norm_tauC_sub_tau0_le {σ α u0 w : ℂ} {m : ℝ} (hα : α ≠ 0) (hw : w ≠ 0)
    (hm : 0 < m) (hwm : m ≤ ‖w‖) (hu0 : ‖u0 - 1‖ ≤ 1 / 2)
    (hrel : 1 - σ * u0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hαs : ‖α‖ ≤ 1 / (2 * Real.pi))
    (hsmall : 2 * Real.pi * ‖α‖ * ‖w‖ ≤ 1 / 2) :
    ‖Work.Pert.tauC σ α w - MandelDim.tau0 w‖ ≤
      4 * Real.pi * ‖α‖ +
        (8 * Real.pi ^ 2 * ‖α‖ + 4 * Real.pi * ‖u0 - 1‖) / (Real.pi * m) := by
  -- `τ₀ w = -1/w`, so `τ_f w - τ₀ w = τ_f w + 1/w`
  have hsub : Work.Pert.tauC σ α w - MandelDim.tau0 w = Work.Pert.tauC σ α w + 1 / w := by
    rw [MandelDim.tau0]; ring
  rw [hsub]
  -- Laurent estimate
  have h1 := Work.Pert.tauC_add_inv_le σ α w hα hw hm hwm hsmall
  -- perturbation bound on `σ/α + 2πi`
  have hσ : ‖σ / α + 2 * Real.pi * Complex.I‖
      ≤ 8 * Real.pi ^ 2 * ‖α‖ + 4 * Real.pi * ‖u0 - 1‖ :=
    (Work.Pert.sigma_alpha_close (u := fun _ => u0) hα hαs hu0 hrel).1
  have hπm : 0 < Real.pi * m := mul_pos Real.pi_pos hm
  have hA : ‖σ / α + 2 * Real.pi * Complex.I‖ / (Real.pi * m)
      ≤ (8 * Real.pi ^ 2 * ‖α‖ + 4 * Real.pi * ‖u0 - 1‖) / (Real.pi * m) :=
    div_le_div_of_nonneg_right hσ hπm.le
  have hB : (2 * Real.pi) ^ 2 * ‖α‖ / Real.pi = 4 * Real.pi * ‖α‖ := by
    rw [div_eq_iff Real.pi_ne_zero]
    ring
  calc ‖Work.Pert.tauC σ α w + 1 / w‖
      ≤ ‖σ / α + 2 * Real.pi * Complex.I‖ / (Real.pi * m)
          + (2 * Real.pi) ^ 2 * ‖α‖ / Real.pi := h1
    _ = ‖σ / α + 2 * Real.pi * Complex.I‖ / (Real.pi * m) + 4 * Real.pi * ‖α‖ := by rw [hB]
    _ ≤ (8 * Real.pi ^ 2 * ‖α‖ + 4 * Real.pi * ‖u0 - 1‖) / (Real.pi * m)
          + 4 * Real.pi * ‖α‖ := by linarith [hA]
    _ = 4 * Real.pi * ‖α‖
          + (8 * Real.pi ^ 2 * ‖α‖ + 4 * Real.pi * ‖u0 - 1‖) / (Real.pi * m) := by ring

end Work.PertCrux
