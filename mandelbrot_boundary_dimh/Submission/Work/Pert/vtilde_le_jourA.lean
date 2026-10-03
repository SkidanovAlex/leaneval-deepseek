import Mathlib
import Submission.Work.Pert.CoordDefs
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Basic
import Submission.Work.Pert.vtilde_le_of_u_dev

namespace Work.Pert

/-- The `ṽ`-bound of `Work.Pert.vtilde_le_of_u_dev`, restricted to the connected journey
`JourA η` (see `CoordDefs.lean`) instead of the whole gate `Qm ξ₁ α`.

It is a VERBATIM copy of the PROVED `Work.Pert.vtilde_le_of_u_dev`
(`Submission/Work/Pert/vtilde_le_of_u_dev.lean`), whose proof is pointwise in `z`: it uses only
`hvt z hz` and `hτs z hz`.  The reason for the restriction is that its hypothesis
`∀ z ∈ Qm ξ₁ α, ‖τ_f z‖ ≤ 1/8` is NOT available for the whole (unbounded) gate, whereas on
`JourA` it follows from `‖τ_f ζ‖ ≤ 4/η` (`tauC_region_le` plus `‖ζ‖ ≥ 13η/40`). -/
theorem vtilde_le_jourA {u : ℂ → ℂ} {σ α : ℂ} {ξ₁ η rr : ℝ}
    (hα : α ≠ 0) (hσ : σ ≠ 0) (hu0 : ‖u 0 - 1‖ ≤ 1 / 1024)
    (heq : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hαs : 2 * Real.pi * ‖α‖ ≤ 1 / 64)
    (hu : DifferentiableOn ℂ u (Metric.ball 0 rr))
    (hτm : ∀ z ∈ Work.Pert.JourA η, Work.Pert.tauC σ α z ∈ Metric.ball 0 rr)
    (hτs : ∀ z ∈ Work.Pert.JourA η, ‖Work.Pert.tauC σ α z‖ ≤ 1 / 8)
    (hvt : ∀ z ∈ Work.Pert.JourA η, ‖Work.Pert.liftF u σ α z - (z + 1)‖ ≤ 1 / 32) :
    ∀ z ∈ Work.Pert.JourA η,
      ‖Work.Pert.liftF u σ α z - (z + 1)‖ ≤
        (3 / 2) * (‖Work.Pert.tauC σ α z‖ * ‖u (Work.Pert.tauC σ α z)‖
          + ‖u (Work.Pert.tauC σ α z) - u 0‖ / ‖u 0‖) := by
  -- the hypotheses `hσ`, `hu`, `hτm` belong to the interface but are not used in the estimate
  have _hσ := hσ
  have _hu := hu
  have _hτm := hτm
  intro z hz
  have hEne : (1 : ℂ) - σ * u 0 ≠ 0 := by rw [heq]; exact Complex.exp_ne_zero _
  have hu0ge : (1 : ℝ) - 1 / 1024 ≤ ‖u 0‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (u 0)
    rw [norm_one, norm_sub_rev] at h
    linarith [hu0, h]
  have hu0nz : ‖u 0‖ ≠ 0 := by
    have hpos : (0 : ℝ) < 1 - 1 / 1024 := by norm_num
    intro h0; rw [h0] at hu0ge; linarith
  have hs_eq : sfun u σ α z = σ * u (tauC σ α z) / (1 + tauC σ α z * u (tauC σ α z)) := rfl
  -- `log (1 - sfun) = 0` contradicts the near-translation hypothesis
  have hlog : Complex.log (1 - sfun u σ α z) ≠ 0 := by
    intro hl
    have hzf : liftF u σ α z = z := by
      unfold liftF
      rw [hl, mul_zero, add_zero]
    have hcon := hvt z hz
    rw [hzf] at hcon
    have hz1 : ‖(z : ℂ) - (z + 1)‖ = 1 := by
      rw [show (z : ℂ) - (z + 1) = -1 by ring, norm_neg, norm_one]
    rw [hz1] at hcon
    linarith
  have h1s : 1 - sfun u σ α z ≠ 0 := by
    intro h0
    exact hlog (by rw [h0, Complex.log_zero])
  have hhh : 1 + tauC σ α z * u (tauC σ α z) ≠ 0 := by
    intro h0
    have hs0 : sfun u σ α z = 0 := by
      rw [hs_eq, h0, div_zero]
    exact hlog (by rw [hs0, sub_zero, Complex.log_one])
  -- the exponential form of `(1 - sfun)/E`
  have hF : liftF u σ α z
      = z + (1 / (2 * Real.pi * Complex.I * α)) * Complex.log (1 - sfun u σ α z) := rfl
  have hexp1 := vtilde_exp (α := α) (z := z) (F := liftF u σ α z) (s := sfun u σ α z) hα hF h1s
  -- the algebraic identity for `(1 - sfun)/E - 1`
  have halg := vtilde_alg (σ := σ) (u0 := u 0) (uτ := u (tauC σ α z))
    (τ := tauC σ α z) hhh hEne
  have hexp2 : (1 - sfun u σ α z) / Complex.exp (2 * Real.pi * Complex.I * α) - 1
      = σ * (tauC σ α z * u (tauC σ α z) * u 0 - (u (tauC σ α z) - u 0))
          / ((1 - σ * u 0) * (1 + tauC σ α z * u (tauC σ α z))) := by
    rw [← heq, hs_eq]
    exact halg
  have hkey : Complex.exp (2 * Real.pi * Complex.I * α * (liftF u σ α z - z - 1)) - 1
      = σ * (tauC σ α z * u (tauC σ α z) * u 0 - (u (tauC σ α z) - u 0))
          / ((1 - σ * u 0) * (1 + tauC σ α z * u (tauC σ α z))) := by
    rw [← hexp1]
    exact hexp2
  have hnorm : ‖Complex.exp (2 * Real.pi * Complex.I * α * (liftF u σ α z - z - 1)) - 1‖
      = ‖σ‖ * ‖tauC σ α z * u (tauC σ α z) * u 0 - (u (tauC σ α z) - u 0)‖
          / (‖1 - σ * u 0‖ * ‖1 + tauC σ α z * u (tauC σ α z)‖) := by
    rw [hkey, norm_div, norm_mul, norm_mul]
  have hκ : ‖σ‖ / ‖1 - σ * u 0‖
      = ‖Complex.exp (-(2 * Real.pi * Complex.I * α)) - 1‖ / ‖u 0‖ := by
    rw [div_eq_div_iff (norm_ne_zero_iff.mpr hEne) hu0nz]
    rw [← norm_mul, ← norm_mul]
    have hsu : σ * u 0 = 1 - Complex.exp (2 * Real.pi * Complex.I * α) := by
      rw [← heq]; ring
    have hexpw : (Complex.exp (-(2 * Real.pi * Complex.I * α)) - 1)
        * Complex.exp (2 * Real.pi * Complex.I * α)
        = 1 - Complex.exp (2 * Real.pi * Complex.I * α) := by
      rw [sub_mul, Complex.exp_neg, inv_mul_cancel₀ (Complex.exp_ne_zero _), one_mul]
    rw [heq, hsu, hexpw]
  have hident : ‖Complex.exp (2 * Real.pi * Complex.I * α * (liftF u σ α z - (z + 1))) - 1‖
      = ‖Complex.exp (-(2 * Real.pi * Complex.I * α)) - 1‖
        * ‖tauC σ α z * u (tauC σ α z) * u 0 - (u (tauC σ α z) - u 0)‖
          / (‖u 0‖ * ‖1 + tauC σ α z * u (tauC σ α z)‖) := by
    have hsub : liftF u σ α z - (z + 1) = liftF u σ α z - z - 1 := by ring
    rw [hsub, hnorm, ← div_mul_div_comm, ← div_mul_div_comm, hκ]
  exact vtilde_numeric (σ := σ) (τ := tauC σ α z) (uτ := u (tauC σ α z)) (u0 := u 0)
    (W := liftF u σ α z - (z + 1)) hα hhh hαs hu0 (hτs z hz) (hvt z hz) hident

end Work.Pert
