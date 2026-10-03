import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Basic
import Submission.Work.Pert.scale_lattice
import Submission.Work.Pert.DiffGate.diff_tauC_gate

/-!
# PERT · the differentiability gate for the lift `F_f = liftF u σ α` on the lower gate `Qm Ξ α`

`liftF u σ α w = w + (2πiα)⁻¹ · log (1 - sfun u σ α w)` is the lift of the perturbed germ
(Shishikura (A.1.6)), and `sfun u σ α w = σ u(τ w)/(1 + τ w u(τ w))`, `τ = tauC σ α`, is the
quotient of the universal cover (A.1.5).

The gate `Qm Ξ α = Qreg (Ξ - 1/α) (-Ξ)` avoids the pole lattice of `τ`, so `τ` is holomorphic
there (`Work.Pert.DiffGate.diff_tauC_gate`).  On top of that:

* the hypothesis `hNT` (`‖F w - (w+1)‖ ≤ 1/32`) forbids *both* degeneracies of the expression
  `sfun`: if `1 + τ w · u(τ w) = 0`, Lean's `x / 0 = 0` makes `sfun` vanish and `F w = w`, and if
  `1 - sfun w = 0` then `Complex.log 0 = 0` and again `F w = w`; either way `‖F w - (w+1)‖ = 1`,
  contradicting `1/32`.  Hence `sfun` is a genuine quotient on `Qm Ξ α` (so it is holomorphic);
* the same hypothesis pins the argument of the logarithm: `log (1 - sfun w) ≈ 2πiα` with
  `‖2πiα‖ ≤ 2π/64 < 1`, so `1 - sfun w = exp (log (1 - sfun w))` is within distance `<1` of `1`
  and therefore lies in `Complex.slitPlane`, the domain on which `Complex.log` is complex
  differentiable.

Both together give `DifferentiableOn ℂ (liftF u σ α) (Qm Ξ α)`.
-/

namespace Work.Pert

open Complex

set_option linter.unusedVariables false

theorem liftF_differentiableOn_gate {Ξ rr : ℝ} {α σ : ℂ} {u : ℂ → ℂ}
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hInF1 : MandelDim.InF1 α) (hα64 : ‖α‖ ≤ 1 / 64)
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    (hσ : σ ≠ 0) (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hτQ : ∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr)
    (hNT : ∀ z ∈ Work.Pert.Qm Ξ α, ‖Work.Pert.liftF u σ α z - (z + 1)‖ ≤ 1 / 32) :
    DifferentiableOn ℂ (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α) := by
  have hαne : α ≠ 0 := by
    have hαre : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hInF1
    intro h; rw [h] at hαre; simp at hαre
  have hfac : (2 * Real.pi * Complex.I * α) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero) hαne
    exact_mod_cast Real.pi_ne_zero
  have hτ : DifferentiableOn ℂ (tauC σ α) (Qm Ξ α) :=
    (DiffGate.diff_tauC_gate (σ := σ) (α := α) hΞ hInF1).2
  -- `hNT` forbids the vanishing of the quotient denominator of `sfun`
  have hden : ∀ w ∈ Qm Ξ α, 1 + tauC σ α w * u (tauC σ α w) ≠ 0 := by
    intro w hw h
    have h1 := hNT w hw
    have hg : (1 : ℂ) - sfun u σ α w = 1 := by simp [sfun, h]
    simp only [liftF, hg, Complex.log_one, mul_zero, add_zero] at h1
    have h2 : ‖w - (w + 1)‖ = 1 := by
      rw [show w - (w + 1) = (-1 : ℂ) by ring, norm_neg, norm_one]
    rw [h2] at h1
    linarith
  -- hence `sfun` is holomorphic on the gate
  have hsfun : DifferentiableOn ℂ (sfun u σ α) (Qm Ξ α) := by
    have htu : DifferentiableOn ℂ (fun w => u (tauC σ α w)) (Qm Ξ α) := hu.comp hτ hτQ
    have hnum : DifferentiableOn ℂ (fun w => σ * u (tauC σ α w)) (Qm Ξ α) := htu.const_mul σ
    have hden' : DifferentiableOn ℂ (fun w => 1 + tauC σ α w * u (tauC σ α w)) (Qm Ξ α) :=
      (differentiableOn_const 1).add (hτ.mul htu)
    exact hnum.div hden' hden
  -- `hNT` forbids `1 - sfun = 0` (Lean's `log 0 = 0` would give `F w = w`)
  have hg_ne : ∀ w ∈ Qm Ξ α, (1 : ℂ) - sfun u σ α w ≠ 0 := by
    intro w hw h
    have h1 := hNT w hw
    simp only [liftF, h, Complex.log_zero, mul_zero, add_zero] at h1
    have h2 : ‖w - (w + 1)‖ = 1 := by
      rw [show w - (w + 1) = (-1 : ℂ) by ring, norm_neg, norm_one]
    rw [h2] at h1
    linarith
  -- the argument of the logarithm lies in the slit plane
  have hslit : ∀ w ∈ Qm Ξ α, (1 : ℂ) - sfun u σ α w ∈ Complex.slitPlane := by
    intro w hw
    set g : ℂ := 1 - sfun u σ α w with hg
    have hgn : g ≠ 0 := by rw [hg]; exact hg_ne w hw
    set L : ℂ := (1 / (2 * Real.pi * Complex.I * α)) * Complex.log g with hL
    -- `L` is `F w - w`, so `hNT` bounds `‖L - 1‖`
    have hL1 : ‖L - 1‖ ≤ 1 / 32 := by
      have h1 := hNT w hw
      have hkey : liftF u σ α w - (w + 1) = L - 1 := by
        rw [hL, hg]; simp only [liftF]; ring
      rwa [hkey] at h1
    have hLn : ‖L‖ ≤ 33 / 32 := by
      have h := norm_add_le (L - 1) (1 : ℂ)
      rw [sub_add_cancel] at h
      simp only [norm_one] at h
      linarith
    have hI : ‖(2 : ℂ) * Real.pi * Complex.I‖ = 2 * Real.pi := by
      rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_nonneg]
    have h1 : ‖2 * Real.pi * Complex.I * α‖ ≤ 2 * Real.pi * (1 / 64) := by
      rw [norm_mul, hI]
      exact mul_le_mul_of_nonneg_left hα64 (by positivity)
    have hz : ‖2 * Real.pi * Complex.I * α * L‖ < 1 / 2 := by
      rw [show 2 * Real.pi * Complex.I * α * L = (2 * Real.pi * Complex.I * α) * L by ring,
        norm_mul]
      have h2 := mul_le_mul h1 hLn (norm_nonneg L)
        (by positivity : (0 : ℝ) ≤ 2 * Real.pi * (1 / 64))
      nlinarith [Real.pi_lt_four]
    -- hence `g = exp (2πiα L)`, exponentially close to `1`
    have hexp : Complex.exp (2 * Real.pi * Complex.I * α * L) = g := by
      rw [hL]
      have hAB : (2 * Real.pi * Complex.I * α) * (1 / (2 * Real.pi * Complex.I * α)) = 1 := by
        rw [mul_one_div, div_self hfac]
      rw [show 2 * Real.pi * Complex.I * α * ((1 / (2 * Real.pi * Complex.I * α)) * Complex.log g)
            = ((2 * Real.pi * Complex.I * α) * (1 / (2 * Real.pi * Complex.I * α))) * Complex.log g
            by ring, hAB, one_mul, Complex.exp_log hgn]
    have hb : ‖g - 1‖ < 1 := by
      rw [← hexp]
      calc ‖Complex.exp (2 * Real.pi * Complex.I * α * L) - 1‖
          ≤ 2 * ‖2 * Real.pi * Complex.I * α * L‖ := Complex.norm_exp_sub_one_le (by linarith)
        _ < 1 := by linarith
    have hmem : g ∈ Complex.slitPlane := by
      have := Complex.mem_slitPlane_of_norm_lt_one hb
      simpa [add_sub_cancel_left] using this
    rw [hg] at hmem
    exact hmem
  have h1 : DifferentiableOn ℂ (fun w => (1 : ℂ) - sfun u σ α w) (Qm Ξ α) :=
    (differentiableOn_const 1).sub hsfun
  have h2 : DifferentiableOn ℂ (fun w => Complex.log ((1 : ℂ) - sfun u σ α w)) (Qm Ξ α) :=
    h1.clog hslit
  have h3 : DifferentiableOn ℂ
      (fun w => (1 / (2 * Real.pi * Complex.I * α)) * Complex.log ((1 : ℂ) - sfun u σ α w))
      (Qm Ξ α) := h2.const_mul _
  have h4 : DifferentiableOn ℂ
      (fun w => w + (1 / (2 * Real.pi * Complex.I * α)) * Complex.log ((1 : ℂ) - sfun u σ α w))
      (Qm Ξ α) := differentiableOn_id.add h3
  exact h4

end Work.Pert
