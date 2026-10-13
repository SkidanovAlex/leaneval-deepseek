/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/L12JepsAux/Basic.lean`

Helper lemmas for the target `Work.FTS.StrongEps.EpsE4Thr.L12JepsDeriv`
(`Submission/Work/FTS/StrongEps/EpsE4Thr/L12JepsDeriv.lean`), which asks for the fake-time
derivative of the `L₁₂`-zero mode of the mollified family:

  `∂_τ L₁₂ (J_ε (slice g τ)) 0 = L₁₂ (J_ε (epsRHSP … g τ)) 0`.

The analytic content is the *two-level* differentiation (the outer `r`-integral, the inner
`θ`-integral) together with the one genuinely non-elementary input: the **measurability in `θ`**
of `θ ↦ J_ε f r θ`, which the hypotheses of the target do *not* state directly and which has to be
produced from the all-`(r,θ)` integrability hypothesis `hint` (it forces the slice to be a.e.
measurable on the quadrant, hence — in the log coordinates where `J_ε` is a convolution — the slice
function is a.e. measurable).

This file collects the elementary parts: the existence of a point where `Jker ρ ε > 0`, the
transport of `hint` to the log coordinates, and the integrability of the two `θ`-integrands.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.Jker_integral_eq_one
import Submission.Work.FTS.StrongEps.JepsBasic
import Submission.Work.FTS.StrongEps.EpsE4Thr.hasDerivWithinAt_Jeps_slice_repair
import Submission.Work.FTS.StrongEps.EpsE4Thr.Repair.aestronglyMeasurable_Jker_mul_epsRHSP
import Submission.Work.FTS.StrongEps.EpsE4Thr.L12JepsAux.aesm_of_integrable_mul_shift

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open Work.FTS.StrongEps (Jeps Jker logPull zShift thShift sOf zetaOf IsMollKernel IsSmoothKernel)
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.StrongEps.EpsE4Thr.L12JepsAux

set_option autoImplicit false

/-! ## The kernel has a point of strict positivity -/

theorem exists_pos_Jker {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ × ℝ, 0 < Jker ρ ε p := by
  by_contra h
  simp only [not_exists, not_lt] at h
  have hρ0 : ∀ q : ℝ × ℝ, ρ q = 0 := by
    intro q
    have h1 : Jker ρ ε (ε • q) ≤ 0 := h (ε • q)
    have heq : Jker ρ ε (ε • q) = ε⁻¹ ^ 2 * ρ q := by
      simp only [Jker, smul_smul, inv_mul_cancel₀ hε.ne', one_smul]
    rw [heq] at h1
    have h2 : ρ q ≤ 0 := by
      by_contra hlt
      push_neg at hlt
      have : 0 < ε⁻¹ ^ 2 * ρ q := mul_pos (by positivity) hlt
      linarith
    exact le_antisymm h2 (hρ.nonneg q)
  have hzero : (∫ p : ℝ × ℝ, ρ p) = 0 := by
    rw [show (fun p : ℝ × ℝ => ρ p) = fun _ => (0 : ℝ) from funext hρ0, integral_zero]
  rw [hρ.mass] at hzero
  norm_num at hzero

/-! ## The transport of `hint` to the log coordinates -/

/-- The integrability hypothesis `hint` of the target, transported to the log coordinates: for
every shift vector `x` of the plane the log-pull of the slice is integrable against the shifted
kernel.  This is the hypothesis of `aesm_of_integrable_mul_shift`. -/
theorem integrable_shift_logPull_of_hint {ρ : ℝ × ℝ → ℝ} {ε T : ℝ} {g : Fam}
    (hint : ∀ r θ : ℝ, 0 < r → θ ∈ Set.Ioo 0 (Real.pi / 2) → ∀ s ∈ Set.Icc 0 T,
      MeasureTheory.Integrable (fun p : ℝ × ℝ => Jker ρ ε p *
        (slice g s) (zShift r p.1) (thShift θ p.2)) MeasureTheory.volume) :
    ∀ s ∈ Set.Icc 0 T, ∀ x : ℝ × ℝ,
      MeasureTheory.Integrable (fun p : ℝ × ℝ => Jker ρ ε p *
        logPull (slice g s) (x - p)) MeasureTheory.volume := by
  intro s hs x
  have hr : 0 < Real.exp x.1 := Real.exp_pos x.1
  have hθ : Real.arctan (Real.exp x.2) ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨(Real.arctan_pos).2 (Real.exp_pos x.2), Real.arctan_lt_pi_div_two _⟩
  refine (hint (Real.exp x.1) (Real.arctan (Real.exp x.2)) hr hθ s hs).congr ?_
  refine Eventually.of_forall fun p => ?_
  show Jker ρ ε p * slice g s (zShift (Real.exp x.1) p.1)
      (thShift (Real.arctan (Real.exp x.2)) p.2)
    = Jker ρ ε p * logPull (slice g s) (x - p)
  have hp : x - p
      = (sOf (Real.exp x.1) - p.1, zetaOf (Real.arctan (Real.exp x.2)) - p.2) := by
    ext <;> simp only [Prod.fst_sub, Prod.snd_sub, sOf, zetaOf, Real.log_exp, Real.tan_arctan]
  rw [hp, logPull_shift (slice g s) hr hθ]

/-- **The log-pull of a slice is a.e. strongly measurable**, from the all-`(r,θ)` integrability
hypothesis `hint` of the target: the kernel has a point of strict positivity, so the shift family
of integrable products forces measurability of the log-pull. -/
theorem aesm_logPull_slice_of_hint {ρ : ℝ × ℝ → ℝ} {ε T : ℝ} {g : Fam}
    (hρ : IsMollKernel ρ) (hε : 0 < ε)
    (hint : ∀ r θ : ℝ, 0 < r → θ ∈ Set.Ioo 0 (Real.pi / 2) → ∀ s ∈ Set.Icc 0 T,
      MeasureTheory.Integrable (fun p : ℝ × ℝ => Jker ρ ε p *
        (slice g s) (zShift r p.1) (thShift θ p.2)) MeasureTheory.volume) :
    ∀ s ∈ Set.Icc 0 T, MeasureTheory.AEStronglyMeasurable (logPull (slice g s))
      MeasureTheory.volume := by
  intro s hs
  exact aesm_of_integrable_mul_shift (Jker_continuous hρ ε) (exists_pos_Jker hρ hε)
    (integrable_shift_logPull_of_hint hint s hs)

/-- Componentwise bounds give the product norm bound (the norm on `ℝ × ℝ` is the sup norm). -/
lemma norm_le_of_abs_le {p : ℝ × ℝ} {ε : ℝ} (h1 : |p.1| ≤ ε) (h2 : |p.2| ≤ ε) :
    ‖p‖ ≤ ε := by
  rw [Prod.norm_def, max_le_iff]
  exact ⟨by simpa [Real.norm_eq_abs] using h1, by simpa [Real.norm_eq_abs] using h2⟩

/-! ## Integrability of the two `θ`-integrands -/

/-- **Integrability of the `p`-integrand of the right-hand-side profile**: a uniform bound on the
profile over the shifted points (the `‖p‖ ≤ ε`-cone carrying the support of `Jker ρ ε`) plus
a.e.-strong measurability of the product make it integrable against `C · ‖Jker ρ ε‖`. -/
theorem integrable_Jker_mul_of_bound {ρ : ℝ × ℝ → ℝ} {ε r C : ℝ} {f : Fn}
    (hρ : IsMollKernel ρ) (hε : 0 < ε) (hC : 0 ≤ C)
    (hmeas : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Jker ρ ε p * f (zShift r p.1) (thShift θ p.2)) MeasureTheory.volume)
    (hb : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ p : ℝ × ℝ, ‖p‖ ≤ ε →
      |f (zShift r p.1) (thShift θ p.2)| ≤ C) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Jker ρ ε p * f (zShift r p.1) (thShift θ p.2)) MeasureTheory.volume := by
  intro θ hθ
  refine MeasureTheory.Integrable.mono' ((Jker_integrable hρ hε).norm.const_mul C)
    (hmeas θ hθ) ?_
  refine Eventually.of_forall fun p => ?_
  by_cases hp : ‖p‖ ≤ ε
  · show ‖Jker ρ ε p * f (zShift r p.1) (thShift θ p.2)‖ ≤ C * ‖Jker ρ ε p‖
    rw [norm_mul, Real.norm_eq_abs]
    calc ‖Jker ρ ε p‖ * |f (zShift r p.1) (thShift θ p.2)|
        ≤ ‖Jker ρ ε p‖ * C := mul_le_mul_of_nonneg_left (hb θ hθ p hp) (norm_nonneg _)
      _ = C * ‖Jker ρ ε p‖ := by ring
  · have hz : Jker ρ ε p = 0 :=
      Jker_eq_zero_of_not_mem hρ hε (by
        rw [Metric.mem_closedBall, dist_zero_right]; exact hp)
    calc ‖Jker ρ ε p * f (zShift r p.1) (thShift θ p.2)‖ = 0 := by rw [hz, zero_mul, norm_zero]
      _ ≤ C * ‖Jker ρ ε p‖ := mul_nonneg hC (norm_nonneg _)

/-- **Integrability of the `θ`-integrand of a slice on `[0, π/2]`**: a.e.-strong measurability in
`θ` plus the sup-bound of `J_ε` over the shifted region (`abs_Jeps_le_sup`). -/
theorem integrable_Jeps_slice_Icc_of_bound {ρ : ℝ × ℝ → ℝ} {ε r C : ℝ} {f : Fn}
    (hρ : IsMollKernel ρ) (hε : 0 < ε) (hr : 0 < r) (hC : 0 ≤ C)
    (hmeas : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => Jeps ρ ε f r θ)
      (MeasureTheory.volume.restrict (Set.Icc 0 (Real.pi / 2))))
    (hb : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ p : ℝ × ℝ, ‖p‖ ≤ ε →
      |f (zShift r p.1) (thShift θ p.2)| ≤ C) :
    MeasureTheory.Integrable (fun θ : ℝ => Jeps ρ ε f r θ)
      (MeasureTheory.volume.restrict (Set.Icc 0 (Real.pi / 2))) := by
  refine MeasureTheory.Integrable.of_bound hmeas C (Eventually.of_forall fun θ => ?_)
  by_cases hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)
  · have hle : |Jeps ρ ε f r θ| ≤ C :=
      abs_Jeps_le_sup ρ hρ hε hr hθ
        (fun p hp1 hp2 => hb θ hθ p (norm_le_of_abs_le hp1 hp2))
        hC
    rwa [Real.norm_eq_abs]
  · rw [Jeps_eq_zero ρ ε f (fun hc => hθ hc.2), norm_zero]
    exact hC

end Work.FTS.StrongEps.EpsE4Thr.L12JepsAux
