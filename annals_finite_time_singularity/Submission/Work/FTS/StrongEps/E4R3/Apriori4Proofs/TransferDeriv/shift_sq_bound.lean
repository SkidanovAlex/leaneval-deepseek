import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.shift_diff_ftc
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.sq_intervalIntegral_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

/-- `ENNReal.ofReal` of a real integral is at most the lintegral of `ENNReal.ofReal`
(no integrability hypothesis is needed: either the lintegral is `∞`, or the function is
integrable and the two sides agree). -/
lemma ofReal_integral_le_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hfm : AEStronglyMeasurable f μ) (hf : 0 ≤ᵐ[μ] f) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases h : ∫⁻ x, ENNReal.ofReal (f x) ∂μ = ⊤
  · rw [h]; exact le_top
  · have h' : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≠ ⊤ := h
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      ((MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hfm hf).mp h') hf]

/-! **`shift_sq_bound`** — the second moment of the two-sided shift difference of a `C¹` profile.

For a nonnegative weight comparable to its translates forward and a `C¹` profile `G₂` with
weighted gradient in `L²`, `∫ Q y (G₂ (y+p) − G₂ (y−p))² ≤ 4‖p‖² e^{Cw(|p.1|+|p.2|)} ∫ Q y ‖fderiv ℝ G₂ y‖²`,
and the left integrand is integrable.

Suggested proof (feel free to restructure, and to delegate sub-steps):
* for fixed `y`, `φ t = G₂ (y + t • p)` has derivative `(fderiv ℝ G₂ (y + t•p)) p` at `t`
  (`ContDiff.continuous_fderiv`, `ContDiffAt.differentiableAt` → `DifferentiableAt.hasFDerivAt`,
  `HasFDerivAt.comp_hasDerivAt` with the affine parametrisation), so
  `intervalIntegral.integral_eq_sub_of_hasDerivAt` gives
  `G₂ (y+p) − G₂ (y−p) = ∫ t in (-1)..1, (fderiv ℝ G₂ (y + t•p)) p`;
* Cauchy–Schwarz in `t` (`ContinuousLinearMap.le_opNorm` then
  `MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg` with `p = q = 2` on the restricted
  measure, or `(∫ g)² ≤ (∫ 1²)(∫ g²)`) gives pointwise
  `(G₂ (y+p) − G₂ (y−p))² ≤ 2‖p‖² ∫ t in (-1)..1, ‖fderiv ℝ G₂ (y + t•p)‖²`;
* multiply by `Q y ≥ 0`, use `Q y ≤ e^{Cw|t||p|₁} Q (y + t•p) ≤ e^{Cw|p|₁} Q (y + t•p)` for
  `|t| ≤ 1` (`hQsh'` with shift `t • p`), and integrate in `y`, swapping the `y`- and
  `t`-integrals (Tonelli: `MeasureTheory.lintegral_lintegral_swap`,
  `MeasureTheory.ofReal_integral_eq_lintegral_ofReal`, translation invariance
  `MeasureTheory.lintegral_add_right_eq_self`), using `∫_{(-1)..1} 1 = 2`;
* integrability of the difference moment follows from finiteness of its lintegral
  (`MeasureTheory.hasFiniteIntegral_iff_ofReal`). -/
theorem shift_sq_bound {Q G₂ : ℝ × ℝ → ℝ} {Cw : ℝ} (hCw : 0 ≤ Cw)
    (hQ0 : ∀ y : ℝ × ℝ, 0 ≤ Q y) (hQm : Measurable Q)
    (hQsh' : ∀ y p : ℝ × ℝ, Q y ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q (y + p))
    (hG2d : ContDiff ℝ 1 G₂)
    (hI2 : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * ‖fderiv ℝ G₂ y‖ ^ 2))
    (p : ℝ × ℝ) :
    MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2)
      ∧ ∫ y : ℝ × ℝ, Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2
        ≤ 4 * ‖p‖ ^ 2 * Real.exp (Cw * (|p.1| + |p.2|))
            * ∫ y : ℝ × ℝ, Q y * ‖fderiv ℝ G₂ y‖ ^ 2 := by
  set K : ℝ := Cw * (|p.1| + |p.2|) with hK
  set J : ℝ := ∫ y : ℝ × ℝ, Q y * ‖fderiv ℝ G₂ y‖ ^ 2 with hJ
  set F : ℝ × ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal (Q u * ‖fderiv ℝ G₂ u‖ ^ 2) with hF
  set s : Set ℝ := Set.Ioc (-1 : ℝ) 1 with hs
  set H : (ℝ × ℝ) × ℝ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (2 * ‖p‖ ^ 2 * Real.exp K
      * (Q (z.1 + z.2 • p) * ‖fderiv ℝ G₂ (z.1 + z.2 • p)‖ ^ 2)) with hH
  have hexpK : 0 ≤ Real.exp K := (Real.exp_pos K).le
  have hJ0 : 0 ≤ J := by
    rw [hJ]
    exact integral_nonneg (fun y => mul_nonneg (hQ0 y) (sq_nonneg _))
  have hcfd : Continuous (fun u : ℝ × ℝ => fderiv ℝ G₂ u) := hG2d.continuous_fderiv (by norm_num)
  have hG2c : Continuous G₂ := hG2d.continuous
  -- ### the weight comparison
  have hweight : ∀ (y : ℝ × ℝ) (t : ℝ), |t| ≤ 1 → Q y ≤ Real.exp K * Q (y + t • p) := by
    intro y t ht
    have hexp_eq : |(t • p).1| + |(t • p).2| = |t| * (|p.1| + |p.2|) := by
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, abs_mul]
      ring
    have h := hQsh' y (t • p)
    rw [hexp_eq] at h
    have hKle : Cw * (|t| * (|p.1| + |p.2|)) ≤ K := by
      rw [hK]
      have h2 : |t| * (|p.1| + |p.2|) ≤ |p.1| + |p.2| := by
        calc |t| * (|p.1| + |p.2|) ≤ 1 * (|p.1| + |p.2|) :=
              mul_le_mul_of_nonneg_right ht (by positivity)
          _ = |p.1| + |p.2| := by ring
      exact mul_le_mul_of_nonneg_left h2 hCw
    calc Q y ≤ Real.exp (Cw * (|t| * (|p.1| + |p.2|))) * Q (y + t • p) := h
      _ ≤ Real.exp K * Q (y + t • p) :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hKle) (hQ0 _)
  -- ### the pointwise bound in real numbers: FTC + Cauchy--Schwarz + weight comparison
  have hpt : ∀ y : ℝ × ℝ, Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2
      ≤ 2 * ‖p‖ ^ 2 * ∫ t in (-1 : ℝ)..1, Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2 := by
    intro y
    have hcont1 : Continuous (fun t : ℝ => y + t • p) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hca : Continuous (fun t : ℝ => (fderiv ℝ G₂ (y + t • p)) p) :=
      (hcfd.comp hcont1).clm_apply continuous_const
    have hcs := sq_intervalIntegral_le (f := fun t : ℝ => (fderiv ℝ G₂ (y + t • p)) p)
      (a := -1) (b := 1) (by norm_num) (hca.intervalIntegrable (-1) 1)
      ((hca.pow 2).intervalIntegrable (-1) 1)
    have hbnd : ∀ t : ℝ,
        ((fderiv ℝ G₂ (y + t • p)) p) ^ 2 ≤ ‖p‖ ^ 2 * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2 := by
      intro t
      have hop := ContinuousLinearMap.le_opNorm (fderiv ℝ G₂ (y + t • p)) p
      rw [Real.norm_eq_abs] at hop
      calc ((fderiv ℝ G₂ (y + t • p)) p) ^ 2
          = |(fderiv ℝ G₂ (y + t • p)) p| ^ 2 := by rw [sq_abs]
        _ ≤ (‖fderiv ℝ G₂ (y + t • p)‖ * ‖p‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hop 2
        _ = ‖p‖ ^ 2 * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2 := by ring
    have hstep : (∫ t in (-1 : ℝ)..1, (fderiv ℝ G₂ (y + t • p)) p) ^ 2
        ≤ 2 * ‖p‖ ^ 2 * ∫ t in (-1 : ℝ)..1, ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2 := by
      have hmono : ∫ t in (-1 : ℝ)..1, (fderiv ℝ G₂ (y + t • p)) p ^ 2
          ≤ ∫ t in (-1 : ℝ)..1, ‖p‖ ^ 2 * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2 :=
        intervalIntegral.integral_mono (μ := volume) (by norm_num)
          ((hca.pow 2).intervalIntegrable (-1) 1)
          ((continuous_const.mul ((hcfd.comp hcont1).norm.pow 2)).intervalIntegrable (-1) 1) hbnd
      have hcs' : (∫ t in (-1 : ℝ)..1, (fderiv ℝ G₂ (y + t • p)) p) ^ 2
          ≤ 2 * ∫ t in (-1 : ℝ)..1, (fderiv ℝ G₂ (y + t • p)) p ^ 2 := by
        simpa only [show (1 : ℝ) - (-1) = 2 from by norm_num] using hcs
      calc (∫ t in (-1 : ℝ)..1, (fderiv ℝ G₂ (y + t • p)) p) ^ 2
          ≤ 2 * ∫ t in (-1 : ℝ)..1, (fderiv ℝ G₂ (y + t • p)) p ^ 2 := hcs'
        _ ≤ 2 * ∫ t in (-1 : ℝ)..1, ‖p‖ ^ 2 * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2 :=
              mul_le_mul_of_nonneg_left hmono (by norm_num)
        _ = 2 * ‖p‖ ^ 2 * ∫ t in (-1 : ℝ)..1, ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2 := by
              rw [intervalIntegral.integral_const_mul]; ring
    rw [shift_diff_ftc hG2d y p]
    calc Q y * (∫ t in (-1 : ℝ)..1, (fderiv ℝ G₂ (y + t • p)) p) ^ 2
        ≤ Q y * (2 * ‖p‖ ^ 2 * ∫ t in (-1 : ℝ)..1, ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hstep (hQ0 y)
      _ = 2 * ‖p‖ ^ 2 * ∫ t in (-1 : ℝ)..1, Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2 := by
          rw [intervalIntegral.integral_const_mul]; ring
  -- ### the same bound, upgraded to `ℝ≥0∞` so that Tonelli applies
  have hpt2 : ∀ y : ℝ × ℝ,
      ENNReal.ofReal (Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2)
        ≤ ∫⁻ t in s, H (y, t) := by
    intro y
    have hmeas_t : AEStronglyMeasurable
        (fun t : ℝ => Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2) (volume.restrict s) := by
      apply Measurable.aestronglyMeasurable
      have hc : Continuous (fun t : ℝ => y + t • p) :=
        continuous_const.add (continuous_id.smul continuous_const)
      exact measurable_const.mul (((hcfd.comp hc).norm).pow 2).measurable
    have hmt : Measurable
        (fun t : ℝ => ENNReal.ofReal (Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2)) := by
      have hc : Continuous (fun t : ℝ => y + t • p) :=
        continuous_const.add (continuous_id.smul continuous_const)
      exact ENNReal.measurable_ofReal.comp
        (measurable_const.mul (((hcfd.comp hc).norm).pow 2).measurable)
    have hstep1 : ENNReal.ofReal (Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2)
        ≤ ENNReal.ofReal (2 * ‖p‖ ^ 2)
          * ENNReal.ofReal (∫ t in (-1 : ℝ)..1, Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2) := by
      calc ENNReal.ofReal (Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2)
          ≤ ENNReal.ofReal (2 * ‖p‖ ^ 2
              * ∫ t in (-1 : ℝ)..1, Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2) :=
            ENNReal.ofReal_le_ofReal (hpt y)
        _ = ENNReal.ofReal (2 * ‖p‖ ^ 2)
              * ENNReal.ofReal (∫ t in (-1 : ℝ)..1, Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2) :=
            ENNReal.ofReal_mul (by positivity)
    have hstep2 : ENNReal.ofReal (∫ t in (-1 : ℝ)..1, Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2)
        ≤ ∫⁻ t in s, ENNReal.ofReal (Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2) := by
      have h1 : (∫ t in (-1 : ℝ)..1, Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2)
          = ∫ t, Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2 ∂(volume.restrict s) := by
        rw [hs, intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      rw [h1]
      exact ofReal_integral_le_lintegral hmeas_t
        (Eventually.of_forall (fun t => mul_nonneg (hQ0 y) (sq_nonneg _)))
    have hstep3 : ENNReal.ofReal (2 * ‖p‖ ^ 2)
          * ENNReal.ofReal (∫ t in (-1 : ℝ)..1, Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2)
        ≤ ENNReal.ofReal (2 * ‖p‖ ^ 2)
          * ∫⁻ t in s, ENNReal.ofReal (Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2) :=
      mul_le_mul_right hstep2 _
    have hstep4 : ENNReal.ofReal (2 * ‖p‖ ^ 2)
          * ∫⁻ t in s, ENNReal.ofReal (Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2)
        = ∫⁻ t in s, ENNReal.ofReal (2 * ‖p‖ ^ 2)
          * ENNReal.ofReal (Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2) :=
      (MeasureTheory.lintegral_const_mul (ENNReal.ofReal (2 * ‖p‖ ^ 2)) hmt).symm
    have hstep5 : ∫⁻ t in s, ENNReal.ofReal (2 * ‖p‖ ^ 2)
          * ENNReal.ofReal (Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2)
        ≤ ∫⁻ t in s, H (y, t) := by
      rw [hH]
      refine MeasureTheory.lintegral_mono_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
      have htabs : |t| ≤ 1 := by
        rcases ht with ⟨h1, h2⟩
        rw [abs_le]
        exact ⟨by linarith, by linarith⟩
      have hw := hweight y t htabs
      have hreal : 2 * ‖p‖ ^ 2 * (Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2)
          ≤ 2 * ‖p‖ ^ 2 * Real.exp K
            * (Q (y + t • p) * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2) := by
        have h1 : Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2
            ≤ Real.exp K * Q (y + t • p) * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hw (sq_nonneg _)
        have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 2 * ‖p‖ ^ 2 by positivity)
        calc 2 * ‖p‖ ^ 2 * (Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2)
            ≤ 2 * ‖p‖ ^ 2
              * (Real.exp K * Q (y + t • p) * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2) := h2
          _ = 2 * ‖p‖ ^ 2 * Real.exp K
              * (Q (y + t • p) * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2) := by ring
      calc ENNReal.ofReal (2 * ‖p‖ ^ 2)
            * ENNReal.ofReal (Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2)
          = ENNReal.ofReal (2 * ‖p‖ ^ 2 * (Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2)) :=
            (ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 * ‖p‖ ^ 2 by positivity)).symm
        _ ≤ ENNReal.ofReal (2 * ‖p‖ ^ 2 * Real.exp K
              * (Q (y + t • p) * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2)) :=
            ENNReal.ofReal_le_ofReal hreal
    calc ENNReal.ofReal (Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2)
        ≤ ENNReal.ofReal (2 * ‖p‖ ^ 2)
          * ENNReal.ofReal (∫ t in (-1 : ℝ)..1, Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2) := hstep1
      _ ≤ ENNReal.ofReal (2 * ‖p‖ ^ 2)
          * ∫⁻ t in s, ENNReal.ofReal (Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2) := hstep3
      _ = ∫⁻ t in s, ENNReal.ofReal (2 * ‖p‖ ^ 2)
          * ENNReal.ofReal (Q y * ‖fderiv ℝ G₂ (y + t • p)‖ ^ 2) := hstep4
      _ ≤ ∫⁻ t in s, H (y, t) := hstep5
  -- ### Tonelli: swap the `y`- and `t`-integrals, then use translation invariance
  have hHmeas : AEMeasurable H (volume.prod (volume.restrict s)) := by
    rw [hH]
    apply Measurable.aemeasurable
    have hc : Continuous (fun z : (ℝ × ℝ) × ℝ => z.1 + z.2 • p) :=
      continuous_fst.add (continuous_snd.smul continuous_const)
    exact ENNReal.measurable_ofReal.comp
      (measurable_const.mul ((hQm.comp hc.measurable).mul
        (((hcfd.comp hc).norm).pow 2).measurable))
  have hlin1 : ∫⁻ y : ℝ × ℝ, ENNReal.ofReal (Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2)
      ≤ ∫⁻ y : ℝ × ℝ, ∫⁻ t in s, H (y, t) :=
    MeasureTheory.lintegral_mono hpt2
  have hswap : ∫⁻ y : ℝ × ℝ, ∫⁻ t in s, H (y, t)
      = ∫⁻ t in s, ∫⁻ y : ℝ × ℝ, H (y, t) := by
    have h1 : ∫⁻ y : ℝ × ℝ, ∫⁻ t in s, H (y, t)
        = ∫⁻ z : (ℝ × ℝ) × ℝ, H z ∂(volume.prod (volume.restrict s)) :=
      (MeasureTheory.lintegral_prod (μ := volume) (ν := volume.restrict s) H hHmeas).symm
    have h2 : ∫⁻ t in s, ∫⁻ y : ℝ × ℝ, H (y, t)
        = ∫⁻ z : (ℝ × ℝ) × ℝ, H z ∂(volume.prod (volume.restrict s)) :=
      (MeasureTheory.lintegral_prod_symm (μ := volume) (ν := volume.restrict s) H hHmeas).symm
    rw [h1, h2]
  have hinner : ∀ t : ℝ, ∫⁻ y : ℝ × ℝ, H (y, t)
      = ENNReal.ofReal (2 * ‖p‖ ^ 2 * Real.exp K) * ∫⁻ y : ℝ × ℝ, F y := by
    intro t
    have h1 : ∀ y : ℝ × ℝ, H (y, t)
        = ENNReal.ofReal (2 * ‖p‖ ^ 2 * Real.exp K) * F (y + t • p) := by
      intro y
      rw [hH, hF]
      exact ENNReal.ofReal_mul (by positivity)
    have hmt : Measurable (fun y : ℝ × ℝ => F (y + t • p)) := by
      rw [hF]
      have hc : Continuous (fun y : ℝ × ℝ => y + t • p) := continuous_id.add continuous_const
      exact ENNReal.measurable_ofReal.comp
        ((hQm.comp hc.measurable).mul (((hcfd.comp hc).norm).pow 2).measurable)
    rw [MeasureTheory.lintegral_congr h1, MeasureTheory.lintegral_const_mul _ hmt,
      MeasureTheory.lintegral_add_right_eq_self F (t • p)]
  have hvol : (volume.restrict s) Set.univ = ENNReal.ofReal 2 := by
    rw [hs, Measure.restrict_apply_univ, Real.volume_Ioc]
    norm_num
  have hconst : ∫⁻ t in s, (ENNReal.ofReal (2 * ‖p‖ ^ 2 * Real.exp K) * ∫⁻ y : ℝ × ℝ, F y)
      = ENNReal.ofReal (2 * ‖p‖ ^ 2 * Real.exp K) * (∫⁻ y : ℝ × ℝ, F y)
        * ENNReal.ofReal 2 := by
    rw [MeasureTheory.lintegral_const, hvol]
  have hcF : ∫⁻ y : ℝ × ℝ, F y = ENNReal.ofReal J := by
    rw [hJ, hF]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hI2
      (Eventually.of_forall (fun y => mul_nonneg (hQ0 y) (sq_nonneg _)))).symm
  have hArit : ENNReal.ofReal (2 * ‖p‖ ^ 2 * Real.exp K) * ENNReal.ofReal J * ENNReal.ofReal 2
      = ENNReal.ofReal (4 * ‖p‖ ^ 2 * Real.exp K * J) := by
    calc ENNReal.ofReal (2 * ‖p‖ ^ 2 * Real.exp K) * ENNReal.ofReal J * ENNReal.ofReal 2
        = ENNReal.ofReal (2 * ‖p‖ ^ 2 * Real.exp K)
          * (ENNReal.ofReal J * ENNReal.ofReal 2) := by rw [mul_assoc]
      _ = ENNReal.ofReal (2 * ‖p‖ ^ 2 * Real.exp K) * ENNReal.ofReal (J * 2) := by
            rw [ENNReal.ofReal_mul hJ0]
      _ = ENNReal.ofReal (2 * ‖p‖ ^ 2 * Real.exp K * (J * 2)) := by
            rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 * ‖p‖ ^ 2 * Real.exp K by positivity)]
      _ = ENNReal.ofReal (4 * ‖p‖ ^ 2 * Real.exp K * J) := by
            congr 1; ring
  have hlin : ∫⁻ y : ℝ × ℝ, ENNReal.ofReal (Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2)
      ≤ ENNReal.ofReal (4 * ‖p‖ ^ 2 * Real.exp K * J) := by
    calc ∫⁻ y : ℝ × ℝ, ENNReal.ofReal (Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2)
        ≤ ∫⁻ y : ℝ × ℝ, ∫⁻ t in s, H (y, t) := hlin1
      _ = ∫⁻ t in s, ∫⁻ y : ℝ × ℝ, H (y, t) := hswap
      _ = ∫⁻ t in s, (ENNReal.ofReal (2 * ‖p‖ ^ 2 * Real.exp K) * ∫⁻ y : ℝ × ℝ, F y) :=
            MeasureTheory.lintegral_congr hinner
      _ = ENNReal.ofReal (2 * ‖p‖ ^ 2 * Real.exp K) * (∫⁻ y : ℝ × ℝ, F y)
            * ENNReal.ofReal 2 := hconst
      _ = ENNReal.ofReal (2 * ‖p‖ ^ 2 * Real.exp K) * ENNReal.ofReal J
            * ENNReal.ofReal 2 := by rw [hcF]
      _ = ENNReal.ofReal (4 * ‖p‖ ^ 2 * Real.exp K * J) := hArit
  -- ### back to the real statement
  have hnonneg : 0 ≤ᵐ[volume]
      (fun y : ℝ × ℝ => Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2) :=
    Eventually.of_forall (fun y => mul_nonneg (hQ0 y) (sq_nonneg _))
  have hmeasJ : AEStronglyMeasurable
      (fun y : ℝ × ℝ => Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2) volume := by
    apply Measurable.aestronglyMeasurable
    have hc : Continuous (fun y : ℝ × ℝ => G₂ (y + p) - G₂ (y - p)) :=
      (hG2c.comp (continuous_id.add continuous_const)).sub
        (hG2c.comp (continuous_id.sub continuous_const))
    exact hQm.mul (hc.pow 2).measurable
  have hne : ∫⁻ y : ℝ × ℝ, ENNReal.ofReal (Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2) ≠ ⊤ := by
    intro htop
    rw [htop] at hlin
    exact absurd hlin
      (not_le.mpr (ENNReal.ofReal_lt_top (r := 4 * ‖p‖ ^ 2 * Real.exp K * J)))
  have hInt : MeasureTheory.Integrable
      (fun y : ℝ × ℝ => Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2) :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hmeasJ hnonneg).mp hne
  have hval : ENNReal.ofReal (∫ y : ℝ × ℝ, Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2)
      = ∫⁻ y : ℝ × ℝ, ENNReal.ofReal (Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2) :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hnonneg
  have hle : (∫ y : ℝ × ℝ, Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2)
      ≤ 4 * ‖p‖ ^ 2 * Real.exp K * J := by
    have hq : (0 : ℝ) ≤ 4 * ‖p‖ ^ 2 * Real.exp K * J := mul_nonneg (by positivity) hJ0
    exact (ENNReal.ofReal_le_ofReal_iff hq).mp (by rw [hval]; exact hlin)
  exact ⟨hInt, hle⟩

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
