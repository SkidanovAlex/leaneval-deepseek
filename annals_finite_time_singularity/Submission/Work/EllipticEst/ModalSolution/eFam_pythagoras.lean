/-
# `eFam_pythagoras` — Pythagoras for the truncated angular eigenbasis

For a square-integrable slice `θ ↦ F z θ` in the self-adjoint weight `cos θ dθ`, the truncated
`cos θ`-orthogonal projection onto the Dirichlet eigenbasis `eFam 0, …, eFam N` of
`Work.Elliptic.Lzero` satisfies the Pythagoras identity

  `∫_{Iθ} (F - Σ_{m ≤ N} c_m e_m)² cos θ = ∫_{Iθ} F² cos θ - Σ_{m ≤ N} c_m² ∫_{Iθ} e_m² cos θ`,

where `c_m = cmode m F z` is the `e_m`-coefficient of the slice `F z ·` (`Series/Defs.lean`).
This is the finite-`N` counterpart of the Parseval identity `eFam_parseval` and the `L²`-convergence
`eFam_expansion_L2`.

**Route.**  Everything is done with the weighted pairing `⟨f, g⟩ = ∫_{Iθ} f g cos θ`:

* `cmode_mul_norm`: `c_m · ∫ e_m² cos = ∫ F e_m cos` (the definition of `cmode`, after
  converting the interval integral of `cmode` into the set integral over `Iθ`);
* `sum_sq_orth_collapse`: `∫ (Σ_m c_m e_m)² cos = Σ_m c_m² ∫ e_m² cos`, which uses only
  linearity of the integral plus the orthogonality `eFam_orthogonal_Iθ`;
* `integral_mul_finset_sum`: linearity of the integral against the finite sum, i.e.
  `∫ F (Σ_m c_m e_m) cos = Σ_m c_m ∫ F e_m cos`;
* the pointwise expansion `(F - S)² cos = F² cos - 2 F S cos + S² cos` together with the
  linearity of the integral (`integral_add`/`integral_sub`/`integral_const_mul`).

The only integrability input needed for the products involving `F` is that `F z · · cos` is
dominated on `Iθ` by `F² cos + Σ² cos` (AM–GM, using `cos ≥ 0` on `Iθ`) — this is
`Integrable.mono'` together with `Integrable.const_mul`.

All the integrability bookkeeping about the single-mode cross terms
`θ ↦ F z θ · eFam m θ · cos θ` is delegated to `EFP.integrableOn_mul_eFam_cos`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts
import Submission.Work.Spaces.Defs
import Submission.Work.EllipticEst.ModalSolution.eFamBasisFts_FALSE
import Submission.Work.EllipticEst.ModalSolution.EFP.sum_sq_orth_collapse
import Submission.Work.EllipticEst.ModalSolution.EFP.integral_mul_finset_sum
import Submission.Work.EllipticEst.ModalSolution.EFP.integrableOn_mul_eFam_cos

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set
open scoped Real BigOperators

namespace Work.EllipticEst.ModalSolution

/-- The truncated mode sum `∑_{m ≤ N} cmode m F z · eFam m θ`, as a function of `θ`. -/
def sumEFam (F : ℝ → ℝ → ℝ) (z : ℝ) (N : ℕ) : ℝ → ℝ :=
  fun θ => ∑ m ∈ Finset.range (N + 1),
    Work.FTS.PhiStar.Series.cmode m F z * Work.FTS.PhiStar.Gegenbauer.eFam m θ

/-- The set integral over `Iθ = [0, π/2]` is the interval integral over `0..π/2`. -/
theorem setIntegral_Iθ_eq_intervalIntegral (g : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, g θ) = ∫ θ in (0 : ℝ)..(Real.pi / 2), g θ := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)]

/-- `eFam m` is continuous. -/
theorem continuous_eFam (m : ℕ) :
    Continuous (fun θ : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m θ) := by
  rw [show Work.FTS.PhiStar.Gegenbauer.eFam m
      = fun θ : ℝ => Real.cos θ * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)
      from rfl]
  exact Real.continuous_cos.mul
    (((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous).comp Real.continuous_sin)

attribute [local fun_prop] continuous_eFam

/-- `cmode m F z` times the norm of `eFam m` is the `e_m`-moment of the slice `F z ·`. -/
theorem cmode_mul_norm (F : ℝ → ℝ → ℝ) (z : ℝ) (m : ℕ) :
    Work.FTS.PhiStar.Series.cmode m F z
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)
      = ∫ θ in Work.Spaces.Iθ, F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ := by
  have hnum : (∫ θ in (0 : ℝ)..(Real.pi / 2),
        F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
      = ∫ θ in Work.Spaces.Iθ, F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ :=
    (setIntegral_Iθ_eq_intervalIntegral _).symm
  have hden : (∫ θ in (0 : ℝ)..(Real.pi / 2),
        Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)
      = ∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ :=
    (setIntegral_Iθ_eq_intervalIntegral _).symm
  have hne : (∫ θ in Work.Spaces.Iθ,
        Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ) ≠ 0 := by
    rw [Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts m]
    positivity
  simp only [Work.FTS.PhiStar.Series.cmode, hnum, hden]
  exact div_mul_cancel₀ _ hne

/-- **Pythagoras for the truncated angular eigenbasis.** -/
theorem eFam_pythagoras (F : ℝ → ℝ → ℝ) (z : ℝ) (N : ℕ)
    (hmeas : MeasureTheory.AEStronglyMeasurable (fun θ => F z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hz : MeasureTheory.IntegrableOn (fun θ => F z θ ^ 2 * Real.cos θ) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ,
        (F z θ - ∑ m ∈ Finset.range (N + 1),
          Work.FTS.PhiStar.Series.cmode m F z *
            Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2 * Real.cos θ)
      = (∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ)
        - ∑ m ∈ Finset.range (N + 1), (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ,
              Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ) := by
  change (∫ θ in Work.Spaces.Iθ, (F z θ - sumEFam F z N θ) ^ 2 * Real.cos θ)
      = (∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ)
        - ∑ m ∈ Finset.range (N + 1), (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ,
              Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)
  have hzI : MeasureTheory.Integrable (fun θ => F z θ ^ 2 * Real.cos θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hz
  have hint : ∀ m : ℕ, MeasureTheory.IntegrableOn
      (fun θ => F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
      Work.Spaces.Iθ := fun m =>
        Work.EllipticEst.ModalSolution.EFP.integrableOn_mul_eFam_cos F z m hmeas hz
  have hcontS : Continuous (sumEFam F z N) := by
    show Continuous (fun θ : ℝ => ∑ m ∈ Finset.range (N + 1),
      Work.FTS.PhiStar.Series.cmode m F z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
    fun_prop
  have hmeasS : MeasureTheory.AEStronglyMeasurable (sumEFam F z N)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hcontS.aestronglyMeasurable
  have hSSI : MeasureTheory.Integrable (fun θ => sumEFam F z N θ ^ 2 * Real.cos θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    ((hcontS.pow 2).mul Real.continuous_cos).continuousOn.integrableOn_compact isCompact_Icc
  have hFSI : MeasureTheory.Integrable (fun θ => F z θ * sumEFam F z N θ * Real.cos θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine MeasureTheory.Integrable.mono'
      (g := fun θ : ℝ => (1 / 2) * (F z θ ^ 2 * Real.cos θ)
        + (1 / 2) * (sumEFam F z N θ ^ 2 * Real.cos θ)) ?_ ?_ ?_
    · exact (hzI.const_mul (1 / 2)).add (hSSI.const_mul (1 / 2))
    · exact (hmeas.mul hmeasS).mul Real.continuous_cos.aestronglyMeasurable
    · filter_upwards [MeasureTheory.ae_restrict_mem (s := Work.Spaces.Iθ) measurableSet_Icc]
        with θ hθ
      have hc : 0 ≤ Real.cos θ :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩
      have hsq : Real.sqrt (Real.cos θ) ^ 2 = Real.cos θ := Real.sq_sqrt hc
      rw [Real.norm_eq_abs]
      have hAB : (|F z θ| * Real.sqrt (Real.cos θ)) * (|sumEFam F z N θ| * Real.sqrt (Real.cos θ))
          = |F z θ * sumEFam F z N θ * Real.cos θ| := by
        rw [mul_mul_mul_comm, ← sq, hsq, abs_mul, abs_mul, abs_of_nonneg hc]
      rw [← hAB]
      nlinarith [sq_nonneg (|F z θ| * Real.sqrt (Real.cos θ)
            - |sumEFam F z N θ| * Real.sqrt (Real.cos θ)),
        sq_abs (F z θ), sq_abs (sumEFam F z N θ), hsq]
  -- (P) the cross integral
  have hP : (∫ θ in Work.Spaces.Iθ, F z θ * sumEFam F z N θ * Real.cos θ)
      = ∑ m ∈ Finset.range (N + 1), (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 *
          (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ) := by
    have h1 : (∫ θ in Work.Spaces.Iθ, F z θ * (∑ m ∈ Finset.range (N + 1),
          Work.FTS.PhiStar.Series.cmode m F z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
          * Real.cos θ)
        = ∑ m ∈ Finset.range (N + 1), Work.FTS.PhiStar.Series.cmode m F z *
            (∫ θ in Work.Spaces.Iθ, F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ
              * Real.cos θ) :=
      Work.EllipticEst.ModalSolution.EFP.integral_mul_finset_sum (Finset.range (N + 1))
        (fun m => Work.FTS.PhiStar.Series.cmode m F z)
        (fun m => Work.FTS.PhiStar.Gegenbauer.eFam m) (fun θ => F z θ)
        (fun m _ => hint m)
    have h2 : (∑ m ∈ Finset.range (N + 1), Work.FTS.PhiStar.Series.cmode m F z *
            (∫ θ in Work.Spaces.Iθ, F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ
              * Real.cos θ))
        = ∑ m ∈ Finset.range (N + 1), (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 *
            (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2
              * Real.cos θ) := by
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [← cmode_mul_norm F z m]
      ring
    exact h1.trans h2
  -- (Q) the squared-sum integral
  have hQ : (∫ θ in Work.Spaces.Iθ, sumEFam F z N θ ^ 2 * Real.cos θ)
      = ∑ m ∈ Finset.range (N + 1), (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 *
          (∫ θ in Work.Spaces.Iθ, Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ) :=
    Work.EllipticEst.ModalSolution.EFP.sum_sq_orth_collapse (Finset.range (N + 1))
      (fun m => Work.FTS.PhiStar.Series.cmode m F z)
      (fun m => Work.FTS.PhiStar.Gegenbauer.eFam m)
      (fun m => continuous_eFam m)
      (fun m _ n _ hmn => eFam_orthogonal_Iθ m n hmn)
  -- the expansion of the square
  have hexp : (∫ θ in Work.Spaces.Iθ, (F z θ - sumEFam F z N θ) ^ 2 * Real.cos θ)
      = (∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ)
        - 2 * (∫ θ in Work.Spaces.Iθ, F z θ * sumEFam F z N θ * Real.cos θ)
        + (∫ θ in Work.Spaces.Iθ, sumEFam F z N θ ^ 2 * Real.cos θ) := by
    have hA : MeasureTheory.Integrable
        (fun θ : ℝ => F z θ ^ 2 * Real.cos θ - 2 * (F z θ * sumEFam F z N θ * Real.cos θ))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hzI.sub (hFSI.const_mul 2)
    have hB : MeasureTheory.Integrable
        (fun θ : ℝ => 2 * (F z θ * sumEFam F z N θ * Real.cos θ))
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hFSI.const_mul 2
    have hC : MeasureTheory.Integrable (fun θ : ℝ => sumEFam F z N θ ^ 2 * Real.cos θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hSSI
    have e1 : (∫ θ in Work.Spaces.Iθ, (F z θ - sumEFam F z N θ) ^ 2 * Real.cos θ)
        = (∫ θ in Work.Spaces.Iθ, (fun θ : ℝ => F z θ ^ 2 * Real.cos θ
              - 2 * (F z θ * sumEFam F z N θ * Real.cos θ)) θ
            + (fun θ : ℝ => sumEFam F z N θ ^ 2 * Real.cos θ) θ) :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => by ring))
    have e2 : (∫ θ in Work.Spaces.Iθ, (fun θ : ℝ => F z θ ^ 2 * Real.cos θ
              - 2 * (F z θ * sumEFam F z N θ * Real.cos θ)) θ
            + (fun θ : ℝ => sumEFam F z N θ ^ 2 * Real.cos θ) θ)
        = (∫ θ in Work.Spaces.Iθ, (fun θ : ℝ => F z θ ^ 2 * Real.cos θ
              - 2 * (F z θ * sumEFam F z N θ * Real.cos θ)) θ)
          + (∫ θ in Work.Spaces.Iθ, (fun θ : ℝ => sumEFam F z N θ ^ 2 * Real.cos θ) θ) :=
      MeasureTheory.integral_add hA hC
    have e3 : (∫ θ in Work.Spaces.Iθ, (fun θ : ℝ => F z θ ^ 2 * Real.cos θ
              - 2 * (F z θ * sumEFam F z N θ * Real.cos θ)) θ)
        = (∫ θ in Work.Spaces.Iθ, (fun θ : ℝ => F z θ ^ 2 * Real.cos θ) θ)
          - (∫ θ in Work.Spaces.Iθ,
              (fun θ : ℝ => 2 * (F z θ * sumEFam F z N θ * Real.cos θ)) θ) :=
      MeasureTheory.integral_sub (f := fun θ : ℝ => F z θ ^ 2 * Real.cos θ)
        (g := fun θ : ℝ => 2 * (F z θ * sumEFam F z N θ * Real.cos θ)) hzI hB
    have e4 : (∫ θ in Work.Spaces.Iθ,
          (fun θ : ℝ => 2 * (F z θ * sumEFam F z N θ * Real.cos θ)) θ)
        = 2 * (∫ θ in Work.Spaces.Iθ, F z θ * sumEFam F z N θ * Real.cos θ) :=
      MeasureTheory.integral_const_mul 2 (fun θ : ℝ => F z θ * sumEFam F z N θ * Real.cos θ)
    have e5 : (∫ θ in Work.Spaces.Iθ, (fun θ : ℝ => sumEFam F z N θ ^ 2 * Real.cos θ) θ)
        = (∫ θ in Work.Spaces.Iθ, sumEFam F z N θ ^ 2 * Real.cos θ) := rfl
    have e6 : (∫ θ in Work.Spaces.Iθ, (fun θ : ℝ => F z θ ^ 2 * Real.cos θ) θ)
        = (∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ) := rfl
    rw [e1, e2, e3, e4, e5, e6]
  rw [hexp, hP, hQ]
  ring

end Work.EllipticEst.ModalSolution
