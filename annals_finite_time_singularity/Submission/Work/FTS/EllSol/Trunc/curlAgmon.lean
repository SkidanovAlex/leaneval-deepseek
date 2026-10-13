/-
Copyright: work module for the Elgindi finite-time singularity project (area `FTS.EllSol`).

# The complex-valued angular Agmon inequality (open class)

`Work.FTS.EllSol.Trunc.curlAgmon` is the complex form of the weighted angular interpolation
inequality `Work.EllipticEst.Core.i0Aux.thetaInterpCore`:

  `∫_{Iθ} ‖F'‖² σ ≤ C (∫_{Iθ} ‖F‖² σ + √(∫_{Iθ} ‖F‖² σ · ∫_{Iθ} ‖F''‖² σ))`,  `σ = thEta`,

for `F : ℝ → ℂ` of class `C²` on the open interval `(0, π/2)`, with `F 0 = F (π/2) = 0` and the
three weighted `L²`-slots finite (the *values* at the endpoints vanish; no trace condition is
imposed on `F'`, `F''`).

The reduction to the real statement is the projection argument: apply `thetaInterpCore` to the
two real functions `θ ↦ (F θ).re` and `θ ↦ (F θ).im`, use

  `‖z‖² = z.re² + z.im²`   and   `deriv (re ∘ F) = re ∘ deriv F`, `deriv (im ∘ F) = im ∘ deriv F`

(the projections `Complex.reCLM`, `Complex.imCLM` are `ℝ`-linear and continuous, so they commute
with `deriv`, also at the second order on the open interval), and merge the two square roots with
Cauchy–Schwarz `√(ab) + √(cd) ≤ √((a+c)(b+d))`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllSol.Trunc.CxAgmonAux
import Submission.Work.EllipticEst.Core.i0Aux.thetaInterpCore
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.Trunc

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

set_option autoImplicit false

local notation "σ" => Work.FTS.EllipticEst.thEta
local notation "Iθ" => Work.Spaces.Iθ
local notation "J" => Set.Ioo (0 : ℝ) (Real.pi / 2)

/-- A function continuous on the *open* interval is a.e.-strongly-measurable for the restriction
of Lebesgue measure to the closed interval `Iθ = [0, π/2]` (the two sets differ by the null set
`{0, π/2}`). -/
private theorem aesm_restrict_Iθ_of_continuousOn {f : ℝ → ℝ} (h : ContinuousOn f J) :
    AEStronglyMeasurable f ((volume : Measure ℝ).restrict Iθ) := by
  have h1 : AEStronglyMeasurable f ((volume : Measure ℝ).restrict J) :=
    h.aestronglyMeasurable measurableSet_Ioo
  rw [MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := (volume : Measure ℝ)))] at h1
  exact h1

/-- Integrability on `Iθ` from a pointwise bound valid on the open interval. -/
private theorem integrableOn_Iθ_of_abs_le {f g : ℝ → ℝ} (hg : IntegrableOn g Iθ)
    (hf : AEStronglyMeasurable f ((volume : Measure ℝ).restrict Iθ))
    (hle : ∀ θ ∈ J, |f θ| ≤ |g θ|) : IntegrableOn f Iθ := by
  refine (hg.abs).mono' hf ?_
  filter_upwards [Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo hle] with θ hθ
  simpa [Real.norm_eq_abs] using hθ

theorem curlAgmon : ∃ C : ℝ, 0 < C ∧ ∀ F : ℝ → ℂ, ContDiffOn ℝ 2 F (Set.Ioo 0 (Real.pi / 2)) → F 0 = 0 → F (Real.pi / 2) = 0 → MeasureTheory.IntegrableOn (fun θ : ℝ => ‖F θ‖ ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ → MeasureTheory.IntegrableOn (fun θ : ℝ => ‖deriv F θ‖ ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ → MeasureTheory.IntegrableOn (fun θ : ℝ => ‖deriv (deriv F) θ‖ ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ → (∫ θ in Work.Spaces.Iθ, ‖deriv F θ‖ ^ 2 * Work.FTS.EllipticEst.thEta θ) ≤ C * ((∫ θ in Work.Spaces.Iθ, ‖F θ‖ ^ 2 * Work.FTS.EllipticEst.thEta θ) + Real.sqrt ((∫ θ in Work.Spaces.Iθ, ‖F θ‖ ^ 2 * Work.FTS.EllipticEst.thEta θ) * (∫ θ in Work.Spaces.Iθ, ‖deriv (deriv F) θ‖ ^ 2 * Work.FTS.EllipticEst.thEta θ))) := by
  obtain ⟨C, hCpos, hC⟩ := Work.EllipticEst.Core.i0Aux.thetaInterpCore
  refine ⟨C, hCpos, ?_⟩
  intro F hF hF0 hFπ hP hQ hE
  -- the two real projections
  set U : ℝ → ℝ := fun θ => (F θ).re with hU
  set W : ℝ → ℝ := fun θ => (F θ).im with hW
  -- ## differentiability on the open interval
  have hdiff : ∀ θ ∈ J, DifferentiableAt ℝ F θ := fun θ hθ =>
    (hF.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hθ)
  -- ## the derivative identities (projections commute with `deriv`)
  have hdU : ∀ θ ∈ J, deriv U θ = (deriv F θ).re := by
    intro θ hθ
    rw [hU]
    exact deriv_re_eq (hdiff θ hθ)
  have hdW : ∀ θ ∈ J, deriv W θ = (deriv F θ).im := by
    intro θ hθ
    rw [hW]
    exact deriv_im_eq (hdiff θ hθ)
  have hddU : ∀ θ ∈ J, deriv (deriv U) θ = (deriv (deriv F) θ).re := by
    intro θ hθ
    rw [hU]
    exact deriv_deriv_re_eq isOpen_Ioo hθ hF
  have hddW : ∀ θ ∈ J, deriv (deriv W) θ = (deriv (deriv F) θ).im := by
    intro θ hθ
    rw [hW]
    exact deriv_deriv_im_eq isOpen_Ioo hθ hF
  -- ## the pointwise splitting of the squared norm
  have hnorm : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    intro z
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hpt0 : ∀ θ ∈ J, ‖F θ‖ ^ 2 * σ θ = (U θ) ^ 2 * σ θ + (W θ) ^ 2 * σ θ := by
    intro θ _
    have h1 : U θ = (F θ).re := by rw [hU]
    have h2 : W θ = (F θ).im := by rw [hW]
    rw [hnorm (F θ), h1, h2]
    ring
  have hpt1 : ∀ θ ∈ J,
      ‖deriv F θ‖ ^ 2 * σ θ = (deriv U θ) ^ 2 * σ θ + (deriv W θ) ^ 2 * σ θ := by
    intro θ hθ
    have h1 : deriv U θ = (deriv F θ).re := hdU θ hθ
    have h2 : deriv W θ = (deriv F θ).im := hdW θ hθ
    rw [hnorm (deriv F θ), h1, h2]
    ring
  have hpt2 : ∀ θ ∈ J, ‖deriv (deriv F) θ‖ ^ 2 * σ θ
      = (deriv (deriv U) θ) ^ 2 * σ θ + (deriv (deriv W) θ) ^ 2 * σ θ := by
    intro θ hθ
    have h1 : deriv (deriv U) θ = (deriv (deriv F) θ).re := hddU θ hθ
    have h2 : deriv (deriv W) θ = (deriv (deriv F) θ).im := hddW θ hθ
    rw [hnorm (deriv (deriv F) θ), h1, h2]
    ring
  -- ## regularity of the projections and of their derivatives
  have hUcd : ContDiffOn ℝ 2 U J := by rw [hU]; exact contDiffOn_re hF
  have hWcd : ContDiffOn ℝ 2 W J := by rw [hW]; exact contDiffOn_im hF
  have hdUcd : ContDiffOn ℝ 1 (deriv U) J :=
    hUcd.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  have hdWcd : ContDiffOn ℝ 1 (deriv W) J :=
    hWcd.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  have hddUcd : ContDiffOn ℝ 0 (deriv (deriv U)) J :=
    hdUcd.deriv_of_isOpen isOpen_Ioo (m := 0) (by norm_num)
  have hddWcd : ContDiffOn ℝ 0 (deriv (deriv W)) J :=
    hdWcd.deriv_of_isOpen isOpen_Ioo (m := 0) (by norm_num)
  have haesm_U : AEStronglyMeasurable U ((volume : Measure ℝ).restrict Iθ) :=
    aesm_restrict_Iθ_of_continuousOn hUcd.continuousOn
  have haesm_W : AEStronglyMeasurable W ((volume : Measure ℝ).restrict Iθ) :=
    aesm_restrict_Iθ_of_continuousOn hWcd.continuousOn
  have haesm_dU : AEStronglyMeasurable (deriv U) ((volume : Measure ℝ).restrict Iθ) :=
    aesm_restrict_Iθ_of_continuousOn hdUcd.continuousOn
  have haesm_dW : AEStronglyMeasurable (deriv W) ((volume : Measure ℝ).restrict Iθ) :=
    aesm_restrict_Iθ_of_continuousOn hdWcd.continuousOn
  have haesm_ddU : AEStronglyMeasurable (deriv (deriv U)) ((volume : Measure ℝ).restrict Iθ) :=
    aesm_restrict_Iθ_of_continuousOn hddUcd.continuousOn
  have haesm_ddW : AEStronglyMeasurable (deriv (deriv W)) ((volume : Measure ℝ).restrict Iθ) :=
    aesm_restrict_Iθ_of_continuousOn hddWcd.continuousOn
  have hσmeas : Measurable σ := by
    unfold Work.FTS.EllipticEst.thEta
    exact (Real.measurable_sin.comp (measurable_const.mul measurable_id)).pow measurable_const
  have hσaesm : AEStronglyMeasurable (fun θ : ℝ => σ θ) ((volume : Measure ℝ).restrict Iθ) :=
    hσmeas.aemeasurable.restrict.aestronglyMeasurable
  -- ## the two projections, each with its own three weighted slots
  have hU0 : U 0 = 0 := by rw [hU]; simp [hF0]
  have hUπ : U (Real.pi / 2) = 0 := by rw [hU]; simp [hFπ]
  have hW0 : W 0 = 0 := by rw [hW]; simp [hF0]
  have hWπ : W (Real.pi / 2) = 0 := by rw [hW]; simp [hFπ]
  have hPU : IntegrableOn (fun θ => (U θ) ^ 2 * σ θ) Iθ :=
    integrableOn_Iθ_of_abs_le hP ((haesm_U.pow 2).mul hσaesm) (fun θ _ => by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (U θ)),
        abs_of_nonneg (sq_nonneg ‖F θ‖)]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg (σ θ))
      have h1 : U θ = (F θ).re := by rw [hU]
      rw [hnorm (F θ), h1]
      nlinarith [sq_nonneg (F θ).im])
  have hPW : IntegrableOn (fun θ => (W θ) ^ 2 * σ θ) Iθ :=
    integrableOn_Iθ_of_abs_le hP ((haesm_W.pow 2).mul hσaesm) (fun θ _ => by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (W θ)),
        abs_of_nonneg (sq_nonneg ‖F θ‖)]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg (σ θ))
      have h1 : W θ = (F θ).im := by rw [hW]
      rw [hnorm (F θ), h1]
      nlinarith [sq_nonneg (F θ).re])
  have hQU : IntegrableOn (fun θ => (deriv U θ) ^ 2 * σ θ) Iθ :=
    integrableOn_Iθ_of_abs_le hQ ((haesm_dU.pow 2).mul hσaesm) (fun θ hθ => by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (deriv U θ)),
        abs_of_nonneg (sq_nonneg ‖deriv F θ‖)]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg (σ θ))
      have h1 : deriv U θ = (deriv F θ).re := hdU θ hθ
      rw [hnorm (deriv F θ), h1]
      nlinarith [sq_nonneg (deriv F θ).im])
  have hQW : IntegrableOn (fun θ => (deriv W θ) ^ 2 * σ θ) Iθ :=
    integrableOn_Iθ_of_abs_le hQ ((haesm_dW.pow 2).mul hσaesm) (fun θ hθ => by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (deriv W θ)),
        abs_of_nonneg (sq_nonneg ‖deriv F θ‖)]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg (σ θ))
      have h1 : deriv W θ = (deriv F θ).im := hdW θ hθ
      rw [hnorm (deriv F θ), h1]
      nlinarith [sq_nonneg (deriv F θ).re])
  have hEU : IntegrableOn (fun θ => (deriv (deriv U) θ) ^ 2 * σ θ) Iθ :=
    integrableOn_Iθ_of_abs_le hE ((haesm_ddU.pow 2).mul hσaesm) (fun θ hθ => by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (deriv (deriv U) θ)),
        abs_of_nonneg (sq_nonneg ‖deriv (deriv F) θ‖)]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg (σ θ))
      have h1 : deriv (deriv U) θ = (deriv (deriv F) θ).re := hddU θ hθ
      rw [hnorm (deriv (deriv F) θ), h1]
      nlinarith [sq_nonneg (deriv (deriv F) θ).im])
  have hEW : IntegrableOn (fun θ => (deriv (deriv W) θ) ^ 2 * σ θ) Iθ :=
    integrableOn_Iθ_of_abs_le hE ((haesm_ddW.pow 2).mul hσaesm) (fun θ hθ => by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (deriv (deriv W) θ)),
        abs_of_nonneg (sq_nonneg ‖deriv (deriv F) θ‖)]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg (σ θ))
      have h1 : deriv (deriv W) θ = (deriv (deriv F) θ).im := hddW θ hθ
      rw [hnorm (deriv (deriv F) θ), h1]
      nlinarith [sq_nonneg (deriv (deriv F) θ).re])
  -- ## the real inequality, for each projection
  have hCU := hC U hUcd hU0 hUπ hPU hQU hEU
  have hCW := hC W hWcd hW0 hWπ hPW hQW hEW
  -- ## the three slot integrals split into their two projections
  have hsplit0 : (∫ θ in Iθ, (U θ) ^ 2 * σ θ) + (∫ θ in Iθ, (W θ) ^ 2 * σ θ)
      = ∫ θ in Iθ, ‖F θ‖ ^ 2 * σ θ := by
    rw [← MeasureTheory.integral_add hPU hPW]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo hpt0] with θ hθ
    exact hθ.symm
  have hsplit1 : (∫ θ in Iθ, (deriv U θ) ^ 2 * σ θ) + (∫ θ in Iθ, (deriv W θ) ^ 2 * σ θ)
      = ∫ θ in Iθ, ‖deriv F θ‖ ^ 2 * σ θ := by
    rw [← MeasureTheory.integral_add hQU hQW]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo hpt1] with θ hθ
    exact hθ.symm
  have hsplit2 : (∫ θ in Iθ, (deriv (deriv U) θ) ^ 2 * σ θ)
        + (∫ θ in Iθ, (deriv (deriv W) θ) ^ 2 * σ θ)
      = ∫ θ in Iθ, ‖deriv (deriv F) θ‖ ^ 2 * σ θ := by
    rw [← MeasureTheory.integral_add hEU hEW]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo hpt2] with θ hθ
    exact hθ.symm
  -- ## nonnegativity of the four quadratic slots
  have hσnn : ∀ θ ∈ Iθ, 0 ≤ σ θ := fun θ hθ => Work.FTS.EllipticEst.thEta_nonneg hθ
  have hPUnn : 0 ≤ ∫ θ in Iθ, (U θ) ^ 2 * σ θ :=
    setIntegral_nonneg measurableSet_Icc (fun θ hθ => mul_nonneg (sq_nonneg _) (hσnn θ hθ))
  have hPWnn : 0 ≤ ∫ θ in Iθ, (W θ) ^ 2 * σ θ :=
    setIntegral_nonneg measurableSet_Icc (fun θ hθ => mul_nonneg (sq_nonneg _) (hσnn θ hθ))
  have hEUnn : 0 ≤ ∫ θ in Iθ, (deriv (deriv U) θ) ^ 2 * σ θ :=
    setIntegral_nonneg measurableSet_Icc (fun θ hθ => mul_nonneg (sq_nonneg _) (hσnn θ hθ))
  have hEWnn : 0 ≤ ∫ θ in Iθ, (deriv (deriv W) θ) ^ 2 * σ θ :=
    setIntegral_nonneg measurableSet_Icc (fun θ hθ => mul_nonneg (sq_nonneg _) (hσnn θ hθ))
  -- ## assembly
  have hcs : Real.sqrt ((∫ θ in Iθ, (U θ) ^ 2 * σ θ)
          * (∫ θ in Iθ, (deriv (deriv U) θ) ^ 2 * σ θ))
        + Real.sqrt ((∫ θ in Iθ, (W θ) ^ 2 * σ θ)
          * (∫ θ in Iθ, (deriv (deriv W) θ) ^ 2 * σ θ))
      ≤ Real.sqrt (((∫ θ in Iθ, (U θ) ^ 2 * σ θ) + (∫ θ in Iθ, (W θ) ^ 2 * σ θ))
          * ((∫ θ in Iθ, (deriv (deriv U) θ) ^ 2 * σ θ)
            + (∫ θ in Iθ, (deriv (deriv W) θ) ^ 2 * σ θ))) :=
    sqrt_add_le hPUnn hEUnn hPWnn hEWnn
  calc (∫ θ in Iθ, ‖deriv F θ‖ ^ 2 * σ θ)
      = (∫ θ in Iθ, (deriv U θ) ^ 2 * σ θ) + (∫ θ in Iθ, (deriv W θ) ^ 2 * σ θ) :=
        hsplit1.symm
    _ ≤ C * ((∫ θ in Iθ, (U θ) ^ 2 * σ θ)
            + Real.sqrt ((∫ θ in Iθ, (U θ) ^ 2 * σ θ)
                * (∫ θ in Iθ, (deriv (deriv U) θ) ^ 2 * σ θ)))
          + C * ((∫ θ in Iθ, (W θ) ^ 2 * σ θ)
            + Real.sqrt ((∫ θ in Iθ, (W θ) ^ 2 * σ θ)
                * (∫ θ in Iθ, (deriv (deriv W) θ) ^ 2 * σ θ))) := add_le_add hCU hCW
    _ = C * (((∫ θ in Iθ, (U θ) ^ 2 * σ θ) + (∫ θ in Iθ, (W θ) ^ 2 * σ θ))
            + (Real.sqrt ((∫ θ in Iθ, (U θ) ^ 2 * σ θ)
                  * (∫ θ in Iθ, (deriv (deriv U) θ) ^ 2 * σ θ))
                + Real.sqrt ((∫ θ in Iθ, (W θ) ^ 2 * σ θ)
                  * (∫ θ in Iθ, (deriv (deriv W) θ) ^ 2 * σ θ)))) := by ring
    _ ≤ C * (((∫ θ in Iθ, (U θ) ^ 2 * σ θ) + (∫ θ in Iθ, (W θ) ^ 2 * σ θ))
            + Real.sqrt (((∫ θ in Iθ, (U θ) ^ 2 * σ θ) + (∫ θ in Iθ, (W θ) ^ 2 * σ θ))
                * ((∫ θ in Iθ, (deriv (deriv U) θ) ^ 2 * σ θ)
                  + (∫ θ in Iθ, (deriv (deriv W) θ) ^ 2 * σ θ)))) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hcs) (le_of_lt hCpos)
    _ = C * ((∫ θ in Iθ, ‖F θ‖ ^ 2 * σ θ)
            + Real.sqrt ((∫ θ in Iθ, ‖F θ‖ ^ 2 * σ θ)
                * (∫ θ in Iθ, ‖deriv (deriv F) θ‖ ^ 2 * σ θ))) := by
        rw [hsplit0, hsplit2]

end

end Work.FTS.EllSol.Trunc
