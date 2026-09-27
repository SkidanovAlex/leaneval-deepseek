import Mathlib
import Submission.Work.Mostow.BCGDefs
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.BaryContinuity
import Submission.Work.Mostow.NatMeasure
import Submission.Work.Mostow.visualBasic
import Submission.Work.Mostow.PfunBoundSph
import Submission.Work.Mostow.BCGBlocksContinuous
import Submission.Work.Mostow.HlinPairing

set_option linter.style.haveILetI false

/-!
# The `y`-derivative of the BCG barycentre functional `Phi`

`Phi n φ x y = ∫ ξ, pfun n x ξ * busemann (φ ξ) y ∂(sigma n)` and
`Gv n φ x y = ∫ ξ, pfun n x ξ • gradB n (φ ξ) y ∂(sigma n)` is its formal `y`-gradient.

This file proves that the formal gradient is the actual Fréchet derivative:
`∇_y (Phi n φ x ·) y = innerSL ℝ (Gv n φ x y)`.  The proof is differentiation under the
integral sign (`hasFDerivAt_integral_of_dominated_of_fderiv_le`) against the finite measure
`sigma n`, which is carried by the sphere `Sph n`, so that `φ` lands in the sphere almost
everywhere and the explicit dominance bounds `hg`/`hh` apply.

The technical side conditions are: continuity of the integrands on `Sph n` (from the joint
continuity of the BCG blocks), `sigma n`-a.e. strong measurability of the integrands, and
integrability of the two integrands and of the constant dominating function.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-! ## Continuity on the sphere of the various factors -/

theorem continuousOn_pfun (n : ℕ) (x : E n) :
    ContinuousOn (fun ξ : E n => Work.Mostow.pfun n x ξ) (Sph n) := by
  have hg : Continuous fun ξ : E n => tpart x - inner ℝ x ξ := by fun_prop
  have h := hg.continuousOn.rpow_const (p := -((n : ℝ) - 1))
    (fun ξ hξ => Or.inl (ne_of_gt (busemann_arg_pos ξ hξ x)))
  simpa only [pfun] using h

theorem continuousOn_busemann_fst (n : ℕ) (z : E n) :
    ContinuousOn (fun ξ : E n => busemann ξ z) (Sph n) := by
  have hg : Continuous fun ξ : E n => tpart z - inner ℝ z ξ := by fun_prop
  have h := hg.continuousOn.log (fun ξ hξ => ne_of_gt (busemann_arg_pos ξ hξ z))
  simpa only [busemann] using h

theorem continuousOn_gradB_fst (n : ℕ) (y : E n) :
    ContinuousOn (fun ξ : E n => Work.Mostow.gradB n ξ y) (Sph n) := by
  have hden : ContinuousOn (fun ξ : E n => tpart y - inner ℝ y ξ) (Sph n) := by fun_prop
  have hinv : ContinuousOn (fun ξ : E n => (tpart y - inner ℝ y ξ)⁻¹) (Sph n) :=
    hden.inv₀ (fun ξ hξ => ne_of_gt (busemann_arg_pos ξ hξ y))
  have hnum : ContinuousOn (fun ξ : E n => (tpart y)⁻¹ • y - ξ) (Sph n) := by fun_prop
  have hsm : ContinuousOn ((fun ξ : E n => (tpart y - inner ℝ y ξ)⁻¹) •
      (fun ξ : E n => (tpart y)⁻¹ • y - ξ)) (Sph n) := hinv.smul hnum
  have hfun : (fun ξ : E n => Work.Mostow.gradB n ξ y) =
      (fun ξ : E n => (tpart y - inner ℝ y ξ)⁻¹) •
        (fun ξ : E n => (tpart y)⁻¹ • y - ξ) := by
    funext ξ
    simp only [gradB]
    rfl
  rw [hfun]
  exact hsm

/-! ## Almost everywhere strong measurability -/

/-- `sigma n` is carried by the unit sphere. -/
theorem sigma_ae_mem_Sph (n : ℕ) : ∀ᵐ ξ ∂(sigma n), ξ ∈ Sph n := by
  rw [MeasureTheory.ae_iff]
  simpa only [Set.compl_def] using sigma_compl_sphere n

/-- A function continuous on the unit sphere is a.e. strongly measurable for `sigma n`. -/
theorem aes_of_continuousOn_sph (n : ℕ) {X : Type*} [TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X]
    {f : E n → X} (hf : ContinuousOn f (Sph n)) :
    AEStronglyMeasurable f (sigma n) := by
  rw [← Measure.restrict_eq_self_of_ae_mem (sigma_ae_mem_Sph n)]
  exact hf.aestronglyMeasurable_of_isCompact (isCompact_sphere (0 : E n) 1)
    Metric.isClosed_sphere.measurableSet

/-! ## The main theorem -/

theorem PhiDerivY (n : ℕ) (φ : Submission.Mostow.E n → Submission.Mostow.E n)
    (hbij : Set.BijOn φ (Submission.Mostow.Sph n) (Submission.Mostow.Sph n))
    (hcont : ContinuousOn φ (Submission.Mostow.Sph n))
    (hd1 : ∀ (ξ : Submission.Mostow.E n), ξ ∈ Submission.Mostow.Sph n →
      ∀ y : Submission.Mostow.E n,
        HasFDerivAt (fun y => Submission.Mostow.busemann ξ y)
          (innerSL ℝ (Work.Mostow.gradB n ξ y)) y)
    (hd2 : ∀ (ξ : Submission.Mostow.E n), ξ ∈ Submission.Mostow.Sph n →
      ∀ y : Submission.Mostow.E n, HasFDerivAt (fun y => Work.Mostow.gradB n ξ y)
        (Work.Mostow.hessB n ξ y) y)
    (hg : ∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, ∀ (ξ : Submission.Mostow.E n), ξ ∈ Submission.Mostow.Sph n →
      ∀ y : Submission.Mostow.E n, ‖y‖ ≤ R → ‖Work.Mostow.gradB n ξ y‖ ≤ C)
    (hh : ∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, ∀ (ξ : Submission.Mostow.E n), ξ ∈ Submission.Mostow.Sph n →
      ∀ y : Submission.Mostow.E n, ‖y‖ ≤ R → ‖Work.Mostow.hessB n ξ y‖ ≤ C) :
    ∀ x y : Submission.Mostow.E n,
      HasFDerivAt (fun y => Work.Mostow.Phi n φ x y)
        (innerSL ℝ (Work.Mostow.Gv n φ x y)) y := by
  intro x y
  haveI : IsFiniteMeasure (sigma n) := sigma_isFiniteMeasure n
  have hσ : (sigma n) (Sph n)ᶜ = 0 := sigma_compl_sphere n
  have haeSph : ∀ᵐ ξ ∂(sigma n), ξ ∈ Sph n := sigma_ae_mem_Sph n
  obtain ⟨Cf, hCf0, hCf⟩ := PfunBoundSph n ‖x‖
  obtain ⟨Cg, hCg⟩ := hg (‖y‖ + 1) (by positivity)
  -- the two integrands, as functions of `ξ`
  have hW_cont : ∀ z : E n,
      ContinuousOn (fun ξ : E n => pfun n x ξ * busemann (φ ξ) z) (Sph n) := by
    intro z
    exact (continuousOn_pfun n x).mul
      ((continuousOn_busemann_fst n z).comp hcont hbij.1)
  have hS_cont : ContinuousOn (fun ξ : E n => pfun n x ξ • gradB n (φ ξ) y) (Sph n) :=
    (continuousOn_pfun n x).smul ((continuousOn_gradB_fst n y).comp hcont hbij.1)
  have hD_cont :
      ContinuousOn (fun ξ : E n => pfun n x ξ • innerSL ℝ (gradB n (φ ξ) y)) (Sph n) :=
    (continuousOn_pfun n x).smul
      (((innerSL ℝ).continuous.comp_continuousOn
        ((continuousOn_gradB_fst n y).comp hcont hbij.1)))
  -- the scalar-integrand bound: `|pfun| * ‖gradB‖ ≤ Cf * |Cg|` on the sphere
  have hball : ∀ z ∈ Metric.closedBall y 1, ‖z‖ ≤ ‖y‖ + 1 := by
    intro z hz
    have hd : ‖z - y‖ ≤ 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      exact hz
    have h2 := norm_add_le (z - y) y
    rw [sub_add_cancel] at h2
    linarith
  have hbound : ∀ ξ ∈ Sph n, ∀ z ∈ Metric.closedBall y 1,
      ‖(pfun n x ξ : ℝ) • innerSL ℝ (gradB n (φ ξ) z)‖ ≤ Cf * |Cg| := by
    intro ξ hξ z hz
    have hp : |pfun n x ξ| ≤ Cf := hCf x le_rfl ξ hξ
    have hgrad : ‖Work.Mostow.gradB n (φ ξ) z‖ ≤ Cg :=
      hCg (φ ξ) (hbij.1 hξ) z (hball z hz)
    calc ‖(pfun n x ξ : ℝ) • innerSL ℝ (Work.Mostow.gradB n (φ ξ) z)‖
        = |pfun n x ξ| * ‖innerSL ℝ (Work.Mostow.gradB n (φ ξ) z)‖ := by
          rw [norm_smul, Real.norm_eq_abs]
      _ = |pfun n x ξ| * ‖Work.Mostow.gradB n (φ ξ) z‖ := by
          rw [innerSL_apply_norm]
      _ ≤ Cf * |Cg| :=
          mul_le_mul hp (le_trans hgrad (le_abs_self Cg)) (norm_nonneg _) hCf0
  have hmain :
      HasFDerivAt
        (fun z : E n => ∫ ξ, pfun n x ξ * busemann (φ ξ) z ∂(sigma n))
        (∫ ξ, pfun n x ξ • innerSL ℝ (gradB n (φ ξ) y) ∂(sigma n)) y := by
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le
      (μ := sigma n)
      (F := fun z ξ => pfun n x ξ * busemann (φ ξ) z)
      (F' := fun z ξ => pfun n x ξ • innerSL ℝ (gradB n (φ ξ) z))
      (bound := fun _ : E n => Cf * |Cg|)
      (x₀ := y) (s := Metric.closedBall y 1)
      (Metric.closedBall_mem_nhds y one_pos) ?_ ?_ ?_ ?_ ?_ ?_
    · -- a.e. strong measurability of the integrand, for `z` near `y`
      filter_upwards with z
      exact aes_of_continuousOn_sph n (hW_cont z)
    · -- integrability at the base point
      refine Integrable.of_bound
        (aes_of_continuousOn_sph n (hW_cont y)) (Cf * hdist 0 y) ?_
      filter_upwards [haeSph] with ξ hξ
      have hp : |pfun n x ξ| ≤ Cf := hCf x le_rfl ξ hξ
      have hb : |busemann (φ ξ) y| ≤ hdist 0 y :=
        abs_busemann_le_hdist_zero (φ ξ) (hbij.1 hξ) y
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul hp hb (abs_nonneg _) hCf0
    · -- a.e. strong measurability of the derivative integrand
      exact aes_of_continuousOn_sph n hD_cont
    · -- the uniform bound on the derivative integrand
      filter_upwards [haeSph] with ξ hξ z hz
      exact hbound ξ hξ z hz
    · -- the dominating function is integrable
      exact integrable_const _
    · -- differentiation, for a.e. `ξ ∈ Sph n`
      filter_upwards [haeSph] with ξ hξ z hz
      exact (hd1 (φ ξ) (hbij.1 hξ) z).const_mul (pfun n x ξ)
  -- identify the integrated derivative with `innerSL ℝ (Gv n φ x y)`
  have hInt : Integrable (fun ξ : E n => pfun n x ξ • Work.Mostow.gradB n (φ ξ) y)
      (sigma n) := by
    refine Integrable.of_bound (aes_of_continuousOn_sph n hS_cont) (Cf * |Cg|) ?_
    filter_upwards [haeSph] with ξ hξ
    have hp : |pfun n x ξ| ≤ Cf := hCf x le_rfl ξ hξ
    have hgrad : ‖Work.Mostow.gradB n (φ ξ) y‖ ≤ Cg :=
      hCg (φ ξ) (hbij.1 hξ) y (by linarith [norm_nonneg y])
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hp (le_trans hgrad (le_abs_self Cg)) (norm_nonneg _) hCf0
  have hCLM :
      (∫ ξ, pfun n x ξ • innerSL ℝ (Work.Mostow.gradB n (φ ξ) y) ∂(sigma n))
        = innerSL ℝ (Work.Mostow.Gv n φ x y) := by
    rw [show (∫ ξ, pfun n x ξ • innerSL ℝ (Work.Mostow.gradB n (φ ξ) y) ∂(sigma n))
        = ∫ ξ, innerSL ℝ (pfun n x ξ • Work.Mostow.gradB n (φ ξ) y) ∂(sigma n) from
      integral_congr_ae (Filter.Eventually.of_forall (fun ξ =>
        (ContinuousLinearMap.map_smul (innerSL ℝ) (pfun n x ξ)
          (Work.Mostow.gradB n (φ ξ) y)).symm))]
    exact ContinuousLinearMap.integral_comp_comm (innerSL ℝ) hInt
  rw [hCLM] at hmain
  exact hmain

end

end Work.Mostow
