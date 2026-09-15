import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Separation.CompletelyRegular

open MeasureTheory

namespace Commons.MeasureTheory.Integral

set_option autoImplicit false

/-- For a `C²` function `f : ℂᵈ → ℝ` and a direction `v`, the function
`z ↦ (fderiv ℝ f z) v` is `C¹`. -/
private lemma contDiff_one_fderiv_apply {d : ℕ} {f : (Fin d → ℂ) → ℝ}
    (hf : ContDiff ℝ 2 f) (v : Fin d → ℂ) :
    ContDiff ℝ 1 (fun z => (fderiv ℝ f z) v) := by
  have h := hf.contDiff_fderiv_apply (m := 1) (by norm_num)
  exact h.comp (contDiff_id.prodMk contDiff_const)

private lemma continuous_fderiv_apply_of_contDiff {d : ℕ} {f : (Fin d → ℂ) → ℝ}
    (hf : ContDiff ℝ 2 f) (v : Fin d → ℂ) :
    Continuous (fun z => (fderiv ℝ f z) v) :=
  (contDiff_one_fderiv_apply hf v).continuous

private lemma hasCompactSupport_fderiv_apply' {d : ℕ} {f : (Fin d → ℂ) → ℝ}
    (hf : HasCompactSupport f) (v : Fin d → ℂ) :
    HasCompactSupport (fun z => (fderiv ℝ f z) v) :=
  HasCompactSupport.fderiv_apply (𝕜 := ℝ) hf v

private lemma integrable_of_continuous_of_hasCompactSupport' {d : ℕ}
    {f : (Fin d → ℂ) → ℝ} (h : Continuous f) (hc : HasCompactSupport f) :
    Integrable f :=
  h.integrable_of_hasCompactSupport hc

/-- **Integration by parts for second derivatives on `ℂᵈ`.**  If `ψ` is a compactly supported `C²`
function and `φ` is `C²`, then `∫ φ · ∂_a∂_bψ = ∫ ∂_a∂_bφ · ψ`, where
`∂_a∂_bψ(z) = (iteratedFDeriv ℝ 2 ψ z) ![a,b]`.  (Both sides equal `-∫(∂_aφ)(∂_bψ)`.) -/
theorem integral_mul_iteratedFDeriv_two_eq {d : ℕ} {φ ψ : (Fin d → ℂ) → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ 2 ψ) (hcψ : HasCompactSupport ψ)
    (a b : Fin d → ℂ) :
    ∫ z, φ z * ((iteratedFDeriv ℝ 2 ψ z) ![a, b])
      = ∫ z, ((iteratedFDeriv ℝ 2 φ z) ![a, b]) * ψ z := by
  -- The second iterated derivative is the derivative of the first derivative.
  have hkey1 : ∀ z, iteratedFDeriv ℝ 2 ψ z ![a, b]
      = fderiv ℝ (fun y => (fderiv ℝ ψ y) b) z a := by
    intro z
    rw [iteratedFDeriv_two_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have hd : DifferentiableAt ℝ (fderiv ℝ ψ) z := by fun_prop
    rw [fderiv_clm_apply hd (differentiableAt_const b)]
    simp
  have hkey2 : ∀ z, iteratedFDeriv ℝ 2 φ z ![a, b]
      = fderiv ℝ (fun y => (fderiv ℝ φ y) a) z b := by
    intro z
    rw [iteratedFDeriv_two_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have hd : DifferentiableAt ℝ (fderiv ℝ φ) z := by fun_prop
    rw [fderiv_clm_apply hd (differentiableAt_const a)]
    simp only [fderiv_const_apply, ContinuousLinearMap.comp_apply, add_apply,
      zero_apply, map_zero, ContinuousLinearMap.flip_apply, zero_add]
    exact (ContDiffAt.isSymmSndFDerivAt (hφ.contDiffAt) (by norm_num)).eq a b
  -- Shapes of the auxiliary functions
  have hc_b : HasCompactSupport (fun z : Fin d → ℂ => (fderiv ℝ ψ z) b) :=
    hasCompactSupport_fderiv_apply' hcψ b
  have hg1 : ContDiff ℝ 1 (fun z : Fin d → ℂ => (fderiv ℝ ψ z) b) :=
    contDiff_one_fderiv_apply hψ b
  have hg2 : ContDiff ℝ 1 (fun z : Fin d → ℂ => (fderiv ℝ φ z) a) :=
    contDiff_one_fderiv_apply hφ a
  have hcc_g1 : HasCompactSupport
      (fun z : Fin d → ℂ => (fderiv ℝ (fun y => (fderiv ℝ ψ y) b) z) a) :=
    hasCompactSupport_fderiv_apply' hc_b a
  -- Step A: `∫ φ · ∂_a∂_bψ = -∫ (∂_aφ)(∂_bψ)`
  have hA : ∫ z, φ z * ((iteratedFDeriv ℝ 2 ψ z) ![a, b])
      = - ∫ z, (fderiv ℝ φ z a) * (fderiv ℝ ψ z b) := by
    simp_rw [hkey1]
    refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := (volume : Measure (Fin d → ℂ))) (f := φ)
      (g := fun y => (fderiv ℝ ψ y) b) (v := a) ?_ ?_ ?_ ?_ ?_
    · -- Integrable ((fderiv φ · a) * (fderiv ψ · b))
      have hcont : Continuous (fun z : Fin d → ℂ =>
          (fderiv ℝ φ z) a * (fderiv ℝ ψ z) b) :=
        (continuous_fderiv_apply_of_contDiff hφ a).mul
          (continuous_fderiv_apply_of_contDiff hψ b)
      have hcs : HasCompactSupport (fun z : Fin d → ℂ =>
          (fderiv ℝ φ z) a * (fderiv ℝ ψ z) b) :=
        hc_b.mul_left (f := fun z => (fderiv ℝ φ z) a)
      exact integrable_of_continuous_of_hasCompactSupport' hcont hcs
    · -- Integrable (φ * fderiv (fun y ↦ fderiv ψ y b) · a)
      have hcont : Continuous (fun z : Fin d → ℂ =>
          φ z * (fderiv ℝ (fun y => (fderiv ℝ ψ y) b) z) a) :=
        hφ.continuous.mul ((hg1.continuous_fderiv_apply (by norm_num)).comp
          (continuous_id.prodMk (continuous_const : Continuous fun _ : Fin d → ℂ => a)))
      have hcs : HasCompactSupport (fun z : Fin d → ℂ =>
          φ z * (fderiv ℝ (fun y => (fderiv ℝ ψ y) b) z) a) :=
        hcc_g1.mul_left (f := fun z => φ z)
      exact integrable_of_continuous_of_hasCompactSupport' hcont hcs
    · -- Integrable (φ * fderiv ψ · b)
      have hcont : Continuous (fun z : Fin d → ℂ => φ z * (fderiv ℝ ψ z) b) :=
        hφ.continuous.mul (continuous_fderiv_apply_of_contDiff hψ b)
      have hcs : HasCompactSupport (fun z : Fin d → ℂ => φ z * (fderiv ℝ ψ z) b) :=
        hc_b.mul_left (f := fun z => φ z)
      exact integrable_of_continuous_of_hasCompactSupport' hcont hcs
    · exact fun z _ => (hφ.differentiable (by norm_num)).differentiableAt
    · exact fun z _ => (hg1.differentiable one_ne_zero).differentiableAt
  -- Step B: `∫ (∂_aφ)(∂_bψ) = -∫ ∂_a∂_bφ · ψ`
  have hB : ∫ z, (fderiv ℝ φ z a) * (fderiv ℝ ψ z b)
      = - ∫ z, ((iteratedFDeriv ℝ 2 φ z) ![a, b]) * ψ z := by
    simp_rw [hkey2]
    refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := (volume : Measure (Fin d → ℂ))) (f := fun y => (fderiv ℝ φ y) a)
      (g := ψ) (v := b) ?_ ?_ ?_ ?_ ?_
    · -- Integrable (fderiv (fun y ↦ fderiv φ y a) · b * ψ)
      have hcont : Continuous (fun z : Fin d → ℂ =>
          (fderiv ℝ (fun y => (fderiv ℝ φ y) a) z) b * ψ z) :=
        ((hg2.continuous_fderiv_apply (by norm_num)).comp
          (continuous_id.prodMk (continuous_const : Continuous fun _ : Fin d → ℂ => b))).mul
          hψ.continuous
      have hcs : HasCompactSupport (fun z : Fin d → ℂ =>
          (fderiv ℝ (fun y => (fderiv ℝ φ y) a) z) b * ψ z) :=
        hcψ.mul_left (f := fun z => (fderiv ℝ (fun y => (fderiv ℝ φ y) a) z) b)
      exact integrable_of_continuous_of_hasCompactSupport' hcont hcs
    · -- Integrable ((fderiv φ · a) * (fderiv ψ · b))
      have hcont : Continuous (fun z : Fin d → ℂ =>
          (fderiv ℝ φ z) a * (fderiv ℝ ψ z) b) :=
        (continuous_fderiv_apply_of_contDiff hφ a).mul
          (continuous_fderiv_apply_of_contDiff hψ b)
      have hcs : HasCompactSupport (fun z : Fin d → ℂ =>
          (fderiv ℝ φ z) a * (fderiv ℝ ψ z) b) :=
        hc_b.mul_left (f := fun z => (fderiv ℝ φ z) a)
      exact integrable_of_continuous_of_hasCompactSupport' hcont hcs
    · -- Integrable ((fderiv φ · a) * ψ)
      have hcont : Continuous (fun z : Fin d → ℂ => (fderiv ℝ φ z) a * ψ z) :=
        (continuous_fderiv_apply_of_contDiff hφ a).mul hψ.continuous
      have hcs : HasCompactSupport (fun z : Fin d → ℂ => (fderiv ℝ φ z) a * ψ z) :=
        hcψ.mul_left (f := fun z => (fderiv ℝ φ z) a)
      exact integrable_of_continuous_of_hasCompactSupport' hcont hcs
    · exact fun z _ => (hg2.differentiable one_ne_zero).differentiableAt
    · exact fun z _ => (hψ.differentiable (by norm_num)).differentiableAt
  calc ∫ z, φ z * ((iteratedFDeriv ℝ 2 ψ z) ![a, b])
      = - ∫ z, (fderiv ℝ φ z a) * (fderiv ℝ ψ z b) := hA
    _ = ∫ z, ((iteratedFDeriv ℝ 2 φ z) ![a, b]) * ψ z := by rw [hB]; ring

end Commons.MeasureTheory.Integral