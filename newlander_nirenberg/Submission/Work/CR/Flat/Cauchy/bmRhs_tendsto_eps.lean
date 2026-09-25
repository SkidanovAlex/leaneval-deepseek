/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The regularised Bochner–Martinelli kernel as an approximate identity

This file proves the analytic limit

  `∫ x, n ε² / (nrmSq x + ε²)^{n+1} · g x  ⟶  (∫ y, n / (nrmSq y + 1)^{n+1}) · g 0`

as `ε → 0⁺`, for `g : ℂⁿ → ℂ` of class `C¹` vanishing outside a ball.  This is the
"RHS" half of the divergence computation: the regularised kernel
`n ε² / (nrmSq x + ε²)^{n+1}` is an approximate identity at the origin whose total mass
is the normalising constant `∫ y, n / (nrmSq y + 1)^{n+1}`, the modulus of
`bmGamma n`.

The proof has two steps:

* a *scaling* identity (`integral_scale_bmRhs`): for `ε > 0` the substitution `x = ε y`
  converts the regularised integral into `∫ y, w(y) · g (ε y)`, where
  `w y = n / (nrmSq y + 1)^{n+1}` is the fixed radial weight.  This is the Haar-measure
  rescaling `Measure.integral_comp_smul` combined with the elementary computation
  `n ε² / (nrmSq (ε y) + ε²)^{n+1} = ε^{-2n} w y`;
* dominated convergence (`tendsto_bmW_integral`): the weight is integrable (`hJ`), the
  functions `g (ε ·)` are dominated by `w` times the maximum of `‖g‖` (which exists
  because `g` is continuous with compact support), and `g (ε y) → g 0` pointwise.
-/
import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmKernel_divergence_aux

noncomputable section

open scoped NNReal ENNReal Topology
open MeasureTheory Set Filter

namespace Work.CR.Flat.Cauchy

/-- The radial weight `w y = n / (nrmSq y + 1)^{n+1}` of the Bochner–Martinelli
normalising constant, as a real-valued function. -/
def bmW (n : ℕ) (x : Fin n → ℂ) : ℝ := (n : ℝ) / (nrmSq x + 1) ^ (n + 1)

lemma continuous_bmW {n : ℕ} : Continuous (bmW n) := by
  unfold bmW
  exact Continuous.div continuous_const ((continuous_nrmSq.add continuous_const).pow _)
    (fun x => by
      have h : (0 : ℝ) < nrmSq x + 1 := by linarith [nrmSq_nonneg x]
      positivity)

lemma bmW_nonneg {n : ℕ} (x : Fin n → ℂ) : 0 ≤ bmW n x := by
  unfold bmW
  have h : (0 : ℝ) < nrmSq x + 1 := by linarith [nrmSq_nonneg x]
  positivity

lemma norm_bmW_complex {n : ℕ} (x : Fin n → ℂ) : ‖(bmW n x : ℂ)‖ = bmW n x := by
  rw [Complex.norm_real]
  exact abs_of_nonneg (bmW_nonneg x)

/-- **The scaling computation.**  For `ε ≠ 0`,
`n ε² / (nrmSq (ε y) + ε²)^{n+1} = ε^{-2n} · w y` where `w` is the radial weight. -/
lemma bmKerEps_scaled {n : ℕ} {ε : ℝ} (hε : 0 < ε) (x : Fin n → ℂ) :
    (n : ℂ) * (ε : ℂ) ^ 2 / (((nrmSq (ε • x) + ε ^ 2 : ℝ)) : ℂ) ^ (n + 1)
      = ((ε ^ (2 * n) : ℝ) : ℂ)⁻¹ * (bmW n x : ℂ) := by
  have hreal : (n : ℝ) * ε ^ 2 / (nrmSq (ε • x) + ε ^ 2) ^ (n + 1)
      = (ε ^ (2 * n))⁻¹ * ((n : ℝ) / (nrmSq x + 1) ^ (n + 1)) := by
    rw [nrmSq_smul]
    have h1 : ε ^ 2 * nrmSq x + ε ^ 2 = ε ^ 2 * (nrmSq x + 1) := by ring
    rw [h1, mul_pow]
    have h2 : (ε ^ 2) ^ (n + 1) = ε ^ (2 * n) * ε ^ 2 := by rw [pow_succ, pow_mul]
    rw [h2]
    field_simp
  have hL : (n : ℂ) * (ε : ℂ) ^ 2 / (((nrmSq (ε • x) + ε ^ 2 : ℝ)) : ℂ) ^ (n + 1)
      = (((n : ℝ) * ε ^ 2 / (nrmSq (ε • x) + ε ^ 2) ^ (n + 1) : ℝ) : ℂ) := by
    push_cast
    ring
  have hR : (((ε ^ (2 * n))⁻¹ * ((n : ℝ) / (nrmSq x + 1) ^ (n + 1)) : ℝ) : ℂ)
      = ((ε ^ (2 * n) : ℝ) : ℂ)⁻¹ * (((n : ℝ) / (nrmSq x + 1) ^ (n + 1) : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, Complex.ofReal_inv]
  unfold bmW
  rw [hL, ← hR]
  exact congrArg _ hreal

/-- **Haar rescaling of the regularised integral.**  For `ε > 0`, the substitution
`x = ε y` turns the regularised Bochner–Martinelli integral into the integral of the
fixed radial weight against `g (ε ·)`. -/
lemma integral_scale_bmRhs {n : ℕ} (g : (Fin n → ℂ) → ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∫ x, ((n : ℂ) * (ε : ℂ) ^ 2 / (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ (n + 1)) * g x
      = ∫ y, (bmW n y : ℂ) * g (ε • y) := by
  have hfin : Module.finrank ℝ (Fin n → ℂ) = 2 * n := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Complex.finrank_real_complex, smul_eq_mul]
    ring
  set c : ℂ := ((ε ^ (2 * n) : ℝ) : ℂ) with hc
  have hcne : c ≠ 0 := by rw [hc, Complex.ofReal_ne_zero]; positivity
  -- Haar rescaling: `∫ x, F (ε • x) = (ε^{2n})⁻¹ • ∫ x, F x`
  have hcomp := Measure.integral_comp_smul (μ := volume) (F := ℂ)
    (fun x => ((n : ℂ) * (ε : ℂ) ^ 2 / (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ (n + 1)) * g x) ε
  rw [hfin] at hcomp
  rw [abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hε.le _))] at hcomp
  -- the rescaled integrand is `c⁻¹` times the weighted integrand
  have hA : (∫ x, ((n : ℂ) * (ε : ℂ) ^ 2 / (((nrmSq (ε • x) + ε ^ 2 : ℝ)) : ℂ) ^ (n + 1))
        * g (ε • x))
      = c⁻¹ * (∫ y, (bmW n y : ℂ) * g (ε • y)) := by
    have hpt : ∀ y, ((n : ℂ) * (ε : ℂ) ^ 2 / (((nrmSq (ε • y) + ε ^ 2 : ℝ)) : ℂ) ^ (n + 1))
        * g (ε • y) = c⁻¹ * ((bmW n y : ℂ) * g (ε • y)) := by
      intro y
      rw [bmKerEps_scaled hε y, ← hc]
      ring
    simp_rw [hpt]
    rw [MeasureTheory.integral_const_mul]
  have hcomp' : (∫ x, ((n : ℂ) * (ε : ℂ) ^ 2 / (((nrmSq (ε • x) + ε ^ 2 : ℝ)) : ℂ) ^ (n + 1))
        * g (ε • x))
      = c⁻¹ * (∫ x, ((n : ℂ) * (ε : ℂ) ^ 2 / (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ (n + 1)) * g x) := by
    rw [hcomp, Complex.real_smul, Complex.ofReal_inv, ← hc]
  have hEq : c⁻¹ * (∫ y, (bmW n y : ℂ) * g (ε • y))
      = c⁻¹ * (∫ x, ((n : ℂ) * (ε : ℂ) ^ 2 / (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ (n + 1)) * g x) := by
    rw [← hA, hcomp']
  exact mul_left_cancel₀ (inv_ne_zero hcne) hEq.symm

/-- **Dominated convergence.**  As `ε → 0⁺`, the weighted integral `∫ y, w y · g (ε y)`
converges to `w`-mass times `g 0`. -/
lemma tendsto_bmW_integral {n : ℕ} (_hn : 0 < n) {g : (Fin n → ℂ) → ℂ} {R : ℝ}
    (_hR : 0 < R) (hg : ContDiff ℝ 1 g)
    (hsupp : ∀ x : Fin n → ℂ, R ≤ ‖x‖ → g x = 0)
    (hJ : Integrable (bmW n)) :
    Filter.Tendsto (fun ε : ℝ => ∫ y, (bmW n y : ℂ) * g (ε • y)) (𝓝[>] (0 : ℝ))
      (𝓝 ((((∫ y, bmW n y) : ℝ) : ℂ) * g 0)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_le_of_supp hg hsupp
  have hbound_int : Integrable (fun y => C * bmW n y) volume := hJ.const_mul C
  -- pointwise convergence for every `y`
  have hlim : ∀ᵐ y ∂(volume : Measure (Fin n → ℂ)),
      Filter.Tendsto (fun ε : ℝ => (bmW n y : ℂ) * g (ε • y)) (𝓝[>] (0 : ℝ))
        (𝓝 ((bmW n y : ℂ) * g 0)) := by
    refine Filter.Eventually.of_forall fun y => ?_
    have h2 : Filter.Tendsto (fun ε : ℝ => ε • y) (𝓝[>] (0 : ℝ)) (𝓝 (0 : Fin n → ℂ)) := by
      simpa using
        Tendsto.smul_const ((continuous_id.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds) y
    have hg0 : Filter.Tendsto g (𝓝 (0 : Fin n → ℂ)) (𝓝 (g 0)) := hg.continuous.continuousAt
    exact Tendsto.const_mul ((bmW n y : ℂ)) (hg0.comp h2)
  have hdc := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (l := 𝓝[>] (0 : ℝ)) (fun y => C * bmW n y) ?hmeas ?hbound hbound_int hlim
  case hmeas =>
    filter_upwards with ε
    have hc : Continuous (fun y : Fin n → ℂ => (bmW n y : ℂ) * g (ε • y)) := by
      apply Continuous.mul
      · exact Complex.continuous_ofReal.comp continuous_bmW
      · exact hg.continuous.comp
          ((continuous_const : Continuous (fun _ : Fin n → ℂ => ε)).smul continuous_id)
    exact hc.aestronglyMeasurable
  case hbound =>
    filter_upwards with ε
    filter_upwards with y
    rw [norm_mul, norm_bmW_complex]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left (hC (ε • y)) (bmW_nonneg y)
  -- identify the limit integral
  have htar : (∫ y, (bmW n y : ℂ) * g 0) = (((∫ y, bmW n y) : ℝ) : ℂ) * g 0 := by
    rw [MeasureTheory.integral_mul_const]
    congr 1
    exact integral_ofReal
  rw [htar] at hdc
  exact hdc

theorem bmRhs_tendsto_eps {n : ℕ} (hn : 0 < n) {g : (Fin n → ℂ) → ℂ} {R : ℝ}
    (hR : 0 < R) (hg : ContDiff ℝ 1 g) (hsupp : ∀ x : Fin n → ℂ, R ≤ ‖x‖ → g x = 0)
    (hJ : MeasureTheory.Integrable (fun y : Fin n → ℂ => (n : ℝ) / (nrmSq y + 1) ^ (n + 1))
      MeasureTheory.volume) :
    Filter.Tendsto (fun ε : ℝ =>
        ∫ x, ((n : ℂ) * (ε : ℂ) ^ 2 / (((nrmSq x + ε ^ 2 : ℝ)) : ℂ) ^ (n + 1)) * g x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((((∫ y : Fin n → ℂ, (n : ℝ) / (nrmSq y + 1) ^ (n + 1)) : ℝ) : ℂ) * g 0)) := by
  have hmain := tendsto_bmW_integral hn hR hg hsupp hJ
  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (integral_scale_bmRhs g hε).symm

end Work.CR.Flat.Cauchy
