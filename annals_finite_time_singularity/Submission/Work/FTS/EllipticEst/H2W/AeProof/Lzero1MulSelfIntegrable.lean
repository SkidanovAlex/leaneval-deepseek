import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.StraightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W.AeProof

open MeasureTheory Set Filter
open scoped Real Topology

/-- **`Lzero1 f · f` is integrable** on `(0, π/2)` as soon as `f` is `C²` there, bounded,
with bounded first derivative and bounded `f/cos θ`, and `f''` absolutely integrable.

Indeed `Lzero1 f θ = -f'' θ + (tan θ · f θ)' - 6 f θ`, and on `(0, π/2)` the product rule
gives `(tan θ · f θ)' = (1/cos²θ) f θ + tan θ f' θ`.  Hence `Lzero1 f · f` splits into the
three pieces

* `-f'' θ · f θ`, dominated by `B · |f'' θ|` (integrable by hypothesis),
* `(tan θ · f θ)' · f θ = (f θ / cos θ)² + (tan θ · f θ) · f' θ`, bounded by `K² + K·M`,
* `-6 f θ²`, bounded by `6 B²`,

each of which is integrable on the finite-measure interval `(0, π/2)`. -/
theorem Lzero1MulSelfIntegrable {f : ℝ → ℝ} {B M K : ℝ}
    (hsm : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hB : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |f θ| ≤ B)
    (hM : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv f θ| ≤ M)
    (hK : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |f θ / Real.cos θ| ≤ K)
    (hint : MeasureTheory.IntegrableOn (fun θ => |deriv (fun t : ℝ => deriv f t) θ|)
      (Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.Lzero1 f θ * f θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  set I : Set ℝ := Set.Ioo (0 : ℝ) (Real.pi / 2) with hI
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hmem4 : (Real.pi / 4) ∈ I := ⟨by linarith, by linarith⟩
  have hIopen : IsOpen I := isOpen_Ioo
  have hImeas : MeasurableSet I := measurableSet_Ioo
  -- nonnegativity of the three constants
  have hBnn : 0 ≤ B := by
    have h := hB (Real.pi / 4) hmem4
    linarith [abs_nonneg (f (Real.pi / 4))]
  have hMnn : 0 ≤ M := by
    have h := hM (Real.pi / 4) hmem4
    linarith [abs_nonneg (deriv f (Real.pi / 4))]
  have hKnn : 0 ≤ K := by
    have h := hK (Real.pi / 4) hmem4
    linarith [abs_nonneg (f (Real.pi / 4) / Real.cos (Real.pi / 4))]
  -- the interval has finite measure
  have hvol : volume I < ⊤ := by
    have hsub : I ⊆ Set.Icc (0 : ℝ) (Real.pi / 2) :=
      fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    calc volume I ≤ volume (Set.Icc (0 : ℝ) (Real.pi / 2)) := measure_mono hsub
      _ < ⊤ := isCompact_Icc.measure_lt_top
  -- regularity of `f` and its derivatives
  have hcont : ContinuousOn f I := hsm.continuousOn
  have hcontd : ContinuousOn (deriv f) I := hsm.continuousOn_deriv_of_isOpen hIopen (by norm_num)
  have hdiffOn : DifferentiableOn ℝ f I := hsm.differentiableOn (by norm_num)
  have hcd1 : ContDiffOn ℝ 1 (deriv f) I := hsm.deriv_of_isOpen hIopen (by norm_num)
  have hcont2 : ContinuousOn (deriv (deriv f)) I :=
    hcd1.continuousOn_deriv_of_isOpen hIopen (by norm_num)
  have hcos_ne : ∀ θ ∈ I, Real.cos θ ≠ 0 := fun θ hθ =>
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, hpi], by linarith [hθ.2]⟩)
  -- ### the three pieces
  have hT1 : IntegrableOn (fun θ => -(deriv (fun t : ℝ => deriv f t) θ) * f θ) I := by
    refine Integrable.mono' (hint.const_mul B) ?_ ?_
    · exact ((hcont2.aestronglyMeasurable hImeas).neg).mul (hcont.aestronglyMeasurable hImeas)
    · filter_upwards [ae_restrict_mem hImeas] with θ hθ
      rw [Real.norm_eq_abs, abs_mul, abs_neg]
      calc |deriv (fun t : ℝ => deriv f t) θ| * |f θ|
          ≤ |deriv (fun t : ℝ => deriv f t) θ| * B :=
            mul_le_mul_of_nonneg_left (hB θ hθ) (abs_nonneg _)
        _ = B * |deriv (fun t : ℝ => deriv f t) θ| := by ring
  have hT2eq : ∀ θ ∈ I, deriv (fun t : ℝ => Real.tan t * f t) θ
      = (1 / Real.cos θ ^ 2) * f θ + Real.tan θ * deriv f θ := by
    intro θ hθ
    have h1 : DifferentiableAt ℝ Real.tan θ := Real.differentiableAt_tan.mpr (hcos_ne θ hθ)
    have h2 : DifferentiableAt ℝ f θ := hdiffOn.differentiableAt (hIopen.mem_nhds hθ)
    have h := deriv_mul h1 h2
    rw [Real.deriv_tan] at h
    exact h
  have hT2 : IntegrableOn (fun θ => deriv (fun t : ℝ => Real.tan t * f t) θ * f θ) I := by
    have hgcont : ContinuousOn
        (fun θ => ((1 / Real.cos θ ^ 2) * f θ + Real.tan θ * deriv f θ) * f θ) I := by
      have hc : ContinuousOn (fun θ : ℝ => (1 : ℝ) / Real.cos θ ^ 2) I :=
        continuousOn_const.div (Real.continuous_cos.continuousOn.pow 2)
          (fun θ hθ => pow_ne_zero 2 (hcos_ne θ hθ))
      have ht : ContinuousOn (fun θ : ℝ => Real.tan θ) I :=
        Real.continuousOn_tan.mono (fun θ hθ => hcos_ne θ hθ)
      exact ((hc.mul hcont).add (ht.mul hcontd)).mul hcont
    have hbound : ∀ᵐ θ ∂volume.restrict I,
        ‖((1 / Real.cos θ ^ 2) * f θ + Real.tan θ * deriv f θ) * f θ‖ ≤ K ^ 2 + K * M := by
      filter_upwards [ae_restrict_mem hImeas] with θ hθ
      rw [Real.norm_eq_abs]
      have hcos := hcos_ne θ hθ
      have hsplit : ((1 / Real.cos θ ^ 2) * f θ + Real.tan θ * deriv f θ) * f θ
          = (f θ / Real.cos θ) ^ 2 + Real.tan θ * deriv f θ * f θ := by
        field_simp
      have hA : |(f θ / Real.cos θ) ^ 2| ≤ K ^ 2 := by
        have h1 : |f θ / Real.cos θ| ≤ K := hK θ hθ
        calc |(f θ / Real.cos θ) ^ 2| = (f θ / Real.cos θ) ^ 2 := abs_sq _
          _ = |f θ / Real.cos θ| ^ 2 := (sq_abs _).symm
          _ ≤ K ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      have htan : |Real.tan θ * f θ| ≤ K := by
        have h2 : Real.tan θ * f θ = Real.sin θ * (f θ / Real.cos θ) := by
          rw [Real.tan_eq_sin_div_cos, div_mul_eq_mul_div]
          field_simp
        rw [h2, abs_mul]
        calc |Real.sin θ| * |f θ / Real.cos θ| ≤ 1 * K :=
              mul_le_mul (abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩)
                (hK θ hθ) (abs_nonneg _) (by norm_num)
          _ = K := by ring
      have hB2 : |Real.tan θ * deriv f θ * f θ| ≤ K * M := by
        rw [show Real.tan θ * deriv f θ * f θ = (Real.tan θ * f θ) * deriv f θ by ring,
          abs_mul]
        exact mul_le_mul htan (hM θ hθ) (abs_nonneg _) hKnn
      rw [hsplit]
      calc |(f θ / Real.cos θ) ^ 2 + Real.tan θ * deriv f θ * f θ|
          ≤ |(f θ / Real.cos θ) ^ 2| + |Real.tan θ * deriv f θ * f θ| := abs_add_le _ _
        _ ≤ K ^ 2 + K * M := add_le_add hA hB2
    have hHg : IntegrableOn
        (fun θ => ((1 / Real.cos θ ^ 2) * f θ + Real.tan θ * deriv f θ) * f θ) I :=
      IntegrableOn.of_bound hvol (hgcont.aestronglyMeasurable hImeas) (K ^ 2 + K * M) hbound
    exact hHg.congr_fun (fun θ hθ => by rw [hT2eq θ hθ]) hImeas
  have hT3 : IntegrableOn (fun θ => 6 * f θ ^ 2) I := by
    refine IntegrableOn.of_bound hvol ?_ (6 * B ^ 2) ?_
    · exact ((hcont.pow 2).const_mul 6).aestronglyMeasurable hImeas
    · filter_upwards [ae_restrict_mem hImeas] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hle : f θ ^ 2 ≤ B ^ 2 := by
        have h1 : |f θ| ≤ B := hB θ hθ
        calc f θ ^ 2 = |f θ| ^ 2 := by rw [sq_abs]
          _ ≤ B ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      linarith
  -- ### assembly
  have hsum : IntegrableOn (fun θ => (-(deriv (fun t : ℝ => deriv f t) θ) * f θ)
      + deriv (fun t : ℝ => Real.tan t * f t) θ * f θ - 6 * f θ ^ 2) I :=
    (hT1.add hT2).sub hT3
  refine hsum.congr_fun ?_ hImeas
  intro θ hθ
  simp only [Work.FTS.EllipticEst.Lzero1]
  ring

end Work.FTS.EllipticEst.H2W.AeProof
