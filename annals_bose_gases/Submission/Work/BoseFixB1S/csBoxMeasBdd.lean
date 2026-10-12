import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.UBBInputs8.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory

set_option linter.style.haveILetI false

/-- Bilinear Cauchy–Schwarz on the centred box for *bounded measurable* (not merely continuous)
functions: `(∫ f g)² ≤ (∫ f²)(∫ g²)` over `abox N ℓ`.  This is the box Cauchy–Schwarz needed to
close the flat-count Jensen at the *indicator-carrying* functions produced by
`Work.UBBInputs8.boxPInd` (which are bounded and measurable but not continuous).

Route: this is `Submission.BoseGases.cs_box_product` (`Submission/Q0Convex.lean`) with the
continuity hypotheses replaced by `Measurable` plus the stated pointwise bounds; equivalently,
`MemLp.of_bound` + Hölder (`integral_mul_le_Lp_mul_Lq_of_nonneg` with `Real.HolderConjugate.two_two`)
on the finite measure `volume.restrict (abox N ℓ)`, followed by `Real.sq_sqrt`. -/
theorem csBoxMeasBdd {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {f g : Submission.BoseGases.X N → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    {Cf Cg : ℝ} (hfb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |f x| ≤ Cf)
    (hgb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |g x| ≤ Cg) :
    (∫ x in Submission.BoseGases.abox N ℓ, f x * g x) ^ 2
      ≤ (∫ x in Submission.BoseGases.abox N ℓ, (f x) ^ 2)
        * (∫ x in Submission.BoseGases.abox N ℓ, (g x) ^ 2) := by
  let μ' : Measure (Submission.BoseGases.X N) :=
    (volume : Measure (Submission.BoseGases.X N)).restrict (Submission.BoseGases.abox N ℓ)
  have hfin : IsFiniteMeasure μ' := by
    refine ⟨?set⟩
    rw [Measure.restrict_apply_univ]
    exact Submission.BoseGases.abox_lt_top N ℓ hℓ.le
  letI : IsFiniteMeasure μ' := hfin
  have hbf : ∀ᵐ x ∂μ', |f x| ≤ Cf := by
    rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
    exact ae_of_all volume (fun x hx => hfb x hx)
  have hbg : ∀ᵐ x ∂μ', |g x| ≤ Cg := by
    rw [ae_restrict_iff' (Submission.BoseGases.abox_measurable N ℓ)]
    exact ae_of_all volume (fun x hx => hgb x hx)
  have hmf : AEStronglyMeasurable f μ' := hfm.aestronglyMeasurable
  have hmg : AEStronglyMeasurable g μ' := hgm.aestronglyMeasurable
  have hmemf : MemLp (fun x => |f x|) (ENNReal.ofReal 2) μ' :=
    MemLp.of_bound hmf.norm Cf (by filter_upwards [hbf] with x hx; simpa using hx)
  have hmemg : MemLp (fun x => |g x|) (ENNReal.ofReal 2) μ' :=
    MemLp.of_bound hmg.norm Cg (by filter_upwards [hbg] with x hx; simpa using hx)
  have hnonf : 0 ≤ᵐ[μ'] (fun x => |f x|) := ae_of_all _ (fun _ => abs_nonneg _)
  have hnong : 0 ≤ᵐ[μ'] (fun x => |g x|) := ae_of_all _ (fun _ => abs_nonneg _)
  have hmain := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2) (μ := μ')
    Real.HolderConjugate.two_two hnonf hnong hmemf hmemg
  have hc1 : (∫ x, |f x| * |g x| ∂μ') = ∫ x, |f x * g x| ∂μ' := by
    apply integral_congr_ae
    filter_upwards with x
    rw [abs_mul]
  have hsqf : (fun x => |f x| ^ (2 : ℝ)) = fun x => (f x) ^ 2 := by
    funext x
    rw [Real.rpow_two, sq_abs]
  have hsqg : (fun x => |g x| ^ (2 : ℝ)) = fun x => (g x) ^ 2 := by
    funext x
    rw [Real.rpow_two, sq_abs]
  have hA0 : 0 ≤ ∫ x, (f x) ^ 2 ∂μ' := integral_nonneg (fun _ => sq_nonneg _)
  have hB0 : 0 ≤ ∫ x, (g x) ^ 2 ∂μ' := integral_nonneg (fun _ => sq_nonneg _)
  have hR : (∫ x, |f x * g x| ∂μ')
      ≤ Real.sqrt (∫ x, (f x) ^ 2 ∂μ') * Real.sqrt (∫ x, (g x) ^ 2 ∂μ') := by
    rw [hc1, hsqf, hsqg] at hmain
    simpa [Real.sqrt_eq_rpow] using hmain
  have habs : |∫ x, f x * g x ∂μ'| ≤ ∫ x, |f x * g x| ∂μ' :=
    abs_integral_le_integral_abs (μ := μ') (f := fun x => f x * g x)
  have hsq1 : (∫ x, |f x * g x| ∂μ') ^ 2
      ≤ (∫ x, (f x) ^ 2 ∂μ') * (∫ x, (g x) ^ 2 ∂μ') := by
    have h1 : |∫ x, |f x * g x| ∂μ'| ≤
        |Real.sqrt (∫ x, (f x) ^ 2 ∂μ') * Real.sqrt (∫ x, (g x) ^ 2 ∂μ')| := by
      calc
        |∫ x, |f x * g x| ∂μ'| = ∫ x, |f x * g x| ∂μ' :=
          abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))
        _ ≤ Real.sqrt (∫ x, (f x) ^ 2 ∂μ') * Real.sqrt (∫ x, (g x) ^ 2 ∂μ') := hR
        _ = |Real.sqrt (∫ x, (f x) ^ 2 ∂μ') * Real.sqrt (∫ x, (g x) ^ 2 ∂μ')| :=
          (abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).symm
    calc
      (∫ x, |f x * g x| ∂μ') ^ 2
          ≤ (Real.sqrt (∫ x, (f x) ^ 2 ∂μ') * Real.sqrt (∫ x, (g x) ^ 2 ∂μ')) ^ 2 := sq_le_sq.mpr h1
      _ = (∫ x, (f x) ^ 2 ∂μ') * (∫ x, (g x) ^ 2 ∂μ') := by
        rw [mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt hB0]
  have hsq2 : (∫ x, f x * g x ∂μ') ^ 2 ≤ (∫ x, |f x * g x| ∂μ') ^ 2 := by
    have hnn : 0 ≤ ∫ x, |f x * g x| ∂μ' := integral_nonneg (fun _ => abs_nonneg _)
    have h1 : |∫ x, f x * g x ∂μ'| ≤ |∫ x, |f x * g x| ∂μ'| := by
      calc
        |∫ x, f x * g x ∂μ'| ≤ ∫ x, |f x * g x| ∂μ' := habs
        _ = |∫ x, |f x * g x| ∂μ'| := (abs_of_nonneg hnn).symm
    exact sq_le_sq.mpr h1
  calc
    (∫ x in Submission.BoseGases.abox N ℓ, f x * g x) ^ 2
        = (∫ x, f x * g x ∂μ') ^ 2 := by rfl
    _ ≤ (∫ x, |f x * g x| ∂μ') ^ 2 := hsq2
    _ ≤ (∫ x, (f x) ^ 2 ∂μ') * (∫ x, (g x) ^ 2 ∂μ') := hsq1
    _ = (∫ x in Submission.BoseGases.abox N ℓ, (f x) ^ 2)
          * (∫ x in Submission.BoseGases.abox N ℓ, (g x) ^ 2) := by rfl

end Work.BoseFixB1S
