import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.Jeps_tendsto
import Submission.Work.FTS.StrongEps.EpsLocalPStar.JepsMarginalDefs
import Submission.Work.FTS.StrongEps.EpsLocalPStar.ExpShiftIntegrable
import Submission.Work.FTS.StrongEps.EpsLocalPStar.JkerNormBound
import Submission.Work.FTS.StrongEps.EpsLocalPStar.JkerEqZeroOfAbsGt
import Submission.Work.FTS.StrongEps.EpsLocalPStar.AbsLamShiftIntegrableOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

/-- **Integrability of the dominating density of the trace transfer.**  For a smooth admissible
kernel `ρ` (`IsSmoothKernel`), `ε > 0`, `z > 0`, a measurable `lam` with integrable
log-coordinate trace, and an angular energy `Ibd α f` which is integrable on every compact
subinterval of `(0,∞)`, the density

  `p ↦ ‖Jker ρ ε p‖ * (|lam (z * exp (-p.1))| + Ibd α f (z * exp (-p.1)))`

is integrable on `ℝ²`.  This is the domination needed by the dominated-convergence computation of
the boundary trace of `Jeps`.

Route.  Split into the two summands.
* For `lam`: `‖Jker ρ ε p‖ ≤ ε⁻² ‖ρ‖_∞` and `Jker ρ ε p = 0` unless `|p.1| ≤ ε` and
  `|p.2| ≤ ε` (`Jker_ne_zero_support`, `Jker_integrable`); putting `u = log z - p₁` (translation
  invariance of Lebesgue measure) gives `z * exp (-p₁) = exp u` and hence
  `∫_{|p₁| ≤ ε} |lam (z exp (-p₁))| dp₁ = ∫_{log z - ε}^{log z + ε} |lam (exp u)| du ≤
  ∫_u |lam (exp u)| du < ∞` by `hint`, while the `p₂`-integral runs over a fixed bounded interval.
* For `Ibd`: the same substitution reduces `∫_{|p₁| ≤ ε} Ibd α f (z exp (-p₁)) dp₁` to
  `∫_{z' ∈ [z e^{-ε}, z e^{ε}]} Ibd α f z' / z' dz' ≤ (z e^{-ε})⁻¹ ∫_{z' ∈ [z e^{-ε}, z e^{ε}]} Ibd α f z'`,
  which is finite by `hIbd` with `a = z * exp (-ε) > 0` and `b = z * exp ε`; obtain the
  `1/z'`-weighted form from the plain interval integral by the monotone `C¹` substitution
  `z' = exp u` (`intervalIntegral.integral_comp_mul_deriv` or its `Real.exp` instance), and
  multiply by a bound for the `p₂`-marginal of `‖Jker ρ ε‖`.
The Fubini/Tonelli step is over `(volume : Measure ℝ).prod volume`; note that `p ↦ ‖Jker ρ ε p‖`
is integrable (`Jker_integrable`), so `MeasureTheory.Integrable.mul_prod` (or `Integrable.mono'`
against an explicit dominating density) applies.
Declare the result in the namespace `Work.FTS.StrongEps.EpsLocalPStar`. -/
theorem JkerDomDensityIntegrable {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε z : ℝ} (hε : 0 < ε) (hz : 0 < z) {lam : ℝ → ℝ} (hlamm : Measurable lam)
    (hint : MeasureTheory.Integrable (fun u : ℝ => lam (Real.exp u)))
    {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hIbd : ∀ a b : ℝ, 0 < a → a ≤ b →
      MeasureTheory.IntegrableOn (fun z : ℝ => Ibd α f z) (Set.Icc a b)) :
    MeasureTheory.Integrable
      (fun p : ℝ × ℝ => ‖Work.FTS.StrongEps.Jker ρ ε p‖ *
        (|lam (z * Real.exp (-p.1))| + Ibd α f (z * Real.exp (-p.1))))
      (MeasureTheory.volume : Measure (ℝ × ℝ)) := by
  classical
  -- a uniform bound for the kernel
  obtain ⟨M, hM0, hMle⟩ := JkerNormBound (ρ := ρ) hρ hε
  -- the slice interval of the `z`-coordinate and the square on which the density is supported
  set s : Set ℝ := Set.Icc (-ε) ε with hs_def
  have hs : MeasurableSet s := by rw [hs_def]; exact measurableSet_Icc
  have hsfin : (MeasureTheory.volume : Measure ℝ) s ≠ ⊤ := by
    rw [hs_def, Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  -- the two one-dimensional integrability facts, on the slice interval
  have hlam1 : MeasureTheory.Integrable (fun x : ℝ => |lam (z * Real.exp (-x))|)
      (MeasureTheory.volume.restrict s) := by
    rw [hs_def]; exact AbsLamShiftIntegrableOn hint hz
  have hibd1 : MeasureTheory.Integrable (fun x : ℝ => Ibd α f (z * Real.exp (-x)))
      (MeasureTheory.volume.restrict s) := by
    rw [hs_def]; exact ExpShiftIntegrable (h := fun y => Ibd α f y) hε hz hIbd
  -- the dominating one-dimensional density
  set F : ℝ → ℝ := fun x => |lam (z * Real.exp (-x))| + |Ibd α f (z * Real.exp (-x))| with hF_def
  have hsum1 : MeasureTheory.Integrable F (MeasureTheory.volume.restrict s) := by
    rw [hF_def]; exact hlam1.add hibd1.norm
  -- its two indicator factors
  have hH1 : MeasureTheory.Integrable (s.indicator F) (MeasureTheory.volume : Measure ℝ) :=
    (MeasureTheory.integrable_indicator_iff hs).mpr hsum1
  have hH2 : MeasureTheory.Integrable (s.indicator (fun _ : ℝ => (1 : ℝ)))
      (MeasureTheory.volume : Measure ℝ) :=
    (MeasureTheory.integrable_indicator_iff hs).mpr
      (MeasureTheory.integrableOn_const (C := (1 : ℝ)) hsfin)
  -- the dominating density on the plane, and its integrability (Fubini on the product)
  set D : ℝ × ℝ → ℝ :=
    fun p => M * ((s.indicator F) p.1 * (s.indicator (fun _ : ℝ => (1 : ℝ))) p.2) with hD_def
  have hD : MeasureTheory.Integrable D (MeasureTheory.volume : Measure (ℝ × ℝ)) := by
    rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ]
    have h := (hH1.const_mul M).mul_prod hH2
    simpa only [hD_def, mul_assoc] using h
  -- the kernel vanishes off the square
  have hzero : ∀ p : ℝ × ℝ, p ∉ s ×ˢ s → Work.FTS.StrongEps.Jker ρ ε p = 0 := by
    intro p hp
    refine JkerEqZeroOfAbsGt hρ hε ?_
    rcases not_and_or.mp hp with h | h
    · left
      have h' : p.1 < -ε ∨ ε < p.1 := by
        rw [hs_def, Set.mem_Icc] at h
        simpa only [not_le] using not_and_or.mp h
      rcases h' with h' | h'
      · rw [abs_of_neg (by linarith)]; linarith
      · rwa [abs_of_nonneg (by linarith)]
    · right
      have h' : p.2 < -ε ∨ ε < p.2 := by
        rw [hs_def, Set.mem_Icc] at h
        simpa only [not_le] using not_and_or.mp h
      rcases h' with h' | h'
      · rw [abs_of_neg (by linarith)]; linarith
      · rwa [abs_of_nonneg (by linarith)]
  -- the pointwise domination
  have hdom : ∀ᵐ p ∂(MeasureTheory.volume.restrict (s ×ˢ s)),
      ‖(fun p : ℝ × ℝ => ‖Work.FTS.StrongEps.Jker ρ ε p‖ *
        (|lam (z * Real.exp (-p.1))| + Ibd α f (z * Real.exp (-p.1)))) p‖ ≤ D p := by
    refine Filter.Eventually.of_forall (fun p => ?_)
    change ‖‖Work.FTS.StrongEps.Jker ρ ε p‖ *
        (|lam (z * Real.exp (-p.1))| + Ibd α f (z * Real.exp (-p.1)))‖ ≤ D p
    by_cases hp : p ∈ s ×ˢ s
    · obtain ⟨h1, h2⟩ := hp
      change ‖‖Work.FTS.StrongEps.Jker ρ ε p‖ *
        (|lam (z * Real.exp (-p.1))| + Ibd α f (z * Real.exp (-p.1)))‖
          ≤ M * ((s.indicator F) p.1 * (s.indicator (fun _ : ℝ => (1 : ℝ))) p.2)
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
      calc ‖‖Work.FTS.StrongEps.Jker ρ ε p‖ *
            (|lam (z * Real.exp (-p.1))| + Ibd α f (z * Real.exp (-p.1)))‖
          = ‖Work.FTS.StrongEps.Jker ρ ε p‖ *
            |(|lam (z * Real.exp (-p.1))| + Ibd α f (z * Real.exp (-p.1)))| := by
            rw [norm_mul, norm_norm]; rfl
        _ ≤ M * |(|lam (z * Real.exp (-p.1))| + Ibd α f (z * Real.exp (-p.1)))| :=
            mul_le_mul_of_nonneg_right (hMle p) (abs_nonneg _)
        _ ≤ M * (|lam (z * Real.exp (-p.1))| + |Ibd α f (z * Real.exp (-p.1))|) := by
            refine mul_le_mul_of_nonneg_left ?_ hM0
            simpa only [abs_abs] using
              abs_add_le (|lam (z * Real.exp (-p.1))|) (Ibd α f (z * Real.exp (-p.1)))
        _ = M * (F p.1 * 1) := by simp only [hF_def, mul_one]
    · have hz0 : Work.FTS.StrongEps.Jker ρ ε p = 0 := hzero p hp
      simp only [hz0, norm_zero, zero_mul]
      change (0 : ℝ) ≤ M * ((s.indicator F) p.1 * (s.indicator (fun _ : ℝ => (1 : ℝ))) p.2)
      exact mul_nonneg hM0 (mul_nonneg
        (Set.indicator_nonneg (fun x _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) p.1)
        (Set.indicator_nonneg (fun x _ => zero_le_one) p.2))
  -- measurability of the density on the square
  have hdens_aesm : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => ‖Work.FTS.StrongEps.Jker ρ ε p‖ *
        (|lam (z * Real.exp (-p.1))| + Ibd α f (z * Real.exp (-p.1))))
      (MeasureTheory.volume.restrict (s ×ˢ s)) := by
    have hker : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => ‖Work.FTS.StrongEps.Jker ρ ε p‖)
        (MeasureTheory.volume.restrict (s ×ˢ s)) :=
      (Work.FTS.StrongEps.Jker_continuous hρ.moll ε).norm.aestronglyMeasurable
    have hlam2 : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => |lam (z * Real.exp (-p.1))|)
        (MeasureTheory.volume.restrict (s ×ˢ s)) :=
      ((hlamm.comp (by fun_prop)).norm).aestronglyMeasurable
    have hibd2 : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => Ibd α f (z * Real.exp (-p.1)))
        (MeasureTheory.volume.restrict (s ×ˢ s)) := by
      have h1 : MeasureTheory.AEStronglyMeasurable (fun x : ℝ => Ibd α f (z * Real.exp (-x)))
          (MeasureTheory.volume.restrict s) := hibd1.aestronglyMeasurable
      have h2 := h1.comp_fst (ν := MeasureTheory.volume.restrict s)
      rwa [MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod] at h2
    exact hker.mul (hlam2.add hibd2)
  have hOn : MeasureTheory.IntegrableOn
      (fun p : ℝ × ℝ => ‖Work.FTS.StrongEps.Jker ρ ε p‖ *
        (|lam (z * Real.exp (-p.1))| + Ibd α f (z * Real.exp (-p.1)))) (s ×ˢ s) :=
    (hD.mono_measure MeasureTheory.Measure.restrict_le_self).mono' hdens_aesm hdom
  -- extend from the square to the plane: the density vanishes off the square
  refine ((MeasureTheory.integrable_indicator_iff (hs.prod hs)).mpr hOn).congr ?_
  filter_upwards with p
  change (s ×ˢ s).indicator (fun p : ℝ × ℝ => ‖Work.FTS.StrongEps.Jker ρ ε p‖ *
        (|lam (z * Real.exp (-p.1))| + Ibd α f (z * Real.exp (-p.1)))) p = _
  by_cases hp : p ∈ s ×ˢ s
  · rw [Set.indicator_of_mem hp]
  · rw [Set.indicator_of_notMem hp, hzero p hp]
    simp only [norm_zero, zero_mul]

end Work.FTS.StrongEps.EpsLocalPStar
