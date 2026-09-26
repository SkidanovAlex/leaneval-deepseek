import Mathlib
import Submission.Work.Drive.sweepFamOf
import Submission.Work.Drive.sweepBump_integral

set_option linter.unusedVariables false

namespace Work.Drive

open scoped Real Topology intervalIntegral
open LeanEval.KnotTheory.Quadrisecant

/-!
# The half-space bound for the doubly blurred knot

If the knot `Γ'` lies on one side of a level set of the linear functional `⟪n, ·⟫` over a whole
`s`-window, then so does its double blur: averaging a function which is `≥ c` against a bump of
total mass one cannot decrease the value.

The two ingredients are the elementary "weighted average of a function bounded below is bounded
below" (`integral_bump_mul_ge`) and the commutation of `⟪n, ·⟫` with the interval integral.
-/

/-- The smoothing bump is continuous. -/
lemma sweepBump_cont' : Continuous sweepBump := by
  change Continuous (fun u : ℝ =>
    Real.smoothTransition (1 + u) * Real.smoothTransition (1 - u))
  exact (Real.smoothTransition.continuous.comp (continuous_const.add continuous_id)).mul
    (Real.smoothTransition.continuous.comp (continuous_const.sub continuous_id))

/-- The smoothing bump is nonnegative. -/
lemma sweepBump_nonneg' (u : ℝ) : 0 ≤ sweepBump u := by
  rw [sweepBump]
  exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

/-- A weighted average of a function which is `≥ c` on `[-1,1]`, against a nonnegative weight of
total mass one, is `≥ c`. -/
lemma integral_bump_mul_ge {b g : ℝ → ℝ} {c : ℝ} (hb : Continuous b) (hg : Continuous g)
    (hbnn : ∀ u ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ b u)
    (hb1 : (∫ u in (-1 : ℝ)..1, b u) = 1)
    (hgc : ∀ u ∈ Set.Icc (-1 : ℝ) 1, c ≤ g u) :
    c ≤ ∫ u in (-1 : ℝ)..1, b u * g u := by
  have hle : (∫ u in (-1 : ℝ)..1, b u * c) ≤ ∫ u in (-1 : ℝ)..1, b u * g u :=
    intervalIntegral.integral_mono_on (by norm_num)
      ((hb.mul continuous_const).intervalIntegrable _ _)
      ((hb.mul hg).intervalIntegrable _ _)
      (fun u hu => mul_le_mul_of_nonneg_left (hgc u hu) (hbnn u hu))
  have hconst : (∫ u in (-1 : ℝ)..1, b u * c) = c := by
    rw [intervalIntegral.integral_congr (fun u _ => mul_comm (b u) c),
      intervalIntegral.integral_const_mul, hb1, mul_one]
  linarith

/-- `⟪n, ·⟫` commutes with the interval integral, in the weighted form adapted to the bump. -/
lemma inner_intervalIntegral_smul {b : ℝ → ℝ} (hb : Continuous b) {f : ℝ → Space}
    (hf : Continuous f) (n : Space) :
    inner ℝ n (∫ u in (-1 : ℝ)..1, b u • f u)
      = ∫ u in (-1 : ℝ)..1, b u * inner ℝ n (f u) := by
  have hint : IntervalIntegrable (fun u : ℝ => b u • f u) MeasureTheory.volume (-1 : ℝ) 1 :=
    (hb.smul hf).intervalIntegrable (-1 : ℝ) 1
  have h := ContinuousLinearMap.intervalIntegral_comp_comm (L := innerSL ℝ n)
    (μ := MeasureTheory.volume) (f := fun u : ℝ => b u • f u) hint
  have h' : inner ℝ n (∫ u in (-1 : ℝ)..1, b u • f u)
      = ∫ u in (-1 : ℝ)..1, inner ℝ n (b u • f u) := by
    simpa only [innerSL_apply_apply] using h.symm
  rw [h']
  exact intervalIntegral.integral_congr (fun u _ => inner_smul_right n (f u) (b u))

open scoped Real Topology intervalIntegral in
open LeanEval.KnotTheory.Quadrisecant in
theorem halfspace_of_doubleBlur
    {Γ' : ℝ → ℝ → Space} (hΓ' : Continuous (fun p : ℝ × ℝ => Γ' p.1 p.2))
    {y : ℝ → ℝ} (hy : Continuous y) {n : Space}
    {c sig δ₂ : ℝ} (hc : 0 < c)
    (hpos : ∀ v ∈ Set.Icc (-1 : ℝ) 1, ∀ r : ℝ,
      c ≤ inner ℝ n (Γ' (sig - δ₂ * v) r)) :
    c ≤ inner ℝ n (∫ v in (-1 : ℝ)..1, Work.Drive.sweepBump v •
      (∫ u in (-1 : ℝ)..1, Work.Drive.sweepBump u • Γ' (sig - δ₂ * v) (y u))) := by
  -- The inner blur is continuous in the outer parameter.
  have hInnerCont : Continuous (fun v : ℝ =>
      ∫ u in (-1 : ℝ)..1, Work.Drive.sweepBump u • Γ' (sig - δ₂ * v) (y u)) := by
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (a₀ := -1)
      (f := fun (v : ℝ) (u : ℝ) => Work.Drive.sweepBump u • Γ' (sig - δ₂ * v) (y u))
      ?_ (s := fun _ : ℝ => (1 : ℝ)) continuous_const
    change Continuous (fun p : ℝ × ℝ => Work.Drive.sweepBump p.2 • Γ' (sig - δ₂ * p.1) (y p.2))
    exact ((Work.Drive.sweepBump_cont').comp continuous_snd).smul
      (hΓ'.comp (Continuous.prodMk
        (continuous_const.sub (continuous_const.mul continuous_fst))
        (hy.comp continuous_snd)))
  -- Step 1: for each outer parameter the inner blur is `≥ c`.
  have hstep1 : ∀ v ∈ Set.Icc (-1 : ℝ) 1,
      c ≤ inner ℝ n (∫ u in (-1 : ℝ)..1,
        Work.Drive.sweepBump u • Γ' (sig - δ₂ * v) (y u)) := by
    intro v hv
    have hfcont : Continuous (fun u : ℝ => Γ' (sig - δ₂ * v) (y u)) :=
      hΓ'.comp (Continuous.prodMk continuous_const (hy.comp continuous_id))
    rw [inner_intervalIntegral_smul Work.Drive.sweepBump_cont' hfcont n]
    exact integral_bump_mul_ge Work.Drive.sweepBump_cont'
      (continuous_inner.comp (continuous_const.prodMk hfcont))
      (fun u _ => Work.Drive.sweepBump_nonneg' u) Work.Drive.sweepBump_integral
      (fun u _ => hpos v hv (y u))
  -- Step 2: average the bound of step 1 against the outer bump.
  rw [inner_intervalIntegral_smul Work.Drive.sweepBump_cont' hInnerCont n]
  exact integral_bump_mul_ge Work.Drive.sweepBump_cont'
    (continuous_inner.comp (continuous_const.prodMk hInnerCont))
    (fun u _ => Work.Drive.sweepBump_nonneg' u) Work.Drive.sweepBump_integral hstep1

end Work.Drive
