import Mathlib
import Submission.Work.Drive.Generic.nclmDev
import Submission.Work.Drive.AB.needleShiftedNotOnLine

/-!
# Elementary bump averages

The estimates of `Work.Drive.Generic.needleChartLoop_margin` are all obtained by averaging a
pointwise bound over the two smoothing windows (the loop parameter and the sweep parameter).  This
module collects the purely elementary tools:

* `sweepBump_even`, `integral_sweepBump_mul_id` — the bump is even and its first moment vanishes
  (this is what makes the average arc fraction of the middle of the retained arc equal to `1/2`);
* `bumpAvg_le`, `bumpAvg_ge`, `bumpAvg_abs_le` — a pointwise bound on a continuous function bounds
  its `sweepBump`-average;
* `bumpAvg₂_le`, `bumpAvg₂_ge` — the two-dimensional version (average over the loop parameter and
  then over the sweep parameter);
* `arcFrac_quarter`, `integral_sweepBump_arcFrac` — the arc fraction of the blur of the loop
  parameter `period / 4` is affine with vanishing first moment, hence averages to `1/2`.
-/

noncomputable section
namespace Work.Drive.Generic

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology intervalIntegral

/-! ## The bump is even with vanishing first moment -/

lemma sweepBump_even (u : ℝ) : sweepBump (-u) = sweepBump u := by
  rw [sweepBump, sweepBump]
  have h1 : (1 : ℝ) + -u = 1 - u := by ring
  have h2 : (1 : ℝ) - -u = 1 + u := by ring
  rw [h1, h2, mul_comm]

/-- The first moment of the bump vanishes. -/
lemma integral_sweepBump_mul_id : (∫ u in (-1 : ℝ)..1, sweepBump u * u) = 0 := by
  have h := intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 1)
    (f := fun u : ℝ => sweepBump u * u)
  simp only [neg_neg] at h
  have hfun : ∀ x : ℝ, sweepBump (-x) * (-x) = -(sweepBump x * x) := by
    intro x; rw [sweepBump_even]; ring
  simp only [hfun] at h
  rw [intervalIntegral.integral_neg] at h
  linarith [h]

/-! ## Pointwise bounds give average bounds -/

/-- A continuous function bounded above by `C` on `[-1,1]` has `sweepBump`-average at most `C`. -/
theorem bumpAvg_le {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (-1 : ℝ) 1)) {C : ℝ}
    (h : ∀ u ∈ Set.Icc (-1 : ℝ) 1, f u ≤ C) :
    (∫ u in (-1 : ℝ)..1, sweepBump u * f u) ≤ C := by
  have hf' : ContinuousOn f (Set.uIcc (-1 : ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]; exact hf
  have hint1 : IntervalIntegrable (fun u : ℝ => sweepBump u * f u) volume (-1) 1 :=
    (sweepBump_continuous.continuousOn.mul hf').intervalIntegrable
  have hint2 : IntervalIntegrable (fun u : ℝ => sweepBump u * C) volume (-1) 1 :=
    (sweepBump_continuous.mul continuous_const).intervalIntegrable (-1) 1
  have hmono := intervalIntegral.integral_mono_on (by norm_num : (-1 : ℝ) ≤ 1) hint1 hint2
    (fun u hu => mul_le_mul_of_nonneg_left (h u hu) (sweepBump_nonneg u))
  rwa [intervalIntegral.integral_mul_const, integral_sweepBump, one_mul] at hmono

/-- A continuous function bounded below by `C` on `[-1,1]` has `sweepBump`-average at least `C`. -/
theorem bumpAvg_ge {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (-1 : ℝ) 1)) {C : ℝ}
    (h : ∀ u ∈ Set.Icc (-1 : ℝ) 1, C ≤ f u) :
    C ≤ ∫ u in (-1 : ℝ)..1, sweepBump u * f u := by
  have hf' : ContinuousOn f (Set.uIcc (-1 : ℝ) 1) := by
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]; exact hf
  have hint1 : IntervalIntegrable (fun u : ℝ => sweepBump u * C) volume (-1) 1 :=
    (sweepBump_continuous.mul continuous_const).intervalIntegrable (-1) 1
  have hint2 : IntervalIntegrable (fun u : ℝ => sweepBump u * f u) volume (-1) 1 :=
    (sweepBump_continuous.continuousOn.mul hf').intervalIntegrable
  have hmono := intervalIntegral.integral_mono_on (by norm_num : (-1 : ℝ) ≤ 1) hint1 hint2
    (fun u hu => mul_le_mul_of_nonneg_left (h u hu) (sweepBump_nonneg u))
  rwa [intervalIntegral.integral_mul_const, integral_sweepBump, one_mul] at hmono

/-- A continuous function bounded in absolute value by `C` on `[-1,1]` has `sweepBump`-average
bounded in absolute value by `C`. -/
theorem bumpAvg_abs_le {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (-1 : ℝ) 1)) {C : ℝ}
    (h : ∀ u ∈ Set.Icc (-1 : ℝ) 1, |f u| ≤ C) :
    |∫ u in (-1 : ℝ)..1, sweepBump u * f u| ≤ C := by
  rw [abs_le]
  exact ⟨bumpAvg_ge hf (fun u hu => (abs_le.mp (h u hu)).1),
    bumpAvg_le hf (fun u hu => (abs_le.mp (h u hu)).2)⟩

/-! ## The two-dimensional version -/

/-- **The double `sweepBump`-average of a function bounded above.** -/
theorem bumpAvg₂_le {g : ℝ → ℝ → ℝ} (hg : Continuous (Function.uncurry g)) {C : ℝ}
    (h : ∀ v' ∈ Set.Icc (-1 : ℝ) 1, ∀ u ∈ Set.Icc (-1 : ℝ) 1, g v' u ≤ C) :
    (∫ v' in (-1 : ℝ)..1, sweepBump v' *
        (∫ u in (-1 : ℝ)..1, sweepBump u * g v' u)) ≤ C := by
  have hg' : Continuous (Function.uncurry (fun v' u : ℝ => sweepBump u * g v' u)) :=
    (sweepBump_continuous.comp continuous_snd).mul hg
  have hinner : ∀ v' ∈ Set.Icc (-1 : ℝ) 1,
      (∫ u in (-1 : ℝ)..1, sweepBump u * g v' u) ≤ C := fun v' hv' =>
    bumpAvg_le (hf := (hg.comp (continuous_const.prodMk continuous_id)).continuousOn)
      (fun u hu => h v' hv' u hu)
  have hcont : ContinuousOn (fun v' : ℝ => ∫ u in (-1 : ℝ)..1, sweepBump u * g v' u)
      (Set.Icc (-1 : ℝ) 1) :=
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hg' (-1) 1).continuousOn
  exact bumpAvg_le hcont hinner

/-- **The double `sweepBump`-average of a function bounded below.** -/
theorem bumpAvg₂_ge {g : ℝ → ℝ → ℝ} (hg : Continuous (Function.uncurry g)) {C : ℝ}
    (h : ∀ v' ∈ Set.Icc (-1 : ℝ) 1, ∀ u ∈ Set.Icc (-1 : ℝ) 1, C ≤ g v' u) :
    C ≤ ∫ v' in (-1 : ℝ)..1, sweepBump v' *
        (∫ u in (-1 : ℝ)..1, sweepBump u * g v' u) := by
  have hg' : Continuous (Function.uncurry (fun v' u : ℝ => sweepBump u * g v' u)) :=
    (sweepBump_continuous.comp continuous_snd).mul hg
  have hinner : ∀ v' ∈ Set.Icc (-1 : ℝ) 1,
      C ≤ ∫ u in (-1 : ℝ)..1, sweepBump u * g v' u := fun v' hv' =>
    bumpAvg_ge (hf := (hg.comp (continuous_const.prodMk continuous_id)).continuousOn)
      (fun u hu => h v' hv' u hu)
  have hcont : ContinuousOn (fun v' : ℝ => ∫ u in (-1 : ℝ)..1, sweepBump u * g v' u)
      (Set.Icc (-1 : ℝ) 1) :=
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hg' (-1) 1).continuousOn
  exact bumpAvg_ge hcont hinner

/-! ## The average arc fraction of the blurred middle -/

/-- **The arc fraction of the loop parameter `period/4` is affine** in the loop parameter's blur
variable, and its value at `u = 0` is `1/2`. -/
lemma arcFrac_quarter {lam δ₁ u : ℝ} (hδ₁0 : 0 < δ₁) (hδ₁4 : δ₁ ≤ period / 4)
    (hu : u ∈ Set.Icc (-1 : ℝ) 1) :
    arcFrac lam δ₁ (period / 4) u
      = 1 / 2 - (1 - 2 * lam) * (2 * δ₁ / period) * u := by
  rw [arcFrac_eq_affine hδ₁0 (by linarith [hδ₁4, period_pos]) hu
    (fun u hu => sweepParam_quarter_sub_le hδ₁0.le hδ₁4 hu)]
  have hq : sweepParam (period / 4) = 1 / 4 := by
    rw [sweepParam]
    have h1 : period / 4 / period = 1 / 4 := by
      have hp : period ≠ 0 := ne_of_gt period_pos
      rw [div_div]
      field_simp
    rw [h1]
    have h2 : ⌊((1 : ℝ) / 4)⌋ = 0 := by
      rw [Int.floor_eq_iff]; norm_num
    rw [h2]; norm_num
  rw [hq]
  ring

/-- **The average arc fraction of the blurred middle is `1/2`.** -/
lemma integral_sweepBump_arcFrac {lam δ₁ : ℝ} (hδ₁0 : 0 < δ₁) (hδ₁4 : δ₁ ≤ period / 4) :
    (∫ u in (-1 : ℝ)..1, sweepBump u * arcFrac lam δ₁ (period / 4) u) = 1 / 2 := by
  set c : ℝ := (1 - 2 * lam) * (2 * δ₁ / period) with hc
  have hI1 : IntervalIntegrable (fun u : ℝ => sweepBump u * (1 / 2 : ℝ)) volume (-1) 1 :=
    (sweepBump_continuous.mul continuous_const).intervalIntegrable (-1) 1
  have hI2 : IntervalIntegrable (fun u : ℝ => sweepBump u * (c * u)) volume (-1) 1 :=
    (sweepBump_continuous.mul (continuous_const.mul continuous_id)).intervalIntegrable (-1) 1
  have h1 : (∫ u in (-1 : ℝ)..1, sweepBump u * (1 / 2 : ℝ)) = 1 / 2 := by
    rw [intervalIntegral.integral_mul_const, integral_sweepBump, one_mul]
  have h2 : (∫ u in (-1 : ℝ)..1, sweepBump u * (c * u))
      = c * (∫ u in (-1 : ℝ)..1, sweepBump u * u) := by
    rw [show (fun u : ℝ => sweepBump u * (c * u)) = (fun u : ℝ => c * (sweepBump u * u)) from by
      funext u; ring]
    rw [intervalIntegral.integral_const_mul]
  calc (∫ u in (-1 : ℝ)..1, sweepBump u * arcFrac lam δ₁ (period / 4) u)
      = ∫ u in (-1 : ℝ)..1, sweepBump u * (1 / 2 - c * u) := by
        refine intervalIntegral.integral_congr (fun u hu => ?_)
        rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hu
        rw [arcFrac_quarter hδ₁0 hδ₁4 hu, hc]
    _ = ∫ u in (-1 : ℝ)..1, (sweepBump u * (1 / 2) - sweepBump u * (c * u)) :=
        intervalIntegral.integral_congr (fun u _ => by ring)
    _ = (∫ u in (-1 : ℝ)..1, sweepBump u * (1 / 2)) - (∫ u in (-1 : ℝ)..1, sweepBump u * (c * u)) :=
        intervalIntegral.integral_sub hI1 hI2
    _ = 1 / 2 := by rw [h1, h2, integral_sweepBump_mul_id, mul_zero, sub_zero]

/-! ## Named averages (to keep the statements free of integral notation) -/

/-- The `sweepBump`-weighted average of a scalar function on the smoothing window `[-1,1]`. -/
noncomputable def bumpAvg (f : ℝ → ℝ) : ℝ := ∫ u in (-1 : ℝ)..1, sweepBump u * f u

/-- The iterated `sweepBump`-weighted average of a scalar function of two variables. -/
noncomputable def bumpAvg₂ (g : ℝ → ℝ → ℝ) : ℝ :=
  ∫ v' in (-1 : ℝ)..1, sweepBump v' * (∫ u in (-1 : ℝ)..1, sweepBump u * g v' u)

/-- The `σ`-blurred retained arc of the sweep window: the average over the window of the loops'
retained arcs, at a fixed arc fraction. -/
noncomputable def blurArc' (r : ℝ → Space) {d : BandArcData} (D : SweepData d) (δ₂ ε ξ : ℝ) :
    Space :=
  ∫ v' in (-1 : ℝ)..1, sweepBump v' • sweepArc' r D (ε - δ₂ * v') ξ

theorem bumpAvg_le' {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (-1 : ℝ) 1)) {C : ℝ}
    (h : ∀ u ∈ Set.Icc (-1 : ℝ) 1, f u ≤ C) : bumpAvg f ≤ C :=
  bumpAvg_le hf h

theorem bumpAvg_ge' {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (-1 : ℝ) 1)) {C : ℝ}
    (h : ∀ u ∈ Set.Icc (-1 : ℝ) 1, C ≤ f u) : C ≤ bumpAvg f :=
  bumpAvg_ge hf h

theorem bumpAvg_abs_le' {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (-1 : ℝ) 1)) {C : ℝ}
    (h : ∀ u ∈ Set.Icc (-1 : ℝ) 1, |f u| ≤ C) : |bumpAvg f| ≤ C :=
  bumpAvg_abs_le hf h

theorem bumpAvg₂_le' {g : ℝ → ℝ → ℝ} (hg : Continuous (Function.uncurry g)) {C : ℝ}
    (h : ∀ v' ∈ Set.Icc (-1 : ℝ) 1, ∀ u ∈ Set.Icc (-1 : ℝ) 1, g v' u ≤ C) :
    bumpAvg₂ g ≤ C :=
  bumpAvg₂_le hg h

theorem bumpAvg₂_ge' {g : ℝ → ℝ → ℝ} (hg : Continuous (Function.uncurry g)) {C : ℝ}
    (h : ∀ v' ∈ Set.Icc (-1 : ℝ) 1, ∀ u ∈ Set.Icc (-1 : ℝ) 1, C ≤ g v' u) :
    C ≤ bumpAvg₂ g :=
  bumpAvg₂_ge hg h

/-- **The double `sweepBump`-average of a function with values in an interval.** -/
theorem bumpAvg₂_Icc {g : ℝ → ℝ → ℝ} (hg : Continuous (Function.uncurry g)) {lo hi : ℝ}
    (h : ∀ v' ∈ Set.Icc (-1 : ℝ) 1, ∀ u ∈ Set.Icc (-1 : ℝ) 1, g v' u ∈ Set.Icc lo hi) :
    (∫ v' in (-1 : ℝ)..1, sweepBump v' *
        (∫ u in (-1 : ℝ)..1, sweepBump u * g v' u)) ∈ Set.Icc lo hi :=
  ⟨bumpAvg₂_ge hg (fun v' hv' u hu => (h v' hv' u hu).1),
    bumpAvg₂_le hg (fun v' hv' u hu => (h v' hv' u hu).2)⟩

theorem bumpAvg₂_Icc' {g : ℝ → ℝ → ℝ} (hg : Continuous (Function.uncurry g)) {lo hi : ℝ}
    (h : ∀ v' ∈ Set.Icc (-1 : ℝ) 1, ∀ u ∈ Set.Icc (-1 : ℝ) 1, g v' u ∈ Set.Icc lo hi) :
    bumpAvg₂ g ∈ Set.Icc lo hi :=
  bumpAvg₂_Icc hg h

end Work.Drive.Generic

namespace Work.Drive.Generic

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology intervalIntegral

/-- **The double `sweepBump`-average of a bounded function.** -/
theorem bumpAvg₂_abs_le' {g : ℝ → ℝ → ℝ} (hg : Continuous (Function.uncurry g)) {C : ℝ}
    (h : ∀ v' ∈ Set.Icc (-1 : ℝ) 1, ∀ u ∈ Set.Icc (-1 : ℝ) 1, |g v' u| ≤ C) :
    |bumpAvg₂ g| ≤ C := by
  rw [abs_le]
  exact ⟨bumpAvg₂_ge' hg (fun v' hv' u hu => (abs_le.mp (h v' hv' u hu)).1),
    bumpAvg₂_le' hg (fun v' hv' u hu => (abs_le.mp (h v' hv' u hu)).2)⟩

/-- `|x - y| ≤ |x| + |y|`. -/
theorem abs_sub_le_add (x y : ℝ) : |x - y| ≤ |x| + |y| :=
  abs_sub_le_iff.mpr ⟨by linarith [le_abs_self x, neg_le_abs y],
    by linarith [le_abs_self y, neg_le_abs x]⟩

end Work.Drive.Generic
