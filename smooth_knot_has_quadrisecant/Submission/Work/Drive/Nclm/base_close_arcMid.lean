import Mathlib
import Submission.Work.Drive.AB.shiftedNeedleChart
import Submission.Work.Drive.AB.shiftedNeedleBlur
import Submission.Work.Drive.AB.needleArcZoneMono
import Submission.Work.Drive.AB.windowDataSmall
import Submission.Work.Drive.Generic.nclmDefs

/-!
# The base point of the shifted needle is close to the midpoint of the retained arc

`Work.Drive.Nclm.base_close_arcMid`: the **base point** of the shifted needle (its point at the loop
parameter `period / 4`, i.e. the `δ₁`-blur of the middle of the retained arc, further averaged over
the sweep window at scale `δ₂`) is uniformly close to the midpoint `sweepArc' r D σ (1/2)` of the
retained arc at any sweep parameter `σ` of the window `[ε - δ₂, ε + δ₂]`.

Two elementary facts give the statement, with `ν` fixed and `M` a Lipschitz constant of `r`:

* the needle is a **double `sweepBump`-average** of the chamfered loops
  (`Work.Drive.needleFam_eq_blur_loop`), and a bump-average (total mass `1`) of points that are all
  within `η` of a fixed point is within `η` of it (`bumpAvg_norm_sub_le` below — no continuity is
  needed for this step, only integrability);
* for `δ₁ ≤ period / 4` the whole `δ₁`-blur of the loop parameter `period / 4` stays on the **arc
  branch** of the chamfered loop (`sweepParam ≤ 1/2`), at an arc fraction
  `ξ = lam + (1 - 2 lam) * 2 (sweepParam (period/4 - δ₁ u)) ∈ [0,1]`.  So every point of the
  double blur is a point of the retained arc of some loop of the window, at some fraction of `[0,1]`
  — and `Work.Drive.windowDataSmall` bounds, uniformly, the distance of *every* such point to the
  collapsed end `taR D 0`.
-/

noncomputable section

namespace Work.Drive.Nclm

open LeanEval.KnotTheory.Quadrisecant MeasureTheory
open scoped Real Topology intervalIntegral

/-! ## A bump-average is close to any pointwise-close point -/

lemma bumpAvg_norm_sub_le {F : ℝ → Space} {c : Space} {η : ℝ}
    (hI : IntervalIntegrable (fun u : ℝ => Work.Drive.sweepBump u • F u) volume (-1) 1)
    (h : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ‖F u - c‖ ≤ η) :
    ‖(∫ u in (-1 : ℝ)..1, Work.Drive.sweepBump u • F u) - c‖ ≤ η := by
  have hI2 : IntervalIntegrable (fun u : ℝ => Work.Drive.sweepBump u • c) volume (-1) 1 :=
    (Work.Drive.sweepBump_continuous.smul continuous_const).intervalIntegrable _ _
  have hIc : (∫ u in (-1 : ℝ)..1, Work.Drive.sweepBump u • c) = c := by
    rw [intervalIntegral.integral_smul_const, Work.Drive.integral_sweepBump, one_smul]
  have hcalc : (∫ u in (-1 : ℝ)..1, Work.Drive.sweepBump u • F u)
      - (∫ u in (-1 : ℝ)..1, Work.Drive.sweepBump u • c)
      = ∫ u in (-1 : ℝ)..1, Work.Drive.sweepBump u • (F u - c) := by
    rw [← intervalIntegral.integral_sub hI hI2]
    exact intervalIntegral.integral_congr (fun u _ => by rw [smul_sub])
  have hsub : (∫ u in (-1 : ℝ)..1, Work.Drive.sweepBump u • F u) - c
      = ∫ u in (-1 : ℝ)..1, Work.Drive.sweepBump u • (F u - c) := by
    rw [← hcalc, hIc]
  rw [hsub]
  refine le_trans (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (-1 : ℝ) ≤ 1)) ?_
  have h1 : (∫ u in (-1 : ℝ)..1, ‖Work.Drive.sweepBump u • (F u - c)‖)
      = ∫ u in (-1 : ℝ)..1, Work.Drive.sweepBump u * ‖F u - c‖ :=
    intervalIntegral.integral_congr (fun u _ => by
      rw [norm_smul, Real.norm_of_nonneg (Work.Drive.sweepBump_nonneg u)])
  rw [h1]
  have hint1 : IntervalIntegrable (fun u : ℝ => Work.Drive.sweepBump u * ‖F u - c‖) volume (-1) 1 :=
    (hI.sub hI2).norm.congr (fun u _ => by
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg (Work.Drive.sweepBump_nonneg u)])
  have hint2 : IntervalIntegrable (fun u : ℝ => Work.Drive.sweepBump u * η) volume (-1) 1 :=
    (Work.Drive.sweepBump_continuous.mul continuous_const).intervalIntegrable _ _
  refine le_trans (intervalIntegral.integral_mono_on (by norm_num : (-1 : ℝ) ≤ 1) hint1 hint2
    (fun u hu => mul_le_mul_of_nonneg_left (h u hu) (Work.Drive.sweepBump_nonneg u))) ?_
  rw [intervalIntegral.integral_mul_const, Work.Drive.integral_sweepBump, one_mul]

lemma intervalIntegrable_bump_loopBlur {r : ℝ → Space} (hr : Continuous r) {d : BandArcData}
    (D : Work.Drive.SweepData d) (lam δ₂ ε δ₁ τ : ℝ) :
    IntervalIntegrable
      (fun u : ℝ => Work.Drive.sweepBump u • Work.Drive.loopBlur r D lam δ₂ ε (τ - δ₁ * u))
      volume (-1) 1 := by
  obtain ⟨C, hC0, hCb⟩ := Work.Drive.loopBlurNormBound hr D lam δ₂ ε
  refine IntervalIntegrable.mono_fun'
    ((Work.Drive.sweepBump_continuous.const_mul C).intervalIntegrable (-1) 1) ?_ ?_
  · exact ((Continuous.measurable Work.Drive.sweepBump_continuous).aestronglyMeasurable.smul
      (Work.Drive.aestronglyMeasurable_loopBlur_comp hr D lam δ₂ ε δ₁ τ)).restrict
  · filter_upwards with u
    rw [norm_smul, Real.norm_of_nonneg (Work.Drive.sweepBump_nonneg u)]
    calc Work.Drive.sweepBump u * ‖Work.Drive.loopBlur r D lam δ₂ ε (τ - δ₁ * u)‖
        ≤ Work.Drive.sweepBump u * C :=
          mul_le_mul_of_nonneg_left (hCb _) (Work.Drive.sweepBump_nonneg u)
      _ = C * Work.Drive.sweepBump u := by ring

lemma intervalIntegrable_bump_chamfer {r : ℝ → Space} (hr : Continuous r) {d : BandArcData}
    (D : Work.Drive.SweepData d) (lam δ₂ σ τ : ℝ) :
    IntervalIntegrable
      (fun v : ℝ => Work.Drive.sweepBump v • Work.Drive.sweepLoopChamfer r D lam (σ - δ₂ * v) τ)
      volume (-1) 1 := by
  obtain ⟨C, hC0, hC⟩ := Work.Drive.exists_sweepLoopChamfer_bound hr D lam
  refine IntervalIntegrable.mono_fun'
    ((Work.Drive.sweepBump_continuous.const_mul C).intervalIntegrable (-1) 1) ?_ ?_
  · exact ((Continuous.measurable Work.Drive.sweepBump_continuous).smul
      ((Work.Drive.sweepLoopChamfer_measurable D hr lam).comp
        (show Measurable (fun v : ℝ => (σ - δ₂ * v, τ)) from
          (by fun_prop : Continuous fun v : ℝ => (σ - δ₂ * v, τ)).measurable))).aestronglyMeasurable.restrict
  · filter_upwards with v
    rw [norm_smul, Real.norm_of_nonneg (Work.Drive.sweepBump_nonneg v)]
    calc Work.Drive.sweepBump v * ‖Work.Drive.sweepLoopChamfer r D lam (σ - δ₂ * v) τ‖
        ≤ Work.Drive.sweepBump v * C :=
          mul_le_mul_of_nonneg_left (hC _ _) (Work.Drive.sweepBump_nonneg v)
      _ = C * Work.Drive.sweepBump v := by ring

theorem base_close_arcMid {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d) :
    ∀ ν : ℝ, 0 < ν → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∃ Λ : ℝ, 0 < Λ ∧ Λ ≤ 1 / 4 ∧
        ∀ lam δ₁ δ₂ : ℝ, 0 < lam → lam ≤ Λ → lam < 1 / 2 → 0 < δ₁ → δ₁ ≤ Λ →
          0 < δ₂ → δ₂ ≤ Λ → δ₂ ≤ ε / 2 →
        ∀ σ : ℝ, ε - δ₂ ≤ σ → σ ≤ ε + δ₂ →
          ‖Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε 0 - Work.Drive.sweepArc' r D σ (1 / 2)‖ ≤ ν := by
  intro ν hν
  obtain ⟨M, hM0, hLip⟩ := Work.Drive.exists_knot_lipschitz hr
  have hMne : M ≠ 0 := ne_of_gt hM0
  set δ : ℝ := ν / (2 * M) with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hMδ : M * (2 * δ) = ν := by rw [hδdef]; field_simp
  obtain ⟨ε₁, hε₁0, hε₁1, hwds⟩ := Work.Drive.windowDataSmall hr D δ hδ0
  refine ⟨min ε₁ (1 / 4), lt_min hε₁0 (by norm_num),
    lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
  intro ε hε0 hεε₀
  have hεε₁ : ε ≤ ε₁ := le_trans hεε₀ (min_le_left _ _)
  refine ⟨min (1 / 4) (period / 4), lt_min (by norm_num) (by linarith [period_pos]),
    min_le_left _ _, ?_⟩
  intro lam δ₁ δ₂ hlam0 hlamΛ hlam12 hδ₁0 hδ₁Λ hδ₂0 hδ₂Λ hδ₂ε
  intro sg hsglo hsghi
  have hp : (0 : ℝ) < period := period_pos
  have hδ₁4 : δ₁ ≤ period / 4 := le_trans hδ₁Λ (min_le_right _ _)
  obtain ⟨hrange, -, -⟩ := hwds δ₂ ε hδ₂0 hδ₂ε hε0 hεε₁
  have hrcont : Continuous r := hr.smooth.continuous
  have harc_close : ∀ (σ' ξ : ℝ), ε - δ₂ ≤ σ' → σ' ≤ ε + δ₂ → 0 ≤ ξ → ξ ≤ 1 →
      ‖Work.Drive.sweepArc' r D σ' ξ - Work.Drive.sweepArc' r D sg (1 / 2)‖ ≤ ν := by
    intro σ' ξ hσ'lo hσ'hi hξ0 hξ1
    have hA := hrange σ' hσ'lo hσ'hi ξ hξ0 hξ1
    have hB := hrange sg hsglo hsghi (1 / 2) (by norm_num) (by norm_num)
    have hAB : |(Work.Drive.taR D σ' + ξ * Work.Drive.sweepW' D σ')
        - (Work.Drive.taR D sg + (1 / 2) * Work.Drive.sweepW' D sg)| ≤ 2 * δ := by
      rw [abs_le] at hA hB ⊢
      exact ⟨by linarith [hA.1, hB.1], by linarith [hA.2, hB.2]⟩
    calc ‖Work.Drive.sweepArc' r D σ' ξ - Work.Drive.sweepArc' r D sg (1 / 2)‖
        = ‖r (Work.Drive.taR D σ' + ξ * Work.Drive.sweepW' D σ')
            - r (Work.Drive.taR D sg + (1 / 2) * Work.Drive.sweepW' D sg)‖ := rfl
      _ ≤ M * |(Work.Drive.taR D σ' + ξ * Work.Drive.sweepW' D σ')
            - (Work.Drive.taR D sg + (1 / 2) * Work.Drive.sweepW' D sg)| := hLip _ _
      _ ≤ M * (2 * δ) := mul_le_mul_of_nonneg_left hAB hM0.le
      _ = ν := hMδ
  have hpoint : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∀ v ∈ Set.Icc (-1 : ℝ) 1,
      ‖Work.Drive.sweepLoopChamfer r D lam (ε - δ₂ * v) (period / 4 - δ₁ * u)
        - Work.Drive.sweepArc' r D sg (1 / 2)‖ ≤ ν := by
    intro u hu v hv
    obtain ⟨hu1, hu2⟩ := abs_le.mp (by rw [abs_le]; exact hu : |u| ≤ 1)
    obtain ⟨hv1, hv2⟩ := abs_le.mp (by rw [abs_le]; exact hv : |v| ≤ 1)
    have h1u : δ₁ * u ≤ δ₁ := by nlinarith [hu2, hδ₁0]
    have h2u : -δ₁ ≤ δ₁ * u := by nlinarith [hu1, hδ₁0]
    have ht0 : 0 ≤ period / 4 - δ₁ * u := by nlinarith [hδ₁4, h1u, hp]
    have ht1 : period / 4 - δ₁ * u < period := by nlinarith [hδ₁4, h2u, hp]
    have hsp : Work.Drive.sweepParam (period / 4 - δ₁ * u) ≤ 1 / 2 := by
      rw [Work.Drive.sweepParam_eq_div ⟨ht0, ht1⟩, div_le_iff₀ hp]
      nlinarith [h2u, hδ₁4, hp]
    rw [Work.Drive.sweepLoopChamfer_arcZone' D hsp]
    have hsplo : 0 ≤ Work.Drive.sweepParam (period / 4 - δ₁ * u) :=
      (Work.Drive.sweepParam_mem _).1
    have hξ0 : 0 ≤ lam + (1 - 2 * lam) * (2 * Work.Drive.sweepParam (period / 4 - δ₁ * u)) := by
      nlinarith [hlam0, hlam12, hsplo]
    have hξ1 : lam + (1 - 2 * lam) * (2 * Work.Drive.sweepParam (period / 4 - δ₁ * u)) ≤ 1 := by
      nlinarith [hlam0, hlam12, hsp]
    have hσ'lo : ε - δ₂ ≤ ε - δ₂ * v := by nlinarith [hv2, hδ₂0]
    have hσ'hi : ε - δ₂ * v ≤ ε + δ₂ := by nlinarith [hv1, hδ₂0]
    exact harc_close (ε - δ₂ * v)
      (lam + (1 - 2 * lam) * (2 * Work.Drive.sweepParam (period / 4 - δ₁ * u)))
      hσ'lo hσ'hi hξ0 hξ1
  have hinner : ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      ‖Work.Drive.loopBlur r D lam δ₂ ε (period / 4 - δ₁ * u)
        - Work.Drive.sweepArc' r D sg (1 / 2)‖ ≤ ν := by
    intro u hu
    have h := bumpAvg_norm_sub_le
      (F := fun v : ℝ => Work.Drive.sweepLoopChamfer r D lam (ε - δ₂ * v)
        (period / 4 - δ₁ * u))
      (c := Work.Drive.sweepArc' r D sg (1 / 2)) (η := ν)
      (intervalIntegrable_bump_chamfer hrcont D lam δ₂ ε (period / 4 - δ₁ * u))
      (fun v hv => hpoint u hu v hv)
    simpa only [Work.Drive.loopBlur] using h
  have hneedle : Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε 0
      = ∫ u in (-1 : ℝ)..1, Work.Drive.sweepBump u • Work.Drive.loopBlur r D lam δ₂ ε
          (period / 4 - δ₁ * u) := by
    rw [show Work.Drive.shiftedNeedle r D lam δ₁ δ₂ ε 0
        = Work.Drive.needleFam r D lam δ₁ δ₂ ε (period / 4) from by
      simp only [Work.Drive.shiftedNeedle, zero_add]]
    exact Work.Drive.needleFam_eq_blur_loop hrcont D lam δ₁ δ₂ ε (period / 4)
  rw [hneedle]
  exact bumpAvg_norm_sub_le
    (F := fun u : ℝ => Work.Drive.loopBlur r D lam δ₂ ε (period / 4 - δ₁ * u))
    (c := Work.Drive.sweepArc' r D sg (1 / 2)) (η := ν)
    (intervalIntegrable_bump_loopBlur hrcont D lam δ₂ ε δ₁ (period / 4))
    hinner

end Work.Drive.Nclm
