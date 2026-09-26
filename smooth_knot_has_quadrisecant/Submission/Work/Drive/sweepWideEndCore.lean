import Mathlib
import Submission.Work.Drive.sweepWideEndDefs
import Submission.Work.Drive.chordSweepSmooth
import Submission.Work.Drive.chordSweepDefs
import Submission.Work.Drive.chamferVel_bounds
import Submission.Work.Drive.chamferVel_hasDerivAt
import Submission.Work.Drive.sweepBump_integral
import Submission.Work.Drive.sweepFam_contDiff_periodic
import Submission.Work.Drive.sweepLoopChamfer_locallyIntegrable
import Submission.Work.Drive.sweepTopTools

/-!
# The wide-end estimate of the chord sweep

The doubly smoothed chord sweep `sweepFam r D lam δ₁ δ₂ σ` at a sweep parameter `σ₀` close to `1`
is, after a reparametrisation `Θ` of the loop parameter, `C¹`-close to the shifted knot
`t ↦ r (t + c)`.  This file develops the estimates and assembles the target.

## Contents

* `Work.Drive.wideEnd_*` — the corner set is null, the velocity profile is measurable;
* `Work.Drive.wideEnd_hasDerivAt_sweepFam` — the derivative of the smoothed slice;
* the arclength matching and the reparametrisation;
* `Work.Drive.sweepFam_wideEnd_estimate` — the target.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant
open MeasureTheory

/-! ## The corner set of the loop parameter is null -/

/-- The chamfered loop is `period`-periodic in the loop parameter. -/
lemma wideEnd_loopChamfer_add_period (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam s t : ℝ) : sweepLoopChamfer r D lam s (t + period) = sweepLoopChamfer r D lam s t := by
  simp only [sweepLoopChamfer, sweepParam_add_period]

/-- The solutions of `sweepParam y = c` form a discrete (hence null) set. -/
lemma wideEnd_exists_int_of_sweepParam_eq {y c : ℝ} (h : sweepParam y = c) :
    ∃ k : ℤ, y = (c + (k : ℝ)) * period := by
  simp only [sweepParam] at h
  have h2 : y / period = c + (⌊y / period⌋ : ℝ) := by linarith
  refine ⟨⌊y / period⌋, ?_⟩
  rw [← h2, div_mul_cancel₀ y period_ne_zero]

lemma wideEnd_countable_sweepParam_eq (c : ℝ) : Set.Countable {t : ℝ | sweepParam t = c} := by
  refine Set.Countable.mono ?_ (Set.countable_iUnion
    (fun k : ℤ => Set.countable_singleton ((c + (k : ℝ)) * period)))
  intro t ht
  simp only [Set.mem_setOf_eq] at ht
  obtain ⟨k, hk⟩ := wideEnd_exists_int_of_sweepParam_eq ht
  exact Set.mem_iUnion.mpr ⟨k, hk⟩

lemma wideEnd_measure_zero_chamferCorner (lam : ℝ) :
    (volume : Measure ℝ) {t : ℝ | chamferCorner lam t} = 0 := by
  have hsub : {t : ℝ | chamferCorner lam t} ⊆
      ({t : ℝ | sweepParam t = 0} ∪ {t : ℝ | sweepParam t = 1 / 2}) ∪
      ({t : ℝ | sweepParam t = 1 / 2 + lam / 2} ∪ {t : ℝ | sweepParam t = 1 - lam / 2}) := by
    intro t ht
    simp only [chamferCorner, Set.mem_setOf_eq, Set.mem_union] at ht ⊢
    tauto
  refine measure_mono_null hsub ?_
  refine (((wideEnd_countable_sweepParam_eq 0).union (wideEnd_countable_sweepParam_eq (1/2))).union
    ((wideEnd_countable_sweepParam_eq (1/2 + lam/2)).union
      (wideEnd_countable_sweepParam_eq (1 - lam/2)))).measure_zero volume

/-- The four corner fractions of the loop parameter. -/
def wideCornerC (lam : ℝ) : Fin 4 → ℝ := ![0, 1/2, 1/2 + lam/2, 1 - lam/2]

lemma wideEnd_chamferCorner_iff (lam t : ℝ) :
    chamferCorner lam t ↔ ∃ i : Fin 4, sweepParam t = wideCornerC lam i := by
  constructor
  · intro h
    simp only [chamferCorner] at h
    rcases h with h | h | h | h
    · exact ⟨0, by simp [wideCornerC, h]⟩
    · exact ⟨1, by simp [wideCornerC, h]⟩
    · exact ⟨2, by simp [wideCornerC, h]⟩
    · exact ⟨3, by simp [wideCornerC, h]⟩
  · rintro ⟨i, hi⟩
    fin_cases i <;> simp only [wideCornerC, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_fin_one] at hi <;>
      simp only [chamferCorner] <;> tauto

lemma wideEnd_ae_not_chamferCorner (lam s δ : ℝ) (hδ : δ ≠ 0) :
    ∀ᵐ u : ℝ, ¬ chamferCorner lam (s - δ * u) := by
  rw [MeasureTheory.ae_iff]
  have hcount : Set.Countable {u : ℝ | chamferCorner lam (s - δ * u)} := by
    refine Set.Countable.mono ?_ (Set.countable_range
      (fun p : Fin 4 × ℤ => (s - (wideCornerC lam p.1 + (p.2 : ℝ)) * period) / δ))
    intro u hu
    simp only [Set.mem_setOf_eq] at hu
    rw [wideEnd_chamferCorner_iff] at hu
    obtain ⟨i, hi⟩ := hu
    obtain ⟨k, hk⟩ := wideEnd_exists_int_of_sweepParam_eq hi
    refine ⟨(i, k), ?_⟩
    beta_reduce
    have h1 : s - (wideCornerC lam i + (k : ℝ)) * period = δ * u := by rw [← hk]; ring
    rw [h1, mul_div_cancel_left₀ u hδ]
  simpa using hcount.measure_zero (volume : Measure ℝ)

open scoped Real

lemma wideEnd_measurable_sweepParam' : Measurable (sweepParam : ℝ → ℝ) :=
  sweepLoopChamfer_sweepParam_measurable

lemma wideEnd_measurable_chamferVel {r : ℝ → Space} (hv : Continuous (velocity r))
    {d : BandArcData} (D : SweepData d) (lam sig : ℝ) :
    Measurable (fun y : ℝ => chamferVel r D lam sig y) := by
  have hsp : Measurable (fun y : ℝ => sweepParam y) := wideEnd_measurable_sweepParam'
  simp only [chamferVel]
  refine Measurable.ite (measurableSet_le hsp measurable_const) ?_ ?_
  · refine (hv.measurable.comp ?_).const_smul (((1 - 2 * lam) * (2 / period)) * sweepW' D sig)
    exact measurable_const.add ((measurable_const.add
      (measurable_const.mul (measurable_const.mul hsp))).mul measurable_const)
  · refine Measurable.ite (measurableSet_le hsp measurable_const) measurable_const ?_
    refine Measurable.ite (measurableSet_le hsp measurable_const) measurable_const measurable_const

/-- The slice of the loop at a fixed sweep parameter is bounded, with a bound given by the
velocity bound and the period. -/
lemma wideEnd_loop_bounded {r : ℝ → Space} {d : BandArcData} (D : SweepData d)
    {lam Λ sig : ℝ} (hΛ : 0 ≤ Λ)
    (hlip : ∀ a b : ℝ,
      ‖sweepLoopChamfer r D lam sig a - sweepLoopChamfer r D lam sig b‖ ≤ Λ * |a - b|) :
    ∀ y : ℝ, ‖sweepLoopChamfer r D lam sig y‖ ≤ Λ * period + ‖sweepLoopChamfer r D lam sig 0‖ := by
  intro y
  have hper : Function.Periodic (fun t : ℝ => sweepLoopChamfer r D lam sig t) period :=
    wideEnd_loopChamfer_add_period r D lam sig
  have hy : y - (⌊y / period⌋ : ℝ) * period = sweepParam y * period := by
    rw [sweepParam, sub_mul, div_mul_cancel₀ y period_ne_zero]
  have h0 : 0 ≤ y - (⌊y / period⌋ : ℝ) * period := by
    rw [hy]; exact mul_nonneg (sweepParam_mem y).1 period_pos.le
  have h1 : y - (⌊y / period⌋ : ℝ) * period ≤ period := by
    rw [hy]
    nlinarith [(sweepParam_mem y).2, period_pos]
  have heq : sweepLoopChamfer r D lam sig y
      = sweepLoopChamfer r D lam sig (y - (⌊y / period⌋ : ℝ) * period) :=
    (hper.sub_int_mul_eq (x := y) (⌊y / period⌋)).symm
  have habs : |y - (⌊y / period⌋ : ℝ) * period| ≤ period := by
    rw [abs_of_nonneg h0]; exact h1
  have hstep := hlip (y - (⌊y / period⌋ : ℝ) * period) 0
  rw [sub_zero] at hstep
  calc ‖sweepLoopChamfer r D lam sig y‖
      = ‖sweepLoopChamfer r D lam sig (y - (⌊y / period⌋ : ℝ) * period)‖ := by rw [heq]
    _ ≤ ‖sweepLoopChamfer r D lam sig (y - (⌊y / period⌋ : ℝ) * period)
            - sweepLoopChamfer r D lam sig 0‖ + ‖sweepLoopChamfer r D lam sig 0‖ := by
          have h := norm_add_le (sweepLoopChamfer r D lam sig (y - (⌊y / period⌋ : ℝ) * period)
            - sweepLoopChamfer r D lam sig 0) (sweepLoopChamfer r D lam sig 0)
          simpa using h
    _ ≤ Λ * period + ‖sweepLoopChamfer r D lam sig 0‖ := by
          have h2 : Λ * |y - (⌊y / period⌋ : ℝ) * period| ≤ Λ * period :=
            mul_le_mul_of_nonneg_left habs hΛ
          linarith

theorem wideEnd_hasDerivAt_sweepSmoothT {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData}
    (D : SweepData d) {lam δ siglo sighi Λ : ℝ} (hδ : δ ≠ 0) (h0 : 0 < lam) (h1 : lam < 1 / 2)
    (hl : 0 < siglo) (hh : sighi < 1) (hΛ : 0 ≤ Λ)
    (hbound : ∀ sig ∈ Set.Icc siglo sighi, ∀ t : ℝ, ‖chamferVel r D lam sig t‖ ≤ Λ)
    (hlip : ∀ sig ∈ Set.Icc siglo sighi, ∀ a b : ℝ,
      ‖sweepLoopChamfer r D lam sig a - sweepLoopChamfer r D lam sig b‖ ≤ Λ * |a - b|)
    {sig s : ℝ} (hsig : sig ∈ Set.Icc siglo sighi) :
    HasDerivAt (fun t : ℝ => sweepSmoothT r D lam δ sig t)
      (∫ u in (-1 : ℝ)..1, sweepBump u • chamferVel r D lam sig (s - δ * u)) s := by
  have hv : Continuous (velocity r) := hr.smooth.continuous_deriv (by simp)
  have hvelM : Measurable (fun y : ℝ => chamferVel r D lam sig y) :=
    wideEnd_measurable_chamferVel hv D lam sig
  have hpair : Measurable (fun y : ℝ => ((sig, y) : ℝ × ℝ)) :=
    (measurable_const (a := sig) : Measurable (fun _ : ℝ => sig)).prod measurable_id
  have hloopM : Measurable (fun y : ℝ => sweepLoopChamfer r D lam sig y) :=
    (sweepLoopChamfer_measurable D hr.continuous lam).comp hpair
  have hlip' := hlip sig hsig
  have hbdd := wideEnd_loop_bounded D hΛ hlip'
  set M₀ : ℝ := Λ * period + ‖sweepLoopChamfer r D lam sig 0‖ with hM₀
  -- the Lipschitz bound of the loop
  have hLip : LipschitzWith (Real.toNNReal Λ) (fun y : ℝ => sweepLoopChamfer r D lam sig y) := by
    refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal Λ hΛ]
    exact hlip' x y
  -- measurability of the two integrands
  have hFmeasM : ∀ x : ℝ, Measurable
      (fun u : ℝ => sweepBump u • sweepLoopChamfer r D lam sig (x - δ * u)) := fun x =>
    continuous_sweepBump.measurable.smul (hloopM.comp
      (measurable_const.sub (measurable_const.mul measurable_id)))
  have hF'meas : AEStronglyMeasurable (fun u : ℝ => sweepBump u • chamferVel r D lam sig (s - δ * u))
      (volume.restrict (Set.uIoc (-1) 1)) :=
    (continuous_sweepBump.measurable.smul (hvelM.comp
      (measurable_const.sub (measurable_const.mul measurable_id)))).aestronglyMeasurable
  -- the integrability of the slice
  have hWle : ∀ u : ℝ, ‖sweepBump u‖ ≤ 1 := by
    intro u
    rw [Real.norm_of_nonneg (sweepBump_nonneg u), sweepBump]
    exact mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
      (Real.smoothTransition.le_one _)
  have hFbound : ∀ u : ℝ, ‖sweepBump u • sweepLoopChamfer r D lam sig (s - δ * u)‖ ≤ M₀ := by
    intro u
    rw [norm_smul]
    calc ‖sweepBump u‖ * ‖sweepLoopChamfer r D lam sig (s - δ * u)‖
        ≤ 1 * M₀ := mul_le_mul (hWle u) (hbdd _) (norm_nonneg _) zero_le_one
      _ = M₀ := one_mul _
  have hFint : IntervalIntegrable (fun u : ℝ => sweepBump u • sweepLoopChamfer r D lam sig (s - δ * u))
      volume (-1) 1 := by
    have hI : ∀ {c d : ℝ}, (volume : Measure ℝ) (Set.Ioc c d) < ⊤ := by
      intro c d
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top
    exact ⟨MeasureTheory.IntegrableOn.of_bound hI (hFmeasM s).aestronglyMeasurable M₀
        (Filter.Eventually.of_forall hFbound),
      MeasureTheory.IntegrableOn.of_bound hI (hFmeasM s).aestronglyMeasurable M₀
        (Filter.Eventually.of_forall hFbound)⟩
  -- the Lipschitz bound of the integrand
  have hLipF : ∀ᵐ t : ℝ ∂(volume : Measure ℝ), t ∈ Set.uIoc (-1) 1 →
      LipschitzOnWith (Real.nnabs (‖sweepBump t‖ * Λ)) (fun x : ℝ => sweepBump t • sweepLoopChamfer r D lam sig (x - δ * t)) Set.univ := by
    refine Filter.Eventually.of_forall (fun t _ => ?_)
    refine LipschitzOnWith.of_dist_le_mul (fun x _ y _ => ?_)
    rw [dist_eq_norm, Real.dist_eq, Real.coe_nnabs, ← smul_sub, norm_smul,
      Real.norm_of_nonneg (sweepBump_nonneg t),
      abs_of_nonneg (mul_nonneg (sweepBump_nonneg t) hΛ)]
    calc sweepBump t * ‖sweepLoopChamfer r D lam sig (x - δ * t)
            - sweepLoopChamfer r D lam sig (y - δ * t)‖
        ≤ sweepBump t * (Λ * |x - δ * t - (y - δ * t)|) :=
          mul_le_mul_of_nonneg_left (hlip' _ _) (sweepBump_nonneg t)
      _ = sweepBump t * Λ * |x - y| := by
          rw [show x - δ * t - (y - δ * t) = x - y by ring]; ring
  -- the bound on the derivative
  have hboundF : ∀ᵐ t : ℝ ∂(volume : Measure ℝ), t ∈ Set.uIoc (-1) 1 →
      ‖sweepBump t • chamferVel r D lam sig (s - δ * t)‖ ≤ ‖sweepBump t‖ * Λ := by
    refine Filter.Eventually.of_forall (fun t _ => ?_)
    rw [norm_smul, Real.norm_of_nonneg (sweepBump_nonneg t)]
    exact mul_le_mul_of_nonneg_left (hbound sig hsig _) (sweepBump_nonneg t)
  have hboundint : IntervalIntegrable (fun t : ℝ => ‖sweepBump t‖ * Λ) volume (-1) 1 := by
    refine Continuous.intervalIntegrable ?_ _ _
    exact (continuous_sweepBump.norm).mul continuous_const
  -- the a.e. derivative of the integrand
  have hdiff : ∀ᵐ t : ℝ ∂(volume : Measure ℝ), t ∈ Set.uIoc (-1) 1 →
      HasDerivAt (fun x : ℝ => sweepBump t • sweepLoopChamfer r D lam sig (x - δ * t))
        (sweepBump t • chamferVel r D lam sig (s - δ * t)) s := by
    filter_upwards [wideEnd_ae_not_chamferCorner lam s δ hδ] with t ht _
    have hinner : HasDerivAt (fun x : ℝ => sweepLoopChamfer r D lam sig (x - δ * t))
        (chamferVel r D lam sig (s - δ * t)) s := by
      have hlin : HasDerivAt (fun x : ℝ => x - δ * t) 1 s := by
        simpa using (hasDerivAt_id s).sub_const (δ * t)
      have hrsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r := hr.smooth.of_le (by simp)
      have h2 := chamferVel_hasDerivAt (lam := lam) (sig := sig) (t := s - δ * t) hrsm D h0 h1 ht
      exact (h2.scomp s hlin).congr_deriv (by rw [one_smul])
    exact hinner.const_smul (sweepBump t)
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_lip
    (a := (-1 : ℝ)) (b := 1) (μ := (volume : Measure ℝ)) (E := Space)
    (F := fun x u => sweepBump u • sweepLoopChamfer r D lam sig (x - δ * u))
    (F' := fun u => sweepBump u • chamferVel r D lam sig (s - δ * u))
    (bound := fun u => ‖sweepBump u‖ * Λ) (x₀ := s) (s := Set.univ)
    Filter.univ_mem (Filter.Eventually.of_forall (fun x => (hFmeasM x).aestronglyMeasurable)) hFint hF'meas hLipF hboundint hdiff
  simpa only [sweepSmoothT] using hmain.2

lemma wideEnd_intervalIntegrable_of_bound {g : ℝ → ℝ} {C : ℝ} (hg : Measurable g)
    (hb : ∀ u : ℝ, ‖g u‖ ≤ C) : IntervalIntegrable g volume (-1) 1 := by
  have hI : ∀ {c d : ℝ}, (volume : Measure ℝ) (Set.Ioc c d) < ⊤ := by
    intro c d
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  exact ⟨MeasureTheory.IntegrableOn.of_bound hI hg.aestronglyMeasurable C
      (Filter.Eventually.of_forall hb),
    MeasureTheory.IntegrableOn.of_bound hI hg.aestronglyMeasurable C
      (Filter.Eventually.of_forall hb)⟩

lemma wideEnd_sweepBump_le_one (u : ℝ) : ‖sweepBump u‖ ≤ 1 := by
  rw [Real.norm_of_nonneg (sweepBump_nonneg u), sweepBump]
  exact mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

/-- The knot's range is bounded. -/
lemma wideEnd_knot_bounded {r : ℝ → Space} (hr : Continuous r)
    (hper : Function.Periodic r period) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x : ℝ, ‖r x‖ ≤ R := by
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := r) (hr.continuousOn)
  refine ⟨max R 0, le_max_right _ _, fun x => ?_⟩
  obtain ⟨y, hy, hxy⟩ := hper.exists_mem_Ico period_pos x 0
  rw [hxy]
  exact (hR y (Set.Ico_subset_Icc_self hy)).trans (le_max_left _ _)


lemma wideEnd_measurable_chamferVel_joint {r : ℝ → Space} (hr : Continuous r)
    (hv : Continuous (velocity r))
    {d : BandArcData} (D : SweepData d) (lam : ℝ) :
    Measurable (fun p : ℝ × ℝ => chamferVel r D lam p.1 p.2) := by
  have hsp : Measurable (fun p : ℝ × ℝ => sweepParam p.2) :=
    sweepLoopChamfer_sweepParam_measurable.comp measurable_snd
  have hta : Measurable (fun p : ℝ × ℝ => taR D p.1) :=
    (sweepLoopChamfer_taR_continuous D).measurable.comp measurable_fst
  have htb : Measurable (fun p : ℝ × ℝ => tbR D p.1) :=
    (sweepLoopChamfer_tbR_continuous D).measurable.comp measurable_fst
  have hw : Measurable (fun p : ℝ × ℝ => sweepW' D p.1) :=
    (sweepLoopChamfer_sweepW'_continuous D).measurable.comp measurable_fst
  have hra : Measurable (fun p : ℝ × ℝ => r (taR D p.1)) := hr.measurable.comp hta
  have hrb : Measurable (fun p : ℝ × ℝ => r (tbR D p.1)) := hr.measurable.comp htb
  have hb1 : Measurable (fun p : ℝ × ℝ =>
      (((1 - 2 * lam) * (2 / period)) * sweepW' D p.1) •
        velocity r (taR D p.1 + (lam + (1 - 2 * lam) * (2 * sweepParam p.2)) * sweepW' D p.1)) := by
    refine Measurable.smul (hw.const_mul _) (hv.measurable.comp ?_)
    exact hta.add ((((hsp.const_mul 2).const_mul (1 - 2 * lam)).const_add lam).mul hw)
  have harc₁ : Measurable (fun p : ℝ × ℝ => r (taR D p.1 + (1 - lam) * sweepW' D p.1)) :=
    hr.measurable.comp (hta.add (measurable_const.mul hw))
  have hch₁ : Measurable (fun p : ℝ × ℝ =>
      (1 - (1 - lam)) • r (taR D p.1) + (1 - lam) • r (tbR D p.1)) :=
    (hra.const_smul (1 - (1 - lam))).add (hrb.const_smul (1 - lam))
  have hb2 : Measurable (fun p : ℝ × ℝ => ((2 / lam) * (1 / period)) •
      ((1 - (1 - lam)) • r (taR D p.1) + (1 - lam) • r (tbR D p.1)
        - r (taR D p.1 + (1 - lam) * sweepW' D p.1))) :=
    (hch₁.sub harc₁).const_smul ((2 / lam) * (1 / period))
  have hb3 : Measurable (fun p : ℝ × ℝ =>
      (-((1 - 2 * lam) / ((1 / 2 - lam) * period))) • (r (tbR D p.1) - r (taR D p.1))) :=
    (hrb.sub hra).const_smul (-((1 - 2 * lam) / ((1 / 2 - lam) * period)))
  have harc₂ : Measurable (fun p : ℝ × ℝ => r (taR D p.1 + lam * sweepW' D p.1)) :=
    hr.measurable.comp (hta.add (measurable_const.mul hw))
  have hch₂ : Measurable (fun p : ℝ × ℝ =>
      (1 - lam) • r (taR D p.1) + lam • r (tbR D p.1)) :=
    (hra.const_smul (1 - lam)).add (hrb.const_smul lam)
  have hb4 : Measurable (fun p : ℝ × ℝ => ((2 / lam) * (1 / period)) •
      (r (taR D p.1 + lam * sweepW' D p.1)
        - ((1 - lam) • r (taR D p.1) + lam • r (tbR D p.1)))) :=
    (harc₂.sub hch₂).const_smul ((2 / lam) * (1 / period))
  rw [show (fun p : ℝ × ℝ => chamferVel r D lam p.1 p.2) = (fun p : ℝ × ℝ =>
      if sweepParam p.2 ≤ 1 / 2 then
        (((1 - 2 * lam) * (2 / period)) * sweepW' D p.1) •
          velocity r (taR D p.1 + (lam + (1 - 2 * lam) * (2 * sweepParam p.2)) * sweepW' D p.1)
      else if sweepParam p.2 ≤ 1 / 2 + lam / 2 then ((2 / lam) * (1 / period)) •
        ((1 - (1 - lam)) • r (taR D p.1) + (1 - lam) • r (tbR D p.1)
          - r (taR D p.1 + (1 - lam) * sweepW' D p.1))
      else if sweepParam p.2 ≤ 1 - lam / 2 then
        (-((1 - 2 * lam) / ((1 / 2 - lam) * period))) • (r (tbR D p.1) - r (taR D p.1))
      else ((2 / lam) * (1 / period)) •
        (r (taR D p.1 + lam * sweepW' D p.1)
          - ((1 - lam) • r (taR D p.1) + lam • r (tbR D p.1)))) from by
    funext p
    simp only [chamferVel, sweepChord', sweepArc']]
  exact Measurable.ite (measurableSet_le hsp measurable_const) hb1
    (Measurable.ite (measurableSet_le hsp measurable_const) hb2
      (Measurable.ite (measurableSet_le hsp measurable_const) hb3 hb4))

/-! ## The measurability of the slice in the sweep parameter -/

lemma wideEnd_aestronglyMeasurable_sweepSmoothT {r : ℝ → Space} (hr : Continuous r)
    {d : BandArcData} (D : SweepData d) (lam δ : ℝ) (t : ℝ) :
    AEStronglyMeasurable (fun sig : ℝ => sweepSmoothT r D lam δ sig t) volume := by
  have hpair : Measurable (fun p : ℝ × ℝ => ((p.1, t - δ * p.2) : ℝ × ℝ)) :=
    Measurable.prod measurable_fst
      (((measurable_const : Measurable (fun _ : ℝ × ℝ => (t : ℝ)))).sub
        ((measurable_const : Measurable (fun _ : ℝ × ℝ => (δ : ℝ))).mul measurable_snd))
  have hL : Measurable (fun (p : ℝ × ℝ) =>
      sweepBump p.2 • sweepLoopChamfer r D lam p.1 (t - δ * p.2)) :=
    (continuous_sweepBump.measurable.comp measurable_snd).smul
      ((sweepLoopChamfer_measurable D hr lam).comp hpair)
  have h2 : StronglyMeasurable (fun sig : ℝ =>
      ∫ u : ℝ, sweepBump u • sweepLoopChamfer r D lam sig (t - δ * u)
        ∂(volume.restrict (Set.uIoc (-1 : ℝ) 1))) :=
    MeasureTheory.StronglyMeasurable.integral_prod_right
      (f := fun (sig : ℝ) (u : ℝ) => sweepBump u • sweepLoopChamfer r D lam sig (t - δ * u))
      hL.stronglyMeasurable
  refine h2.aestronglyMeasurable.congr (Filter.Eventually.of_forall (fun sig => ?_))
  beta_reduce
  have hconv : (∫ u : ℝ, sweepBump u • sweepLoopChamfer r D lam sig (t - δ * u)
      ∂(volume.restrict (Set.uIoc (-1 : ℝ) 1)))
      = ∫ u in (-1 : ℝ)..1, sweepBump u • sweepLoopChamfer r D lam sig (t - δ * u) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1), Set.uIoc_of_le (by norm_num)]
  rw [hconv]
  rfl


/-! ## Auxiliary: bounded interval integrals, and the outer derivative -/


/-- The speed of a smooth knot is bounded. -/
theorem wideEnd_speed_bound {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ∃ V : ℝ, 0 < V ∧ ∀ t : ℝ, ‖velocity r t‖ ≤ V := by
  have hv : Continuous (velocity r) := hr.smooth.continuous_deriv (by simp)
  have hper : Function.Periodic (velocity r) period := by
    intro x
    have h2 : (fun y : ℝ => r (y + period)) = r := funext hr.periodic
    have := deriv_comp_add_const r period x
    rw [h2] at this
    exact this.symm
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := velocity r) (hv.continuousOn)
  refine ⟨max M 1, lt_max_of_lt_right one_pos, fun t => ?_⟩
  obtain ⟨y, hy, hty⟩ := hper.exists_mem_Ico period_pos t 0
  rw [hty]
  exact (hM y (Set.Ico_subset_Icc_self hy)).trans (le_max_left _ _)

theorem sweepFam_wideEnd_estimate_of_matching
    (hmatch : ∀ {r : ℝ → Space}, IsSmoothKnot r →
      ∀ {d : BandArcData} (D : SweepData d),
      ∀ η : ℝ, 0 < η → ∃ θ : ℝ, 0 < θ ∧
        ∀ L : ℝ, 0 < L → ∀ ε' : ℝ, 0 < ε' →
        ∃ (σ₀ lam δ₁ δ₂ : ℝ) (Θ rate : ℝ → ℝ),
          0 < lam ∧ lam ≤ L ∧ lam < 1 / 2 ∧ 0 < δ₁ ∧ δ₁ ≤ L ∧ 0 < δ₂ ∧ δ₂ ≤ L ∧
          1 - ε' < σ₀ ∧ σ₀ < 1 ∧
          (∀ sig ∈ Set.Icc (σ₀ - δ₂) (σ₀ + δ₂),
            period - sweepW' D sig ≤ θ * lam) ∧
          ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ ∧
          (∀ t : ℝ, deriv Θ t = rate t) ∧ (∀ t : ℝ, 0 < rate t) ∧
          (∀ t : ℝ, Θ (t + period) = Θ t + period) ∧
          (∀ t : ℝ, ‖sweepFam r D lam δ₁ δ₂ σ₀ t - r (Θ t)‖ < η) ∧
          (∀ t : ℝ, ‖deriv (fun u : ℝ => sweepFam r D lam δ₁ δ₂ σ₀ u) t -
              rate t • velocity r (Θ t)‖ ≤ η * (rate t * ‖velocity r (Θ t)‖)))
    {r : ℝ → Space} (hr : IsSmoothKnot r) {d : BandArcData} (D : SweepData d) :
    ∀ ε₁ : ℝ, 0 < ε₁ → ∀ L : ℝ, 0 < L →
    ∃ (lam δ₁ δ₂ σ₀ c : ℝ) (Θ : ℝ → ℝ),
      0 < lam ∧ lam ≤ L ∧ 0 < δ₁ ∧ δ₁ ≤ L ∧ 0 < δ₂ ∧ δ₂ ≤ L ∧
      1 - ε₁ < σ₀ ∧ σ₀ < 1 ∧
      (∀ t : ℝ, Θ (t + period) = Θ t + period) ∧
      (∀ t : ℝ, 0 < deriv Θ t) ∧
      (∀ t : ℝ, ‖sweepFam r D lam δ₁ δ₂ σ₀ (Θ t) - r (t + c)‖ < ε₁) ∧
      (∀ t : ℝ, ‖deriv (fun u : ℝ => sweepFam r D lam δ₁ δ₂ σ₀ (Θ u)) t
        - velocity r (t + c)‖ < ε₁) := by
  obtain ⟨V, hVpos, hV⟩ := wideEnd_speed_bound hr
  intro ε₁ hε₁ L hL
  set η : ℝ := min (ε₁ / 2) (ε₁ / (2 * (V + 1))) with hη
  have hηpos : 0 < η := lt_min (by linarith) (by positivity)
  have hη1 : η ≤ ε₁ := (min_le_left _ _).trans (by linarith)
  have hηV : η * V < ε₁ := by
    have h1 : η ≤ ε₁ / (2 * (V + 1)) := min_le_right _ _
    have h2 : η * V ≤ (ε₁ / (2 * (V + 1))) * V := mul_le_mul_of_nonneg_right h1 (le_of_lt hVpos)
    have h3 : (ε₁ / (2 * (V + 1))) * V ≤ ε₁ / 2 := by
      have h4 : (0 : ℝ) < 2 * (V + 1) := by positivity
      rw [div_mul_eq_mul_div, div_le_iff₀ h4]
      nlinarith [hε₁, hVpos]
    linarith
  obtain ⟨θ, hθpos, hmain⟩ := hmatch hr D η hηpos
  obtain ⟨σ₀, lam, δ₁, δ₂, Θ, rate, hlam0, hlamL, hlam1, hδ₁0, hδ₁L, hδ₂0, hδ₂L,
    hσlo, hσhi, _, hΘsm, hΘderiv, hratepos, hΘshift, hpos, hder⟩ :=
    hmain L hL (min ε₁ (1 / 2)) (lt_min hε₁ (by norm_num))
  have hσ1 : 1 - ε₁ < σ₀ := lt_of_le_of_lt (by linarith [min_le_left ε₁ (1 / 2)]) hσlo
  obtain ⟨ρ, hρsm, hρpos, hρshift, hleft, hright, hρderiv⟩ :=
    exists_contDiff_inverse_of_shift (Φ := Θ) (p := period) period_pos hΘsm
      (fun t => by rw [hΘderiv t]; exact hratepos t) hΘshift
  refine ⟨lam, δ₁, δ₂, σ₀, 0, ρ, hlam0, hlamL, hδ₁0, hδ₁L, hδ₂0, hδ₂L, hσ1, hσhi,
    hρshift, hρpos, fun t => ?_, fun t => ?_⟩
  · have hp := hpos (ρ t)
    rw [hright t] at hp
    simpa using lt_of_lt_of_le hp hη1
  · rw [add_zero]
    have hslice : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun u : ℝ => sweepFam r D lam δ₁ δ₂ σ₀ u) :=
      (sweepFam_contDiff_periodic hr.smooth.continuous D lam δ₁ δ₂
        (ne_of_gt hδ₁0) (ne_of_gt hδ₂0)).2.2 σ₀
    have hdiffG : DifferentiableAt ℝ (fun u : ℝ => sweepFam r D lam δ₁ δ₂ σ₀ u) (ρ t) :=
      hslice.differentiable (by simp) (ρ t)
    have hdiffρ : DifferentiableAt ℝ ρ t := hρsm.differentiable (by simp) t
    have hchain : deriv (fun u : ℝ => sweepFam r D lam δ₁ δ₂ σ₀ (ρ u)) t
        = deriv ρ t • deriv (fun u : ℝ => sweepFam r D lam δ₁ δ₂ σ₀ u) (ρ t) :=
      deriv.scomp t hdiffG hdiffρ
    rw [hchain, hρderiv t, hΘderiv (ρ t)]
    have hrate : 0 < rate (ρ t) := hratepos (ρ t)
    have hkey : (rate (ρ t))⁻¹ •
          deriv (fun u : ℝ => sweepFam r D lam δ₁ δ₂ σ₀ u) (ρ t) - velocity r t
        = (rate (ρ t))⁻¹ •
          (deriv (fun u : ℝ => sweepFam r D lam δ₁ δ₂ σ₀ u) (ρ t)
            - rate (ρ t) • velocity r (Θ (ρ t))) := by
      rw [hright t, smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt hrate), one_smul]
    rw [hkey, norm_smul, Real.norm_of_nonneg (le_of_lt (inv_pos.mpr hrate))]
    have hb := hder (ρ t)
    calc (rate (ρ t))⁻¹ *
          ‖deriv (fun u : ℝ => sweepFam r D lam δ₁ δ₂ σ₀ u) (ρ t)
            - rate (ρ t) • velocity r (Θ (ρ t))‖
        ≤ (rate (ρ t))⁻¹ * (η * (rate (ρ t) * ‖velocity r (Θ (ρ t))‖)) :=
          mul_le_mul_of_nonneg_left hb (le_of_lt (inv_pos.mpr hrate))
      _ = η * ‖velocity r (Θ (ρ t))‖ := by field_simp
      _ = η * ‖velocity r t‖ := by rw [hright t]
      _ ≤ η * V := mul_le_mul_of_nonneg_left (hV t) (le_of_lt hηpos)
      _ < ε₁ := hηV


end Work.Drive
