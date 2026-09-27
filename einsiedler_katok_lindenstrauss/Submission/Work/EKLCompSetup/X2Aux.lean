import Mathlib
import Submission.Work.EKLComp.C8Defs
import Submission.Work.EKLCompLeaf.measurable_nu
import Submission.Work.EKLCompSetup.tendsto_measure_ballU_gt
import Submission.Work.EKLCompSetup.tendsto_leafMass_gt
import Submission.Work.EKLCompSetup.setIntegral_one_sub_indicator_eq

/-!
# Auxiliary lemmas for the construction of the maximal-inequality set `X₂`

(EKL §4.2, "Construction of `X₂`".)  Main file: `Submission/Work/EKLCompSetup/exists_X2.lean`.

The set is `X₂ = {x ∈ X'' | ∀ R > 0, (1-ε²)·ν_x(ballU R) ≤ ν_x(ballU R ∩ {g | g·x ∈ X₁})}`, and it
has `μ X₂ > 1 - C ε²`.  The maximal inequality `hML` (the frozen component `P_MaxLeaf`) is applied
to the *complement* `f = 1 - 1_{X₁}` of the Luzin compact set `X₁` with `α = ε²`:

* `leafMass_le`, `leafMass_ne_top`: the leaf mass of a ball is at most the mass of the ball;
* `X₂set`: the density condition imposed at *rational* radii, which makes the set measurable
  (`measurableSet_X₂set`); `mem_X₂set_iff` passes from rational to real radii using the
  right-continuity of `R ↦ ν_x(ballU R)` and `R ↦ leafMass ν X₁ R x` (the delegated lemmas
  `tendsto_measure_ballU_gt`, `tendsto_leafMass_gt`);
* `mem_bad_of_not_mem_X₂set`: for `x ∈ X''` outside `X₂set`, the complement of `X₁` occupies more
  than an `ε²`-fraction of the `ballU R`-leaf mass of `x`, so that `x` lies in the maximal set
  (using `setIntegral_one_sub_indicator_eq` to convert the Bochner integral of the indicator to
  the leaf mass);
* `measure_X₂set_ge`: the resulting measure bound `1 - C ε² ≤ μ (X'' ∩ X₂set ν X₁ ε)`.

The only place where the hypothesis `ε ≤ 1` of the paper's setting would be used is the trivial
case `ε = 1`, where `X₂ = X''`; the argument below never needs it.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace Work.EKLCompSetup

open Work.EKLContract

theorem leafMass_le (ν : X3 → MeasureTheory.Measure SL3) (X₁ : Set X3) (R : ℝ) (x : X3) :
    Work.EKLComp.leafMass ν X₁ R x ≤ ν x (Work.EKLContract.ballU Work.EKLComp.h01 R) := by
  have hK : MeasurableSet (Work.EKLContract.ballU Work.EKLComp.h01 R) :=
    (Work.EKLComp.isCompact_ballU R).measurableSet
  rw [Work.EKLComp.leafMass, ← MeasureTheory.lintegral_indicator hK]
  refine le_trans (lintegral_mono fun g => ?_)
    (le_of_eq (MeasureTheory.lintegral_indicator_one hK))
  by_cases hg : g ∈ Work.EKLContract.ballU Work.EKLComp.h01 R
  · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg]
    exact Set.indicator_le_self X₁ (fun _ => (1:ℝ≥0∞)) (g • x)
  · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg]

theorem leafMass_ne_top {ν : X3 → MeasureTheory.Measure SL3}
    (hν : ∀ x, MeasureTheory.IsFiniteMeasureOnCompacts (ν x)) (X₁ : Set X3) (R : ℝ) (x : X3) :
    Work.EKLComp.leafMass ν X₁ R x ≠ ⊤ :=
  ne_top_of_le_ne_top
    (IsFiniteMeasureOnCompacts.lt_top_of_isCompact (μ := ν x) (Work.EKLComp.isCompact_ballU R)).ne
    (leafMass_le ν X₁ R x)

def X₂set (ν : X3 → MeasureTheory.Measure SL3) (X₁ : Set X3) (ε : ℝ) : Set X3 :=
  {x | ∀ q : ℚ, 0 < q →
    (1 - ε^2) * (ν x (Work.EKLContract.ballU Work.EKLComp.h01 (q:ℝ))).toReal
      ≤ (Work.EKLComp.leafMass ν X₁ (q:ℝ) x).toReal}

theorem measurableSet_X₂set
    {μ : MeasureTheory.Measure X3}
    {ν : X3 → MeasureTheory.Measure SL3}
    {X' X₁ : Set X3}
    (hL : IsLeafwise μ (Uij Work.EKLComp.h01) ν X')
    (hν : ∀ x, MeasureTheory.IsFiniteMeasureOnCompacts (ν x))
    (hleaf : ∀ R : ℝ, Measurable fun x => (Work.EKLComp.leafMass ν X₁ R x).toReal)
    (ε : ℝ) : MeasurableSet (X₂set ν X₁ ε) := by
  have hνmeas : ∀ R : ℝ, Measurable fun x : X3 =>
      (ν x (Work.EKLContract.ballU Work.EKLComp.h01 R)).toReal :=
    fun R => (Work.EKLCompLeaf.measurable_apply_isCompact hL.measurable hν
      (Work.EKLComp.isCompact_ballU R)).ennreal_toReal
  have hset : X₂set ν X₁ ε = ⋂ (q : {q : ℚ // 0 < q}),
      {x : X3 | (1 - ε^2) * (ν x (Work.EKLContract.ballU Work.EKLComp.h01 ((q:ℚ):ℝ))).toReal
        ≤ (Work.EKLComp.leafMass ν X₁ ((q:ℚ):ℝ) x).toReal} := by
    ext x
    simp only [X₂set, Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro h q
      exact h q q.2
    · intro h q hq
      exact h ⟨q, hq⟩
  rw [hset]
  refine MeasurableSet.iInter fun q => measurableSet_le (((hνmeas _).const_mul _)) (hleaf _)

theorem tendsto_ballU_toReal_gt {ν : MeasureTheory.Measure SL3}
    (hν : MeasureTheory.IsFiniteMeasureOnCompacts ν) (R : ℝ) :
    Filter.Tendsto (fun r : ℝ => (ν (Work.EKLContract.ballU Work.EKLComp.h01 r)).toReal)
      (nhdsWithin R (Set.Ioi R))
      (nhds ((ν (Work.EKLContract.ballU Work.EKLComp.h01 R)).toReal)) := by
  haveI := hν
  exact (ENNReal.tendsto_toReal
      (IsFiniteMeasureOnCompacts.lt_top_of_isCompact (Work.EKLComp.isCompact_ballU R)).ne).comp
    (tendsto_measure_ballU_gt hν R)

theorem tendsto_leafMass_toReal_gt {ν : X3 → MeasureTheory.Measure SL3}
    (hν : ∀ x, MeasureTheory.IsFiniteMeasureOnCompacts (ν x))
    {X₁ : Set X3} (hX₁ : MeasurableSet X₁) (R : ℝ) (x : X3) :
    Filter.Tendsto (fun r : ℝ => (Work.EKLComp.leafMass ν X₁ r x).toReal)
      (nhdsWithin R (Set.Ioi R)) (nhds ((Work.EKLComp.leafMass ν X₁ R x).toReal)) :=
  (ENNReal.tendsto_toReal (leafMass_ne_top hν X₁ R x)).comp
    (tendsto_leafMass_gt hν hX₁ R x)

theorem mem_X₂set_iff {ν : X3 → MeasureTheory.Measure SL3}
    (hν : ∀ x, MeasureTheory.IsFiniteMeasureOnCompacts (ν x))
    {X₁ : Set X3} (hX₁ : MeasurableSet X₁) {ε : ℝ} (x : X3) :
    x ∈ X₂set ν X₁ ε ↔ ∀ R : ℝ, 0 < R →
      (1 - ε^2) * (ν x (Work.EKLContract.ballU Work.EKLComp.h01 R)).toReal
        ≤ (Work.EKLComp.leafMass ν X₁ R x).toReal := by
  constructor
  · intro hx R hR
    have hpos : ∀ n : ℕ, R < R + ((n:ℝ)+1)⁻¹ := fun n => lt_add_of_pos_right R (by positivity)
    choose q hq1 hq2 using fun n : ℕ => exists_rat_btwn (hpos n)
    have hupper : Tendsto (fun n : ℕ => R + ((n:ℝ)+1)⁻¹) atTop (nhds R) := by
      have h1 : Tendsto (fun n : ℕ => ((n:ℝ)+1)) atTop atTop :=
        Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
      have h2 : Tendsto (fun n : ℕ => ((n:ℝ)+1)⁻¹) atTop (nhds 0) :=
        tendsto_inv_atTop_zero.comp h1
      simpa using tendsto_const_nhds.add h2
    have hlim : Tendsto (fun n : ℕ => (q n : ℝ)) atTop (nhds R) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
        (fun n => le_of_lt (hq1 n)) (fun n => le_of_lt (hq2 n))
    have hqtend : Tendsto (fun n : ℕ => (q n : ℝ)) atTop (nhdsWithin R (Set.Ioi R)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall fun n => hq1 n⟩
    have hA := (tendsto_ballU_toReal_gt (hν x) R).comp hqtend
    have hB := (tendsto_leafMass_toReal_gt hν hX₁ R x).comp hqtend
    have hqpos : ∀ n, (0:ℚ) < q n := fun n => Rat.cast_pos.mp (lt_trans hR (hq1 n))
    exact le_of_tendsto_of_tendsto (hA.const_mul (1 - ε^2)) hB
      (Eventually.of_forall fun n => hx (q n) (hqpos n))
  · intro h q hq
    exact h (q:ℝ) (Rat.cast_pos.mpr hq)

theorem mem_bad_of_not_mem_X₂set {ν : X3 → MeasureTheory.Measure SL3}
    (hν : ∀ x, MeasureTheory.IsFiniteMeasureOnCompacts (ν x))
    {X' X'' X₁ : Set X3} (hX₁meas : MeasurableSet X₁) (hX''sub : X'' ⊆ X')
    {ε : ℝ} {x : X3} (hx : x ∈ X'') (hx2 : x ∉ X₂set ν X₁ ε) :
    x ∈ X' ∧ ∃ r : ℝ, 0 < r ∧
      ε^2 * (ν x (Work.EKLContract.ballU Work.EKLComp.h01 r)).toReal
        < ∫ g in Work.EKLContract.ballU Work.EKLComp.h01 r,
            (X₁ᶜ).indicator (fun _ => (1:ℝ)) (g • x) ∂(ν x) := by
  refine ⟨hX''sub hx, ?_⟩
  have hx2' : ∃ q : ℚ, 0 < q ∧ (Work.EKLComp.leafMass ν X₁ (q:ℝ) x).toReal
      < (1 - ε^2) * (ν x (Work.EKLContract.ballU Work.EKLComp.h01 (q:ℝ))).toReal := by
    simp only [X₂set, Set.mem_ofPred_eq] at hx2
    push_neg at hx2
    exact hx2
  obtain ⟨q, hq, hlt⟩ := hx2'
  refine ⟨(q:ℝ), Rat.cast_pos.mpr hq, ?_⟩
  have hK : MeasurableSet (Work.EKLContract.ballU Work.EKLComp.h01 (q:ℝ)) :=
    (Work.EKLComp.isCompact_ballU (q:ℝ)).measurableSet
  have hpoint : ∀ g : SL3, (X₁ᶜ).indicator (fun _ => (1:ℝ)) (g • x)
      = 1 - X₁.indicator (fun _ => (1:ℝ)) (g • x) := by
    intro g
    by_cases hg : g • x ∈ X₁
    · rw [Set.indicator_of_notMem (by simpa using hg), Set.indicator_of_mem hg]
      norm_num
    · rw [Set.indicator_of_mem (by simpa using hg), Set.indicator_of_notMem hg]
      norm_num
  have key : ∫ g in Work.EKLContract.ballU Work.EKLComp.h01 (q:ℝ),
        (X₁ᶜ).indicator (fun _ => (1:ℝ)) (g • x) ∂(ν x)
      = (ν x (Work.EKLContract.ballU Work.EKLComp.h01 (q:ℝ))).toReal
        - (Work.EKLComp.leafMass ν X₁ (q:ℝ) x).toReal := by
    rw [MeasureTheory.setIntegral_congr_fun hK (fun g _ => hpoint g),
      setIntegral_one_sub_indicator_eq hν hX₁meas (q:ℝ) x]
  rw [key]
  nlinarith [hlt]

theorem measure_X₂set_ge
    {μ : MeasureTheory.Measure X3} [MeasureTheory.IsProbabilityMeasure μ]
    {ν : X3 → MeasureTheory.Measure SL3} {X' X'' X₁ : Set X3}
    (hL : IsLeafwise μ (Uij Work.EKLComp.h01) ν X')
    (hν : ∀ x, MeasureTheory.IsFiniteMeasureOnCompacts (ν x))
    (hX''meas : MeasurableSet X'') (hX''sub : X'' ⊆ X') (hX''conull : μ X''ᶜ = 0)
    (hX₁meas : MeasurableSet X₁)
    (hleaf : ∀ R : ℝ, Measurable fun x => (Work.EKLComp.leafMass ν X₁ R x).toReal)
    {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε)
    (hX₁ : 1 - ε^4 ≤ (μ X₁).toReal)
    (hML : ∀ (f : X3 → ℝ), Measurable f → (∀ x, 0 ≤ f x) →
      MeasureTheory.Integrable f μ →
      ∀ α : ℝ, 0 < α →
        μ {x | x ∈ X' ∧ ∃ r : ℝ, 0 < r ∧
            α * (ν x (Work.EKLContract.ballU Work.EKLComp.h01 r)).toReal
              < ∫ g in Work.EKLContract.ballU Work.EKLComp.h01 r, f (g • x) ∂(ν x)}
          ≤ ENNReal.ofReal (C * (∫ x, f x ∂μ) / α)) :
    1 - C * ε^2 ≤ (μ (X'' ∩ X₂set ν X₁ ε)).toReal := by
  have htop : μ Set.univ ≠ ⊤ := by rw [measure_univ]; exact ENNReal.one_ne_top
  set f : X3 → ℝ := fun y => (X₁ᶜ).indicator (fun _ => (1:ℝ)) y with hfdef
  have hfmeas : Measurable f :=
    (measurable_const : Measurable fun _ : X3 => (1:ℝ)).indicator hX₁meas.compl
  have hfnonneg : ∀ y, 0 ≤ f y := by
    intro y
    have hy : f y = (X₁ᶜ).indicator (fun _ => (1:ℝ)) y := by rw [hfdef]
    rw [hy]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) y
  have hfint : MeasureTheory.Integrable f μ := by
    rw [hfdef]
    exact (MeasureTheory.integrable_const (1:ℝ)).indicator hX₁meas.compl
  have hbad := hML f hfmeas hfnonneg hfint (ε^2) (by positivity)
  set hBset : Set X3 := {x : X3 | x ∈ X' ∧ ∃ r : ℝ, 0 < r ∧
      ε^2 * (ν x (Work.EKLContract.ballU Work.EKLComp.h01 r)).toReal
        < ∫ g in Work.EKLContract.ballU Work.EKLComp.h01 r, f (g • x) ∂(ν x)} with hBdef
  have hsub : (X'' ∩ X₂set ν X₁ ε)ᶜ ⊆ X''ᶜ ∪ hBset := by
    intro x hx
    by_cases hx' : x ∈ X''
    · refine Or.inr ?_
      have hb := mem_bad_of_not_mem_X₂set hν hX₁meas hX''sub hx' (fun h => hx ⟨hx', h⟩)
      simpa only [hBdef, hfdef, Set.mem_ofPred_eq] using hb
    · exact Or.inl hx'
  have hmeasure : μ ((X'' ∩ X₂set ν X₁ ε)ᶜ) ≤ μ hBset := by
    refine le_trans (measure_mono hsub) ?_
    refine le_trans (measure_union_le _ _) (le_of_eq ?_)
    rw [hX''conull, zero_add]
  have hbadB : μ hBset ≤ ENNReal.ofReal (C * (∫ x, f x ∂μ) / ε^2) := by
    simpa only [hBdef] using hbad
  have hle : (μ ((X'' ∩ X₂set ν X₁ ε)ᶜ)).toReal ≤
      (ENNReal.ofReal (C * (∫ x, f x ∂μ) / ε^2)).toReal :=
    ENNReal.toReal_mono ENNReal.ofReal_ne_top (hmeasure.trans hbadB)
  have hInt0 : ∫ y, (X₁ᶜ).indicator (fun _ => (1:ℝ)) y ∂μ = (μ X₁ᶜ).toReal := by
    rw [MeasureTheory.integral_indicator hX₁meas.compl, MeasureTheory.setIntegral_const]
    simp [MeasureTheory.Measure.real_def]
  have hInt : ∫ x, f x ∂μ = (μ X₁ᶜ).toReal := by simpa only [hfdef] using hInt0
  have hnn : 0 ≤ C * (∫ x, f x ∂μ) / ε^2 := by
    apply div_nonneg
    · exact mul_nonneg hC.le (MeasureTheory.integral_nonneg hfnonneg)
    · positivity
  have hreal : (ENNReal.ofReal (C * (∫ x, f x ∂μ) / ε^2)).toReal
      = C * (μ X₁ᶜ).toReal / ε^2 := by
    rw [ENNReal.toReal_ofReal hnn, hInt]
  have hmass : (μ X₁ᶜ).toReal ≤ ε^4 := by
    have hne : μ X₁ ≠ ⊤ :=
      ne_top_of_le_ne_top htop (measure_mono (Set.subset_univ X₁))
    have h2 : (μ X₁ᶜ).toReal = 1 - (μ X₁).toReal := by
      rw [MeasureTheory.measure_compl hX₁meas hne,
        ENNReal.toReal_sub_of_le (measure_mono (Set.subset_univ X₁)) htop]
      rw [measure_univ, ENNReal.toReal_one]
    rw [h2]
    linarith
  have hfinal : C * (μ X₁ᶜ).toReal / ε^2 ≤ C * ε^2 := by
    rw [div_le_iff₀ (by positivity)]
    calc C * (μ X₁ᶜ).toReal ≤ C * ε^4 := mul_le_mul_of_nonneg_left hmass hC.le
      _ = C * ε^2 * ε^2 := by ring
  have hbound : (μ (X'' ∩ X₂set ν X₁ ε)ᶜ).toReal ≤ C * ε^2 :=
    le_trans (le_trans hle (le_of_eq hreal)) hfinal
  have hX₂meas : MeasurableSet (X'' ∩ X₂set ν X₁ ε) :=
    hX''meas.inter (measurableSet_X₂set hL hν hleaf ε)
  have hne1 : μ (X'' ∩ X₂set ν X₁ ε) ≠ ⊤ :=
    ne_top_of_le_ne_top htop (measure_mono (Set.subset_univ _))
  have hne2 : μ (X'' ∩ X₂set ν X₁ ε)ᶜ ≠ ⊤ :=
    ne_top_of_le_ne_top htop (measure_mono (Set.subset_univ _))
  have hsum : (μ (X'' ∩ X₂set ν X₁ ε)).toReal + (μ (X'' ∩ X₂set ν X₁ ε)ᶜ).toReal = 1 := by
    have h1 : μ (X'' ∩ X₂set ν X₁ ε) + μ (X'' ∩ X₂set ν X₁ ε)ᶜ = μ Set.univ :=
      MeasureTheory.measure_add_measure_compl hX₂meas
    rw [measure_univ] at h1
    rw [← ENNReal.toReal_add hne1 hne2, h1, ENNReal.toReal_one]
  linarith

end Work.EKLCompSetup
