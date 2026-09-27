import Mathlib
import Submission.Work.EKLC7.Defs
import Submission.Work.EKLC7.HeisMul
import Submission.Work.EKLC7.HeisShift
import Submission.Work.EKLRelCross.Instances

namespace Work.EKLC7

open MeasureTheory Topology Filter
open scoped ENNReal
open Work.EKLContract

/-- The one-parameter root subgroup `t ↦ u_ij(t)` is continuous. -/
theorem continuous_uij {i j : Fin 3} (hij : i ≠ j) : Continuous (fun t : ℝ => uij hij t) := by
  refine Continuous.subtype_mk (p := fun M : Matrix (Fin 3) (Fin 3) ℝ => M.det = 1)
    (f := fun s : ℝ => (1 : Matrix (Fin 3) (Fin 3) ℝ) + Matrix.single i j s) ?_ ?_
  refine Continuous.add continuous_const ?_
  apply continuous_matrix
  intro k l
  by_cases hkl : i = k ∧ j = l
  · simp only [Matrix.single_apply, if_pos hkl]; exact continuous_id
  · simp only [Matrix.single_apply, if_neg hkl]; exact continuous_const

/-- `u_ij(0) = 1`. -/
theorem uij_zero {i j : Fin 3} (hij : i ≠ j) : uij hij 0 = 1 :=
  Matrix.SpecialLinearGroup.transvection_coeff_zero hij

/-- `u_ij(a + b) = u_ij(a) u_ij(b)`. -/
theorem uij_add {i j : Fin 3} (hij : i ≠ j) (a b : ℝ) :
    uij hij (a + b) = uij hij a * uij hij b :=
  Matrix.SpecialLinearGroup.transvection_add hij a b

/-- Right translation by `u_ij(t)` is measurable. -/
theorem measurable_mulRight_uij {i j : Fin 3} (hij : i ≠ j) (t : ℝ) :
    Measurable (fun g : SL3 => g * uij hij t) :=
  (continuous_id.mul continuous_const).measurable

theorem PerSub :
    ∀ {i j : Fin 3} (hij : i ≠ j) (ν : MeasureTheory.Measure Work.EKLContract.SL3),
      MeasureTheory.IsFiniteMeasureOnCompacts ν →
      (∀ ε : ℝ, 0 < ε → ∃ τ : ℝ, τ ≠ 0 ∧ |τ| ≤ ε ∧
          ν.map (fun g => g * Work.EKLContract.uij hij τ) = ν) →
      ∀ t : ℝ, ν.map (fun g => g * Work.EKLContract.uij hij t) = ν := by
  intro i j hij ν hν hsmall t
  haveI : IsFiniteMeasureOnCompacts ν := hν
  haveI : IsLocallyFiniteMeasure ν := inferInstance
  -- The set of periods.
  set S : Set ℝ := {s : ℝ | ν.map (fun g => g * uij hij s) = ν} with hSdef
  have hzero : (0 : ℝ) ∈ S := by
    change ν.map (fun g => g * uij hij 0) = ν
    have h1 : (fun g : SL3 => g * uij hij 0) = id := by
      funext g; simp [uij_zero hij]
    rw [h1, Measure.map_id]
  have hadd : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S := by
    intro a ha b hb
    have ha' : ν.map (fun g => g * uij hij a) = ν := by simpa [hSdef] using ha
    have hb' : ν.map (fun g => g * uij hij b) = ν := by simpa [hSdef] using hb
    change ν.map (fun g => g * uij hij (a + b)) = ν
    have key : (fun g : SL3 => g * uij hij (a + b))
        = (fun g : SL3 => g * uij hij b) ∘ (fun g : SL3 => g * uij hij a) := by
      funext g
      simp only [Function.comp_apply]
      rw [uij_add hij a b, mul_assoc]
    rw [key, ← Measure.map_map (measurable_mulRight_uij hij b) (measurable_mulRight_uij hij a),
      ha', hb']
  have hneg : ∀ a ∈ S, -a ∈ S := by
    intro a ha
    have ha' : ν.map (fun g => g * uij hij a) = ν := by simpa [hSdef] using ha
    change ν.map (fun g => g * uij hij (-a)) = ν
    have hcomp : (fun g : SL3 => g * uij hij (-a)) ∘ (fun g : SL3 => g * uij hij a) = id := by
      funext g
      simp only [Function.comp_apply, id_eq]
      rw [mul_assoc, ← uij_add hij a (-a), add_neg_cancel, uij_zero hij, mul_one]
    have h := Measure.map_map (μ := ν) (measurable_mulRight_uij hij (-a))
      (measurable_mulRight_uij hij a)
    rw [ha', hcomp, Measure.map_id] at h
    exact h
  let Ssub : AddSubgroup ℝ :=
    { carrier := S
      add_mem' := fun ha hb => hadd _ ha _ hb
      zero_mem' := hzero
      neg_mem' := fun ha => hneg _ ha }
  -- Continuity of the period test functionals.
  have hcont : ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
      Continuous (fun s : ℝ => ∫ g, f (g * uij hij s) ∂ν) := by
    intro f
    rw [continuous_iff_continuousAt]
    intro s₀
    obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ g : SL3, ‖f g‖ ≤ C := by
      have hb := (f.hasCompactSupport.isCompact_range f.continuous).isBounded
      rw [isBounded_iff_forall_norm_le] at hb
      obtain ⟨D, hD⟩ := hb
      exact ⟨D, fun g => hD (f g) ⟨g, rfl⟩⟩
    set R : ℝ := |s₀| + 1 with hRdef
    set K₀ : Set SL3 := (fun p : SL3 × SL3 => p.1 * p.2) ''
      (tsupport (f : SL3 → ℝ) ×ˢ (uij hij '' Set.Icc (-R) R)) with hK₀def
    have hK₀c : IsCompact K₀ := by
      rw [hK₀def]
      exact ((f.hasCompactSupport.isCompact).prod
        (isCompact_Icc.image (continuous_uij hij))).image continuous_mul
    have hfin : ν K₀ ≠ ⊤ := (IsFiniteMeasureOnCompacts.lt_top_of_isCompact hK₀c).ne
    have hbound_int : Integrable (K₀.indicator (fun _ : SL3 => C)) ν :=
      (integrable_indicator_iff hK₀c.measurableSet).mpr
        (integrableOn_const (μ := ν) (s := K₀) (C := C) hfin)
    refine continuousAt_of_dominated (μ := ν) (x₀ := s₀)
      (F := fun s (g : SL3) => f (g * uij hij s))
      (bound := K₀.indicator (fun _ : SL3 => C)) ?_ ?_ hbound_int ?_
    · filter_upwards with s
      exact (f.continuous.comp (continuous_id.mul continuous_const)).aestronglyMeasurable
    · filter_upwards [Metric.ball_mem_nhds s₀ zero_lt_one] with s hs
      have hsub : |s - s₀| < 1 := by
        rw [Metric.mem_ball, Real.dist_eq] at hs
        exact hs
      have habs : |s| < R := by
        rw [hRdef]
        have h2 : |s| ≤ |s - s₀| + |s₀| := by
          calc |s| = |(s - s₀) + s₀| := by rw [sub_add_cancel]
            _ ≤ |s - s₀| + |s₀| := abs_add_le _ _
        linarith
      have hle := le_of_lt habs
      have hnegmem : -s ∈ Set.Icc (-R) R :=
        ⟨by linarith [(abs_le.mp hle).2], by linarith [(abs_le.mp hle).1]⟩
      filter_upwards with g
      by_cases hg : g ∈ K₀
      · rw [Set.indicator_of_mem hg]
        exact hC (g * uij hij s)
      · have hzero : f (g * uij hij s) = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          intro hmem
          exact hg (by
            rw [hK₀def]
            exact ⟨(g * uij hij s, uij hij (-s)), ⟨hmem, ⟨-s, hnegmem, rfl⟩⟩, by
              show (g * uij hij s) * uij hij (-s) = g
              rw [mul_assoc, ← uij_add hij s (-s), add_neg_cancel, uij_zero hij, mul_one]⟩)
        rw [hzero, Set.indicator_of_notMem hg]
        simp
    · filter_upwards with g
      exact (f.continuous.comp (continuous_const.mul (continuous_uij hij))).continuousAt
  -- The period set is closed.
  have hSclosed : IsClosed S := by
    have heq : S = ⋂ (f : CompactlySupportedContinuousMap SL3 ℝ),
        {s : ℝ | ∫ g, f (g * uij hij s) ∂ν = ∫ g, f g ∂ν} := by
      ext s
      rw [hSdef]
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro hs f
        have h := congrArg (fun (m : Measure SL3) => ∫ g, f g ∂m) hs
        have h1 : ∫ g, f g ∂(ν.map (fun g => g * uij hij s)) = ∫ g, f (g * uij hij s) ∂ν :=
          integral_map (μ := ν) (measurable_mulRight_uij hij s).aemeasurable
            f.continuous.aestronglyMeasurable
        exact h1.symm.trans h
      · intro h
        haveI : (ν.map (fun g => g * uij hij s)).Regular :=
          Measure.Regular.map (μ := ν) (Homeomorph.mulRight (uij hij s))
        refine Measure.ext_of_integral_eq_on_compactlySupported (fun f => ?_)
        have h1 : ∫ g, f g ∂(ν.map (fun g => g * uij hij s)) = ∫ g, f (g * uij hij s) ∂ν :=
          integral_map (μ := ν) (measurable_mulRight_uij hij s).aemeasurable
            f.continuous.aestronglyMeasurable
        rw [h1]
        exact h f
    rw [heq]
    exact isClosed_iInter (fun f => IsClosed.preimage (hcont f) isClosed_singleton)
  -- Arbitrarily small positive periods exist.
  have hsmallpos : ∀ δ : ℝ, 0 < δ → ∃ s : ℝ, s ∈ S ∧ 0 < s ∧ s ≤ δ := by
    intro δ hδ
    obtain ⟨τ, hτne, hτabs, hτS⟩ := hsmall δ hδ
    have hτS' : τ ∈ S := by rw [hSdef]; exact hτS
    rcases lt_or_gt_of_ne hτne with hlt | hgt
    · refine ⟨-τ, hneg τ hτS', neg_pos.mpr hlt, ?_⟩
      rw [abs_of_neg hlt] at hτabs
      exact hτabs
    · exact ⟨τ, hτS', hgt, (abs_le.mp hτabs).2⟩
  -- Hence `S` is dense.
  have hSdense : closure S = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨s, hsS, hspos, hsle⟩ := hsmallpos ε hε
    have hfl : (⌊x / s⌋ : ℝ) * s ≤ x := by
      have h := mul_le_mul_of_nonneg_right (Int.floor_le (x / s)) (le_of_lt hspos)
      rwa [div_mul_cancel₀ x (ne_of_gt hspos)] at h
    have hfr : x < (⌊x / s⌋ : ℝ) * s + s := by
      have h := mul_lt_mul_of_pos_right (Int.lt_floor_add_one (x / s)) hspos
      rw [add_mul, one_mul, div_mul_cancel₀ x (ne_of_gt hspos)] at h
      exact h
    refine ⟨(⌊x / s⌋ : ℝ) * s, ?_, ?_⟩
    · have h := AddSubgroup.zsmul_mem Ssub hsS ⌊x / s⌋
      simp only [zsmul_eq_mul] at h
      exact h
    · rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hfl)]
      linarith
  have hSuniv : S = Set.univ := hSclosed.closure_eq.symm.trans hSdense
  have ht : t ∈ S := by rw [hSuniv]; trivial
  simpa [hSdef] using ht

end Work.EKLC7
