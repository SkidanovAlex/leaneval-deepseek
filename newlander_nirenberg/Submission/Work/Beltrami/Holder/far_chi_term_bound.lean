import Mathlib
import Submission.Work.Beltrami.HolderAux
import Submission.Work.Beltrami.Wkernel
import Submission.Work.Beltrami.norm_setIntegral_bumpC_inv_sq_annulus_le
import Submission.Work.Beltrami.integral_norm_rpow_exterior

namespace Work.Beltrami.Holder

open MeasureTheory Set Filter
open scoped Topology

/-- Far-field bound for the cutoff term of the Beurling integrand: for `δ = ‖x-y‖ > 0`,
`‖∫_{(B(x,2δ) ∪ B(y,2δ))ᶜ} bumpC (u-y) * (u-y)⁻² dA(u)‖ ≤ 12 + π`.

This is the term `(f x - f y) * ∫ bumpC (u-y) (u-y)⁻²` of the Calderón–Zygmund decomposition of
`beurling f x - beurling f y`; it is bounded by a *universal* constant.  The cutoff `bumpC`
equals `1` on the disc of radius `1/2` and vanishes for `‖w‖ ≥ 1`, so the inner part of the
annulus contributes the pure kernel `w ↦ w⁻²`, whose integral vanishes by rotation invariance.

Suggested route: the integrand vanishes for `‖u-y‖ ≥ 1`, so the integral equals the integral
over `S := {u | 2δ ≤ ‖u-y‖ < 1} ∩ Far`, and `S = {u | 2δ ≤ ‖u-y‖ < 1} \ B(x,2δ)`.  Hence
`∫_{Far} bumpC (u-y) (u-y)⁻² = ∫_{w ∈ {2δ ≤ ‖w‖ < 1}} bumpC w · w⁻² − ∫_{S ∩ B(x,2δ)} …`;
the first integral is at most `12` in norm by
`Work.Beltrami.norm_setIntegral_bumpC_inv_sq_annulus_le` with `a = 2δ` (the difference between
the non-strict and the strict annulus is the sphere `‖w‖ = 2δ`, of measure zero), and the second
is bounded by `(2δ)⁻² · volume (B(x,2δ)) = π` because `‖u-y‖ ≥ 2δ` and `bumpC ≤ 1` on it.
Use `MeasureTheory.setIntegral_diff` (or `setIntegral_union`) with the integrability of
`u ↦ bumpC (u-y) * (u-y)⁻²` on the annulus (bounded function on a bounded measurable set), and
translation invariance (`MeasureTheory.MeasurePreserving.setIntegral_preimage_emb` for
`u ↦ u + y`, or `integral_add_right_eq_self` on indicators) to convert the annulus integral
around `y` into the one around `0`. -/
theorem far_chi_term_bound {δ : ℝ} (hδ : 0 < δ) {x y : ℂ} (hxy : ‖x - y‖ = δ) :
    ‖∫ u in (Metric.ball x (2 * δ) ∪ Metric.ball y (2 * δ))ᶜ,
        (Work.Beltrami.bumpC (u - y) : ℂ) * (((u - y) ^ 2)⁻¹) ∂MeasureTheory.volume‖
      ≤ 12 + Real.pi := by
  set f : ℂ → ℂ := fun u => (Work.Beltrami.bumpC (u - y) : ℂ) * (((u - y) ^ 2)⁻¹) with hf
  set T : Set ℂ := Metric.ball x (2 * δ) with hT
  set By : Set ℂ := Metric.ball y (2 * δ) with hBy
  set Far : Set ℂ := (T ∪ By)ᶜ with hFar
  set A : Set ℂ := {u : ℂ | 2 * δ ≤ ‖u - y‖ ∧ ‖u - y‖ < 1} with hA
  have hmeasT : MeasurableSet T := by rw [hT]; exact measurableSet_ball
  have hmeasBy : MeasurableSet By := by rw [hBy]; exact measurableSet_ball
  have hmeasFar : MeasurableSet Far := by rw [hFar]; exact (hmeasT.union hmeasBy).compl
  have hcA : Continuous (fun u : ℂ => ‖u - y‖) :=
    continuous_norm.comp (continuous_id.sub continuous_const)
  have hmeasA : MeasurableSet A := by
    rw [hA]
    exact (isClosed_le continuous_const hcA).measurableSet.inter
      (isOpen_lt hcA continuous_const).measurableSet
  have hmemT : ∀ u : ℂ, u ∈ T ↔ ‖u - x‖ < 2 * δ := by
    intro u; rw [hT, Metric.mem_ball, dist_eq_norm]
  have hmemBy : ∀ u : ℂ, u ∈ By ↔ ‖u - y‖ < 2 * δ := by
    intro u; rw [hBy, Metric.mem_ball, dist_eq_norm]
  have hmemA : ∀ u : ℂ, u ∈ A ↔ 2 * δ ≤ ‖u - y‖ ∧ ‖u - y‖ < 1 := by
    intro u; rw [hA]; exact Iff.rfl
  have hmemFar : ∀ u : ℂ, u ∈ Far ↔ u ∉ T ∧ u ∉ By := by
    intro u
    rw [hFar]
    simp only [Set.mem_compl_iff, Set.mem_union, not_or]
  have hfinT : volume T < ⊤ := by
    rw [hT]; exact MeasureTheory.measure_ball_lt_top
  have hfinA : volume A < ⊤ := by
    refine lt_of_le_of_lt (MeasureTheory.measure_mono ?_)
      (MeasureTheory.measure_ball_lt_top (x := y) (r := 1))
    intro u hu
    rw [Metric.mem_ball, dist_eq_norm]
    exact ((hmemA u).mp hu).2
  have hf_meas : Measurable f := by
    rw [hf]
    refine Measurable.mul ?_ ?_
    · exact Complex.measurable_ofReal.comp
        (Work.Beltrami.bumpC_contDiff.continuous.measurable.comp
          (measurable_id.sub measurable_const))
    · exact ((measurable_id.sub measurable_const).pow_const 2).inv
  -- pointwise norm bound on `A`
  have hptA_le : ∀ u ∈ A, ‖f u‖ ≤ ((2 * δ) ^ 2)⁻¹ := by
    intro u hu
    have huy : 2 * δ ≤ ‖u - y‖ := ((hmemA u).mp hu).1
    have h2d : 0 < 2 * δ := by linarith
    rw [hf, norm_mul]
    have hb : ‖(Work.Beltrami.bumpC (u - y) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Work.Beltrami.bumpC_nonneg _)]
      exact Work.Beltrami.bumpC_le_one _
    have hq : ‖(((u - y) ^ 2)⁻¹ : ℂ)‖ ≤ ((2 * δ) ^ 2)⁻¹ := by
      rw [norm_inv, norm_pow]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (le_of_lt h2d) huy 2)
    calc ‖(Work.Beltrami.bumpC (u - y) : ℂ)‖ * ‖(((u - y) ^ 2)⁻¹ : ℂ)‖
        ≤ 1 * ((2 * δ) ^ 2)⁻¹ := mul_le_mul hb hq (norm_nonneg _) (by norm_num)
      _ = ((2 * δ) ^ 2)⁻¹ := by ring
  have hintA : IntegrableOn f A volume := by
    refine MeasureTheory.IntegrableOn.of_bound hfinA
      (hf_meas.aestronglyMeasurable.mono_measure MeasureTheory.Measure.restrict_le_self)
      (((2 * δ) ^ 2)⁻¹) ?_
    rw [MeasureTheory.ae_restrict_iff' hmeasA]
    exact Filter.Eventually.of_forall (fun u hu => hptA_le u hu)
  -- the indicator identity
  have hpt : ∀ u : ℂ, Far.indicator f u = (A \ T).indicator f u := by
    intro u
    rcases lt_or_ge (‖u - y‖) (2 * δ) with hlt | hge
    · have hBy' : u ∈ By := (hmemBy u).mpr hlt
      have hnotFar : u ∉ Far := fun h => (hmemFar u).mp h |>.2 hBy'
      have hnotA : u ∉ A := fun h => absurd ((hmemA u).mp h).1 (not_le.mpr hlt)
      rw [Set.indicator_of_notMem hnotFar,
          Set.indicator_of_notMem (fun h => hnotA h.1)]
    · by_cases hlt1 : ‖u - y‖ < 1
      · have huA : u ∈ A := (hmemA u).mpr ⟨hge, hlt1⟩
        by_cases huT : u ∈ T
        · have hnotFar : u ∉ Far := fun h => (hmemFar u).mp h |>.1 huT
          rw [Set.indicator_of_notMem hnotFar,
              Set.indicator_of_notMem (fun h => h.2 huT)]
        · have hnotBy : u ∉ By := fun h => absurd ((hmemBy u).mp h) (not_lt.mpr hge)
          have huFar : u ∈ Far := (hmemFar u).mpr ⟨huT, hnotBy⟩
          rw [Set.indicator_of_mem huFar,
              Set.indicator_of_mem (show u ∈ A \ T from ⟨huA, huT⟩)]
      · have hf0 : f u = 0 := by
          rw [hf]
          have hbc : Work.Beltrami.bumpC (u - y) = 0 :=
            Work.Beltrami.bumpC_eq_zero (le_of_not_gt hlt1)
          simp [hbc]
        have hnotAT : u ∉ A \ T := fun h => hlt1 ((hmemA u).mp h.1).2
        by_cases huFar : u ∈ Far
        · rw [Set.indicator_of_mem huFar, hf0, Set.indicator_of_notMem hnotAT]
        · rw [Set.indicator_of_notMem huFar, Set.indicator_of_notMem hnotAT]
  have hI : ∫ u in Far, f u = ∫ u in A \ T, f u := by
    rw [← MeasureTheory.integral_indicator hmeasFar,
      ← MeasureTheory.integral_indicator (hmeasA.diff hmeasT)]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hAsdiff : ∫ u in A \ T, f u = (∫ u in A, f u) - (∫ u in A ∩ T, f u) := by
    have hEq : A \ T = A \ (A ∩ T) := by
      ext u
      simp only [Set.mem_sdiff, Set.mem_inter_iff]
      tauto
    rw [hEq, MeasureTheory.setIntegral_sdiff (hmeasA.inter hmeasT) hintA Set.inter_subset_left]
  -- bound for the annulus integral
  have hmeasA0 : MeasurableSet {w : ℂ | 2 * δ ≤ ‖w‖ ∧ ‖w‖ < 1} :=
    (isClosed_le continuous_const continuous_norm).measurableSet.inter
      (isOpen_lt continuous_norm continuous_const).measurableSet
  have hbound1 : ‖∫ u in A, f u‖ ≤ 12 := by
    have hMP : MeasureTheory.MeasurePreserving (fun w : ℂ => w + y)
        MeasureTheory.volume MeasureTheory.volume :=
      MeasureTheory.MeasurePreserving.add_right (MeasureTheory.volume : MeasureTheory.Measure ℂ) y
        (MeasureTheory.MeasurePreserving.id (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    have hEmb : MeasurableEmbedding (fun w : ℂ => w + y) :=
      (Homeomorph.addRight y).measurableEmbedding
    have htrans := hMP.setIntegral_preimage_emb hEmb f A
    have hpre : (fun w : ℂ => w + y) ⁻¹' A =
        {w : ℂ | 2 * δ ≤ ‖w‖ ∧ ‖w‖ < 1} := by
      ext w
      rw [Set.mem_preimage, hmemA]
      simp [add_sub_cancel_right, Set.mem_ofPred_eq]
    have htrans' : ∫ w in {w : ℂ | 2 * δ ≤ ‖w‖ ∧ ‖w‖ < 1},
          (Work.Beltrami.bumpC w : ℂ) * ((w ^ 2)⁻¹)
        = ∫ u in A, f u := by
      rw [← htrans, hpre]
      refine MeasureTheory.setIntegral_congr_fun hmeasA0 ?_
      intro w hw
      simp only [hf, add_sub_cancel_right]
    rw [← htrans']
    have hae : ({w : ℂ | 2 * δ ≤ ‖w‖ ∧ ‖w‖ < 1} : Set ℂ)
        =ᵐ[MeasureTheory.volume] {w : ℂ | 2 * δ < ‖w‖ ∧ ‖w‖ < 1} := by
      rw [MeasureTheory.ae_eq_set]
      constructor
      · refine MeasureTheory.measure_mono_null ?_
          (MeasureTheory.Measure.addHaar_sphere (MeasureTheory.volume : MeasureTheory.Measure ℂ)
            0 (2 * δ))
        intro w hw
        rw [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_ofPred_eq] at hw
        obtain ⟨⟨hg1, hg2⟩, hnt⟩ := hw
        have hle : ‖w‖ ≤ 2 * δ := by
          by_contra h
          exact hnt ⟨lt_of_not_ge h, hg2⟩
        have hval : ‖w‖ = 2 * δ := le_antisymm hle hg1
        rw [Metric.mem_sphere, dist_eq_norm]
        simpa using hval
      · have hempty : ({w : ℂ | 2 * δ < ‖w‖ ∧ ‖w‖ < 1} : Set ℂ)
            \ {w : ℂ | 2 * δ ≤ ‖w‖ ∧ ‖w‖ < 1} = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          intro w hw
          rw [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_ofPred_eq] at hw
          exact hw.2 ⟨le_of_lt hw.1.1, hw.1.2⟩
        rw [hempty, measure_empty]
    rw [MeasureTheory.setIntegral_congr_set
      (f := fun w : ℂ => (Work.Beltrami.bumpC w : ℂ) * ((w ^ 2)⁻¹)) hae]
    exact Work.Beltrami.norm_setIntegral_bumpC_inv_sq_annulus_le (by linarith : 0 < 2 * δ)
  -- bound for the part inside `B(x,2δ)`
  have hbound2 : ‖∫ u in A ∩ T, f u‖ ≤ Real.pi := by
    have hfinAT : volume (A ∩ T) < ⊤ :=
      lt_of_le_of_lt (MeasureTheory.measure_mono (Set.inter_subset_right)) hfinT
    have h1 := MeasureTheory.norm_setIntegral_le_of_norm_le_const hfinAT
      (fun u hu => hptA_le u hu.1)
    have hvolT : volume.real T = (2 * δ) ^ 2 * Real.pi := by
      rw [hT, MeasureTheory.Measure.real_def, Complex.volume_ball, ENNReal.toReal_mul,
        ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)]
      simp [← NNReal.coe_real_pi]
    have hreal : volume.real (A ∩ T) ≤ volume.real T := by
      rw [MeasureTheory.Measure.real_def, MeasureTheory.Measure.real_def]
      exact ENNReal.toReal_mono (ne_of_lt hfinT)
        (MeasureTheory.measure_mono Set.inter_subset_right)
    calc ‖∫ u in A ∩ T, f u‖ ≤ ((2 * δ) ^ 2)⁻¹ * volume.real (A ∩ T) := h1
      _ ≤ ((2 * δ) ^ 2)⁻¹ * volume.real T :=
            mul_le_mul_of_nonneg_left hreal (by positivity)
      _ = ((2 * δ) ^ 2)⁻¹ * ((2 * δ) ^ 2 * Real.pi) := by rw [hvolT]
      _ = Real.pi := by
            rw [← mul_assoc, inv_mul_cancel₀ (by positivity : (2 * δ) ^ 2 ≠ 0), one_mul]
  calc ‖∫ u in Far, f u‖
      = ‖(∫ u in A, f u) - (∫ u in A ∩ T, f u)‖ := by rw [hI, hAsdiff]
    _ ≤ ‖∫ u in A, f u‖ + ‖∫ u in A ∩ T, f u‖ :=
          norm_sub_le (∫ u in A, f u) (∫ u in A ∩ T, f u)
    _ ≤ 12 + Real.pi := add_le_add hbound1 hbound2

end Work.Beltrami.Holder
