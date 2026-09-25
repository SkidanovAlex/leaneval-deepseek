import Mathlib
import Submission.Commons.Analysis.Fourier.nested_scales_maximal_l2_real
import Submission.Commons.Analysis.Fourier.boundary_layer_l2
import Submission.Commons.Analysis.Fourier.bandSum_indicatorSum_l2

namespace Commons.Analysis.Fourier

open MeasureTheory Filter
open scoped ENNReal FourierTransform ComplexInnerProductSpace Topology

noncomputable section

set_option maxHeartbeats 8000000

lemma linearization_bound_dual {M : ℕ} (hM : 1 ≤ M) (C : Fin M → Set ℝ)
    (hmeas : ∀ i, MeasurableSet (C i)) (hbd : ∀ i, Bornology.IsBounded (C i))
    (D : ℝ)
    (hdual : ∀ (J : Finset (Fin M)) (u : Fin M → ℝ → ℂ),
      (∀ j ∈ J, MeasureTheory.MemLp (u j) 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ)) →
      (∀ j ∈ J, ∀ k ∈ J, j ≠ k → ∀ x : ℝ, u j x * star (u k x) = 0) →
      Real.sqrt (∫ x : ℝ, ‖∑ j ∈ J, bandOp (C j) (u j) x‖ ^ 2)
        ≤ D * Real.sqrt (∑ j ∈ J, ∫ x : ℝ, ‖u j x‖ ^ 2))
    (f : ℝ → ℂ) (hf1 : MeasureTheory.Integrable f)
    (hf2 : MeasureTheory.MemLp f 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    (w : ℝ → ℝ) (hw0 : ∀ x, 0 ≤ w x) (hw1 : MeasureTheory.Integrable w)
    (hw2 : MeasureTheory.MemLp w 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    (∫ x : ℝ, w x * (⨆ i : Fin M, ‖bandOp (C i) f x‖))
      ≤ D * Real.sqrt (∫ x : ℝ, w x ^ 2) * Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2) := by
  classical
  have hD : 0 ≤ D := by
    set u₀ : ℝ → ℂ := Set.indicator (Set.Icc (0:ℝ) 1) (fun _ => (1:ℂ)) with hu₀def
    have hu₀_memLp : MemLp u₀ 2 volume := by
      rw [hu₀def]
      exact memLp_indicator_const 2 measurableSet_Icc (1:ℂ)
        (Or.inr (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
    have hu₀_sq : ∀ x : ℝ, ‖u₀ x‖ ^ 2
        = (Set.Icc (0:ℝ) 1).indicator (fun _ => (1:ℝ)) x := by
      intro x
      by_cases hx : x ∈ Set.Icc (0:ℝ) 1
      · rw [hu₀def, Set.indicator_of_mem hx, Set.indicator_of_mem hx]; simp
      · rw [hu₀def, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; simp
    have hS : (∫ x : ℝ, ‖u₀ x‖ ^ 2) = 1 := by
      simp_rw [hu₀_sq]
      rw [integral_indicator measurableSet_Icc, setIntegral_const,
        MeasureTheory.measureReal_def, Real.volume_Icc]
      simp
    set u : Fin M → ℝ → ℂ := fun j => if j = ⟨0, hM⟩ then u₀ else 0 with hudef0
    have hu : ∀ j ∈ ({⟨0, hM⟩} : Finset (Fin M)), MemLp (u j) 2 volume := by
      intro j hj
      rw [Finset.mem_singleton] at hj
      subst hj
      simpa [hudef0] using hu₀_memLp
    have hdisj0 : ∀ j ∈ ({⟨0, hM⟩} : Finset (Fin M)), ∀ k ∈ ({⟨0, hM⟩} : Finset (Fin M)),
        j ≠ k → ∀ x : ℝ, u j x * star (u k x) = 0 := by
      intro j hj k hk hjk x
      rw [Finset.mem_singleton] at hj hk
      exact absurd (hj.trans hk.symm) hjk
    have h := hdual {⟨0, hM⟩} u hu hdisj0
    have hsum : (∑ j ∈ ({⟨0, hM⟩} : Finset (Fin M)), ∫ x : ℝ, ‖u j x‖ ^ 2) = 1 := by
      rw [Finset.sum_singleton]
      have : u ⟨0, hM⟩ = u₀ := by simp [hudef0]
      rw [this, hS]
    rw [hsum, Real.sqrt_one, mul_one] at h
    exact le_trans (Real.sqrt_nonneg _) h
  classical
  haveI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  set F : Fin M → ℝ → ℂ := fun i => bandOp (C i) f with hF
  have hFcont : ∀ i, Continuous (F i) := fun i => bandOp_cont (C i) (hmeas i) (hbd i) f hf1
  have hFmem : ∀ i, MemLp (F i) 2 volume :=
    fun i => bandOp_memLp (C i) (hmeas i) (hbd i) f hf1 hf2
  set G : ℝ → ℝ := fun x => ⨆ i : Fin M, ‖F i x‖ with hG
  have hGbdd : ∀ x : ℝ, BddAbove (Set.range fun i : Fin M => ‖F i x‖) :=
    fun x => (Set.finite_range _).bddAbove
  have hGle : ∀ x (i : Fin M), ‖F i x‖ ≤ G x := fun x i => le_ciSup (hGbdd x) i
  have hGmeas : Measurable G := by
    rw [hG]
    exact Measurable.iSup (fun i => (hFcont i).norm.measurable)
  have hGnonneg : ∀ x, 0 ≤ G x :=
    fun x => le_trans (norm_nonneg _) (hGle x ⟨0, hM⟩)
  -- the phase
  set sg : Fin M → ℝ → ℂ := fun i x => if F i x = 0 then 1
      else (starRingEnd ℂ) (F i x) / ((‖F i x‖ : ℝ) : ℂ) with hsg
  have hsg_apply : ∀ i x, sg i x
      = if F i x = 0 then 1 else (starRingEnd ℂ) (F i x) / ((‖F i x‖ : ℝ) : ℂ) :=
    fun i x => rfl
  have hsg_meas : ∀ i, Measurable (sg i) := by
    intro i
    rw [hsg]
    refine Measurable.ite ?_ measurable_const ?_
    · exact (measurableSet_singleton (0:ℂ)).preimage (hFcont i).measurable
    · exact (Complex.continuous_conj.comp (hFcont i)).measurable.div
        (Complex.measurable_ofReal.comp (hFcont i).norm.measurable)
  have hsg_norm : ∀ i x, ‖sg i x‖ ≤ 1 := by
    intro i x
    rw [hsg_apply]
    by_cases h : F i x = 0
    · rw [if_pos h]; simp
    · rw [if_neg h, norm_div, Complex.norm_conj]
      have hpos : (0:ℝ) < ‖F i x‖ := norm_pos_iff.mpr h
      rw [show ‖((‖F i x‖ : ℝ) : ℂ)‖ = ‖F i x‖ from by
        rw [show ‖((‖F i x‖ : ℝ) : ℂ)‖ = |‖F i x‖| by simp, abs_of_nonneg (norm_nonneg _)],
        div_self (ne_of_gt hpos)]
  have hsg_mul : ∀ i x, sg i x * F i x = ((‖F i x‖ : ℝ) : ℂ) := by
    intro i x
    rw [hsg_apply]
    by_cases h : F i x = 0
    · rw [if_pos h, h, norm_zero]; simp
    · rw [if_neg h, div_mul_eq_mul_div]
      rw [show (starRingEnd ℂ) (F i x) * F i x
          = ((‖F i x‖ : ℝ) : ℂ) * ((‖F i x‖ : ℝ) : ℂ) from by
        rw [RCLike.conj_mul, sq]
        rfl]
      rw [← Complex.ofReal_mul, ← Complex.ofReal_div]
      congr 1
      field_simp
  -- the partition
  set A : Fin M → ℝ → ℝ := fun i x => if (∀ j : Fin M, ‖F j x‖ ≤ ‖F i x‖) then 1 else 0
    with hA
  set B : Fin M → ℝ → ℝ := fun i x => ∏ j : Fin M, (if i < j ∧ G x = ‖F j x‖ then 0 else 1)
    with hB
  set wi : Fin M → ℝ → ℂ := fun i x => (w x : ℂ) * (A i x : ℂ) * (B i x : ℂ) * sg i x
    with hwi
  have hA_meas : ∀ i, Measurable (A i) := by
    intro i
    rw [hA]
    refine Measurable.ite ?_ measurable_const measurable_const
    rw [show {x : ℝ | ∀ j : Fin M, ‖F j x‖ ≤ ‖F i x‖}
        = ⋂ j : Fin M, {x : ℝ | ‖F j x‖ ≤ ‖F i x‖} from by ext x; simp]
    exact MeasurableSet.iInter
      (fun j => measurableSet_le (hFcont j).norm.measurable (hFcont i).norm.measurable)
  have hB_meas : ∀ i, Measurable (B i) := by
    intro i
    rw [hB]
    refine Finset.measurable_prod _ (fun j _ => ?_)
    refine Measurable.ite ?_ measurable_const measurable_const
    by_cases hij : i < j
    · rw [show {x : ℝ | i < j ∧ G x = ‖F j x‖} = {x : ℝ | G x = ‖F j x‖} from by
        ext x; simp [hij]]
      exact measurableSet_eq_fun hGmeas (hFcont j).norm.measurable
    · rw [show {x : ℝ | i < j ∧ G x = ‖F j x‖} = ∅ from by
        ext x; simp [hij]]
      exact MeasurableSet.empty
  have hA_le : ∀ i x, A i x ≤ 1 := by
    intro i x; simp only [hA]; split <;> norm_num
  have hA_nonneg : ∀ i x, 0 ≤ A i x := by
    intro i x; simp only [hA]; split <;> norm_num
  have hB_le : ∀ i x, B i x ≤ 1 := by
    intro i x
    rw [hB]
    refine Finset.prod_le_one₀ (fun j _ => ?_) (fun j _ => ?_)
    · by_cases h : i < j ∧ G x = ‖F j x‖ <;> simp [h]
    · by_cases h : i < j ∧ G x = ‖F j x‖ <;> simp [h]
  have hB_nonneg : ∀ i x, 0 ≤ B i x := by
    intro i x
    rw [hB]
    refine Finset.prod_nonneg (fun j _ => ?_)
    by_cases h : i < j ∧ G x = ‖F j x‖ <;> simp [h]
  have hwi_bound : ∀ i x, ‖wi i x‖ ≤ w x := by
    intro i x
    rw [hwi]
    have h1 : ‖((A i x : ℝ) : ℂ)‖ ≤ 1 := by
      rw [show ‖((A i x : ℝ) : ℂ)‖ = |A i x| by simp, abs_of_nonneg (hA_nonneg i x)]
      exact hA_le i x
    have h2 : ‖((B i x : ℝ) : ℂ)‖ ≤ 1 := by
      rw [show ‖((B i x : ℝ) : ℂ)‖ = |B i x| by simp, abs_of_nonneg (hB_nonneg i x)]
      exact hB_le i x
    have h3 : ‖((w x : ℝ) : ℂ)‖ = w x := by
      rw [show ‖((w x : ℝ) : ℂ)‖ = |w x| by simp, abs_of_nonneg (hw0 x)]
    rw [norm_mul, norm_mul, norm_mul, h3]
    have ha : 0 ≤ ‖((A i x : ℝ) : ℂ)‖ := norm_nonneg _
    have hb : 0 ≤ ‖((B i x : ℝ) : ℂ)‖ := norm_nonneg _
    have hc : 0 ≤ ‖sg i x‖ := norm_nonneg _
    calc w x * ‖((A i x : ℝ) : ℂ)‖ * ‖((B i x : ℝ) : ℂ)‖ * ‖sg i x‖
        ≤ w x * ‖((A i x : ℝ) : ℂ)‖ * ‖((B i x : ℝ) : ℂ)‖ * 1 :=
          mul_le_mul_of_nonneg_left (hsg_norm i x)
            (mul_nonneg (mul_nonneg (hw0 x) ha) hb)
      _ ≤ w x * ‖((A i x : ℝ) : ℂ)‖ * 1 * 1 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2
            (mul_nonneg (hw0 x) ha)) (by norm_num)
      _ ≤ w x * 1 * 1 * 1 := by
          refine mul_le_mul_of_nonneg_right ?_ (by norm_num)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (hw0 x)) (by norm_num)
      _ = w x := by ring
  -- the greatest maximiser
  have hpoint : ∀ x : ℝ, (∑ i, wi i x * F i x) = ((w x * G x : ℝ) : ℂ) := by
    intro x
    obtain ⟨i0, hi0mem, hi0max⟩ := Finset.exists_max_image
      (Finset.univ.filter (fun i : Fin M => ∀ j : Fin M, ‖F j x‖ ≤ ‖F i x‖))
      (fun i : Fin M => i)
      (by
        obtain ⟨i1, -, hi1⟩ := Finset.exists_max_image Finset.univ (fun i : Fin M => ‖F i x‖)
          ⟨⟨0, hM⟩, Finset.mem_univ _⟩
        exact ⟨i1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => hi1 j (Finset.mem_univ j)⟩⟩)
    have hi0amax : ∀ j : Fin M, ‖F j x‖ ≤ ‖F i0 x‖ := (Finset.mem_filter.mp hi0mem).2
    have hGi0 : G x = ‖F i0 x‖ := le_antisymm (ciSup_le hi0amax) (hGle x i0)
    have hA1 : A i0 x = 1 := by
      simp only [hA]
      rw [if_pos hi0amax]
    have hB1 : B i0 x = 1 := by
      rw [hB]
      refine Finset.prod_eq_one (fun j _ => ?_)
      have hnot : ¬ (i0 < j ∧ G x = ‖F j x‖) := by
        rintro ⟨hij, hGj⟩
        have hmax : ∀ k : Fin M, ‖F k x‖ ≤ ‖F j x‖ := fun k => by rw [← hGj]; exact hGle x k
        have hmem : j ∈ Finset.univ.filter
            (fun i : Fin M => ∀ k : Fin M, ‖F k x‖ ≤ ‖F i x‖) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ j, hmax⟩
        exact absurd (hi0max j hmem) (not_le.mpr hij)
      simp only [hnot, if_false]
    have hzero : ∀ i : Fin M, i ≠ i0 → wi i x * F i x = 0 := by
      intro i hi
      by_cases hamax : ∀ j : Fin M, ‖F j x‖ ≤ ‖F i x‖
      · have hmem : i ∈ Finset.univ.filter
            (fun k : Fin M => ∀ j : Fin M, ‖F j x‖ ≤ ‖F k x‖) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ i, hamax⟩
        have hlt : i < i0 := lt_of_le_of_ne (hi0max i hmem) hi
        have hBzero : B i x = 0 := by
          rw [hB]
          exact Finset.prod_eq_zero (Finset.mem_univ i0) (by rw [if_pos ⟨hlt, hGi0⟩])
        simp only [hwi]
        rw [hBzero]
        simp
      · have hAzero : A i x = 0 := by
          simp only [hA]
          rw [if_neg hamax]
        simp only [hwi]
        rw [hAzero]
        simp
    rw [Finset.sum_eq_single i0 (fun i _ hi => hzero i hi)
      (fun h => absurd (Finset.mem_univ i0) h)]
    simp only [hwi, hA1, hB1, Pi.one_apply, Complex.ofReal_one, mul_one]
    rw [mul_assoc, hsg_mul i0 x, ← hGi0]
    push_cast
    ring

  -- disjointness of the supports of the weights
  have hdisj : ∀ i j : Fin M, i ≠ j → ∀ x : ℝ, wi i x * star (wi j x) = 0 := by
    intro i j hij x
    by_cases hamax_i : ∀ k : Fin M, ‖F k x‖ ≤ ‖F i x‖
    · by_cases hamax_j : ∀ k : Fin M, ‖F k x‖ ≤ ‖F j x‖
      · rcases lt_or_gt_of_ne hij with hlt | hlt
        · have hGj : G x = ‖F j x‖ := le_antisymm (ciSup_le hamax_j) (hGle x j)
          have hBzero : B i x = 0 := by
            rw [hB]
            exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [if_pos ⟨hlt, hGj⟩])
          rw [hwi]
          simp [hBzero]
        · have hGi : G x = ‖F i x‖ := le_antisymm (ciSup_le hamax_i) (hGle x i)
          have hBzero : B j x = 0 := by
            rw [hB]
            exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [if_pos ⟨hlt, hGi⟩])
          rw [hwi]
          simp [hBzero]
      · have hAj : A j x = 0 := by
          simp only [hA]
          rw [if_neg hamax_j]
        rw [hwi]
        simp [hAj]
    · have hAi : A i x = 0 := by
        simp only [hA]
        rw [if_neg hamax_i]
      rw [hwi]
      simp [hAi]
  -- measurability and integrability of the weights
  have hwi_aemeas : ∀ i, AEMeasurable (wi i) volume := by
    intro i
    have h1 : AEMeasurable (fun x : ℝ => ((w x : ℝ) : ℂ)) volume :=
      Complex.measurable_ofReal.comp_aemeasurable hw2.aemeasurable
    have h2 : AEMeasurable (fun x : ℝ => ((A i x : ℝ) : ℂ)) volume :=
      (Complex.measurable_ofReal.comp (hA_meas i)).aemeasurable
    have h3 : AEMeasurable (fun x : ℝ => ((B i x : ℝ) : ℂ)) volume :=
      (Complex.measurable_ofReal.comp (hB_meas i)).aemeasurable
    have h4 : AEMeasurable (sg i) volume := (hsg_meas i).aemeasurable
    exact ((h1.mul h2).mul h3).mul h4
  have hwi_memLp : ∀ i, MemLp (wi i) 2 volume := by
    intro i
    refine MemLp.of_le (memLp_ofReal hw2) (hwi_aemeas i).aestronglyMeasurable ?_
    filter_upwards with x
    rw [norm_ofReal_eq, abs_of_nonneg (hw0 x)]
    exact hwi_bound i x
  have hwi_int : ∀ i, Integrable (wi i) := by
    intro i
    rw [← memLp_one_iff_integrable]
    refine MemLp.of_le (memLp_ofReal (memLp_one_iff_integrable.mpr hw1))
      (hwi_aemeas i).aestronglyMeasurable ?_
    filter_upwards with x
    rw [norm_ofReal_eq, abs_of_nonneg (hw0 x)]
    exact hwi_bound i x
  -- integrability of the individual terms and of the sum
  have hFsum_memLp : MemLp (fun x : ℝ => ∑ i : Fin M, ‖F i x‖) 2 volume :=
    memLp_finsetSum (Finset.univ : Finset (Fin M)) (fun i _ => (hFmem i).norm)
  have hprod_int : Integrable (fun x : ℝ => w x * ∑ i : Fin M, ‖F i x‖) := by
    have h : Integrable (fun x : ℝ => (((w x * ∑ i : Fin M, ‖F i x‖ : ℝ)) : ℂ)) := by
      have hh := (memLp_ofReal hw2).integrable_mul (memLp_ofReal hFsum_memLp)
      refine hh.congr ?_
      filter_upwards with x
      simp only [Pi.mul_apply, Complex.ofReal_mul]
    refine h.norm.congr ?_
    filter_upwards with x
    have hw : ‖((w x : ℝ) : ℂ)‖ = w x := by
      rw [norm_ofReal_eq, abs_of_nonneg (hw0 x)]
    have hs : ‖(((∑ i : Fin M, ‖F i x‖) : ℝ) : ℂ)‖ = ∑ i : Fin M, ‖F i x‖ := by
      rw [norm_ofReal_eq, abs_of_nonneg (Finset.sum_nonneg (fun i _ => norm_nonneg _))]
    show ‖(((w x * ∑ i : Fin M, ‖F i x‖ : ℝ)) : ℂ)‖ = w x * ∑ i : Fin M, ‖F i x‖
    rw [show (((w x * ∑ i : Fin M, ‖F i x‖ : ℝ)) : ℂ)
        = ((w x : ℝ) : ℂ) * (((∑ i : Fin M, ‖F i x‖) : ℝ) : ℂ) by push_cast; ring,
      norm_mul, hw, hs]
  have hterm_int : ∀ i : Fin M, Integrable (fun x : ℝ => wi i x * F i x) := by
    intro i
    refine Integrable.mono' hprod_int ?_ ?_
    · exact (hwi_int i).aestronglyMeasurable.mul (hFmem i).aestronglyMeasurable
    · filter_upwards with x
      calc ‖wi i x * F i x‖ = ‖wi i x‖ * ‖F i x‖ := norm_mul _ _
        _ ≤ w x * ‖F i x‖ := mul_le_mul_of_nonneg_right (hwi_bound i x) (norm_nonneg _)
        _ ≤ w x * ∑ j : Fin M, ‖F j x‖ := by
            refine mul_le_mul_of_nonneg_left ?_ (hw0 x)
            exact Finset.single_le_sum (fun j _ => norm_nonneg (F j x)) (Finset.mem_univ i)
  have hsum_int : Integrable (fun x : ℝ => ∑ i : Fin M, wi i x * F i x) := by
    rw [← memLp_one_iff_integrable]
    exact memLp_finsetSum (Finset.univ : Finset (Fin M)) (fun i _ => memLp_one_iff_integrable.mpr (hterm_int i))
  -- Step 1: the left-hand side is the real part of the total sum
  have hAeq : (∫ x : ℝ, w x * G x) = (∫ x : ℝ, ∑ i : Fin M, wi i x * F i x).re := by
    have h1 : (∫ x : ℝ, w x * G x) = ∫ x : ℝ, (∑ i : Fin M, wi i x * F i x).re := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show w x * G x = (∑ i : Fin M, wi i x * F i x).re
      rw [hpoint x]
      simp
    rw [h1]
    exact integral_re hsum_int
  -- Step 2: each term is a Fourier pairing
  have hterm : ∀ i : Fin M, (∫ x : ℝ, wi i x * F i x)
      = ∫ ξ : ℝ, (Set.indicator (C i) (𝓕 f)) ξ * (𝓕 (wi i)) (-ξ) := by
    intro i
    simp only [hF]
    exact integral_mul_fourierInv _ _
      (memLp_one_iff_integrable.mp (memLp_one_indicator_fourier (C i) (hmeas i) (hbd i) f hf1))
      (hwi_int i)
      (memLp_two_indicator_fourier (C i) (hmeas i) (hbd i) f hf1)
      (hwi_memLp i)
  -- the Fourier transforms of the weights
  set V : Fin M → ℝ → ℂ := fun i ξ => (𝓕 (wi i)) (-ξ) with hVdef
  have hV_memLp : ∀ i, MemLp (V i) 2 volume := by
    intro i
    rw [hVdef]
    exact memLp_comp_neg (memLp_fourier (hwi_int i) (hwi_memLp i))
  have hV_orth : ∀ i j : Fin M, i ≠ j → ∫ ξ : ℝ, V i ξ * star (V j ξ) = 0 := by
    intro i j hij
    have h1 : (∫ ξ : ℝ, V i ξ * star (V j ξ))
        = ∫ ξ : ℝ, (𝓕 (wi i)) ξ * star ((𝓕 (wi j)) ξ) := by
      rw [show (fun ξ : ℝ => V i ξ * star (V j ξ))
          = (fun ξ : ℝ => (fun η : ℝ => (𝓕 (wi i)) η * star ((𝓕 (wi j)) η)) (-ξ)) from by
        funext ξ; simp only [hVdef, neg_neg]]
      exact MeasureTheory.integral_neg_eq_self
        (fun η : ℝ => (𝓕 (wi i)) η * star ((𝓕 (wi j)) η)) (volume : Measure ℝ)
    have h2 : (∫ ξ : ℝ, (𝓕 (wi i)) ξ * star ((𝓕 (wi j)) ξ))
        = ∫ x : ℝ, wi i x * star (wi j x) :=
      integral_fourier_mul_star (wi i) (wi j) (hwi_int i) (hwi_int j) (hwi_memLp i) (hwi_memLp j)
    have h3 : (∫ x : ℝ, wi i x * star (wi j x)) = 0 := by
      rw [show (fun x : ℝ => wi i x * star (wi j x)) = fun _ => (0 : ℂ) from
        funext (fun x => hdisj i j hij x)]
      simp
    rw [h1, h2, h3]
  -- the pointwise `ℓ²` bound for the weights
  have hpt : ∀ x : ℝ, ∑ i : Fin M, ‖wi i x‖ ^ 2 ≤ w x ^ 2 := by
    intro x
    have hcard : (Finset.univ.filter (fun i : Fin M => wi i x ≠ 0)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro i hi j hj
      by_contra hij
      exact mul_ne_zero (Finset.mem_filter.mp hi).2
        (star_ne_zero.mpr (Finset.mem_filter.mp hj).2) (hdisj i j hij x)
    calc ∑ i : Fin M, ‖wi i x‖ ^ 2
        = ∑ i ∈ Finset.univ.filter (fun i : Fin M => wi i x ≠ 0), ‖wi i x‖ ^ 2 := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          by_cases h : wi i x = 0 <;> simp [h]
      _ ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin M => wi i x ≠ 0), w x ^ 2 := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          have h1 : ‖wi i x‖ ≤ w x := hwi_bound i x
          have h2 : 0 ≤ ‖wi i x‖ := norm_nonneg _
          have h3 : 0 ≤ w x := hw0 x
          nlinarith [h1, h2, h3]
      _ = ((Finset.univ.filter (fun i : Fin M => wi i x ≠ 0)).card : ℝ) * w x ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 1 * w x ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          exact_mod_cast hcard
      _ = w x ^ 2 := one_mul _
  -- integrability of the squared norms
  have hw_sq_int : Integrable (fun x : ℝ => w x ^ 2) := by
    have h : Integrable (fun x : ℝ => (((w x * w x : ℝ)) : ℂ)) := by
      have hh := (memLp_ofReal hw2).integrable_mul (memLp_ofReal hw2)
      refine hh.congr ?_
      filter_upwards with x
      simp only [Pi.mul_apply, Complex.ofReal_mul]
    refine h.norm.congr ?_
    filter_upwards with x
    have h1 : ‖((w x : ℝ) : ℂ)‖ = w x := by rw [norm_ofReal_eq, abs_of_nonneg (hw0 x)]
    show ‖(((w x * w x : ℝ)) : ℂ)‖ = w x ^ 2
    rw [show (((w x * w x : ℝ)) : ℂ) = ((w x : ℝ) : ℂ) * ((w x : ℝ) : ℂ) by push_cast; ring,
      norm_mul, h1]
    ring
  have hwi_sq_int : ∀ i : Fin M, Integrable (fun x : ℝ => ‖wi i x‖ ^ 2) := by
    intro i
    refine Integrable.mono' hw_sq_int ?_ ?_
    · exact ((hwi_aemeas i).norm.pow_const 2).aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_of_nonneg (by positivity)]
      have h1 : ‖wi i x‖ ≤ w x := hwi_bound i x
      nlinarith [norm_nonneg (wi i x), hw0 x, h1]
  have hnorm_w : (∑ i : Fin M, ∫ x : ℝ, ‖wi i x‖ ^ 2) ≤ ∫ x : ℝ, w x ^ 2 := by
    rw [← integral_finsetSum _ (fun i _ => hwi_sq_int i)]
    refine integral_mono_ae (integrable_finsetSum _ (fun i _ => hwi_sq_int i)) hw_sq_int ?_
    filter_upwards with x
    exact hpt x
  -- Plancherel for the weights
  have hnorm_wi : ∀ i : Fin M, (∫ ξ : ℝ, ‖V i ξ‖ ^ 2) = ∫ x : ℝ, ‖wi i x‖ ^ 2 := by
    intro i
    have hVeq : ∀ ξ : ℝ, V i ξ = 𝓕⁻ (wi i) ξ := by
      intro ξ
      rw [hVdef]
      exact (Real.fourierInv_eq_fourier_neg (wi i) ξ).symm
    have h1 : (∫⁻ ξ : ℝ, ‖V i ξ‖ₑ ^ (2:ℝ) ∂volume)
        = ∫⁻ ξ : ℝ, ‖𝓕⁻ (wi i) ξ‖ₑ ^ (2:ℝ) ∂volume :=
      lintegral_congr (fun ξ => by rw [hVeq ξ])
    have hVl : (∫⁻ a : ℝ, ‖V i a‖ₑ ^ (2:ℝ) ∂volume)
        = ENNReal.ofReal (∫ a : ℝ, ‖V i a‖ ^ (2:ℝ)) :=
      NestedIndicator.lintegral_enorm_rpow_two volume (hV_memLp i)
    have hwl : (∫⁻ a : ℝ, ‖wi i a‖ₑ ^ (2:ℝ) ∂volume)
        = ENNReal.ofReal (∫ a : ℝ, ‖wi i a‖ ^ (2:ℝ)) :=
      NestedIndicator.lintegral_enorm_rpow_two volume (hwi_memLp i)
    have h6 : ENNReal.ofReal (∫ a : ℝ, ‖V i a‖ ^ (2:ℝ))
        = ENNReal.ofReal (∫ a : ℝ, ‖wi i a‖ ^ (2:ℝ)) := by
      calc ENNReal.ofReal (∫ a : ℝ, ‖V i a‖ ^ (2:ℝ))
          = ∫⁻ a : ℝ, ‖V i a‖ₑ ^ (2:ℝ) ∂volume := hVl.symm
        _ = ∫⁻ a : ℝ, ‖𝓕⁻ (wi i) a‖ₑ ^ (2:ℝ) ∂volume := h1
        _ = ∫⁻ a : ℝ, ‖wi i a‖ₑ ^ (2:ℝ) ∂volume :=
              lintegral_enorm_fourierInv_eq (memLp_one_iff_integrable.mpr (hwi_int i)) (hwi_memLp i)
        _ = ENNReal.ofReal (∫ a : ℝ, ‖wi i a‖ ^ (2:ℝ)) := hwl
    have h7 := (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg (fun a => by positivity))
      (integral_nonneg (fun a => by positivity))).mp h6
    simpa only [Real.rpow_two] using h7
  have hnorm_ui : ∀ i : Fin M, (∫ x : ℝ, ‖wi i (-x)‖ ^ 2) = ∫ x : ℝ, ‖wi i x‖ ^ 2 := by
    intro i
    have h1 : (∫⁻ x : ℝ, ‖wi i (-x)‖ₑ ^ (2:ℝ) ∂volume)
        = ENNReal.ofReal (∫ x : ℝ, ‖wi i (-x)‖ ^ 2) := by
      simpa only [Real.rpow_two] using
        NestedIndicator.lintegral_enorm_rpow_two volume (memLp_comp_neg (hwi_memLp i))
    have h2 : (∫⁻ x : ℝ, ‖wi i x‖ₑ ^ (2:ℝ) ∂volume)
        = ENNReal.ofReal (∫ x : ℝ, ‖wi i x‖ ^ 2) := by
      simpa only [Real.rpow_two] using
        NestedIndicator.lintegral_enorm_rpow_two volume (hwi_memLp i)
    have h3 : (∫⁻ x : ℝ, ‖wi i (-x)‖ₑ ^ (2:ℝ) ∂volume)
        = ∫⁻ x : ℝ, ‖wi i x‖ₑ ^ (2:ℝ) ∂volume :=
      lintegral_neg_eq_self (fun y : ℝ => ‖wi i y‖ₑ ^ (2:ℝ))
    rw [h1, h2] at h3
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg (fun a => by positivity))
      (integral_nonneg (fun a => by positivity))).mp h3
  have hB_memLp : MemLp (fun ξ : ℝ => ∑ i : Fin M, Set.indicator (C i) (V i) ξ) 2 volume :=
    memLp_finsetSum (Finset.univ : Finset (Fin M)) (fun i _ => MemLp.indicator (hmeas i) (hV_memLp i))
  have hBnd : Real.sqrt (∫ ξ : ℝ, ‖∑ i : Fin M, Set.indicator (C i) (V i) ξ‖ ^ 2)
      ≤ D * Real.sqrt (∑ i : Fin M, ∫ ξ : ℝ, ‖V i ξ‖ ^ 2) := by
    set u : Fin M → ℝ → ℂ := fun i x => wi i (-x) with hudef
    have hu1 : ∀ i : Fin M, MemLp (u i) 1 volume :=
      fun i => memLp_comp_neg (memLp_one_iff_integrable.mpr (hwi_int i))
    have hu2 : ∀ i : Fin M, MemLp (u i) 2 volume := fun i => memLp_comp_neg (hwi_memLp i)
    have hdisj_u : ∀ i j : Fin M, i ≠ j → ∀ x : ℝ, u i x * star (u j x) = 0 := by
      intro i j hij x
      have h := hdisj i j hij (-x)
      simpa only [hudef] using h
    have hdual_app := hdual Finset.univ u (fun j _ => hu2 j) (fun j _ k _ hj => hdisj_u j k hj)
    have hFu : ∀ j : Fin M, 𝓕 (u j) = V j := by
      intro j
      ext ξ
      have h1 : (𝓕 (u j)) ξ = 𝓕⁻ (fun y : ℝ => u j (-y)) ξ := fourier_eq_fourierInv_comp_neg (u j) ξ
      rw [h1]
      have h2 : (fun y : ℝ => u j (-y)) = wi j := by
        funext y
        simp only [hudef, neg_neg]
      rw [h2, hVdef]
      exact Real.fourierInv_eq_fourier_neg (wi j) ξ
    have hA_mem : MemLp (fun x : ℝ => ∑ j : Fin M, bandOp (C j) (u j) x) 2 volume :=
      memLp_finsetSum _ (fun j _ => bandOp_memLp (C j) (hmeas j) (hbd j) (u j)
        (memLp_one_iff_integrable.mp (hu1 j)) (hu2 j))
    have hbridge : (∫⁻ x : ℝ, ‖∑ j : Fin M, bandOp (C j) (u j) x‖ₑ ^ (2:ℝ) ∂volume)
        = ∫⁻ ξ : ℝ, ‖∑ j : Fin M, Set.indicator (C j) (𝓕 (u j)) ξ‖ₑ ^ (2:ℝ) ∂volume :=
      bandSum_indicatorSum_l2 C hmeas hbd u hu1 hu2
    have hbridgeV : (∫⁻ x : ℝ, ‖∑ j : Fin M, bandOp (C j) (u j) x‖ₑ ^ (2:ℝ) ∂volume)
        = ∫⁻ ξ : ℝ, ‖∑ j : Fin M, Set.indicator (C j) (V j) ξ‖ₑ ^ (2:ℝ) ∂volume := by
      rw [hbridge]
      refine lintegral_congr (fun ξ => ?_)
      rw [show (∑ j : Fin M, Set.indicator (C j) (𝓕 (u j)) ξ)
          = ∑ j : Fin M, Set.indicator (C j) (V j) ξ from
        Finset.sum_congr rfl (fun j _ => by rw [hFu j])]
    have hAlin : (∫⁻ x : ℝ, ‖∑ j : Fin M, bandOp (C j) (u j) x‖ₑ ^ (2:ℝ) ∂volume)
        = ENNReal.ofReal (∫ x : ℝ, ‖∑ j : Fin M, bandOp (C j) (u j) x‖ ^ 2) := by
      simpa only [Real.rpow_two] using NestedIndicator.lintegral_enorm_rpow_two volume hA_mem
    have hBlin : (∫⁻ ξ : ℝ, ‖∑ j : Fin M, Set.indicator (C j) (V j) ξ‖ₑ ^ (2:ℝ) ∂volume)
        = ENNReal.ofReal (∫ ξ : ℝ, ‖∑ j : Fin M, Set.indicator (C j) (V j) ξ‖ ^ 2) := by
      simpa only [Real.rpow_two] using NestedIndicator.lintegral_enorm_rpow_two volume hB_memLp
    have hLEFT : (∫ x : ℝ, ‖∑ j : Fin M, bandOp (C j) (u j) x‖ ^ 2)
        = ∫ ξ : ℝ, ‖∑ j : Fin M, Set.indicator (C j) (V j) ξ‖ ^ 2 := by
      have hof : ENNReal.ofReal (∫ x : ℝ, ‖∑ j : Fin M, bandOp (C j) (u j) x‖ ^ 2)
          = ENNReal.ofReal (∫ ξ : ℝ, ‖∑ j : Fin M, Set.indicator (C j) (V j) ξ‖ ^ 2) := by
        rw [← hAlin, hbridgeV, hBlin]
      exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg (fun a => by positivity))
        (integral_nonneg (fun a => by positivity))).mp hof
    have hRIGHT : (∑ j : Fin M, ∫ x : ℝ, ‖u j x‖ ^ 2)
        = ∑ j : Fin M, ∫ ξ : ℝ, ‖V j ξ‖ ^ 2 := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [hudef]
      rw [hnorm_ui j, ← hnorm_wi j]
    calc Real.sqrt (∫ ξ : ℝ, ‖∑ i : Fin M, Set.indicator (C i) (V i) ξ‖ ^ 2)
        = Real.sqrt (∫ x : ℝ, ‖∑ j : Fin M, bandOp (C j) (u j) x‖ ^ 2) := by rw [← hLEFT]
      _ ≤ D * Real.sqrt (∑ j : Fin M, ∫ x : ℝ, ‖u j x‖ ^ 2) := hdual_app
      _ = D * Real.sqrt (∑ j : Fin M, ∫ ξ : ℝ, ‖V j ξ‖ ^ 2) := by rw [hRIGHT]
  -- Cauchy--Schwarz
  have hCS : ‖∫ ξ : ℝ, (𝓕 f) ξ * (∑ i : Fin M, Set.indicator (C i) (V i) ξ)‖
      ≤ Real.sqrt (∫ ξ : ℝ, ‖(𝓕 f) ξ‖ ^ 2)
        * Real.sqrt (∫ ξ : ℝ, ‖∑ i : Fin M, Set.indicator (C i) (V i) ξ‖ ^ 2) := by
    have hFmem2 : MemLp (𝓕 f) (ENNReal.ofReal 2) volume := by
      simpa using memLp_fourier hf1 hf2
    have h1 : ‖∫ ξ : ℝ, (𝓕 f) ξ * (∑ i : Fin M, Set.indicator (C i) (V i) ξ)‖
        ≤ ∫ ξ : ℝ, ‖(𝓕 f) ξ‖ * ‖∑ i : Fin M, Set.indicator (C i) (V i) ξ‖ := by
      refine le_trans (norm_integral_le_integral_norm _) ?_
      refine integral_mono_ae ?_ ?_ ?_
      · exact ((memLp_fourier hf1 hf2).integrable_mul hB_memLp).norm
      · exact ((memLp_fourier hf1 hf2).norm).integrable_mul hB_memLp.norm
      · filter_upwards with ξ
        rw [norm_mul]
    have h2 := integral_mul_norm_le_Lp_mul_Lq (μ := volume) (f := 𝓕 f)
      (g := fun ξ : ℝ => ∑ i : Fin M, Set.indicator (C i) (V i) ξ) (p := 2) (q := 2)
      (by rw [Real.holderConjugate_iff]; norm_num) hFmem2
      (by simpa only [ENNReal.ofReal_ofNat] using hB_memLp)
    refine le_trans h1 ?_
    simpa only [Real.rpow_two, Real.sqrt_eq_rpow] using h2
  -- Plancherel for `f`
  have hnorm_f : (∫ ξ : ℝ, ‖(𝓕 f) ξ‖ ^ 2) = ∫ x : ℝ, ‖f x‖ ^ 2 := by
    have h1 : (∫⁻ ξ : ℝ, ‖(𝓕 f) ξ‖ₑ ^ (2:ℝ) ∂volume)
        = ENNReal.ofReal (∫ ξ : ℝ, ‖(𝓕 f) ξ‖ ^ 2) := by
      simpa only [Real.rpow_two] using
        NestedIndicator.lintegral_enorm_rpow_two volume (memLp_fourier hf1 hf2)
    have h2 : (∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ) ∂volume)
        = ENNReal.ofReal (∫ x : ℝ, ‖f x‖ ^ 2) := by
      simpa only [Real.rpow_two] using
        NestedIndicator.lintegral_enorm_rpow_two volume hf2
    have h3 := lintegral_enorm_fourier_eq hf1 hf2
    rw [h1, h2] at h3
    exact (ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)).mp h3
  -- assembly
  have hCsum : (∫ x : ℝ, ∑ i : Fin M, wi i x * F i x)
      = ∫ ξ : ℝ, (𝓕 f) ξ * (∑ i : Fin M, Set.indicator (C i) (V i) ξ) := by
    have hsumm : ∀ i : Fin M,
        Integrable (fun ξ : ℝ => (Set.indicator (C i) (𝓕 f)) ξ * (𝓕 (wi i)) (-ξ)) := by
      intro i
      have h1 : MemLp (fun ξ : ℝ => (Set.indicator (C i) (𝓕 f)) ξ) 2 volume :=
        memLp_two_indicator_fourier (C i) (hmeas i) (hbd i) f hf1
      have h2 : MemLp (fun ξ : ℝ => (𝓕 (wi i)) (-ξ)) 2 volume :=
        memLp_comp_neg (memLp_fourier (hwi_int i) (hwi_memLp i))
      exact memLp_one_iff_integrable.mp (MemLp.mul' (p := 2) (q := 2) (r := 1) h1 h2)
    rw [integral_finsetSum _ (fun i _ => hterm_int i)]
    simp only [hterm]
    rw [← integral_finsetSum _ (fun i _ => hsumm i)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    show (∑ i : Fin M, (Set.indicator (C i) (𝓕 f)) ξ * (𝓕 (wi i)) (-ξ))
        = (𝓕 f) ξ * ∑ i : Fin M, Set.indicator (C i) (V i) ξ
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases h : ξ ∈ C i <;> simp [h, hVdef]
  have hmain : (∫ x : ℝ, w x * G x) ≤ D
      * Real.sqrt (∫ x : ℝ, w x ^ 2) * Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2) := by
    calc (∫ x : ℝ, w x * G x) = (∫ x : ℝ, ∑ i : Fin M, wi i x * F i x).re := hAeq
      _ ≤ ‖∫ x : ℝ, ∑ i : Fin M, wi i x * F i x‖ := Complex.re_le_norm _
      _ = ‖∫ ξ : ℝ, (𝓕 f) ξ * (∑ i : Fin M, Set.indicator (C i) (V i) ξ)‖ := by rw [hCsum]
      _ ≤ Real.sqrt (∫ ξ : ℝ, ‖(𝓕 f) ξ‖ ^ 2)
            * Real.sqrt (∫ ξ : ℝ, ‖∑ i : Fin M, Set.indicator (C i) (V i) ξ‖ ^ 2) := hCS
      _ ≤ Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2) * (D
            * Real.sqrt (∑ i : Fin M, ∫ ξ : ℝ, ‖V i ξ‖ ^ 2)) := by
          rw [hnorm_f]
          exact mul_le_mul_of_nonneg_left hBnd (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2) * (D
            * Real.sqrt (∫ x : ℝ, w x ^ 2)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hD)
            (Real.sqrt_nonneg _)
          refine Real.sqrt_le_sqrt ?_
          calc (∑ i : Fin M, ∫ ξ : ℝ, ‖V i ξ‖ ^ 2)
              = ∑ i : Fin M, ∫ x : ℝ, ‖wi i x‖ ^ 2 := Finset.sum_congr rfl (fun i _ => hnorm_wi i)
            _ ≤ ∫ x : ℝ, w x ^ 2 := hnorm_w
      _ = D * Real.sqrt (∫ x : ℝ, w x ^ 2)
            * Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2) := by ring
  simpa only [hG, hF] using hmain


end

end Commons.Analysis.Fourier
