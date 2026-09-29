import Mathlib
import Submission.Work.Holonomy3.defs
import Submission.Work.Holonomy3.count_le_of_disc

open scoped BigOperators
open MeasureTheory

namespace Work.Holonomy3

open Submission.CDT.Discrepancy

/-- The box discrepancy is nonnegative. -/
lemma disc_nonneg {N : ℕ} (t : Fin N → ℝ) : 0 ≤ disc t := by
  rw [disc]
  refine le_csSup (disc_bddAbove t) ?_
  refine ⟨(0, 0), ?_, ?_⟩
  · norm_num
  · simp [cnt]

/-- Interval integrability of a (globally) bounded measurable function. -/
lemma intervalIntegrable_of_measurable_of_bound {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) (a b : ℝ) : IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff]
  have hfin : volume (Set.uIoc a b) ≠ ⊤ := by
    rw [Real.volume_uIoc]; exact ENNReal.ofReal_ne_top
  have hI : IsFiniteMeasure (volume.restrict (Set.uIoc a b)) := isFiniteMeasure_restrict.2 hfin
  exact Integrable.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hC x))

/-- The empirical count of the points `t j ≤ c`, divided by `N`, exceeds `c` by at most `disc t`. -/
lemma count_le_div_le_add_disc {N : ℕ} (hN : 0 < N) (t : Fin N → ℝ)
    (ht : ∀ j, t j ∈ Set.Icc 0 1) {c : ℝ} (hc : c ∈ Set.Icc 0 1) :
    ((Finset.univ.filter (fun j : Fin N => t j ≤ c)).card : ℝ) / (N : ℝ) ≤
      c + disc t := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have key : ∀ b : ℝ, c < b → b ≤ 1 →
      (((Finset.univ.filter (fun j : Fin N => t j ≤ c)).card : ℝ)) / (N : ℝ) ≤ b + disc t := by
    intro b hcb hb1
    have hcard : (Finset.univ.filter (fun j : Fin N => t j ≤ c)).card ≤ cnt t 0 b := by
      rw [cnt]
      apply Finset.card_le_card
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact ⟨(ht j).1, lt_of_le_of_lt hj hcb⟩
    have hcard' : (((Finset.univ.filter (fun j : Fin N => t j ≤ c)).card : ℝ)) ≤ (cnt t 0 b : ℝ) := by
      exact_mod_cast hcard
    have hdiv : ((cnt t 0 b : ℝ)) / (N : ℝ) ≤ b + disc t := by
      have h := abs_sub_cnt_div_le_disc (disc t) t le_rfl (a := 0) (b := b) le_rfl
        (by linarith [hc.1]) hb1
      have h1 := (abs_le.mp h).1
      have h2 := (abs_le.mp h).2
      simp only [sub_zero] at h1 h2
      linarith
    calc (((Finset.univ.filter (fun j : Fin N => t j ≤ c)).card : ℝ)) / (N : ℝ)
        ≤ (cnt t 0 b : ℝ) / (N : ℝ) := div_le_div_of_nonneg_right hcard' (le_of_lt hNpos)
      _ ≤ b + disc t := hdiv
  rcases eq_or_lt_of_le hc.2 with h1 | h1
  · rw [h1]
    have hfilt : (Finset.univ.filter (fun j : Fin N => t j ≤ 1)).card = N := by
      rw [Finset.filter_true_of_mem (fun j _ => (ht j).2)]
      simp
    rw [hfilt]
    have hdiv : ((N : ℝ)) / (N : ℝ) = 1 := by field_simp
    rw [hdiv]
    linarith [disc_nonneg t]
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hbgt : c < min 1 (c + ε / 2) := lt_min h1 (by linarith)
    have hble : min 1 (c + ε / 2) ≤ 1 := min_le_left _ _
    have hb2 : min 1 (c + ε / 2) ≤ c + ε / 2 := min_le_right _ _
    have := key (min 1 (c + ε / 2)) hbgt hble
    linarith

/-- Layer-cake identity for a finite sum. -/
lemma sum_eq_integral_count {N : ℕ} (G : ℝ → ℝ) (hmono : Monotone G) (hG0 : G 0 = 0)
    (t : Fin N → ℝ) (ht : ∀ j, t j ∈ Set.Icc 0 1) :
    ∑ j, G (t j) =
      ∫ y in (0 : ℝ)..(G 1),
        ((Finset.univ.filter (fun j : Fin N => y ≤ G (t j))).card : ℝ) := by
  have hG1 : 0 ≤ G 1 := by rw [← hG0]; exact hmono (by norm_num)
  have hle : ∀ j, G (t j) ≤ G 1 := fun j => hmono (ht j).2
  have hge : ∀ j, 0 ≤ G (t j) := fun j => by rw [← hG0]; exact hmono (ht j).1
  have hpt : ∀ y : ℝ, ((Finset.univ.filter (fun j : Fin N => y ≤ G (t j))).card : ℝ)
      = ∑ j, (Set.Iic (G (t j))).indicator (1 : ℝ → ℝ) y := by
    intro y
    rw [← Finset.sum_boole (fun j : Fin N => y ≤ G (t j)) Finset.univ]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp [Set.indicator_apply]
  have hcongr : (fun y : ℝ => ((Finset.univ.filter (fun j : Fin N => y ≤ G (t j))).card : ℝ))
      = fun y => ∑ j, (Set.Iic (G (t j))).indicator (1 : ℝ → ℝ) y := funext hpt
  rw [hcongr, intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [intervalIntegral.integral_of_le hG1]
    have hset : Set.Ioc 0 (G 1) ∩ Set.Iic (G (t j)) = Set.Ioc 0 (G (t j)) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iic]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, le_trans h3 (hle j)⟩, h3⟩
    have hstep : (∫ y in Set.Ioc 0 (G 1), (Set.Iic (G (t j))).indicator (1 : ℝ → ℝ) y
          ∂volume) = volume.real (Set.Ioc 0 (G 1) ∩ Set.Iic (G (t j))) := by
      rw [← MeasureTheory.integral_indicator measurableSet_Ioc, Set.indicator_indicator,
        MeasureTheory.integral_indicator_one (measurableSet_Ioc.inter measurableSet_Iic)]
    rw [hstep, hset, MeasureTheory.measureReal_def, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by linarith [hge j]), sub_zero]
  · intro j _
    exact intervalIntegrable_of_measurable_of_bound
      (measurable_const.indicator measurableSet_Iic) (C := 1) (fun x => by
        by_cases hx : x ∈ Set.Iic (G (t j))
        · rw [Set.indicator_of_mem hx]
          change |(1:ℝ)| ≤ 1
          norm_num
        · rw [Set.indicator_of_notMem hx]; norm_num) 0 (G 1)

/-- Layer-cake / Cavalieri identity in interval form. -/
lemma layercake_mono {G : ℝ → ℝ} (hmono : Monotone G) (hG0 : G 0 = 0) :
    ∫ u in (0 : ℝ)..1, G u =
      ∫ y in (0 : ℝ)..(G 1),
        (volume.restrict (Set.Icc 0 1)).real {x : ℝ | y ≤ G x} := by
  have hG1 : 0 ≤ G 1 := by rw [← hG0]; exact hmono (by norm_num)
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc 0 1)] G := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall (fun x hx => by
      simp only [Pi.zero_apply]
      rw [← hG0]; exact hmono hx.1)
  have hbdd : G ≤ᵐ[volume.restrict (Set.Icc 0 1)] fun _ => G 1 := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall (fun x hx => hmono hx.2)
  have hint : Integrable G (volume.restrict (Set.Icc 0 1)) := by
    refine Integrable.of_bound hmono.measurable.aestronglyMeasurable (G 1) ?_
    rw [ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall (fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by rw [← hG0]; exact hmono hx.1)]
      exact hmono hx.2)
  have hkey := hint.integral_eq_integral_Ioc_meas_le hnn hbdd
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    intervalIntegral.integral_of_le hG1, ← hkey, MeasureTheory.integral_Icc_eq_integral_Ioc]


lemma volume_ne_top_Icc : (volume : Measure ℝ) (Set.Icc (0:ℝ) 1) ≠ ⊤ := by
  rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top

lemma volume_ne_top_Ioc {x : ℝ} : (volume : Measure ℝ) (Set.Ioc x 1) ≠ ⊤ := by
  rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top

lemma volume_ne_top_of_subset_Icc {s : Set ℝ} (hs : s ⊆ Set.Icc (0:ℝ) 1) :
    (volume : Measure ℝ) s ≠ ⊤ :=
  ne_top_of_le_ne_top volume_ne_top_Icc (measure_mono hs)

/-- Pointwise (in `y`) discrepancy bound for the upper level sets of a monotone function: the
empirical fraction of the points `t j` with `y ≤ G (t j)` differs from the measure of
`{x ∈ [0,1] : y ≤ G x}` by at most the box discrepancy `disc t`. -/
lemma slice_bound {N : ℕ} (hN : 0 < N) {G : ℝ → ℝ} (hmono : Monotone G) (hG0 : G 0 = 0)
    (t : Fin N → ℝ) (ht : ∀ j, t j ∈ Set.Icc 0 1) (y : ℝ) :
    |(((Finset.univ.filter (fun j : Fin N => y ≤ G (t j))).card : ℝ) / (N : ℝ)) -
      (volume.restrict (Set.Icc 0 1)).real {x : ℝ | y ≤ G x}| ≤ disc t := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  set U : Set ℝ := {x : ℝ | y ≤ G x} ∩ Set.Icc 0 1 with hU
  have hreal : (volume.restrict (Set.Icc 0 1)).real {x : ℝ | y ≤ G x} = volume.real U := by
    rw [MeasureTheory.measureReal_def,
      MeasureTheory.Measure.restrict_apply (measurableSet_le measurable_const hmono.measurable),
      MeasureTheory.measureReal_def, hU]
  have hB0 : 0 ≤ volume.real U := MeasureTheory.measureReal_nonneg
  have hvolIcc : (volume : Measure ℝ).real (Set.Icc (0:ℝ) 1) = 1 := by
    rw [MeasureTheory.measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1 - 0)]
    norm_num
  have hB1 : volume.real U ≤ 1 := by
    rw [← hvolIcc]
    exact MeasureTheory.measureReal_mono Set.inter_subset_right volume_ne_top_Icc
  have hup : ∀ x z, x ∈ U → x ≤ z → z ∈ Set.Icc 0 1 → z ∈ U := by
    intro x z hx hxz hz
    rw [hU] at hx ⊢
    exact ⟨le_trans hx.1 (hmono hxz), hz⟩
  have hsub1 : Set.Ioc (1 - volume.real U) 1 ⊆ U := by
    intro x hx
    by_contra hxU
    have hx0 : 0 ≤ x := by linarith [hB0, hx.1]
    have hxIcc : x ∈ Set.Icc 0 1 := ⟨hx0, hx.2⟩
    have hsub : U ⊆ Set.Ioc x 1 := by
      intro z hz
      refine ⟨?_, (hU ▸ hz).2.2⟩
      by_contra hzx
      push_neg at hzx
      exact hxU (hup z x hz hzx hxIcc)
    have hle : volume.real U ≤ 1 - x := by
      calc volume.real U ≤ volume.real (Set.Ioc x 1) :=
            MeasureTheory.measureReal_mono hsub volume_ne_top_Ioc
        _ = 1 - x := by
            rw [MeasureTheory.measureReal_def, Real.volume_Ioc,
              ENNReal.toReal_ofReal (by linarith [hxIcc.2] : (0:ℝ) ≤ 1 - x)]
    linarith [hx.1]
  have hsub2 : U ⊆ Set.Ici (1 - volume.real U) := by
    intro z hz
    by_contra hzc
    simp only [Set.mem_Ici, not_le] at hzc
    have hz1 : z ≤ 1 := (hU ▸ hz).2.2
    have hz0 : 0 ≤ z := (hU ▸ hz).2.1
    have hsub : Set.Ioc z 1 ⊆ U := by
      intro w hw
      exact hup z w hz (le_of_lt hw.1) ⟨le_trans hz0 (le_of_lt hw.1), hw.2⟩
    have hge : 1 - z ≤ volume.real U := by
      calc 1 - z = volume.real (Set.Ioc z 1) := by
            rw [MeasureTheory.measureReal_def, Real.volume_Ioc,
              ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ 1 - z)]
        _ ≤ volume.real U :=
            MeasureTheory.measureReal_mono hsub (volume_ne_top_of_subset_Icc Set.inter_subset_right)
    linarith
  have hcnt : cnt t 0 (1 - volume.real U) =
      (Finset.univ.filter (fun j : Fin N => t j < 1 - volume.real U)).card := by
    rw [cnt]
    congr 1
    apply Finset.filter_congr
    intro j _
    simp only [Set.mem_Ico]
    exact ⟨fun h => h.2, fun h => ⟨(ht j).1, h⟩⟩
  have hflt : ({a ∈ (Finset.univ : Finset (Fin N)) | ¬ (1 - volume.real U ≤ t a)}) =
      Finset.univ.filter (fun j : Fin N => t j < 1 - volume.real U) := by
    apply Finset.filter_congr
    intro j _
    exact not_le
  have hcomp := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin N))) (p := fun j : Fin N => 1 - volume.real U ≤ t j)
  rw [hflt, ← hcnt] at hcomp
  simp only [Finset.card_univ, Fintype.card_fin] at hcomp
  have hS1S2 : (Finset.univ.filter (fun j : Fin N => y ≤ G (t j))).card ≤
      (Finset.univ.filter (fun j : Fin N => 1 - volume.real U ≤ t j)).card := by
    apply Finset.card_le_card
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact hsub2 ⟨hj, ht j⟩
  have hS3S1 : (Finset.univ.filter (fun j : Fin N => 1 - volume.real U < t j)).card ≤
      (Finset.univ.filter (fun j : Fin N => y ≤ G (t j))).card := by
    apply Finset.card_le_card
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact (hsub1 ⟨hj, (ht j).2⟩).1
  have hcover : (Finset.univ : Finset (Fin N)) ⊆
      (Finset.univ.filter (fun j : Fin N => 1 - volume.real U < t j)) ∪
        (Finset.univ.filter (fun j : Fin N => t j ≤ 1 - volume.real U)) := by
    intro j _
    by_cases h : 1 - volume.real U < t j
    · exact Finset.mem_union_left _ (by simp [h])
    · push_neg at h
      exact Finset.mem_union_right _ (by simp [h])
  have hcardcover : N ≤ (Finset.univ.filter (fun j : Fin N => 1 - volume.real U < t j)).card +
      (Finset.univ.filter (fun j : Fin N => t j ≤ 1 - volume.real U)).card := by
    have h1 := Finset.card_le_card hcover
    rw [Finset.card_univ, Fintype.card_fin] at h1
    have h2 := Finset.card_union_le
      (Finset.univ.filter (fun j : Fin N => 1 - volume.real U < t j))
      (Finset.univ.filter (fun j : Fin N => t j ≤ 1 - volume.real U))
    omega
  have hdisc1 : (1 - volume.real U) - disc t ≤ ((cnt t 0 (1 - volume.real U) : ℝ)) / (N:ℝ) := by
    have h := abs_sub_cnt_div_le_disc (disc t) t le_rfl
      (a := 0) (b := 1 - volume.real U) le_rfl (by linarith [hB1]) (by linarith [hB0])
    have h7 := (abs_le.mp h).2
    simp only [sub_zero] at h7
    linarith
  have hdisc2 : ((Finset.univ.filter (fun j : Fin N => t j ≤ 1 - volume.real U)).card : ℝ) / (N:ℝ) ≤
      (1 - volume.real U) + disc t :=
    count_le_div_le_add_disc hN t ht ⟨by linarith [hB0], by linarith [hB1]⟩
  set A : ℝ := ((Finset.univ.filter (fun j : Fin N => y ≤ G (t j))).card : ℝ) / (N : ℝ) with hA
  have hAup : A ≤ volume.real U + disc t := by
    have h1 : A ≤ 1 - ((cnt t 0 (1 - volume.real U) : ℝ)) / (N:ℝ) := by
      rw [hA]
      have h2 : ((Finset.univ.filter (fun j : Fin N => y ≤ G (t j))).card : ℝ) ≤
          ((Finset.univ.filter (fun j : Fin N => 1 - volume.real U ≤ t j)).card : ℝ) := by
        exact_mod_cast hS1S2
      have h3 : ((Finset.univ.filter (fun j : Fin N => 1 - volume.real U ≤ t j)).card : ℝ) =
          (N:ℝ) - (cnt t 0 (1 - volume.real U) : ℝ) := by
        have h5 : ((Finset.univ.filter (fun j : Fin N => 1 - volume.real U ≤ t j)).card : ℝ) +
            (cnt t 0 (1 - volume.real U) : ℝ) = (N:ℝ) := by exact_mod_cast hcomp
        linarith
      rw [le_sub_iff_add_le, ← add_div, div_le_one hNpos]
      linarith [h2, h3]
    linarith [hdisc1]
  have hAlow : volume.real U - disc t ≤ A := by
    have h1 : 1 - ((Finset.univ.filter (fun j : Fin N => t j ≤ 1 - volume.real U)).card : ℝ) / (N:ℝ)
        ≤ A := by
      rw [hA, le_div_iff₀ hNpos]
      have h2 : (N:ℝ) - ((Finset.univ.filter (fun j : Fin N => t j ≤ 1 - volume.real U)).card : ℝ) ≤
          ((Finset.univ.filter (fun j : Fin N => y ≤ G (t j))).card : ℝ) := by
        have h3 : (N:ℝ) - ((Finset.univ.filter (fun j : Fin N => t j ≤ 1 - volume.real U)).card : ℝ) ≤
            ((Finset.univ.filter (fun j : Fin N => 1 - volume.real U < t j)).card : ℝ) := by
          have h5 : (N:ℝ) ≤
              ((Finset.univ.filter (fun j : Fin N => 1 - volume.real U < t j)).card : ℝ) +
              ((Finset.univ.filter (fun j : Fin N => t j ≤ 1 - volume.real U)).card : ℝ) := by
            exact_mod_cast hcardcover
          linarith
        have h6 : ((Finset.univ.filter (fun j : Fin N => 1 - volume.real U < t j)).card : ℝ) ≤
            ((Finset.univ.filter (fun j : Fin N => y ≤ G (t j))).card : ℝ) := by
          exact_mod_cast hS3S1
        linarith
      rw [sub_mul, one_mul, div_mul_cancel₀ _ hNne]
      exact h2
    linarith [hdisc2]
  rw [hreal, abs_le]
  exact ⟨by linarith [hAlow], by linarith [hAup]⟩


lemma measureReal_restrict_Icc_le_one (s : Set ℝ) :
    (volume.restrict (Set.Icc (0:ℝ) 1)).real s ≤ 1 := by
  calc (volume.restrict (Set.Icc (0:ℝ) 1)).real s
      ≤ (volume.restrict (Set.Icc (0:ℝ) 1)).real Set.univ :=
        MeasureTheory.measureReal_mono (Set.subset_univ _)
          (by rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Icc];
              exact ENNReal.ofReal_ne_top)
    _ = 1 := by
        rw [MeasureTheory.measureReal_def, MeasureTheory.Measure.restrict_apply_univ,
          Real.volume_Icc, ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1 - 0)]
        norm_num

/-- The core Koksma estimate for a globally monotone `G` with `G 0 = 0`. -/
lemma koksma_core {N : ℕ} (hN : 0 < N) {G : ℝ → ℝ} (hmono : Monotone G) (hG0 : G 0 = 0)
    (t : Fin N → ℝ) (ht : ∀ j, t j ∈ Set.Icc 0 1) :
    |(1 / (N : ℝ)) * ∑ j, G (t j) - ∫ u in (0 : ℝ)..1, G u| ≤ (G 1 - G 0) * disc t := by
  have hG1 : 0 ≤ G 1 := by rw [← hG0]; exact hmono (by norm_num)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hA := sum_eq_integral_count G hmono hG0 t ht
  have hB := layercake_mono hmono hG0
  have hcardmeas : Measurable
      (fun y : ℝ => ((Finset.univ.filter (fun j : Fin N => y ≤ G (t j))).card : ℝ)) := by
    have h : (fun y : ℝ => ((Finset.univ.filter (fun j : Fin N => y ≤ G (t j))).card : ℝ))
        = fun y : ℝ => ∑ j : Fin N, (Set.Iic (G (t j))).indicator (1 : ℝ → ℝ) y := by
      funext y
      rw [← Finset.sum_boole (fun j : Fin N => y ≤ G (t j)) Finset.univ]
      exact Finset.sum_congr rfl (fun j _ => by simp [Set.indicator_apply])
    rw [h]
    exact Finset.measurable_sum Finset.univ
      (fun j _ => measurable_const.indicator measurableSet_Iic)
  have hF1int : IntervalIntegrable
      (fun y : ℝ => ((Finset.univ.filter (fun j : Fin N => y ≤ G (t j))).card : ℝ) / (N : ℝ))
      volume 0 (G 1) := by
    refine intervalIntegrable_of_measurable_of_bound (hcardmeas.div_const _) (C := 1) ?_ 0 (G 1)
    intro y
    have h0 : (0:ℝ) ≤
        ((Finset.univ.filter (fun j : Fin N => y ≤ G (t j))).card : ℝ) / (N : ℝ) := by positivity
    have h1 : ((Finset.univ.filter (fun j : Fin N => y ≤ G (t j))).card : ℝ) / (N : ℝ) ≤ 1 := by
      rw [div_le_one hNpos]
      have h2 := Finset.card_filter_le Finset.univ (fun j : Fin N => y ≤ G (t j))
      rw [Finset.card_univ, Fintype.card_fin] at h2
      exact_mod_cast h2
    exact abs_le.mpr ⟨by linarith, h1⟩
  have hF2anti : Antitone
      (fun y : ℝ => (volume.restrict (Set.Icc 0 1)).real {x : ℝ | y ≤ G x}) := by
    intro y y' hyy'
    refine MeasureTheory.measureReal_mono ?_ ?_
    · intro x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      exact le_trans hyy' hx
    · rw [MeasureTheory.Measure.restrict_apply
        (measurableSet_le measurable_const hmono.measurable)]
      exact volume_ne_top_of_subset_Icc Set.inter_subset_right
  have hF2int : IntervalIntegrable
      (fun y : ℝ => (volume.restrict (Set.Icc 0 1)).real {x : ℝ | y ≤ G x}) volume 0 (G 1) := by
    refine intervalIntegrable_of_measurable_of_bound hF2anti.measurable (C := 1) ?_ 0 (G 1)
    intro y
    exact abs_le.mpr ⟨by
        have := MeasureTheory.measureReal_nonneg
          (μ := volume.restrict (Set.Icc (0:ℝ) 1)) (s := {x : ℝ | y ≤ G x})
        linarith, measureReal_restrict_Icc_le_one _⟩
  have hident : (1 / (N : ℝ)) * ∑ j, G (t j) - ∫ u in (0 : ℝ)..1, G u
      = ∫ y in (0 : ℝ)..(G 1),
          (((Finset.univ.filter (fun j : Fin N => y ≤ G (t j))).card : ℝ) / (N : ℝ) -
            (volume.restrict (Set.Icc 0 1)).real {x : ℝ | y ≤ G x}) := by
    rw [hA, hB]
    have hconv : (1 / (N:ℝ)) * (∫ y in (0:ℝ)..(G 1),
          ((Finset.univ.filter (fun j : Fin N => y ≤ G (t j))).card : ℝ))
        = ∫ y in (0:ℝ)..(G 1),
          ((Finset.univ.filter (fun j : Fin N => y ≤ G (t j))).card : ℝ) / (N:ℝ) := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      funext y
      ring
    rw [hconv, ← intervalIntegral.integral_sub hF1int hF2int]
  rw [hident]
  have hbound : ∀ y ∈ Set.uIoc (0:ℝ) (G 1),
      ‖((Finset.univ.filter (fun j : Fin N => y ≤ G (t j))).card : ℝ) / (N : ℝ) -
        (volume.restrict (Set.Icc 0 1)).real {x : ℝ | y ≤ G x}‖ ≤ disc t := by
    intro y _
    rw [Real.norm_eq_abs]
    exact slice_bound hN hmono hG0 t ht y
  have h1 := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [Real.norm_eq_abs] at h1
  have h2 : disc t * |G 1 - 0| = (G 1 - G 0) * disc t := by
    rw [hG0, sub_zero, abs_of_nonneg hG1]; ring
  linarith


/-- **Koksma's inequality** (monotone form), the equidistribution estimate used twice in the paper's
§"Seeding" and §"Equidistribution". For a function `f` monotone on `[0,1]` and points
`t j ∈ [0,1]`, the deviation of the Riemann sum from the integral is bounded by the box discrepancy
times the total variation `|f 1 - f 0|`. -/
theorem koksma_monotone {N : ℕ} (hN : 0 < N) (f : ℝ → ℝ) (hf : MonotoneOn f (Set.Icc 0 1))
    (t : Fin N → ℝ) (ht : ∀ j, t j ∈ Set.Icc 0 1) :
    |(1 / (N : ℝ)) * ∑ j, f (t j) - ∫ u in (0 : ℝ)..1, f u| ≤
      |f 1 - f 0| * Submission.CDT.Discrepancy.disc t := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have h01 : f 0 ≤ f 1 := hf (by norm_num) (by norm_num) (by norm_num)
  set G : ℝ → ℝ := fun x => f (min 1 (max 0 x)) - f 0 with hGdef
  have hclamp : ∀ x : ℝ, min 1 (max 0 x) ∈ Set.Icc 0 1 := fun x =>
    ⟨le_min (by norm_num) (le_max_left 0 x), min_le_left 1 (max 0 x)⟩
  have hGmono : Monotone G := by
    intro x y hxy
    have h1 : min 1 (max 0 x) ≤ min 1 (max 0 y) := min_le_min le_rfl (max_le_max le_rfl hxy)
    have h2 := hf (hclamp x) (hclamp y) h1
    simp only [hGdef]
    exact sub_le_sub_right h2 (f 0)
  have hG0 : G 0 = 0 := by simp [hGdef]
  have hG1 : G 1 = f 1 - f 0 := by simp [hGdef]
  have hGeq : ∀ x ∈ Set.Icc 0 1, G x = f x - f 0 := by
    intro x hx
    simp only [hGdef]
    rw [min_eq_right (max_le (by norm_num) hx.2), max_eq_right hx.1]
  have hcore := koksma_core hN hGmono hG0 t ht
  have hGbnd : ∀ x : ℝ, |G x| ≤ |f 1 - f 0| := by
    intro x
    have hfa : f 0 ≤ f (min 1 (max 0 x)) := hf (by norm_num) (hclamp x) (hclamp x).1
    have hfb : f (min 1 (max 0 x)) ≤ f 1 := hf (hclamp x) (by norm_num) (hclamp x).2
    have hGx0 : 0 ≤ G x := by simp only [hGdef]; linarith
    have hGx1 : G x ≤ f 1 - f 0 := by simp only [hGdef]; linarith
    rw [abs_of_nonneg hGx0, abs_of_nonneg (by linarith : (0:ℝ) ≤ f 1 - f 0)]
    linarith
  have hsum : ∑ j, f (t j) = ∑ j, G (t j) + (N : ℝ) * f 0 := by
    rw [show (∑ j : Fin N, f (t j)) = ∑ j : Fin N, (G (t j) + f 0) from
      Finset.sum_congr rfl (fun j _ => by rw [hGeq (t j) (ht j)]; ring)]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hint : (∫ u in (0:ℝ)..1, f u) = (∫ u in (0:ℝ)..1, G u) + f 0 := by
    have h1 : (∫ u in (0:ℝ)..1, f u) = ∫ u in (0:ℝ)..1, (G u + f 0) := by
      refine intervalIntegral.integral_congr (fun u hu => ?_)
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hu
      rw [hGeq u hu]
      ring
    rw [h1, intervalIntegral.integral_add
      (intervalIntegrable_of_measurable_of_bound hGmono.measurable hGbnd 0 1)
      intervalIntegrable_const, intervalIntegral.integral_const]
    simp
  have hL : (1 / (N:ℝ)) * ∑ j, f (t j) - (∫ u in (0:ℝ)..1, f u)
      = (1 / (N:ℝ)) * ∑ j, G (t j) - (∫ u in (0:ℝ)..1, G u) := by
    rw [hsum, hint]
    field_simp
    ring
  rw [hL, abs_of_nonneg (by linarith : (0:ℝ) ≤ f 1 - f 0)]
  exact le_trans hcore (le_of_eq (by rw [hG1, hG0, sub_zero]))

end Work.Holonomy3
