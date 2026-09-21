import Mathlib
import Submission.Commons.Geometry.Ulam.body_of_revolution_cap_integrals_even
import Submission.Commons.Geometry.Ulam.intervalIntegral_abs_affine_ball_section_le

namespace Commons.Geometry.Ulam

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

noncomputable section

set_option linter.unusedVariables false


set_option linter.unusedVariables false

private lemma measurableSet_fin_ball_le {m : ℕ} (c : ℝ) :
    MeasurableSet {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ c} := by
  have hsum : Measurable (fun y : Fin m → ℝ => ∑ j : Fin m, (y j)^2) := by
    refine Finset.measurable_sum (Finset.univ : Finset (Fin m)) ?_
    intro j hj
    exact (measurable_pi_apply j).pow measurable_const
  exact measurableSet_le hsum measurable_const

private lemma measurableSet_section {m : ℕ} (L R : ℝ) :
    MeasurableSet {q : ℝ × (Fin m → ℝ) | q.1 ≤ L ∧ q.1 ^ 2 + ∑ j : Fin m, (q.2 j)^2 ≤ R^2} := by
  have h1 : MeasurableSet {q : ℝ × (Fin m → ℝ) | q.1 ≤ L} := by
    exact measurableSet_le (measurable_fst) measurable_const
  have h2 : MeasurableSet {q : ℝ × (Fin m → ℝ) | q.1 ^ 2 + ∑ j : Fin m, (q.2 j)^2 ≤ R^2} := by
    have hz : Measurable (fun q : ℝ × (Fin m → ℝ) => q.1 ^ 2) :=
      (measurable_fst.pow measurable_const)
    have hsum : Measurable (fun q : ℝ × (Fin m → ℝ) => ∑ j : Fin m, (q.2 j)^2) := by
      refine Finset.measurable_sum (Finset.univ : Finset (Fin m)) ?_
      intro j hj
      have hpj : Measurable (fun q : ℝ × (Fin m → ℝ) => q.2 j) :=
        (measurable_pi_apply j).comp measurable_snd
      exact hpj.pow measurable_const
    exact measurableSet_le (hz.add hsum) measurable_const
  exact h1.inter h2

private lemma sq_lt_sq_of_lt_neg {R z : ℝ} (hR : 0 ≤ R) (hz : z < -R) :
    R ^ 2 < z ^ 2 := by
  have hz_neg : z < 0 := by linarith
  have hR_lt_negz : R < -z := by linarith
  rw [sq_lt_sq]
  simpa [abs_of_nonneg hR, abs_of_neg hz_neg] using hR_lt_negz

private lemma sq_lt_sq_of_lt_of_nonneg_left {R z : ℝ} (hR : 0 ≤ R) (h : R < z) :
    R ^ 2 < z ^ 2 := by
  have hz_pos : 0 < z := lt_of_le_of_lt hR h
  rw [sq_lt_sq]
  simpa [abs_of_nonneg hR, abs_of_nonneg hz_pos.le] using h

private lemma fin_ball_le_empty_of_lt_neg {m : ℕ} {R z : ℝ} (hR : 0 ≤ R) (hz : z < -R) :
    {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ R^2 - z^2} = ∅ := by
  have hz_sq_gt : R ^ 2 < z ^ 2 := sq_lt_sq_of_lt_neg hR hz
  have hneg : R ^ 2 - z ^ 2 < 0 := by nlinarith
  ext y
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hy
  have hy' : ∑ j : Fin m, (y j)^2 ≤ R^2 - z^2 := by simpa using hy
  have hsum_nonneg : 0 ≤ ∑ j : Fin m, (y j)^2 := by
    exact Finset.sum_nonneg (by intro j hj; exact sq_nonneg _)
  nlinarith

private lemma section_integral_eq {m : ℕ} {L R : ℝ} {φt : ℝ → ℝ} {ψ : (Fin m → ℝ) → ℝ}
    (hR : 0 ≤ R) {z : ℝ} (hz : z ≠ -R) :
    (∫ y : Fin m → ℝ,
      ({q : ℝ × (Fin m → ℝ) | q.1 ≤ L ∧ q.1 ^ 2 + ∑ j : Fin m, (q.2 j)^2 ≤ R^2}.indicator
        (fun q => φt q.1 * ψ q.2)) (z, y))
    = (Set.Ioc (-R) (min R L)).indicator
        (fun w => φt w * ∫ y : Fin m → ℝ in {y | ∑ j : Fin m, (y j)^2 ≤ R^2 - w^2}, ψ y) z := by
  classical
  let T : Set (ℝ × (Fin m → ℝ)) := {q | q.1 ≤ L ∧ q.1 ^ 2 + ∑ j : Fin m, (q.2 j)^2 ≤ R^2}
  let B : ℝ → Set (Fin m → ℝ) := fun w => {y | ∑ j : Fin m, (y j)^2 ≤ R^2 - w^2}
  let I : Set ℝ := Set.Ioc (-R) (min R L)
  by_cases hzI : z ∈ I
  · have hzI' : -R < z ∧ z ≤ min R L := by simpa [I] using hzI
    have hzL : z ≤ L := by
      have hmin : min R L ≤ L := min_le_right R L
      exact le_trans hzI'.2 hmin
    have hzR : z ≤ R := by
      have hmin : min R L ≤ R := min_le_left R L
      exact le_trans hzI'.2 hmin
    have hz_lower : -R ≤ z := le_of_lt hzI'.1
    have hB_meas : MeasurableSet (B z) := by
      dsimp [B]
      exact measurableSet_fin_ball_le (R ^ 2 - z ^ 2)
    have hmem_iff : ∀ y : Fin m → ℝ, ((z, y) ∈ T ↔ y ∈ B z) := by
      intro y
      constructor
      · intro hq
        rcases hq with ⟨hz_le, hsum_le⟩
        dsimp [B]
        nlinarith
      · intro hy
        dsimp [B] at hy
        constructor
        · exact hzL
        · nlinarith
    have hfun_eq : (fun y : Fin m → ℝ => T.indicator (fun q => φt q.1 * ψ q.2) (z, y))
        = fun y => (B z).indicator (fun y => φt z * ψ y) y := by
      ext y
      by_cases hyB : y ∈ B z
      · have hq : (z, y) ∈ T := (hmem_iff y).mpr hyB
        rw [Set.indicator_of_mem hq, Set.indicator_of_mem hyB]
      · have hq : (z, y) ∉ T := by
          intro hq; exact hyB ((hmem_iff y).mp hq)
        rw [Set.indicator_apply, if_neg hq, Set.indicator_apply, if_neg hyB]
    calc
      ∫ y : Fin m → ℝ, T.indicator (fun q => φt q.1 * ψ q.2) (z, y)
          = ∫ y : Fin m → ℝ, (B z).indicator (fun y => φt z * ψ y) y := by
                rw [hfun_eq]
      _ = ∫ y : Fin m → ℝ in B z, φt z * ψ y := by
                rw [MeasureTheory.integral_indicator hB_meas]
      _ = φt z * ∫ y : Fin m → ℝ in B z, ψ y := by
                rw [MeasureTheory.integral_const_mul]
      _ = I.indicator (fun w => φt w * ∫ y : Fin m → ℝ in B w, ψ y) z := by
                rw [Set.indicator_of_mem hzI]
  · have h_left_zero : (∫ y : Fin m → ℝ, T.indicator (fun q => φt q.1 * ψ q.2) (z, y)) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards with y
      by_cases hzL : z ≤ L
      · by_cases hz_le_neg : z ≤ -R
        · have hz_lt_neg : z < -R := lt_of_le_of_ne hz_le_neg hz
          have hz_sq_gt : R ^ 2 < z ^ 2 := sq_lt_sq_of_lt_neg hR hz_lt_neg
          have hnot : (z, y) ∉ T := by
            intro hq
            rcases hq with ⟨_, hle⟩
            have hsum_nonneg : 0 ≤ ∑ j : Fin m, (y j)^2 := by
              exact Finset.sum_nonneg (by intro j hj; exact sq_nonneg _)
            nlinarith
          rw [Set.indicator_apply, if_neg hnot]
          simp
        · have hlt : -R < z := lt_of_not_ge hz_le_neg
          have hz_not_min : ¬ z ≤ min R L := by
            intro hmin
            exact hzI (by simpa [I] using And.intro hlt hmin)
          have hmin_lt : min R L < z := lt_of_not_ge hz_not_min
          have hz_gt_R : R < z := by
            by_cases hRL : R ≤ L
            · have hmin_eq : min R L = R := min_eq_left hRL
              linarith
            · have hLR : L < R := lt_of_not_ge hRL
              have hmin_eq : min R L = L := min_eq_right (le_of_lt hLR)
              linarith
          have hz_sq_gt : R ^ 2 < z ^ 2 := sq_lt_sq_of_lt_of_nonneg_left hR hz_gt_R
          have hnot : (z, y) ∉ T := by
            intro hq
            rcases hq with ⟨_, hle⟩
            have hsum_nonneg : 0 ≤ ∑ j : Fin m, (y j)^2 := by
              exact Finset.sum_nonneg (by intro j hj; exact sq_nonneg _)
            nlinarith
          rw [Set.indicator_apply, if_neg hnot]
          simp
      · have hz_gt_L : L < z := lt_of_not_ge hzL
        have hnot : (z, y) ∉ T := by
          intro hq
          rcases hq with ⟨hz_le, _⟩
          linarith
        rw [Set.indicator_apply, if_neg hnot]
        simp
    have h_right_zero : I.indicator (fun w => φt w * ∫ y : Fin m → ℝ in B w, ψ y) z = 0 := by
      rw [Set.indicator_apply, if_neg hzI]
    rw [h_left_zero, h_right_zero]

lemma indicator_section_integral_eq_interval {m : ℕ} [Nonempty (Fin m)] {L R : ℝ} {φt : ℝ → ℝ}
    {ψ : (Fin m → ℝ) → ℝ}
    (hR : 0 ≤ R)
    (h_ind_int : MeasureTheory.Integrable ({q : ℝ × (Fin m → ℝ) | q.1 ≤ L ∧ q.1 ^ 2 + ∑ j : Fin m, (q.2 j)^2 ≤ R^2}.indicator
        (fun q : ℝ × (Fin m → ℝ) => φt q.1 * ψ q.2))
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ)))) :
    (∫ q : ℝ × (Fin m → ℝ) in {q : ℝ × (Fin m → ℝ) | q.1 ≤ L ∧ q.1 ^ 2 + ∑ j : Fin m, (q.2 j)^2 ≤ R^2},
        φt q.1 * ψ q.2
      ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod (MeasureTheory.volume : MeasureTheory.Measure (Fin m → ℝ))))
    = ∫ z in (-R)..(min R L),
        φt z * (∫ y : Fin m → ℝ in {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ R^2 - z^2}, ψ y) := by
  classical
  let μℝ : Measure ℝ := volume
  let μy : Measure (Fin m → ℝ) := volume
  let ν : Measure (ℝ × (Fin m → ℝ)) := μℝ.prod μy
  let T : Set (ℝ × (Fin m → ℝ)) := {q | q.1 ≤ L ∧ q.1 ^ 2 + ∑ j : Fin m, (q.2 j)^2 ≤ R^2}
  let F : ℝ × (Fin m → ℝ) → ℝ := fun q => φt q.1 * ψ q.2
  let B : ℝ → Set (Fin m → ℝ) := fun w => {y | ∑ j : Fin m, (y j)^2 ≤ R^2 - w^2}
  let G : ℝ → ℝ := fun w => φt w * ∫ y : Fin m → ℝ in B w, ψ y
  let I : Set ℝ := Set.Ioc (-R) (min R L)
  have hT_meas : MeasurableSet T := by
    simpa [T] using measurableSet_section (m := m) L R
  have hF_ind_int : Integrable (T.indicator F) ν := by
    simpa [ν, μℝ, μy, T, F] using h_ind_int
  have hFub := MeasureTheory.integral_prod (μ := μℝ) (ν := μy) (T.indicator F) hF_ind_int
  have hset_int : (∫ q : ℝ × (Fin m → ℝ) in T, F q ∂ν) = ∫ q, T.indicator F q ∂ν := by
    rw [MeasureTheory.integral_indicator hT_meas]
  have h_all : (∫ q : ℝ × (Fin m → ℝ), T.indicator F q ∂ν) =
      ∫ z : ℝ, ∫ y : Fin m → ℝ, T.indicator F (z, y) ∂μy ∂μℝ := by
    simpa [ν, μℝ, μy, F] using hFub
  have h_ae : (fun z => ∫ y : Fin m → ℝ, T.indicator F (z, y) ∂μy) =ᵐ[μℝ] I.indicator G := by
    filter_upwards [Measure.ae_ne μℝ (-R)] with z hz
    have hsec := section_integral_eq (m := m) (L := L) (R := R) (φt := φt) (ψ := ψ) hR hz
    simpa [T, F, B, G, I, μℝ, μy] using hsec
  have h_zint : (∫ z : ℝ, ∫ y : Fin m → ℝ, T.indicator F (z, y) ∂μy ∂μℝ) =
      ∫ z : ℝ, I.indicator G z ∂μℝ := by
    exact integral_congr_ae h_ae
  have h_Iint : (∫ z : ℝ, I.indicator G z ∂μℝ) = ∫ z : ℝ in I, G z ∂μℝ := by
    rw [MeasureTheory.integral_indicator]
    exact measurableSet_Ioc
  have h_all_I : (∫ q : ℝ × (Fin m → ℝ), T.indicator F q ∂ν) = ∫ z : ℝ in I, G z ∂μℝ := by
    rw [h_all, h_zint, h_Iint]
  by_cases hle : -R ≤ min R L
  · have h_interval : (∫ z in (-R)..(min R L), G z) = ∫ z : ℝ in I, G z ∂μℝ := by
      rw [intervalIntegral.integral_of_le hle]
    calc
      (∫ q : ℝ × (Fin m → ℝ) in T, F q ∂ν) = ∫ q : ℝ × (Fin m → ℝ), T.indicator F q ∂ν := hset_int
      _ = ∫ z : ℝ in I, G z ∂μℝ := h_all_I
      _ = ∫ z in (-R)..(min R L), G z := h_interval.symm
      _ = ∫ z in (-R)..(min R L), φt z * (∫ y : Fin m → ℝ in B z, ψ y) := by rfl
  · have hgt : min R L < -R := lt_of_not_ge hle
    have hI_empty : I = ∅ := by
      dsimp [I]
      exact Set.Ioc_eq_empty_of_le hgt.le
    have h_all_zero : (∫ q : ℝ × (Fin m → ℝ), T.indicator F q ∂ν) = 0 := by
      rw [h_all_I, hI_empty, MeasureTheory.setIntegral_empty]
    have h_interval_zero : (∫ z in (-R)..(min R L), G z) = 0 := by
      rw [intervalIntegral.integral_of_ge hgt.le]
      have hset : (∫ z : ℝ in Set.Ioc (min R L) (-R), G z ∂μℝ) = 0 := by
        apply setIntegral_eq_zero_of_ae_eq_zero
        filter_upwards [Measure.ae_ne μℝ (-R)] with z hzne hzmem
        have hzmem' : min R L < z ∧ z ≤ -R := Set.mem_Ioc.mp hzmem
        have hz_lt : z < -R := lt_of_le_of_ne hzmem'.2 hzne
        have hB_empty : B z = ∅ := by
          dsimp [B]
          exact fin_ball_le_empty_of_lt_neg hR hz_lt
        dsimp [G]
        rw [hB_empty]
        simp
      have hset_vol : (∫ z : ℝ in Set.Ioc (min R L) (-R), G z) = 0 := by
        simpa [μℝ] using hset
      simp [hset_vol]
    calc
      (∫ q : ℝ × (Fin m → ℝ) in T, F q ∂ν) = ∫ q : ℝ × (Fin m → ℝ), T.indicator F q ∂ν := hset_int
      _ = 0 := h_all_zero
      _ = ∫ z in (-R)..(min R L), G z := h_interval_zero.symm
      _ = ∫ z in (-R)..(min R L), φt z * (∫ y : Fin m → ℝ in B z, ψ y) := by rfl


set_option linter.unusedVariables false

-- finite measure of section in z,y
lemma section_finite {m : ℕ} {L R : ℝ} :
    (volume : Measure (ℝ × (Fin m → ℝ))) {q : ℝ × (Fin m → ℝ) | q.1 ≤ L ∧ q.1 ^ 2 + ∑ j : Fin m, (q.2 j)^2 ≤ R ^ 2} < ⊤ := by
  have hsub : {q : ℝ × (Fin m → ℝ) | q.1 ≤ L ∧ q.1 ^ 2 + ∑ j : Fin m, (q.2 j)^2 ≤ R ^ 2} ⊆
      Metric.closedBall (0 : ℝ × (Fin m → ℝ)) |R| := by
    intro q hq
    rcases hq with ⟨hL, hsum⟩
    have hsum_nonneg : 0 ≤ ∑ j : Fin m, (q.2 j)^2 := by positivity
    have hq1_sq : q.1 ^ 2 ≤ R ^ 2 := by nlinarith
    have hq1_abs : |q.1| ≤ |R| := by
      exact abs_le_of_sq_le_sq (by nlinarith [sq_abs R]) (abs_nonneg R)
    have hy_abs : ∀ j : Fin m, |q.2 j| ≤ |R| := by
      intro j
      have hcoord : (q.2 j)^2 ≤ ∑ i : Fin m, (q.2 i)^2 := by
        exact Finset.single_le_sum (f := fun i : Fin m => (q.2 i)^2) (s := Finset.univ) (by intro i hi; exact sq_nonneg _) (Finset.mem_univ j)
      have hcoord_sum : ∑ i : Fin m, (q.2 i)^2 ≤ q.1 ^ 2 + ∑ i : Fin m, (q.2 i)^2 := by nlinarith [sq_nonneg q.1]
      have hsq : (q.2 j)^2 ≤ R ^ 2 := le_trans (le_trans hcoord hcoord_sum) hsum
      exact abs_le_of_sq_le_sq (by nlinarith [sq_abs R]) (abs_nonneg R)
    have hq2_norm : ‖q.2‖ ≤ |R| := by
      rw [pi_norm_le_iff_of_nonneg (abs_nonneg R)]
      intro j
      simpa [Real.norm_eq_abs] using hy_abs j
    have hq1_norm : ‖q.1‖ ≤ |R| := by simpa [Real.norm_eq_abs] using hq1_abs
    rw [Metric.mem_closedBall, dist_eq_norm]
    simpa [Prod.norm_def, hq1_norm, hq2_norm] using max_le hq1_norm hq2_norm
  exact lt_of_le_of_lt (measure_mono hsub) (measure_closedBall_lt_top)

lemma integrableOn_affine_abs_section {m : ℕ} {t L R : ℝ} {A B C : ℝ} (hR : 0 ≤ R) :
    IntegrableOn (fun q : ℝ × (Fin m → ℝ) => |A * t + B * q.1 + C|)
      ({q : ℝ × (Fin m → ℝ) | q.1 ≤ L ∧ q.1 ^ 2 + ∑ j : Fin m, (q.2 j)^2 ≤ R ^ 2})
      (volume : Measure (ℝ × (Fin m → ℝ))) := by
  let T : Set (ℝ × (Fin m → ℝ)) := {q | q.1 ≤ L ∧ q.1 ^ 2 + ∑ j : Fin m, (q.2 j)^2 ≤ R ^ 2}
  have hT_finite : volume T < ⊤ := by simpa [T] using section_finite (m := m) (L := L) (R := R)
  have hmeas : AEStronglyMeasurable (fun q : ℝ × (Fin m → ℝ) => |A * t + B * q.1 + C|) volume := by
    measurability
  let M : ℝ := |A * t + C| + |B| * |R|
  have hT_meas : MeasurableSet T := by
    dsimp [T]
    measurability
  refine Measure.integrableOn_of_bounded (s := T) (μ := (volume : Measure (ℝ × (Fin m → ℝ))))
    (ne_of_lt hT_finite) hmeas (M := M) ?_
  rw [ae_restrict_iff' hT_meas]
  filter_upwards with q hqT
  have hq_mem : q ∈ T → |q.1| ≤ |R| := by
    intro hq
    rcases hq with ⟨hL, hsum⟩
    have hq1_sq : q.1 ^ 2 ≤ R ^ 2 := by
      have hsum_nonneg : 0 ≤ ∑ j : Fin m, (q.2 j)^2 := by positivity
      nlinarith
    exact abs_le_of_sq_le_sq (by nlinarith [sq_abs R]) (abs_nonneg R)
  have hz : |q.1| ≤ |R| := hq_mem hqT
  have hb : |B * q.1| ≤ |B| * |R| := by
    calc
      |B * q.1| = |B| * |q.1| := abs_mul B q.1
      _ ≤ |B| * |R| := mul_le_mul_of_nonneg_left hz (abs_nonneg B)
  have htri : |A * t + B * q.1 + C| ≤ |A * t + C| + |B * q.1| := by
    simpa [add_assoc, add_comm, add_left_comm] using abs_add_le (A * t + C) (B * q.1)
  calc
    ‖|A * t + B * q.1 + C|‖ = |A * t + B * q.1 + C| := by simp [Real.norm_eq_abs]
    _ ≤ |A * t + C| + |B * q.1| := htri
    _ ≤ |A * t + C| + |B| * |R| := by exact add_le_add_right hb (|A * t + C|)


set_option linter.unusedVariables false

lemma inner_norm_integral_eq_interval {m : ℕ} [Nonempty (Fin m)] {t L R : ℝ} {A B C : ℝ}
    (hR : 0 ≤ R)
    (h_ind_int : Integrable ({q : ℝ × (Fin m → ℝ) | q.1 ≤ L ∧ q.1 ^ 2 + ∑ j : Fin m, (q.2 j)^2 ≤ R^2}.indicator
        (fun q : ℝ × (Fin m → ℝ) => |A * t + B * q.1 + C|))
      ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ)))) :
    (∫ q : ℝ × (Fin m → ℝ), ‖({q : ℝ × (Fin m → ℝ) | q.1 ≤ L ∧ q.1 ^ 2 + ∑ j : Fin m, (q.2 j)^2 ≤ R^2}.indicator
        (fun q : ℝ × (Fin m → ℝ) => A * t + B * q.1 + C)) q‖
      ∂((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))))
    = ∫ z in (-R)..(min R L),
        |A * t + B * z + C| * volume.real {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ R^2 - z^2} := by
  let T : Set (ℝ × (Fin m → ℝ)) := {q | q.1 ≤ L ∧ q.1 ^ 2 + ∑ j : Fin m, (q.2 j)^2 ≤ R^2}
  let F : ℝ × (Fin m → ℝ) → ℝ := fun q => A * t + B * q.1 + C
  have hT_meas : MeasurableSet T := by
    dsimp [T]
    measurability
  change (∫ q : ℝ × (Fin m → ℝ), ‖T.indicator F q‖ ∂((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ)))) =
      ∫ z in (-R)..(min R L),
        |A * t + B * z + C| * volume.real {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ R^2 - z^2}
  have h_left : (∫ q : ℝ × (Fin m → ℝ), ‖T.indicator F q‖ ∂((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ)))) =
      ∫ q : ℝ × (Fin m → ℝ), T.indicator (fun q => |F q|) q ∂((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))) := by
    apply integral_congr_ae
    filter_upwards with q
    by_cases hq : q ∈ T
    · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq]
      dsimp [F]
    · rw [Set.indicator_apply, if_neg hq, Set.indicator_apply, if_neg hq]
      simp [F]
  have h_abs_ind_int : Integrable (T.indicator (fun q : ℝ × (Fin m → ℝ) => |F q| * (1 : ℝ)))
      ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))) := by
    simpa [T, F] using h_ind_int
  rw [h_left]
  have hsec := indicator_section_integral_eq_interval (m := m) (L := L) (R := R)
    (φt := fun z => |A * t + B * z + C|) (ψ := fun _ : Fin m → ℝ => (1 : ℝ)) hR h_abs_ind_int
  have hy : ∀ z, (∫ y : Fin m → ℝ in {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ R^2 - z^2}, (1 : ℝ)) =
      volume.real {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ R^2 - z^2} := by
    intro z
    rw [MeasureTheory.setIntegral_const]
    simp
  have hsec_T : (∫ q : ℝ × (Fin m → ℝ) in T, (fun q => |F q| * (1 : ℝ)) q ∂((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ)))) =
      ∫ z in (-R)..(min R L),
        |A * t + B * z + C| * volume.real {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ R^2 - z^2} := by
    simpa [T, F, hy] using hsec
  rw [← MeasureTheory.integral_indicator hT_meas] at hsec_T
  simpa [T, F] using hsec_T


lemma intervalIntegral_section_eq_setIntegral_Icc_max {m : ℕ} [Nonempty (Fin m)] {F L : ℝ}
    {φ : ℝ → ℝ} (hF : 0 ≤ F) :
    (∫ z in (-F)..(min F L), φ z * volume.real {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ F^2 - z^2})
    = ∫ z in Set.Icc (-F) (max (-F) (min F L)),
        φ z * volume.real {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ F^2 - z^2} := by
  let U : ℝ := max (-F) (min F L)
  by_cases hle : -F ≤ min F L
  · have hUeq : U = min F L := by
      dsimp [U]
      exact max_eq_right hle
    have hU_lower : -F ≤ U := by
      rw [hUeq]; exact hle
    have hset : (∫ z in (-F)..(min F L), φ z * volume.real {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ F^2 - z^2}) =
        ∫ z in Set.Icc (-F) (min F L), φ z * volume.real {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ F^2 - z^2} := by
      rw [Commons.Geometry.Ulam.intervalIntegral_eq_setIntegral_Icc hle]
    simpa [U, hUeq] using hset
  · have hgt : min F L < -F := lt_of_not_ge hle
    have hUeq : U = -F := by
      dsimp [U]
      exact max_eq_left hgt.le
    have h_left : (∫ z in (-F)..(min F L), φ z * volume.real {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ F^2 - z^2}) = 0 := by
      rw [intervalIntegral.integral_of_ge hgt.le]
      have hset_int : (∫ z in Set.Ioc (min F L) (-F), φ z * volume.real {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ F^2 - z^2}) = 0 := by
        apply setIntegral_eq_zero_of_ae_eq_zero
        filter_upwards [Measure.ae_ne volume (-F)] with z hzne hzmem
        have hzmem' : min F L < z ∧ z ≤ -F := Set.mem_Ioc.mp hzmem
        have hz_lt : z < -F := lt_of_le_of_ne hzmem'.2 hzne
        have hball_empty : {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ F^2 - z^2} = ∅ := by
          have hz_sq_gt : F ^ 2 < z ^ 2 := by
            have hz_neg : z < 0 := by linarith
            have hF_lt_negz : F < -z := by linarith
            rw [sq_lt_sq]
            simpa [abs_of_nonneg hF, abs_of_neg hz_neg] using hF_lt_negz
          have hneg : F ^ 2 - z ^ 2 < 0 := by nlinarith
          ext y
          simp only [Set.mem_empty_iff_false, iff_false]
          intro hy
          have hy' : ∑ j : Fin m, (y j)^2 ≤ F^2 - z^2 := by simpa using hy
          have hsum_nonneg : 0 ≤ ∑ j : Fin m, (y j)^2 := by
            exact Finset.sum_nonneg (by intro j hj; exact sq_nonneg _)
          nlinarith
        rw [hball_empty]
        simp
      simp [hset_int]
    have h_right : (∫ z in Set.Icc (-F) (max (-F) (min F L)), φ z * volume.real {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ F^2 - z^2}) = 0 := by
      have hUeq' : max (-F) (min F L) = -F := hUeq
      rw [hUeq']
      have hIcc_sing : Set.Icc (-F) (-F) = ({(-F)} : Set ℝ) := by
        ext z
        simp [le_antisymm_iff]
      rw [hIcc_sing]
      rw [← MeasureTheory.integral_indicator (measurableSet_singleton (-F) : MeasurableSet ({(-F)} : Set ℝ))]
      apply integral_eq_zero_of_ae
      filter_upwards [Measure.ae_ne volume (-F)] with z hz
      rw [Set.indicator_apply, if_neg]
      · simp
      · intro h; exact hz (Set.mem_singleton_iff.mp h)
    rw [h_left, h_right]


lemma measurableSet_target_S {m : ℕ} {a b s h : ℝ} {f : ℝ → ℝ}
    (hf_meas : Measurable f) :
    MeasurableSet ({p : ℝ × (ℝ × (Fin m → ℝ)) | p.1 ∈ Set.Icc a b ∧ p.2.1 ≤ s * p.1 + h ∧
        p.2.1 ^ 2 + ∑ j : Fin m, (p.2.2 j)^2 ≤ f p.1 ^ 2}) := by
  measurability

lemma integrable_ball_section_affine_of_intervalIntegrable
    {m : ℕ} [Nonempty (Fin m)] {a b s h : ℝ} {f : ℝ → ℝ} {A B C : ℝ}
    (hab : a ≤ b) (hf_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t) (hf_meas : Measurable f)
    (hG : IntervalIntegrable (fun t => ∫ z in (-f t)..(min (f t) (s * t + h)),
        (A * t + B * z + C) * volume.real {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ f t ^ 2 - z ^ 2}) volume a b) :
    Integrable (({p : ℝ × (ℝ × (Fin m → ℝ)) | p.1 ∈ Set.Icc a b ∧ p.2.1 ≤ s * p.1 + h ∧
        p.2.1 ^ 2 + ∑ j : Fin m, (p.2.2 j)^2 ≤ f p.1 ^ 2}).indicator (fun p : ℝ × (ℝ × (Fin m → ℝ)) => A * p.1 + B * p.2.1 + C))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ)))) := by
  classical
  let S : Set (ℝ × (ℝ × (Fin m → ℝ))) :=
    {p | p.1 ∈ Set.Icc a b ∧ p.2.1 ≤ s * p.1 + h ∧
      p.2.1 ^ 2 + ∑ j : Fin m, (p.2.2 j)^2 ≤ f p.1 ^ 2}
  let g : ℝ × (ℝ × (Fin m → ℝ)) → ℝ := fun p => A * p.1 + B * p.2.1 + C
  let P : Measure (ℝ × (ℝ × (Fin m → ℝ))) :=
    (volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ)))
  change Integrable (S.indicator g) P
  let A_set : Set ℝ := Set.Icc a b
  let U : ℝ → ℝ := fun t => max (-f t) (min (f t) (s * t + h))
  let φ : ℝ → ℝ → ℝ := fun t z => A * t + B * z + C
  let W : ℝ → ℝ → ℝ := fun t z => volume.real {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ f t ^ 2 - z ^ 2}
  have hS_meas : MeasurableSet S := by
    dsimp [S]
    exact measurableSet_target_S (m := m) (a := a) (b := b) (s := s) (h := h) (f := f) hf_meas
  have hg_meas : Measurable g := by
    dsimp [g]
    measurability
  have hg_aestrong : AEStronglyMeasurable (S.indicator g) P := by
    exact (hg_meas.indicator hS_meas).aestronglyMeasurable
  have h_inner_int : ∀ t : ℝ,
      Integrable (fun q : ℝ × (Fin m → ℝ) => (S.indicator g) (t, q))
        ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))) := by
    intro t
    by_cases ht : t ∈ A_set
    · let Tt : Set (ℝ × (Fin m → ℝ)) := {q | q.1 ≤ s * t + h ∧ q.1 ^ 2 + ∑ j : Fin m, (q.2 j)^2 ≤ f t ^ 2}
      have hTt_meas : MeasurableSet Tt := by
        dsimp [Tt]
        measurability
      have hR : 0 ≤ f t := hf_nonneg t ht
      have h_eq : (fun q : ℝ × (Fin m → ℝ) => (S.indicator g) (t, q)) =
          Tt.indicator (fun q : ℝ × (Fin m → ℝ) => A * t + B * q.1 + C) := by
        ext q
        by_cases hq : q ∈ Tt
        · have hp : (t, q) ∈ S := by
            dsimp [S, Tt] at hq ⊢
            exact ⟨ht, hq.1, hq.2⟩
          rw [Set.indicator_of_mem hp]
          rw [Set.indicator_of_mem hq]
        · have hp : (t, q) ∉ S := by
            intro hp
            dsimp [S, Tt] at hp ⊢
            exact hq ⟨hp.2.1, hp.2.2⟩
          rw [Set.indicator_apply, if_neg hp, Set.indicator_apply, if_neg hq]
      have hIntOn : IntegrableOn (fun q : ℝ × (Fin m → ℝ) => A * t + B * q.1 + C) Tt
          (volume : Measure (ℝ × (Fin m → ℝ))) := by
        have hTt_finite : volume Tt < ⊤ := by
          simpa [Tt] using section_finite (m := m) (L := s * t + h) (R := f t)
        have hmeas : AEStronglyMeasurable (fun q : ℝ × (Fin m → ℝ) => A * t + B * q.1 + C) volume := by
          measurability
        let M : ℝ := |A * t| + |B| * |f t| + |C|
        refine Measure.integrableOn_of_bounded (s := Tt) (μ := (volume : Measure (ℝ × (Fin m → ℝ))))
          (ne_of_lt hTt_finite) hmeas (M := M) ?_
        rw [ae_restrict_iff' hTt_meas]
        filter_upwards with q hqT
        have hz : |q.1| ≤ |f t| := by
          rcases hqT with ⟨hL, hsum⟩
          have hsum_nonneg : 0 ≤ ∑ j : Fin m, (q.2 j)^2 := by positivity
          have hq1_sq : q.1 ^ 2 ≤ f t ^ 2 := by nlinarith
          exact abs_le_of_sq_le_sq (by nlinarith [sq_abs (f t)]) (abs_nonneg (f t))
        have hb : |B * q.1| ≤ |B| * |f t| := by
          calc
            |B * q.1| = |B| * |q.1| := abs_mul B q.1
            _ ≤ |B| * |f t| := mul_le_mul_of_nonneg_left hz (abs_nonneg B)
        have htri : |A * t + B * q.1 + C| ≤ |A * t| + |B * q.1| + |C| := by
          have h1 := abs_add_le (A * t) (B * q.1 + C)
          have h2 := abs_add_le (B * q.1) C
          have h1' : |A * t + (B * q.1 + C)| ≤ |A * t| + (|B * q.1| + |C|) := by
            exact le_trans h1 (add_le_add_right h2 (|A * t|))
          simpa [add_assoc] using h1'
        calc
          ‖A * t + B * q.1 + C‖ = |A * t + B * q.1 + C| := by simp [Real.norm_eq_abs]
          _ ≤ |A * t| + |B * q.1| + |C| := htri
          _ ≤ |A * t| + |B| * |f t| + |C| := by nlinarith [hb]
      have hind : Integrable (Tt.indicator (fun q : ℝ × (Fin m → ℝ) => A * t + B * q.1 + C))
          (volume : Measure (ℝ × (Fin m → ℝ))) :=
        MeasureTheory.IntegrableOn.integrable_indicator hIntOn hTt_meas
      exact hind.congr (Filter.Eventually.of_forall (fun q => by rw [h_eq]))
    · have hzero : (fun q : ℝ × (Fin m → ℝ) => (S.indicator g) (t, q)) = 0 := by
        ext q
        have hp : (t, q) ∉ S := by
          intro hp
          exact ht hp.1
        rw [Set.indicator_apply, if_neg hp]
        simp [g]
      rw [hzero]
      exact integrable_zero (α := ℝ × (Fin m → ℝ)) (ε' := ℝ)
        ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ)))
  have h_inner_norm_eq : ∀ t : ℝ, t ∈ A_set →
      (∫ q : ℝ × (Fin m → ℝ), ‖(S.indicator g) (t, q)‖
        ∂((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ)))) =
      ∫ z in Set.Icc (-f t) (U t), |φ t z| * W t z := by
    intro t ht
    let Tt : Set (ℝ × (Fin m → ℝ)) := {q | q.1 ≤ s * t + h ∧ q.1 ^ 2 + ∑ j : Fin m, (q.2 j)^2 ≤ f t ^ 2}
    have hTt_meas : MeasurableSet Tt := by
      dsimp [Tt]
      measurability
    have hR : 0 ≤ f t := hf_nonneg t ht
    have h_eq : (fun q : ℝ × (Fin m → ℝ) => (S.indicator g) (t, q)) =
        Tt.indicator (fun q : ℝ × (Fin m → ℝ) => A * t + B * q.1 + C) := by
      ext q
      by_cases hq : q ∈ Tt
      · have hp : (t, q) ∈ S := by
          dsimp [S, Tt] at hq ⊢
          exact ⟨ht, hq.1, hq.2⟩
        rw [Set.indicator_of_mem hp, Set.indicator_of_mem hq]
      · have hp : (t, q) ∉ S := by
          intro hp
          dsimp [S, Tt] at hp ⊢
          exact hq ⟨hp.2.1, hp.2.2⟩
        rw [Set.indicator_apply, if_neg hp, Set.indicator_apply, if_neg hq]
    have h_abs_ind_int : Integrable (Tt.indicator (fun q : ℝ × (Fin m → ℝ) => |A * t + B * q.1 + C|))
        ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))) := by
      have hIntOn : IntegrableOn (fun q : ℝ × (Fin m → ℝ) => |A * t + B * q.1 + C|) Tt
          (volume : Measure (ℝ × (Fin m → ℝ))) := by
        exact integrableOn_affine_abs_section (m := m) (t := t) (L := s * t + h) (R := f t) (A := A) (B := B) (C := C) hR
      exact MeasureTheory.IntegrableOn.integrable_indicator hIntOn hTt_meas
    have hnorm : (∫ q : ℝ × (Fin m → ℝ), ‖(S.indicator g) (t, q)‖
          ∂((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ)))) =
        ∫ q : ℝ × (Fin m → ℝ), ‖Tt.indicator (fun q : ℝ × (Fin m → ℝ) => A * t + B * q.1 + C) q‖
          ∂((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))) := by
      apply integral_congr_ae
      filter_upwards with q
      have hqeq := congrFun h_eq q
      exact congrArg abs hqeq
    rw [hnorm]
    have hformula := inner_norm_integral_eq_interval (m := m) (t := t) (L := s * t + h) (R := f t)
      (A := A) (B := B) (C := C) hR h_abs_ind_int
    have hconv := intervalIntegral_section_eq_setIntegral_Icc_max (m := m) (F := f t) (L := s * t + h)
      (φ := fun z => |A * t + B * z + C|) hR
    rw [hconv] at hformula
    simpa [Tt, φ, W, U] using hformula
  have hconv_G : ∀ t : ℝ, t ∈ A_set →
      (∫ z in (-f t)..(min (f t) (s * t + h)), φ t z * W t z) =
      ∫ z in Set.Icc (-f t) (U t), φ t z * W t z := by
    intro t ht
    have hF : 0 ≤ f t := hf_nonneg t ht
    simpa [φ, W, U] using (intervalIntegral_section_eq_setIntegral_Icc_max (m := m) (F := f t) (L := s * t + h) (φ := fun z => φ t z) hF)
  have hG_Icc : IntegrableOn (fun t => ∫ z in (-f t)..(min (f t) (s * t + h)), φ t z * W t z) A_set volume := by
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hG
  have hG'_Icc : IntegrableOn (fun t => ∫ z in Set.Icc (-f t) (U t), φ t z * W t z) A_set volume := by
    refine hG_Icc.congr_fun ?_ measurableSet_Icc
    intro t ht
    exact hconv_G t ht
  have hG_ind_int : Integrable (A_set.indicator (fun t => ∫ z in Set.Icc (-f t) (U t), φ t z * W t z)) volume :=
    MeasureTheory.IntegrableOn.integrable_indicator hG'_Icc measurableSet_Icc
  have hH_eq_ind : (fun t : ℝ => ∫ q : ℝ × (Fin m → ℝ), ‖(S.indicator g) (t, q)‖
        ∂((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ)))) =
      A_set.indicator (fun t => ∫ z in Set.Icc (-f t) (U t), |φ t z| * W t z) := by
    funext t
    by_cases ht : t ∈ A_set
    · rw [Set.indicator_of_mem ht, h_inner_norm_eq t ht]
    · have hzero : (∫ q : ℝ × (Fin m → ℝ), ‖(S.indicator g) (t, q)‖
          ∂((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ)))) = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards with q
        have hp : (t, q) ∉ S := by
          intro hp
          exact ht hp.1
        rw [Set.indicator_apply, if_neg hp]
        simp [g]
      rw [Set.indicator_apply, if_neg ht, hzero]
  rcases intervalIntegral_abs_affine_ball_section_le (m := m) (a := a) (b := b) (s := s) (h := h)
    (f := f) (A := A) (B := B) (C := C) hab hf_nonneg with ⟨C1, C2, hC1_nonneg, hC2_nonneg, hbound⟩
  have hbound_full : ∀ᵐ t ∂volume, t ∈ A_set →
      (∫ z in Set.Icc (-f t) (U t), |φ t z| * W t z) ≤
        C1 * |∫ z in Set.Icc (-f t) (U t), φ t z * W t z| + C2 := by
    have hb := (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp hbound
    filter_upwards [hb] with t ht hmem
    have hW_nonneg : ∀ z, 0 ≤ W t z := by
      intro z
      dsimp [W]
      exact measureReal_nonneg
    have hleft_eq : (∫ z in Set.Icc (-f t) (U t), |(A * t + B * z + C) * W t z|) =
        ∫ z in Set.Icc (-f t) (U t), |φ t z| * W t z := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro z hz
      dsimp [φ, W]
      rw [abs_mul, abs_of_nonneg (hW_nonneg z)]
    have hright_eq : (∫ z in Set.Icc (-f t) (U t), (A * t + B * z + C) * W t z) =
        ∫ z in Set.Icc (-f t) (U t), φ t z * W t z := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro z hz
      dsimp [φ]
    have hmain := ht hmem
    rw [hleft_eq] at hmain
    rw [hright_eq] at hmain
    simpa [A_set, U, φ, W] using hmain
  have hH_aestrong : AEStronglyMeasurable (fun t : ℝ => ∫ q : ℝ × (Fin m → ℝ), ‖(S.indicator g) (t, q)‖
        ∂((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ)))) volume :=
    hg_aestrong.norm.integral_prod_right'
  have hH_eq_ind_abs : (fun t : ℝ => ∫ q : ℝ × (Fin m → ℝ), |(S.indicator g) (t, q)|
        ∂((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ)))) =
      A_set.indicator (fun t => ∫ z in Set.Icc (-f t) (U t), |φ t z| * W t z) := by
    simpa [Real.norm_eq_abs] using hH_eq_ind
  have hHind_aestrong : AEStronglyMeasurable (A_set.indicator (fun t => ∫ z in Set.Icc (-f t) (U t), |φ t z| * W t z)) volume := by
    simpa [hH_eq_ind_abs] using hH_aestrong
  have hA_finite : volume A_set < ⊤ := by
    dsimp [A_set]
    exact measure_Icc_lt_top
  have hC2_ind_int : Integrable (A_set.indicator (fun _ : ℝ => C2)) volume := by
    exact MeasureTheory.IntegrableOn.integrable_indicator
      (integrableOn_const (μ := volume) (s := A_set) (C := C2) (ne_of_lt hA_finite)) measurableSet_Icc
  have hG_abs_int : Integrable (fun t : ℝ => |A_set.indicator (fun t => ∫ z in Set.Icc (-f t) (U t), φ t z * W t z) t|) volume :=
    hG_ind_int.abs
  have hRHS_int : Integrable (fun t : ℝ => C1 * |A_set.indicator (fun t => ∫ z in Set.Icc (-f t) (U t), φ t z * W t z) t| + A_set.indicator (fun _ : ℝ => C2) t) volume :=
    (hG_abs_int.const_mul C1).add hC2_ind_int
  have hH_bound : ∀ᵐ t ∂volume,
      ‖A_set.indicator (fun t => ∫ z in Set.Icc (-f t) (U t), |φ t z| * W t z) t‖ ≤
        C1 * |A_set.indicator (fun t => ∫ z in Set.Icc (-f t) (U t), φ t z * W t z) t| + A_set.indicator (fun _ : ℝ => C2) t := by
    filter_upwards [hbound_full] with t ht
    by_cases htA : t ∈ A_set
    · have h := ht htA
      have hnonneg : 0 ≤ A_set.indicator (fun t => ∫ z in Set.Icc (-f t) (U t), |φ t z| * W t z) t := by
        simp [htA]
        exact setIntegral_nonneg measurableSet_Icc (fun z hz => mul_nonneg (abs_nonneg _) (by dsimp [W]; exact measureReal_nonneg))
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      simpa [htA] using h
    · have hzero : A_set.indicator (fun t => ∫ z in Set.Icc (-f t) (U t), |φ t z| * W t z) t = 0 := by
        simp [htA]
      simp [htA, hzero]
  have hHind_int : Integrable (A_set.indicator (fun t => ∫ z in Set.Icc (-f t) (U t), |φ t z| * W t z)) volume := by
    exact Integrable.mono' hRHS_int hHind_aestrong hH_bound
  have hH_full_int : Integrable (fun t : ℝ => ∫ q : ℝ × (Fin m → ℝ), ‖(S.indicator g) (t, q)‖
        ∂((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ)))) volume := by
    simpa [Real.norm_eq_abs, hH_eq_ind_abs] using hHind_int
  rw [MeasureTheory.integrable_prod_iff hg_aestrong]
  constructor
  · filter_upwards with t
    exact h_inner_int t
  · exact hH_full_int


end

end Commons.Geometry.Ulam
