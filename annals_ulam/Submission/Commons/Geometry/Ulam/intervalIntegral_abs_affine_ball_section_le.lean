import Mathlib
import Submission.Commons.Geometry.Ulam.body_of_revolution_cap_integrals_even

namespace Commons.Geometry.Ulam

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

noncomputable section

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

noncomputable def ballMeasure (m : ℕ) [Nonempty (Fin m)] (F z : ℝ) : ℝ :=
  volume.real {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ F^2 - z^2}

noncomputable def ballMeasureC (m : ℕ) [Nonempty (Fin m)] : ℝ :=
  volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) 1)

lemma ballMeasure_eq_sqrt {m : ℕ} [Nonempty (Fin m)] {F z : ℝ} (hF : 0 ≤ F)
    (hz : z ∈ Set.Icc (-F) F) :
    ballMeasure m F z = ballMeasureC m * (Real.sqrt (F^2 - z^2)) ^ m := by
  have hnonneg : 0 ≤ F^2 - z^2 := by
    have hz_sq_le : z^2 ≤ F^2 := sq_le_sq' hz.1 hz.2
    nlinarith
  let R := Real.sqrt (F^2 - z^2)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R^2 = F^2 - z^2 := Real.sq_sqrt hnonneg
  have h := volume_real_fin_ball_pow (m := m) R hR
  simpa [ballMeasure, ballMeasureC, R, hR2] using h

lemma ballMeasure_even {m : ℕ} [Nonempty (Fin m)] (F z : ℝ) :
    ballMeasure m F (-z) = ballMeasure m F z := by
  simp [ballMeasure, neg_sq]

lemma ballMeasure_nonneg {m : ℕ} [Nonempty (Fin m)] (F z : ℝ) :
    0 ≤ ballMeasure m F z := by
  dsimp [ballMeasure]
  exact measureReal_nonneg

lemma ballMeasure_le {m : ℕ} [Nonempty (Fin m)] {F z : ℝ} (hF : 0 ≤ F)
    (hz : z ∈ Set.Icc (-F) F) :
    ballMeasure m F z ≤ ballMeasureC m * F ^ m := by
  have hsub : {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ F^2 - z^2} ⊆
      {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ F^2} := by
    intro y hy
    simp at hy ⊢
    have hzsq : 0 ≤ z^2 := sq_nonneg z
    nlinarith
  calc
    ballMeasure m F z = volume.real {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ F^2 - z^2} := rfl
    _ ≤ volume.real {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ F^2} := by
          apply measureReal_mono hsub (ne_of_lt (volume_fin_ball_lt_top F))
    _ = ballMeasureC m * F ^ m := by
          exact volume_real_fin_ball_pow F hF

lemma ballMeasure_ge_of_abs_le {m : ℕ} [Nonempty (Fin m)] {F z : ℝ} (hF : 0 ≤ F)
    (hz : |z| ≤ F / 2) :
    ballMeasureC m * (F / 2) ^ m ≤ ballMeasure m F z := by
  have hFhalf : 0 ≤ F / 2 := by nlinarith
  have hsub : {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ (F / 2)^2} ⊆
      {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ F^2 - z^2} := by
    intro y hy
    simp at hy ⊢
    have hzsq : z^2 ≤ (F/2)^2 := by
      rw [sq_le_sq]
      simpa [abs_of_nonneg hFhalf] using hz
    nlinarith
  have hfin : volume {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ F^2 - z^2} < ⊤ := by
    apply lt_of_le_of_lt (measure_mono ?_) (volume_fin_ball_lt_top F)
    intro y hy
    simp at hy ⊢
    have hzsq : 0 ≤ z^2 := sq_nonneg z
    nlinarith
  calc
    ballMeasureC m * (F / 2) ^ m
        = volume.real {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ (F / 2)^2} := by
          exact (volume_real_fin_ball_pow (F / 2) hFhalf).symm
    _ ≤ volume.real {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ F^2 - z^2} := by
          apply measureReal_mono hsub (ne_of_lt hfin)
    _ = ballMeasure m F z := rfl

lemma ballMeasure_ge_of_abs_le_three_quarters {m : ℕ} [Nonempty (Fin m)] {F z : ℝ} (hF : 0 ≤ F)
    (hz : |z| ≤ 3 * F / 4) :
    ballMeasureC m * (F / 2) ^ m ≤ ballMeasure m F z := by
  have hFhalf : 0 ≤ F / 2 := by nlinarith
  have hsub : {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ (F / 2)^2} ⊆
      {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ F^2 - z^2} := by
    intro y hy
    simp at hy ⊢
    have hzsq : z^2 ≤ (3*F/4)^2 := by
      rw [sq_le_sq]
      have hpos : 0 ≤ 3 * F / 4 := by nlinarith
      simpa [abs_of_nonneg hpos] using hz
    nlinarith
  have hfin : volume {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ F^2 - z^2} < ⊤ := by
    apply lt_of_le_of_lt (measure_mono ?_) (volume_fin_ball_lt_top F)
    intro y hy
    simp at hy ⊢
    have hzsq : 0 ≤ z^2 := sq_nonneg z
    nlinarith
  calc
    ballMeasureC m * (F / 2) ^ m
        = volume.real {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ (F / 2)^2} := by
          exact (volume_real_fin_ball_pow (F / 2) hFhalf).symm
    _ ≤ volume.real {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ F^2 - z^2} := by
          apply measureReal_mono hsub (ne_of_lt hfin)
    _ = ballMeasure m F z := rfl

lemma intervalIntegrable_ballMeasure_of_mem_Icc {m : ℕ} [Nonempty (Fin m)] {F a b : ℝ}
    (hF : 0 ≤ F) (ha : a ∈ Set.Icc (-F) F) (hb : b ∈ Set.Icc (-F) F) :
    IntervalIntegrable (fun z => ballMeasure m F z) volume a b := by
  let g : ℝ → ℝ := fun z => ballMeasureC m * (Real.sqrt (F^2 - z^2)) ^ m
  have hcont : ContinuousOn g (Set.uIcc a b) := by
    dsimp [g]
    fun_prop
  have hsub : Set.uIcc a b ⊆ Set.Icc (-F) F := Set.uIcc_subset_Icc ha hb
  have h_eq : Set.EqOn (fun z => ballMeasure m F z) g (Set.uIcc a b) := by
    intro z hz
    exact ballMeasure_eq_sqrt hF (hsub hz)
  have hcont' : ContinuousOn (fun z => ballMeasure m F z) (Set.uIcc a b) := by
    exact hcont.congr h_eq
  exact hcont'.intervalIntegrable

lemma intervalIntegrable_z_ballMeasure_of_mem_Icc {m : ℕ} [Nonempty (Fin m)] {F a b : ℝ}
    (hF : 0 ≤ F) (ha : a ∈ Set.Icc (-F) F) (hb : b ∈ Set.Icc (-F) F) :
    IntervalIntegrable (fun z => z * ballMeasure m F z) volume a b := by
  let g : ℝ → ℝ := fun z => z * ballMeasureC m * (Real.sqrt (F^2 - z^2)) ^ m
  have hcont : ContinuousOn g (Set.uIcc a b) := by
    dsimp [g]
    fun_prop
  have hsub : Set.uIcc a b ⊆ Set.Icc (-F) F := Set.uIcc_subset_Icc ha hb
  have h_eq : Set.EqOn (fun z => z * ballMeasure m F z) g (Set.uIcc a b) := by
    intro z hz
    have hzI := hsub hz
    change z * ballMeasure m F z = g z
    have hball := ballMeasure_eq_sqrt (m := m) hF hzI
    rw [hball]
    dsimp [g]
    ring
  have hcont' : ContinuousOn (fun z => z * ballMeasure m F z) (Set.uIcc a b) := by
    exact hcont.congr h_eq
  exact hcont'.intervalIntegrable

lemma integral_odd_symm {F : ℝ} {W : ℝ → ℝ} (hWeven : ∀ z, W (-z) = W z) :
    (∫ z in (-F)..F, z * W z) = 0 := by
  let g : ℝ → ℝ := fun z => z * W z
  have hg_odd : ∀ z, g (-z) = - g z := by
    intro z
    simp [g, hWeven z]
  have hcomp := intervalIntegral.integral_comp_neg (a := -F) (b := F) (f := g)
  have hcong : (∫ z in (-F)..F, g (-z)) = (∫ z in (-F)..F, -g z) := by
    apply intervalIntegral.integral_congr
    intro z hz
    exact hg_odd z
  have hmain : (∫ z in (-F)..F, g z) = - (∫ z in (-F)..F, g z) := by
    calc
      (∫ z in (-F)..F, g z) = (∫ z in (-F)..F, g (-z)) := by simpa using hcomp.symm
      _ = (∫ z in (-F)..F, -g z) := hcong
      _ = - (∫ z in (-F)..F, g z) := by rw [intervalIntegral.integral_neg]
  linarith

lemma intervalIntegral_z_ball_eq_neg {m : ℕ} [Nonempty (Fin m)] {F U : ℝ} (hF : 0 ≤ F)
    (hU_lower : -F ≤ U) (hU_upper : U ≤ F) :
    (∫ z in (-F)..U, z * ballMeasure m F z) =
      - ∫ z in U..F, z * ballMeasure m F z := by
  let g : ℝ → ℝ := fun z => z * ballMeasure m F z
  have hWeven : ∀ z, ballMeasure m F (-z) = ballMeasure m F z := ballMeasure_even (m := m) F
  have hsymm : (∫ z in (-F)..F, g z) = 0 := by
    simpa [g] using integral_odd_symm (F := F) (W := fun z => ballMeasure m F z) hWeven
  have h_negF_mem : (-F) ∈ Set.Icc (-F) F := ⟨le_rfl, by linarith⟩
  have hF_mem : F ∈ Set.Icc (-F) F := ⟨by linarith, le_rfl⟩
  have hU_mem : U ∈ Set.Icc (-F) F := ⟨hU_lower, hU_upper⟩
  have hIU : IntervalIntegrable g volume (-F) U := by
    exact intervalIntegrable_z_ballMeasure_of_mem_Icc (m := m) (F := F) (a := -F) (b := U) hF h_negF_mem hU_mem
  have hUF : IntervalIntegrable g volume U F := by
    exact intervalIntegrable_z_ballMeasure_of_mem_Icc (m := m) (F := F) (a := U) (b := F) hF hU_mem hF_mem
  have hadd := intervalIntegral.integral_add_adjacent_intervals (a := -F) (b := U) (c := F)
      (f := g) (μ := volume) hIU hUF
  have hsum : (∫ z in (-F)..U, g z) + ∫ z in U..F, g z = 0 := by
    simpa [hsymm] using hadd
  linarith

lemma intervalIntegral_z_even_eq_negU {F U : ℝ} {W : ℝ → ℝ} (hWeven : ∀ z, W (-z) = W z)
    (hintU0 : IntervalIntegrable (fun z => z * W z) volume U 0)
    (hint0F : IntervalIntegrable (fun z => z * W z) volume 0 F)
    (hintnU0 : IntervalIntegrable (fun z => z * W z) volume (-U) 0) :
    (∫ z in U..F, z * W z) = ∫ z in (-U)..F, z * W z := by
  let g : ℝ → ℝ := fun z => z * W z
  have hg_odd : ∀ z, g (-z) = - g z := by
    intro z
    simp [g, hWeven z]
  have hcomp := intervalIntegral.integral_comp_neg (a := U) (b := 0) (f := g)
  have hcong : (∫ x in U..0, g (-x)) = ∫ x in U..0, -g x := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact hg_odd x
  have hU0 : (∫ x in U..0, g x) = ∫ x in (-U)..0, g x := by
    have hneg : (∫ x in U..0, -g x) = - ∫ x in U..0, g x := by
      rw [intervalIntegral.integral_neg]
    have hcomp' : - ∫ x in U..0, g x = ∫ x in 0..(-U), g x := by
      have htemp := hcomp.symm.trans hcong
      rw [hneg] at htemp
      have htemp' := htemp.symm
      simpa using htemp'
    have hsymm : ∫ x in 0..(-U), g x = - ∫ x in (-U)..0, g x := by
      rw [intervalIntegral.integral_symm]
    linarith
  have hadd1 := intervalIntegral.integral_add_adjacent_intervals (a := U) (b := 0) (c := F)
      (f := g) (μ := volume) hintU0 hint0F
  have hadd2 := intervalIntegral.integral_add_adjacent_intervals (a := -U) (b := 0) (c := F)
      (f := g) (μ := volume) hintnU0 hint0F
  calc
    (∫ z in U..F, g z) = (∫ z in U..0, g z) + ∫ z in 0..F, g z := by simpa using hadd1.symm
    _ = (∫ z in (-U)..0, g z) + ∫ z in 0..F, g z := by rw [hU0]
    _ = ∫ z in (-U)..F, g z := by simpa using hadd2

lemma intervalIntegral_z_ball_eq_negU {m : ℕ} [Nonempty (Fin m)] {F U : ℝ} (hF : 0 ≤ F)
    (hU_lower : -F ≤ U) (hU_upper : U ≤ F) :
    (∫ z in U..F, z * ballMeasure m F z) = ∫ z in (-U)..F, z * ballMeasure m F z := by
  have hW_even : ∀ z, ballMeasure m F (-z) = ballMeasure m F z := ballMeasure_even (m := m) F
  have h_negF_mem : (-F) ∈ Set.Icc (-F) F := ⟨le_rfl, by linarith⟩
  have hF_mem : F ∈ Set.Icc (-F) F := ⟨by linarith, le_rfl⟩
  have hU_mem : U ∈ Set.Icc (-F) F := ⟨hU_lower, hU_upper⟩
  have h0_mem : (0 : ℝ) ∈ Set.Icc (-F) F := ⟨by linarith, by linarith⟩
  have hnegU_mem : (-U) ∈ Set.Icc (-F) F := by
    constructor <;> nlinarith
  have hintU0 : IntervalIntegrable (fun z => z * ballMeasure m F z) volume U 0 := by
    exact intervalIntegrable_z_ballMeasure_of_mem_Icc (m := m) (F := F) (a := U) (b := 0) hF hU_mem h0_mem
  have hint0F : IntervalIntegrable (fun z => z * ballMeasure m F z) volume 0 F := by
    exact intervalIntegrable_z_ballMeasure_of_mem_Icc (m := m) (F := F) (a := 0) (b := F) hF h0_mem hF_mem
  have hintnU0 : IntervalIntegrable (fun z => z * ballMeasure m F z) volume (-U) 0 := by
    exact intervalIntegrable_z_ballMeasure_of_mem_Icc (m := m) (F := F) (a := -U) (b := 0) hF hnegU_mem h0_mem
  exact intervalIntegral_z_even_eq_negU hW_even hintU0 hint0F hintnU0

lemma intervalIntegral_z_ball_subinterval_lower {m : ℕ} [Nonempty (Fin m)] {F : ℝ} (hF : 0 ≤ F) :
    ballMeasureC m * (1 / (8 * (2 : ℝ) ^ m)) * F ^ (m + 2) ≤
      ∫ z in (F / 2)..(3 * F / 4), z * ballMeasure m F z := by
  let W : ℝ → ℝ := fun z => ballMeasure m F z
  let const : ℝ := ballMeasureC m * (F / 2) ^ m * (F / 2)
  have h_meas : IntervalIntegrable (fun z => z * W z) volume (F / 2) (3 * F / 4) := by
    have h1 : (F / 2) ∈ Set.Icc (-F) F := by constructor <;> nlinarith
    have h2 : (3 * F / 4) ∈ Set.Icc (-F) F := by constructor <;> nlinarith
    exact intervalIntegrable_z_ballMeasure_of_mem_Icc (m := m) (F := F) (a := F / 2) (b := 3 * F / 4) hF h1 h2
  have h_const_int : IntervalIntegrable (fun _ : ℝ => const) volume (F / 2) (3 * F / 4) := by
    exact intervalIntegrable_const
  have hle : ∀ z ∈ Set.Icc (F / 2) (3 * F / 4), const ≤ z * W z := by
    intro z hz
    have hz_ge : F / 2 ≤ z := hz.1
    have hz_le : z ≤ 3 * F / 4 := hz.2
    have hz_abs : |z| ≤ 3 * F / 4 := by
      rw [abs_le]
      constructor
      · linarith
      · linarith
    have hW_ge : ballMeasureC m * (F / 2) ^ m ≤ W z := by
      dsimp [W]
      exact ballMeasure_ge_of_abs_le_three_quarters (m := m) hF hz_abs
    have hprod : ballMeasureC m * (F / 2) ^ m * (F / 2) ≤ z * W z := by
      have hmul := mul_le_mul (a := ballMeasureC m * (F / 2) ^ m) (b := W z) (c := F / 2) (d := z)
        hW_ge hz_ge (by nlinarith) (ballMeasure_nonneg (m := m) F z)
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    simpa [const, mul_assoc] using hprod
  have hmono := intervalIntegral.integral_mono_on (a := F / 2) (b := 3 * F / 4) (μ := volume)
    (f := fun _ : ℝ => const) (g := fun z => z * W z) (by nlinarith) h_const_int h_meas hle
  have hconst_eq : (∫ z in (F / 2)..(3 * F / 4), const) = ballMeasureC m * (1 / (8 * (2 : ℝ) ^ m)) * F ^ (m + 2) := by
    rw [intervalIntegral.integral_const]
    dsimp [const]
    rw [show (3 * F / 4 - F / 2) = F / 4 by ring]
    rw [div_pow]
    ring_nf
  calc
    ballMeasureC m * (1 / (8 * (2 : ℝ) ^ m)) * F ^ (m + 2)
        = ∫ z in (F / 2)..(3 * F / 4), const := by rw [hconst_eq]
    _ ≤ ∫ z in (F / 2)..(3 * F / 4), z * W z := hmono

lemma intervalIntegral_z_ball_ge_of_U_between {m : ℕ} [Nonempty (Fin m)] {F U : ℝ} (hF : 0 ≤ F)
    (hU_le : U ≤ F / 2) (hU_ge : -F / 2 ≤ U) :
    (∫ z in (F / 2)..(3 * F / 4), z * ballMeasure m F z) ≤
      ∫ z in U..F, z * ballMeasure m F z := by
  let g : ℝ → ℝ := fun z => z * ballMeasure m F z
  have hU_lower : -F ≤ U := by linarith
  have hU_upper : U ≤ F := by linarith
  have hU_mem : U ∈ Set.Icc (-F) F := ⟨hU_lower, hU_upper⟩
  have hF_mem : F ∈ Set.Icc (-F) F := ⟨by linarith, le_rfl⟩
  have h0_mem : (0 : ℝ) ∈ Set.Icc (-F) F := ⟨by linarith, by linarith⟩
  have hnegU_mem : (-U) ∈ Set.Icc (-F) F := by constructor <;> nlinarith
  have hintUF : IntervalIntegrable g volume U F := by
    exact intervalIntegrable_z_ballMeasure_of_mem_Icc (m := m) (F := F) (a := U) (b := F) hF hU_mem hF_mem
  have hintnUF : IntervalIntegrable g volume (-U) F := by
    exact intervalIntegrable_z_ballMeasure_of_mem_Icc (m := m) (F := F) (a := -U) (b := F) hF hnegU_mem hF_mem
  by_cases hU0 : 0 ≤ U
  · have hmono := intervalIntegral.integral_mono_interval (f := g) (a := F / 2) (b := 3 * F / 4)
      (c := U) (d := F) hU_le (by nlinarith) (by nlinarith) ?_ hintUF
    · simpa [g] using hmono
    · change ∀ᵐ z ∂(volume.restrict (Set.Ioc U F)), 0 ≤ g z
      rw [ae_restrict_iff' measurableSet_Ioc]
      filter_upwards with z hz
      have hz_pos : 0 ≤ z := by
        have hz_low : U < z := hz.1
        linarith
      exact mul_nonneg hz_pos (ballMeasure_nonneg (m := m) F z)
  · have hUneg : U < 0 := lt_of_not_ge hU0
    have hnegU_nonneg : 0 ≤ -U := by linarith
    have hnegU_le : -U ≤ F / 2 := by linarith
    have hshift := intervalIntegral_z_ball_eq_negU (m := m) (F := F) (U := U) hF hU_lower hU_upper
    have hmono := intervalIntegral.integral_mono_interval (f := g) (a := F / 2) (b := 3 * F / 4)
      (c := -U) (d := F) hnegU_le (by nlinarith) (by nlinarith) ?_ hintnUF
    · calc
        (∫ z in (F / 2)..(3 * F / 4), g z) ≤ ∫ z in (-U)..F, g z := hmono
        _ = ∫ z in U..F, g z := by simpa [g] using hshift.symm
    · change ∀ᵐ z ∂(volume.restrict (Set.Ioc (-U) F)), 0 ≤ g z
      rw [ae_restrict_iff' measurableSet_Ioc]
      filter_upwards with z hz
      have hz_pos : 0 ≤ z := by
        have hz_low : -U < z := hz.1
        linarith
      exact mul_nonneg hz_pos (ballMeasure_nonneg (m := m) F z)


lemma abs_le_C1_abs_of_bounds {E O J I Iabs α β Rc C1 : ℝ}
    (hE_nonneg : 0 ≤ E) (hO_nonpos : O ≤ 0)
    (hI_eq : I = α * E + β * O)
    (hIabs_le : Iabs ≤ |α| * E + |β| * J)
    (hJ_le_O : J ≤ Rc * (-O))
    (hY_ge_2X : 2 * (|α| * E) ≤ |β| * (-O))
    (hRc_nonneg : 0 ≤ Rc)
    (hC1_eq : C1 = 1 + 2 * Rc) :
    Iabs ≤ C1 * |I| := by
  have hIminus : I - α * E = β * O := by linarith [hI_eq]
  have htri := abs_add_le I (-(α * E))
  have htri' : |β * O| ≤ |I| + |α * E| := by
    calc
      |β * O| = |I - α * E| := by rw [hIminus]
      _ = |I + -(α * E)| := by ring
      _ ≤ |I| + |-(α * E)| := htri
      _ = |I| + |α * E| := by rw [abs_neg]
  have hβO_abs : |β * O| = |β| * (-O) := by
    rw [abs_mul, abs_of_nonpos hO_nonpos]
  have hαE_abs : |α * E| = |α| * E := by
    rw [abs_mul, abs_of_nonneg hE_nonneg]
  have hlower : |β| * (-O) - |α| * E ≤ |I| := by linarith
  have hI_lower : (1 / 2 : ℝ) * (|β| * (-O)) ≤ |I| := by linarith
  have hJpart : |β| * J ≤ Rc * (|β| * (-O)) := by
    calc
      |β| * J ≤ |β| * (Rc * (-O)) := mul_le_mul_of_nonneg_left hJ_le_O (abs_nonneg β)
      _ = Rc * (|β| * (-O)) := by ring
  have hX_le_Y_half : |α| * E ≤ (1 / 2 : ℝ) * (|β| * (-O)) := by
    have h2 : 2 * (|α| * E) ≤ |β| * (-O) := hY_ge_2X
    calc
      |α| * E = (1 / 2 : ℝ) * (2 * (|α| * E)) := by ring
      _ ≤ (1 / 2 : ℝ) * (|β| * (-O)) := mul_le_mul_of_nonneg_left h2 (by norm_num)
  have hY_nonneg : 0 ≤ |β| * (-O) := by
    exact mul_nonneg (abs_nonneg β) (neg_nonneg_of_nonpos hO_nonpos)
  have hY_le : |β| * (-O) ≤ 2 * |I| := by
    calc
      |β| * (-O) = 2 * ((1 / 2 : ℝ) * (|β| * (-O))) := by ring
      _ ≤ 2 * |I| := mul_le_mul_of_nonneg_left hI_lower (by norm_num)
  have hcoeff_nonneg : 0 ≤ (1 / 2 : ℝ) + Rc := by linarith [hRc_nonneg]
  calc
    Iabs ≤ |α| * E + |β| * J := hIabs_le
    _ ≤ (1 / 2 : ℝ) * (|β| * (-O)) + Rc * (|β| * (-O)) := add_le_add hX_le_Y_half hJpart
    _ = ((1 / 2 : ℝ) + Rc) * (|β| * (-O)) := by ring
    _ ≤ ((1 / 2 : ℝ) + Rc) * (2 * |I|) := by
      apply mul_le_mul_of_nonneg_left hY_le hcoeff_nonneg
    _ = (1 + 2 * Rc) * |I| := by ring
    _ = C1 * |I| := by rw [hC1_eq]


lemma intervalIntegral_abs_affine_ball_le_const_aux {m : ℕ} [Nonempty (Fin m)]
    {K M β0 : ℝ} (hK : 0 ≤ K) (hM : 0 ≤ M) (hβ0 : 0 < β0) :
    ∃ C1 C2 : ℝ, 0 ≤ C1 ∧ 0 ≤ C2 ∧
      ∀ F L α β : ℝ, 0 ≤ F → |L| ≤ M → |α| ≤ K → β0 ≤ |β| → |β| ≤ K →
      (∫ z in (-F)..(max (-F) (min F L)), |(α + β * z) * ballMeasure m F z|) ≤
        C1 * |∫ z in (-F)..(max (-F) (min F L)), (α + β * z) * ballMeasure m F z| + C2 := by
  classical
  let c : ℝ := ballMeasureC m
  let Rc : ℝ := 16 * (2 : ℝ) ^ m
  let A_o : ℝ := 1 / (8 * (2 : ℝ) ^ m)
  let C1 : ℝ := 1 + 2 * Rc
  let Fmax : ℝ := max (4 * M) (32 * (2 : ℝ) ^ m * K / β0)
  let C2 : ℝ := 2 * c * Fmax ^ (m + 1) * (K + K * Fmax)
  have hc_nonneg : 0 ≤ c := by dsimp [c, ballMeasureC]; exact measureReal_nonneg
  have hRc_nonneg : 0 ≤ Rc := by dsimp [Rc]; positivity
  have hA_o_pos : 0 < A_o := by dsimp [A_o]; positivity
  have hFmax_nonneg : 0 ≤ Fmax := by
    dsimp [Fmax]
    have h4M : 0 ≤ 4 * M := by positivity
    exact le_trans h4M (le_max_left (4 * M) (32 * (2 : ℝ) ^ m * K / β0))
  have hC1_nonneg : 0 ≤ C1 := by dsimp [C1]; positivity
  have hC2_nonneg : 0 ≤ C2 := by
    dsimp [C2]
    positivity
  refine ⟨C1, C2, hC1_nonneg, hC2_nonneg, ?_⟩
  intro F L α β hF hL hα hβlow hβup
  let U : ℝ := max (-F) (min F L)
  let W : ℝ → ℝ := fun z => ballMeasure m F z
  have hU_lower : -F ≤ U := by dsimp [U]; exact le_max_left _ _
  have hU_upper : U ≤ F := by
    dsimp [U]
    exact max_le (by linarith) (min_le_left _ _)
  have h_negF_mem : (-F) ∈ Set.Icc (-F) F := ⟨le_rfl, by linarith⟩
  have hF_mem : F ∈ Set.Icc (-F) F := ⟨by linarith, le_rfl⟩
  have hU_mem : U ∈ Set.Icc (-F) F := ⟨hU_lower, hU_upper⟩
  have hW_int : IntervalIntegrable W volume (-F) U := by
    exact intervalIntegrable_ballMeasure_of_mem_Icc (m := m) (F := F) (a := -F) (b := U) hF h_negF_mem hU_mem
  have hzW_int : IntervalIntegrable (fun z => z * W z) volume (-F) U := by
    exact intervalIntegrable_z_ballMeasure_of_mem_Icc (m := m) (F := F) (a := -F) (b := U) hF h_negF_mem hU_mem
  have hlin_int : IntervalIntegrable (fun z => (α + β * z) * W z) volume (-F) U := by
    have hlin_cont : ContinuousOn (fun z : ℝ => α + β * z) (Set.uIcc (-F) U) := by fun_prop
    exact hW_int.continuousOn_mul hlin_cont
  have habs_int : IntervalIntegrable (fun z => |(α + β * z) * W z|) volume (-F) U := by
    exact hlin_int.abs
  have habszW_int : IntervalIntegrable (fun z => |z| * W z) volume (-F) U := by
    have hzW_abs : (fun z => |z| * W z) = fun z => |z * W z| := by
      funext z
      rw [abs_mul]
      rw [abs_of_nonneg (ballMeasure_nonneg (m := m) F z)]
    rw [hzW_abs]
    exact hzW_int.abs
  have hE_nonneg : 0 ≤ (∫ z in (-F)..U, W z) := by
    exact intervalIntegral.integral_nonneg_of_forall hU_lower (fun z => ballMeasure_nonneg (m := m) F z)
  have hJ_nonneg : 0 ≤ (∫ z in (-F)..U, |z| * W z) := by
    exact intervalIntegral.integral_nonneg_of_forall hU_lower (fun z => by
      exact mul_nonneg (abs_nonneg z) (ballMeasure_nonneg (m := m) F z))
  let E : ℝ := ∫ z in (-F)..U, W z
  let O : ℝ := ∫ z in (-F)..U, z * W z
  let J : ℝ := ∫ z in (-F)..U, |z| * W z
  let I : ℝ := ∫ z in (-F)..U, (α + β * z) * W z
  let Iabs : ℝ := ∫ z in (-F)..U, |(α + β * z) * W z|
  have hI_eq : I = α * E + β * O := by
    dsimp [I, E, O]
    have hfun : (fun z => (α + β * z) * W z) = fun z => α * W z + β * (z * W z) := by
      funext z; ring
    rw [hfun]
    rw [intervalIntegral.integral_add]
    · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    · exact hW_int.const_mul α
    · exact hzW_int.const_mul β
  have hIabs_le : Iabs ≤ |α| * E + |β| * J := by
    dsimp [Iabs, E, J]
    have hpoint : ∀ z ∈ Set.Icc (-F) U, |(α + β * z) * W z| ≤ |α| * W z + |β| * (|z| * W z) := by
      intro z hz
      have hWnonneg : 0 ≤ W z := by dsimp [W]; exact ballMeasure_nonneg (m := m) F z
      have htri : |α + β * z| ≤ |α| + |β| * |z| := by
        calc
          |α + β * z| ≤ |α| + |β * z| := abs_add_le α (β * z)
          _ = |α| + |β| * |z| := by rw [abs_mul]
      have hmul := mul_le_mul_of_nonneg_right htri hWnonneg
      have hrewrite : |(α + β * z) * W z| = |α + β * z| * W z := by
        rw [abs_mul, abs_of_nonneg hWnonneg]
      rw [hrewrite]
      nlinarith
    have hsum_int : IntervalIntegrable (fun z => |α| * W z + |β| * (|z| * W z)) volume (-F) U := by
      exact (hW_int.const_mul |α|).add (habszW_int.const_mul |β|)
    have hmono := intervalIntegral.integral_mono_on (a := -F) (b := U) (μ := volume)
      (f := fun z => |(α + β * z) * W z|) (g := fun z => |α| * W z + |β| * (|z| * W z))
      hU_lower habs_int hsum_int hpoint
    calc
      (∫ z in (-F)..U, |(α + β * z) * W z|) ≤ ∫ z in (-F)..U, (|α| * W z + |β| * (|z| * W z)) := hmono
      _ = |α| * (∫ z in (-F)..U, W z) + |β| * (∫ z in (-F)..U, |z| * W z) := by
        rw [intervalIntegral.integral_add]
        · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
        · exact hW_int.const_mul |α|
        · exact habszW_int.const_mul |β|
  by_cases hbig : Fmax ≤ F
  · -- large case
    have hF_ge_4M : 4 * M ≤ F := by
      have hmax := le_max_left (4 * M) (32 * (2 : ℝ) ^ m * K / β0)
      have hFmax_le : Fmax ≤ F := hbig
      dsimp [Fmax] at hFmax_le
      linarith
    have hF_ge_32 : 32 * (2 : ℝ) ^ m * K / β0 ≤ F := by
      have hmax := le_max_right (4 * M) (32 * (2 : ℝ) ^ m * K / β0)
      have hFmax_le : Fmax ≤ F := hbig
      dsimp [Fmax] at hFmax_le
      linarith
    have hL_le_half : L ≤ F / 2 := by
      have hLabs := abs_le.mp hL
      nlinarith
    have hL_ge_neg_half : -F / 2 ≤ L := by
      have hLabs := abs_le.mp hL
      nlinarith
    have hnegF_le_half : -F ≤ F / 2 := by nlinarith
    have hF_ge_neg_half : -F / 2 ≤ F := by nlinarith
    have hU_le_half : U ≤ F / 2 := by
      dsimp [U]
      exact max_le hnegF_le_half (le_trans (min_le_right _ _) hL_le_half)
    have hU_ge_neg_half : -F / 2 ≤ U := by
      dsimp [U]
      have hmin_ge : -F / 2 ≤ min F L := le_min hF_ge_neg_half hL_ge_neg_half
      exact le_trans hmin_ge (le_max_right _ _)
    have hO_eq : O = - ∫ z in U..F, z * W z := by
      dsimp [O, W]
      exact intervalIntegral_z_ball_eq_neg (m := m) (F := F) (U := U) hF hU_lower hU_upper
    have hsub_lower := intervalIntegral_z_ball_subinterval_lower (m := m) (F := F) hF
    have hge := intervalIntegral_z_ball_ge_of_U_between (m := m) (F := F) (U := U) hF hU_le_half hU_ge_neg_half
    have hUF_lower : c * A_o * F ^ (m + 2) ≤ ∫ z in U..F, z * W z := by
      dsimp [c, A_o, W]
      exact le_trans hsub_lower hge
    have hO_lower : c * A_o * F ^ (m + 2) ≤ -O := by
      rw [hO_eq]
      simpa using hUF_lower
    have hO_nonpos : O ≤ 0 := by
      have hpos : 0 ≤ c * A_o * F ^ (m + 2) := by positivity
      linarith
    have hE_le : E ≤ 2 * c * F ^ (m + 1) := by
      dsimp [E, W]
      have hpoint : ∀ z ∈ Set.Icc (-F) U, ballMeasure m F z ≤ c * F ^ m := by
        intro z hz
        have hzI : z ∈ Set.Icc (-F) F := ⟨hz.1, le_trans hz.2 hU_upper⟩
        exact ballMeasure_le (m := m) hF hzI
      have hconst_int : IntervalIntegrable (fun _ : ℝ => c * F ^ m) volume (-F) U := intervalIntegrable_const
      have hmono := intervalIntegral.integral_mono_on (a := -F) (b := U) (μ := volume)
        (f := fun z => ballMeasure m F z) (g := fun _ : ℝ => c * F ^ m) hU_lower hW_int hconst_int hpoint
      calc
        (∫ z in (-F)..U, ballMeasure m F z) ≤ ∫ z in (-F)..U, c * F ^ m := hmono
        _ = (U - (-F)) * (c * F ^ m) := by rw [intervalIntegral.integral_const]; ring_nf
        _ ≤ (2 * F) * (c * F ^ m) := by
          apply mul_le_mul_of_nonneg_right
          · nlinarith
          · positivity
        _ = 2 * c * F ^ (m + 1) := by ring_nf
    have hJ_le : J ≤ 2 * c * F ^ (m + 2) := by
      dsimp [J, W]
      have hWle : ∀ z ∈ Set.Icc (-F) U, ballMeasure m F z ≤ c * F ^ m := by
        intro z hz
        have hzI : z ∈ Set.Icc (-F) F := ⟨hz.1, le_trans hz.2 hU_upper⟩
        exact ballMeasure_le (m := m) hF hzI
      have hpoint : ∀ z ∈ Set.Icc (-F) U, |z| * ballMeasure m F z ≤ F * (c * F ^ m) := by
        intro z hz
        have hz_abs_le : |z| ≤ F := by
          rw [abs_le]
          exact ⟨hz.1, le_trans hz.2 hU_upper⟩
        exact mul_le_mul hz_abs_le (hWle z hz) (ballMeasure_nonneg (m := m) F z) hF
      have hconst_int : IntervalIntegrable (fun _ : ℝ => F * (c * F ^ m)) volume (-F) U := intervalIntegrable_const
      have hmono := intervalIntegral.integral_mono_on (a := -F) (b := U) (μ := volume)
        (f := fun z => |z| * ballMeasure m F z) (g := fun _ : ℝ => F * (c * F ^ m)) hU_lower habszW_int hconst_int hpoint
      calc
        (∫ z in (-F)..U, |z| * ballMeasure m F z) ≤ ∫ z in (-F)..U, F * (c * F ^ m) := hmono
        _ = (U - (-F)) * (F * (c * F ^ m)) := by rw [intervalIntegral.integral_const]; ring_nf
        _ ≤ (2 * F) * (F * (c * F ^ m)) := by
          apply mul_le_mul_of_nonneg_right
          · nlinarith
          · positivity
        _ = 2 * c * F ^ (m + 2) := by ring_nf
    have hRcA : Rc * A_o = 2 := by
      dsimp [Rc, A_o]
      field_simp
      ring
    have hJ_le_O : J ≤ Rc * (-O) := by
      have hleft : J ≤ 2 * c * F ^ (m + 2) := hJ_le
      have hright : 2 * c * F ^ (m + 2) = Rc * (c * A_o * F ^ (m + 2)) := by
        calc
          2 * c * F ^ (m + 2) = (Rc * A_o) * c * F ^ (m + 2) := by rw [hRcA]
          _ = Rc * (c * A_o * F ^ (m + 2)) := by ring
      have hmul := mul_le_mul_of_nonneg_left hO_lower hRc_nonneg
      nlinarith
    have hY_ge_2X : 2 * (|α| * E) ≤ |β| * (-O) := by
      have hE_bound : E ≤ 2 * c * F ^ (m + 1) := hE_le
      have hX_bound : |α| * E ≤ K * (2 * c * F ^ (m + 1)) := by
        have hmul := mul_le_mul hα hE_bound hE_nonneg hK
        nlinarith
      have hO_bound_low : c * A_o * F ^ (m + 2) ≤ -O := hO_lower
      have hY_bound : β0 * (c * A_o * F ^ (m + 2)) ≤ |β| * (-O) := by
        have hmul := mul_le_mul hβlow hO_bound_low (by positivity) (abs_nonneg β)
        nlinarith
      have hmain : 2 * (K * (2 * c * F ^ (m + 1))) ≤ β0 * (c * A_o * F ^ (m + 2)) := by
        have hF_ineq : 4 * K ≤ β0 * A_o * F := by
          have h1 : 32 * (2 : ℝ) ^ m * K / β0 ≤ F := hF_ge_32
          dsimp [A_o]
          have hmul := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ β0 * (1 / (8 * (2 : ℝ) ^ m)))
          have hcoeff : β0 * (1 / (8 * (2 : ℝ) ^ m)) * (32 * (2 : ℝ) ^ m * K / β0) = 4 * K := by
            field_simp
            ring
          nlinarith
        have hmul := mul_le_mul_of_nonneg_right hF_ineq (by positivity : 0 ≤ c * F ^ (m + 1))
        have hleft_eq : 2 * (K * (2 * c * F ^ (m + 1))) = (4 * K) * (c * F ^ (m + 1)) := by ring
        have hpow : F ^ (m + 2) = F ^ (m + 1) * F := by
          rw [← pow_succ]
        have hright_eq : β0 * (c * A_o * F ^ (m + 2)) = (β0 * A_o * F) * (c * F ^ (m + 1)) := by
          rw [hpow]
          ring
        nlinarith
      nlinarith
    have hI_lower : (1 / 2 : ℝ) * (|β| * (-O)) ≤ |I| := by
      have hIminus : I - α * E = β * O := by linarith [hI_eq]
      have htri := abs_add_le I (-(α * E))
      have htri' : |β * O| ≤ |I| + |α * E| := by
        calc
          |β * O| = |I - α * E| := by rw [hIminus]
          _ = |I + -(α * E)| := by ring
          _ ≤ |I| + |-(α * E)| := htri
          _ = |I| + |α * E| := by rw [abs_neg]
      have hβO_abs : |β * O| = |β| * (-O) := by
        rw [abs_mul, abs_of_nonpos hO_nonpos]
      have hαE_abs : |α * E| = |α| * E := by
        rw [abs_mul, abs_of_nonneg hE_nonneg]
      have hlower : |β| * (-O) - |α| * E ≤ |I| := by linarith
      linarith
    have hIabs_bound : Iabs ≤ C1 * |I| := by
      have hJpart : |β| * J ≤ Rc * (|β| * (-O)) := by
        calc
          |β| * J ≤ |β| * (Rc * (-O)) := mul_le_mul_of_nonneg_left hJ_le_O (abs_nonneg β)
          _ = Rc * (|β| * (-O)) := by ring
      have hX_le_Y_half : |α| * E ≤ (1 / 2 : ℝ) * (|β| * (-O)) := by
        have h2 : 2 * (|α| * E) ≤ |β| * (-O) := hY_ge_2X
        calc
          |α| * E = (1 / 2 : ℝ) * (2 * (|α| * E)) := by ring
          _ ≤ (1 / 2 : ℝ) * (|β| * (-O)) := mul_le_mul_of_nonneg_left h2 (by norm_num)
      have hY_nonneg : 0 ≤ |β| * (-O) := by
        exact mul_nonneg (abs_nonneg β) (neg_nonneg_of_nonpos hO_nonpos)
      have hY_le : |β| * (-O) ≤ 2 * |I| := by
        calc
          |β| * (-O) = 2 * ((1 / 2 : ℝ) * (|β| * (-O))) := by ring
          _ ≤ 2 * |I| := mul_le_mul_of_nonneg_left hI_lower (by norm_num)
      have hcoeff_nonneg : 0 ≤ (1 / 2 : ℝ) + Rc := by positivity
      calc
        Iabs ≤ |α| * E + |β| * J := hIabs_le
        _ ≤ (1 / 2 : ℝ) * (|β| * (-O)) + Rc * (|β| * (-O)) := add_le_add hX_le_Y_half hJpart
        _ = ((1 / 2 : ℝ) + Rc) * (|β| * (-O)) := by ring
        _ ≤ ((1 / 2 : ℝ) + Rc) * (2 * |I|) := by
          apply mul_le_mul_of_nonneg_left hY_le hcoeff_nonneg
        _ = (1 + 2 * Rc) * |I| := by ring
        _ = C1 * |I| := by dsimp [C1]
    have hfinal : Iabs ≤ C1 * |I| + C2 := by
      calc
        Iabs ≤ C1 * |I| := hIabs_bound
        _ ≤ C1 * |I| + C2 := by linarith [hC2_nonneg]
    simpa [Iabs, I, U, W] using hfinal
  · -- small case
    have hF_le : F ≤ Fmax := le_of_lt (lt_of_not_ge hbig)
    have hW_le_point : ∀ z ∈ Set.Icc (-F) U, W z ≤ c * Fmax ^ m := by
      intro z hz
      have hzI : z ∈ Set.Icc (-F) F := ⟨hz.1, le_trans hz.2 hU_upper⟩
      have hWle : ballMeasure m F z ≤ c * F ^ m := ballMeasure_le (m := m) hF hzI
      have hFpow : F ^ m ≤ Fmax ^ m := pow_le_pow_left₀ hF hF_le _
      dsimp [W]
      nlinarith
    have hlin_abs_le : ∀ z ∈ Set.Icc (-F) U, |α + β * z| ≤ K + K * Fmax := by
      intro z hz
      have hz_abs_le : |z| ≤ Fmax := by
        have hzF : |z| ≤ F := by
          rw [abs_le]; exact ⟨hz.1, le_trans hz.2 hU_upper⟩
        linarith
      have hβz : |β * z| ≤ K * Fmax := by
        calc
          |β * z| = |β| * |z| := abs_mul β z
          _ ≤ K * Fmax := mul_le_mul hβup hz_abs_le (abs_nonneg z) (by positivity)
      have htri := abs_add_le α (β * z)
      nlinarith
    have hpoint : ∀ z ∈ Set.Icc (-F) U, |(α + β * z) * W z| ≤ c * Fmax ^ m * (K + K * Fmax) := by
      intro z hz
      have hWnonneg : 0 ≤ W z := by dsimp [W]; exact ballMeasure_nonneg (m := m) F z
      have hWle : W z ≤ c * Fmax ^ m := hW_le_point z hz
      have hlinle : |α + β * z| ≤ K + K * Fmax := hlin_abs_le z hz
      have hrewrite : |(α + β * z) * W z| = |α + β * z| * W z := by
        rw [abs_mul, abs_of_nonneg hWnonneg]
      rw [hrewrite]
      have hmul := mul_le_mul (a := |α + β * z|) (b := K + K * Fmax) (c := W z) (d := c * Fmax ^ m)
        hlinle hWle hWnonneg (add_nonneg hK (mul_nonneg hK hFmax_nonneg))
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    have hconst_int : IntervalIntegrable (fun _ : ℝ => c * Fmax ^ m * (K + K * Fmax)) volume (-F) U := intervalIntegrable_const
    have hmono := intervalIntegral.integral_mono_on (a := -F) (b := U) (μ := volume)
      (f := fun z => |(α + β * z) * W z|) (g := fun _ : ℝ => c * Fmax ^ m * (K + K * Fmax))
      hU_lower habs_int hconst_int hpoint
    have hIabs_small : Iabs ≤ 2 * c * Fmax ^ (m + 1) * (K + K * Fmax) := by
      dsimp [Iabs, W]
      calc
        (∫ z in (-F)..U, |(α + β * z) * ballMeasure m F z|)
            ≤ ∫ z in (-F)..U, c * Fmax ^ m * (K + K * Fmax) := hmono
        _ = (U - (-F)) * (c * Fmax ^ m * (K + K * Fmax)) := by rw [intervalIntegral.integral_const]; ring_nf
        _ ≤ (2 * Fmax) * (c * Fmax ^ m * (K + K * Fmax)) := by
          apply mul_le_mul_of_nonneg_right
          · nlinarith
          · positivity
        _ = 2 * c * Fmax ^ (m + 1) * (K + K * Fmax) := by ring_nf
    have hfinal : Iabs ≤ C1 * |I| + C2 := by
      have hC1_nonneg' : 0 ≤ C1 := hC1_nonneg
      have hC2_nonneg' : 0 ≤ C2 := hC2_nonneg
      have hle : Iabs ≤ C2 := by
        dsimp [C2]
        exact hIabs_small
      have hC1abs_nonneg : 0 ≤ C1 * |I| := mul_nonneg hC1_nonneg' (abs_nonneg I)
      linarith
    simpa [Iabs, I, U, W] using hfinal


lemma intervalIntegral_abs_affine_ball_section_le
    {m : ℕ} [Nonempty (Fin m)] {a b s h : ℝ} {f : ℝ → ℝ} {A B C : ℝ}
    (hab : a ≤ b) (hf_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ f t) :
    ∃ C1 C2 : ℝ, 0 ≤ C1 ∧ 0 ≤ C2 ∧ ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc a b)),
      (∫ z in Set.Icc (-f t) (max (-f t) (min (f t) (s * t + h))),
        |(A * t + B * z + C) * MeasureTheory.Measure.real MeasureTheory.volume {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ f t ^ 2 - z ^ 2}|) ≤
      C1 * |∫ z in Set.Icc (-f t) (max (-f t) (min (f t) (s * t + h))),
        (A * t + B * z + C) * MeasureTheory.Measure.real MeasureTheory.volume {y : Fin m → ℝ | ∑ j : Fin m, (y j)^2 ≤ f t ^ 2 - z ^ 2}| + C2 := by
  classical
  let M : ℝ := |s| * max |a| |b| + |h|
  let K : ℝ := max (|A| * max |a| |b| + |C|) |B|
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    have hfirst : 0 ≤ |A| * max |a| |b| + |C| := by positivity
    exact le_trans hfirst (le_max_left (|A| * max |a| |b| + |C|) |B|)
  by_cases hB : B = 0
  · refine ⟨1, 0, by norm_num, by norm_num, ?_⟩
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards with t ht
    let F : ℝ := f t
    let U : ℝ := max (-F) (min F (s * t + h))
    have hF : 0 ≤ F := hf_nonneg t ht
    have hU_lower : -F ≤ U := by dsimp [U]; exact le_max_left _ _
    have hU_upper : U ≤ F := by
      dsimp [U]
      exact max_le (by linarith) (min_le_left _ _)
    change (∫ z in Set.Icc (-F) U, |(A * t + B * z + C) * ballMeasure m F z|) ≤
        1 * |∫ z in Set.Icc (-F) U, (A * t + B * z + C) * ballMeasure m F z| + 0
    have hset_abs : (∫ z in Set.Icc (-F) U, |(A * t + B * z + C) * ballMeasure m F z|) =
        ∫ z in (-F)..U, |(A * t + B * z + C) * ballMeasure m F z| := by
      exact (intervalIntegral_eq_setIntegral_Icc hU_lower _).symm
    have hset_I : (∫ z in Set.Icc (-F) U, (A * t + B * z + C) * ballMeasure m F z) =
        ∫ z in (-F)..U, (A * t + B * z + C) * ballMeasure m F z := by
      exact (intervalIntegral_eq_setIntegral_Icc hU_lower _).symm
    rw [hset_abs, hset_I]
    have hBzero : B = 0 := hB
    have hlin : ∀ z, A * t + B * z + C = A * t + C := by
      intro z; rw [hBzero]; ring
    have h_abs_eq : (∫ z in (-F)..U, |(A * t + B * z + C) * ballMeasure m F z|) =
        |∫ z in (-F)..U, (A * t + B * z + C) * ballMeasure m F z| := by
      simp_rw [hlin]
      have hball_nonneg : ∀ z, 0 ≤ ballMeasure m F z := by
        intro z; exact ballMeasure_nonneg (m := m) F z
      have h_integrand : (fun z => |(A * t + C) * ballMeasure m F z|) =
          fun z => |A * t + C| * ballMeasure m F z := by
        funext z
        rw [abs_mul, abs_of_nonneg (hball_nonneg z)]
      rw [h_integrand]
      have h_nonneg : 0 ≤ ∫ z in (-F)..U, ballMeasure m F z := by
        exact intervalIntegral.integral_nonneg_of_forall hU_lower (fun z => ballMeasure_nonneg (m := m) F z)
      rw [intervalIntegral.integral_const_mul]
      rw [intervalIntegral.integral_const_mul]
      rw [abs_mul, abs_of_nonneg h_nonneg]
    linarith
  · have hB_ne : B ≠ 0 := hB
    have hβ0_pos : 0 < |B| := abs_pos.mpr hB_ne
    rcases intervalIntegral_abs_affine_ball_le_const_aux (m := m) (K := K) (M := M) (β0 := |B|)
        hK_nonneg hM_nonneg hβ0_pos with ⟨C1, C2, hC1, hC2, hmain⟩
    refine ⟨C1, C2, hC1, hC2, ?_⟩
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards with t ht
    let F : ℝ := f t
    let U : ℝ := max (-F) (min F (s * t + h))
    have hF : 0 ≤ F := hf_nonneg t ht
    have hL_abs : |s * t + h| ≤ M := by
      dsimp [M]
      exact abs_affine_le_const hab ht
    have hα_abs : |A * t + C| ≤ |A| * max |a| |b| + |C| := by
      exact abs_affine_le_const hab ht
    have hα_abs_K : |A * t + C| ≤ K := by
      dsimp [K]
      exact le_trans hα_abs (le_max_left _ _)
    have hβ_abs_K : |B| ≤ K := by
      dsimp [K]
      exact le_max_right _ _
    have hU_lower : -F ≤ U := by dsimp [U]; exact le_max_left _ _
    change (∫ z in Set.Icc (-F) U, |(A * t + B * z + C) * ballMeasure m F z|) ≤
        C1 * |∫ z in Set.Icc (-F) U, (A * t + B * z + C) * ballMeasure m F z| + C2
    have hbound := hmain F (s * t + h) (A * t + C) B hF hL_abs hα_abs_K le_rfl hβ_abs_K
    have hset_abs : (∫ z in Set.Icc (-F) U, |(A * t + B * z + C) * ballMeasure m F z|) =
        ∫ z in (-F)..U, |(A * t + B * z + C) * ballMeasure m F z| := by
      exact (intervalIntegral_eq_setIntegral_Icc hU_lower _).symm
    have hset_I : (∫ z in Set.Icc (-F) U, (A * t + B * z + C) * ballMeasure m F z) =
        ∫ z in (-F)..U, (A * t + B * z + C) * ballMeasure m F z := by
      exact (intervalIntegral_eq_setIntegral_Icc hU_lower _).symm
    rw [hset_abs, hset_I]
    simpa [U, F, ballMeasure, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hbound



end

end Commons.Geometry.Ulam
