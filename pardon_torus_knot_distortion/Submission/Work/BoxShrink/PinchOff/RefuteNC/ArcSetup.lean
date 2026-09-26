import Mathlib
import Submission.Work.BoxShrink.PinchOff.RefuteNC.Config

/-!
# The explicit arc of the `nc` trace

The slice `Σ` of the configuration `RefuteNC/Config.lean` is (the open part of) the trace of the
plane `{x = 1/2}` on the standard torus, cut by the `y₁`-window of the box.  In the parameter plane
`(θ, φ)` of the parametrisation `torusMap` the trace is the image of the curve

  `ncArc φ = torusMap (ncTheta φ) φ`,  `ncTheta φ = arccos (1 / (2 * (2 + cos φ)))`,

whose `y`-coordinate is `ncY1 φ = (2 + cos φ) * sin (ncTheta φ)`.  This module fixes the vocabulary
and proves the elementary algebraic/analytic facts about it (values, continuity, periodicity, the
closed form `ncY1 φ = √((2 + cos φ)² - 1/4)`, and the two threshold cosines

  `ncCosHi = √(433/50) - 2`  (where `ncY1 φ = 29/10`),  `ncCosLo = √(53/50) - 2`  (where
  `ncY1 φ = 9/10`),

together with the corresponding angles `ncPhiA = arccos ncCosHi`, `ncPhiB = arccos ncCosLo`).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff.RefuteNC

noncomputable section

/-! ## The curve -/

/-- The longitude parameter of the trace of the plane `{x = 1/2}` on the standard torus:
`cos θ = 1 / (2 * (2 + cos φ))`. -/
def ncTheta (φ : ℝ) : ℝ := Real.arccos (1 / (2 * (2 + Real.cos φ)))

/-- The trace of the plane `{x = 1/2}` on the standard torus, parametrised by `φ`. -/
def ncArc (φ : ℝ) : R3 := Work.Core.torusMap (ncTheta φ) φ

/-- The `y`-coordinate `(2 + cos φ) * sin (ncTheta φ)` of `ncArc φ`. -/
def ncY1 (φ : ℝ) : ℝ := (2 + Real.cos φ) * Real.sin (ncTheta φ)

/-- The cosine `√(433/50) - 2`, where the `y`-coordinate of the trace equals `29/10`. -/
def ncCosHi : ℝ := Real.sqrt (433 / 50) - 2

/-- The cosine `√(53/50) - 2`, where the `y`-coordinate of the trace equals `9/10`. -/
def ncCosLo : ℝ := Real.sqrt (53 / 50) - 2

/-- The angle `arccos ncCosHi`, an endpoint of the two arcs of the slice. -/
def ncPhiA : ℝ := Real.arccos ncCosHi

/-- The angle `arccos ncCosLo`, an endpoint of the two arcs of the slice. -/
def ncPhiB : ℝ := Real.arccos ncCosLo

/-! ## Elementary facts about the two threshold cosines and angles -/

theorem ncCosHi_lt_one : ncCosHi < 1 := by
  have h : Real.sqrt (433 / 50) < 3 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  simp only [ncCosHi]; linarith

theorem ncCosHi_gt_neg_one : -1 < ncCosHi := by
  have h : (1 : ℝ) < Real.sqrt (433 / 50) := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  simp only [ncCosHi]; linarith

theorem ncCosLo_lt_one : ncCosLo < 1 := by
  have h : Real.sqrt (53 / 50) < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  simp only [ncCosLo]; linarith

theorem ncCosLo_gt_neg_one : -1 < ncCosLo := by
  have h : (1 : ℝ) < Real.sqrt (53 / 50) := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  simp only [ncCosLo]; linarith

theorem ncCosLo_lt_ncCosHi : ncCosLo < ncCosHi := by
  have h : Real.sqrt (53 / 50) < Real.sqrt (433 / 50) :=
    Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  simp only [ncCosLo, ncCosHi]; linarith

theorem cos_ncPhiA : Real.cos ncPhiA = ncCosHi :=
  Real.cos_arccos (le_of_lt ncCosHi_gt_neg_one) (le_of_lt ncCosHi_lt_one)

theorem cos_ncPhiB : Real.cos ncPhiB = ncCosLo :=
  Real.cos_arccos (le_of_lt ncCosLo_gt_neg_one) (le_of_lt ncCosLo_lt_one)

theorem ncPhiA_pos : 0 < ncPhiA := by
  rw [ncPhiA, Real.arccos_pos]; exact ncCosHi_lt_one

theorem ncPhiA_lt_pi : ncPhiA < Real.pi := by
  rw [ncPhiA, Real.arccos_lt_pi]; exact ncCosHi_gt_neg_one

theorem ncPhiB_pos : 0 < ncPhiB := by
  rw [ncPhiB, Real.arccos_pos]; exact ncCosLo_lt_one

theorem ncPhiB_lt_pi : ncPhiB < Real.pi := by
  rw [ncPhiB, Real.arccos_lt_pi]; exact ncCosLo_gt_neg_one

theorem ncPhiA_lt_ncPhiB : ncPhiA < ncPhiB :=
  Real.arccos_lt_arccos (le_of_lt ncCosLo_gt_neg_one) ncCosLo_lt_ncCosHi
    (le_of_lt ncCosHi_lt_one)

lemma ncPhiA_le_pi : ncPhiA ≤ Real.pi := le_of_lt ncPhiA_lt_pi
lemma ncPhiB_le_pi : ncPhiB ≤ Real.pi := le_of_lt ncPhiB_lt_pi

/-! ## Elementary facts about the curve -/

theorem two_add_cos_pos (φ : ℝ) : 0 < 2 + Real.cos φ := by
  linarith [Real.neg_one_le_cos φ]

theorem two_add_cos_ne_zero (φ : ℝ) : 2 + Real.cos φ ≠ 0 :=
  ne_of_gt (two_add_cos_pos φ)

private lemma denom_pos (φ : ℝ) : 0 < 2 * (2 + Real.cos φ) := by
  have := two_add_cos_pos φ; linarith

/-- The defining relation: `(2 + cos φ) * cos (ncTheta φ) = 1/2`. -/
theorem ncTheta_cos (φ : ℝ) : Real.cos (ncTheta φ) = 1 / (2 * (2 + Real.cos φ)) := by
  rw [ncTheta]
  refine Real.cos_arccos ?_ ?_
  · rw [le_div_iff₀ (denom_pos φ)]
    have h := Real.neg_one_le_cos φ
    nlinarith
  · rw [div_le_iff₀ (denom_pos φ)]
    have h := Real.neg_one_le_cos φ
    nlinarith

theorem ncTheta_cos_mul (φ : ℝ) : (2 + Real.cos φ) * Real.cos (ncTheta φ) = 1 / 2 := by
  rw [ncTheta_cos]
  field_simp [two_add_cos_ne_zero φ]

/-- `ncTheta φ` lies in `(0, π)`. -/
theorem ncTheta_pos (φ : ℝ) : 0 < ncTheta φ := by
  rw [ncTheta, Real.arccos_pos, div_lt_one (denom_pos φ)]
  have h := Real.neg_one_le_cos φ
  nlinarith

theorem ncTheta_nonneg (φ : ℝ) : 0 ≤ ncTheta φ := le_of_lt (ncTheta_pos φ)

theorem ncTheta_lt_pi (φ : ℝ) : ncTheta φ < Real.pi := by
  rw [ncTheta, Real.arccos_lt_pi, lt_div_iff₀ (denom_pos φ)]
  have h := Real.neg_one_le_cos φ
  nlinarith

theorem ncTheta_sin_pos (φ : ℝ) : 0 < Real.sin (ncTheta φ) :=
  Real.sin_pos_of_pos_of_lt_pi (ncTheta_pos φ) (ncTheta_lt_pi φ)

theorem ncTheta_sin_nonneg (φ : ℝ) : 0 ≤ Real.sin (ncTheta φ) :=
  le_of_lt (ncTheta_sin_pos φ)

theorem continuous_ncTheta : Continuous ncTheta :=
  Real.continuous_arccos.comp <|
    continuous_const.div (by fun_prop) (fun φ => ne_of_gt (denom_pos φ))

theorem continuous_ncArc : Continuous ncArc := by
  have h : Continuous (fun φ : ℝ => Work.Core.torusMap (ncTheta φ) φ) := by
    have h2 : Continuous fun φ : ℝ => (fun i : Fin 3 =>
        (if i.val = 0 then (2 + Real.cos φ) * Real.cos (ncTheta φ)
         else if i.val = 1 then (2 + Real.cos φ) * Real.sin (ncTheta φ)
         else Real.sin φ : ℝ)) := by
      apply continuous_pi
      intro i
      fin_cases i <;> simp
      · exact (continuous_const.add Real.continuous_cos).mul (Real.continuous_cos.comp continuous_ncTheta)
      · exact (continuous_const.add Real.continuous_cos).mul (Real.continuous_sin.comp continuous_ncTheta)
      · exact Real.continuous_sin
    exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp h2
  exact h

theorem ncTheta_add_two_pi (φ : ℝ) : ncTheta (φ + 2 * Real.pi) = ncTheta φ := by
  simp only [ncTheta, Real.cos_add_two_pi]

theorem ncArc_add_two_pi (φ : ℝ) : ncArc (φ + 2 * Real.pi) = ncArc φ := by
  rw [ncArc, ncArc, ncTheta_add_two_pi, Work.Core.torusMap_add_two_pi_right]

theorem ncArc_periodic : Function.Periodic ncArc (2 * Real.pi) := ncArc_add_two_pi

/-- The components of `ncArc φ`. -/
theorem ncArc_apply_zero (φ : ℝ) : ncArc φ 0 = 1 / 2 := by
  rw [ncArc, Work.Core.torusMap_apply_zero]
  exact ncTheta_cos_mul φ

theorem ncArc_apply_one (φ : ℝ) : ncArc φ 1 = ncY1 φ := by
  rw [ncArc, Work.Core.torusMap_apply_one, ncY1]

theorem ncArc_apply_two (φ : ℝ) : ncArc φ 2 = Real.sin φ := by
  rw [ncArc, Work.Core.torusMap_apply_two]

theorem ncY1_nonneg (φ : ℝ) : 0 ≤ ncY1 φ :=
  mul_nonneg (le_of_lt (two_add_cos_pos φ)) (ncTheta_sin_nonneg φ)

theorem ncY1_sq (φ : ℝ) : ncY1 φ ^ 2 = (2 + Real.cos φ) ^ 2 - 1 / 4 := by
  have h := two_add_cos_ne_zero φ
  rw [ncY1, mul_pow, Real.sin_sq, ncTheta_cos]
  field_simp [h]
  ring

/-- The closed form of the `y`-coordinate. -/
theorem ncY1_eq (φ : ℝ) : ncY1 φ = Real.sqrt ((2 + Real.cos φ) ^ 2 - 1 / 4) := by
  rw [← Real.sqrt_sq (ncY1_nonneg φ), ncY1_sq]

theorem ncY1_add_two_pi (φ : ℝ) : ncY1 (φ + 2 * Real.pi) = ncY1 φ := by
  simp only [ncY1, Real.cos_add_two_pi, ncTheta_add_two_pi]

theorem ncY1_periodic : Function.Periodic ncY1 (2 * Real.pi) := ncY1_add_two_pi

/-- At `ncPhiA` the `y`-coordinate of the trace equals `29/10`. -/
theorem ncY1_ncPhiA : ncY1 ncPhiA = 29 / 10 := by
  rw [ncY1_eq, cos_ncPhiA]
  have h1 : 2 + ncCosHi = Real.sqrt (433 / 50) := by rw [ncCosHi]; ring
  have hsq : (2 + ncCosHi) ^ 2 - 1 / 4 = (29 / 10) ^ 2 := by
    rw [h1, Real.sq_sqrt (by norm_num)]; norm_num
  rw [hsq, Real.sqrt_sq (by norm_num)]

/-- At `ncPhiB` the `y`-coordinate of the trace equals `9/10`. -/
theorem ncY1_ncPhiB : ncY1 ncPhiB = 9 / 10 := by
  rw [ncY1_eq, cos_ncPhiB]
  have h1 : 2 + ncCosLo = Real.sqrt (53 / 50) := by rw [ncCosLo]; ring
  have hsq : (2 + ncCosLo) ^ 2 - 1 / 4 = (9 / 10) ^ 2 := by
    rw [h1, Real.sq_sqrt (by norm_num)]; norm_num
  rw [hsq, Real.sqrt_sq (by norm_num)]

/-! ## The threshold characterisation -/

/-- **The window of the `y`-coordinate in terms of `cos φ`.**  Since
`ncY1 φ = √((2 + cos φ)² - 1/4)` and `2 + cos φ ≥ 1 > 0`, the inequalities
`9/10 ≤ ncY1 φ ≤ 29/10` are equivalent to `ncCosLo ≤ cos φ ≤ ncCosHi`. -/
theorem ncY1_mem_Icc_iff (φ : ℝ) :
    (9 / 10 ≤ ncY1 φ ∧ ncY1 φ ≤ 29 / 10) ↔
      (ncCosLo ≤ Real.cos φ ∧ Real.cos φ ≤ ncCosHi) := by
  have hA : 0 < 2 + Real.cos φ := two_add_cos_pos φ
  have hnn : 0 ≤ (2 + Real.cos φ) ^ 2 - 1 / 4 := by
    rw [← ncY1_sq]; exact sq_nonneg _
  rw [ncY1_eq]
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : (53 / 50 : ℝ) ≤ (2 + Real.cos φ) ^ 2 := by
      have := (Real.le_sqrt (show (0 : ℝ) ≤ 9 / 10 by norm_num) hnn).mp h1
      nlinarith
    have h2' : (2 + Real.cos φ) ^ 2 ≤ 433 / 50 := by
      have := (Real.sqrt_le_iff).mp h2
      nlinarith [this.2]
    constructor
    · have h3 : Real.sqrt (53 / 50) ≤ 2 + Real.cos φ := Real.sqrt_le_iff.mpr ⟨le_of_lt hA, h1'⟩
      rw [ncCosLo]; linarith
    · have h3 : 2 + Real.cos φ ≤ Real.sqrt (433 / 50) := by
        rw [Real.le_sqrt (le_of_lt hA) (by norm_num)]; exact h2'
      rw [ncCosHi]; linarith
  · rintro ⟨h1, h2⟩
    have h1' : (53 / 50 : ℝ) ≤ (2 + Real.cos φ) ^ 2 := by
      have h3 : Real.sqrt (53 / 50) ≤ 2 + Real.cos φ := by rw [ncCosLo] at h1; linarith
      exact (Real.sqrt_le_iff.mp h3).2
    have h2' : (2 + Real.cos φ) ^ 2 ≤ 433 / 50 := by
      have h3 : 2 + Real.cos φ ≤ Real.sqrt (433 / 50) := by rw [ncCosHi] at h2; linarith
      exact (Real.le_sqrt (le_of_lt hA) (by norm_num)).mp h3
    constructor
    · rw [Real.le_sqrt (show (0 : ℝ) ≤ 9 / 10 by norm_num) hnn]
      nlinarith
    · rw [Real.sqrt_le_iff]
      exact ⟨by norm_num, by nlinarith⟩

/-- **The closed arc's `cos` range.**  For `ψ ∈ [ncPhiA, ncPhiB]` the cosine lies in
`[ncCosLo, ncCosHi]` (the cosine is strictly antitone on `[0, π]` and the two angles are the
`arccos` of the two thresholds). -/
theorem cos_mem_Icc_of_mem_Icc_phiA_phiB {ψ : ℝ}
    (hψ : ψ ∈ Set.Icc ncPhiA ncPhiB) : Real.cos ψ ∈ Set.Icc ncCosLo ncCosHi := by
  have hmemA : ncPhiA ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨le_of_lt ncPhiA_pos, le_of_lt ncPhiA_lt_pi⟩
  have hmemB : ncPhiB ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨le_of_lt ncPhiB_pos, le_of_lt ncPhiB_lt_pi⟩
  have hmemψ : ψ ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨le_trans (le_of_lt ncPhiA_pos) hψ.1, le_trans hψ.2 (le_of_lt ncPhiB_lt_pi)⟩
  constructor
  · have h : Real.cos ncPhiB ≤ Real.cos ψ :=
      (Real.strictAntiOn_cos.le_iff_ge hmemB hmemψ).mpr hψ.2
    rwa [cos_ncPhiB] at h
  · have h : Real.cos ψ ≤ Real.cos ncPhiA :=
      (Real.strictAntiOn_cos.le_iff_ge hmemψ hmemA).mpr hψ.1
    rwa [cos_ncPhiA] at h

/-- **The threshold characterisation of `cos`.**  For `φ ∈ [0, 2π]`, the cosine lies in
`[ncCosLo, ncCosHi]` exactly for `φ` in the two closed arcs of the slice. -/
theorem cos_mem_Icc_iff (φ : ℝ) (h0 : 0 ≤ φ) (h2 : φ ≤ 2 * Real.pi) :
    Real.cos φ ∈ Set.Icc ncCosLo ncCosHi ↔
      φ ∈ Set.Icc ncPhiA ncPhiB ∪ Set.Icc (2 * Real.pi - ncPhiB) (2 * Real.pi - ncPhiA) := by
  have hmemA : ncPhiA ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨le_of_lt ncPhiA_pos, le_of_lt ncPhiA_lt_pi⟩
  have hmemB : ncPhiB ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨le_of_lt ncPhiB_pos, le_of_lt ncPhiB_lt_pi⟩
  constructor
  · intro hc
    rw [Set.mem_Icc] at hc
    rcases le_or_gt φ Real.pi with hpi | hpi
    · left
      have hmemφ : φ ∈ Set.Icc (0 : ℝ) Real.pi := ⟨h0, hpi⟩
      refine ⟨?_, ?_⟩
      · have h : Real.cos φ ≤ Real.cos ncPhiA := by rw [cos_ncPhiA]; exact hc.2
        exact (Real.strictAntiOn_cos.le_iff_ge hmemφ hmemA).mp h
      · have h : Real.cos ncPhiB ≤ Real.cos φ := by rw [cos_ncPhiB]; exact hc.1
        exact (Real.strictAntiOn_cos.le_iff_ge hmemB hmemφ).mp h
    · right
      have hψ0 : 0 ≤ 2 * Real.pi - φ := by linarith
      have hψpi : 2 * Real.pi - φ ≤ Real.pi := by linarith
      have hmemψ : 2 * Real.pi - φ ∈ Set.Icc (0 : ℝ) Real.pi := ⟨hψ0, hψpi⟩
      have hcosψ : Real.cos (2 * Real.pi - φ) = Real.cos φ := Real.cos_two_pi_sub φ
      have hA : ncPhiA ≤ 2 * Real.pi - φ := by
        have h : Real.cos (2 * Real.pi - φ) ≤ Real.cos ncPhiA := by
          rw [hcosψ, cos_ncPhiA]; exact hc.2
        exact (Real.strictAntiOn_cos.le_iff_ge hmemψ hmemA).mp h
      have hB : 2 * Real.pi - φ ≤ ncPhiB := by
        have h : Real.cos ncPhiB ≤ Real.cos (2 * Real.pi - φ) := by
          rw [hcosψ, cos_ncPhiB]; exact hc.1
        exact (Real.strictAntiOn_cos.le_iff_ge hmemB hmemψ).mp h
      exact ⟨by linarith, by linarith⟩
  · rintro (h | h)
    · exact cos_mem_Icc_of_mem_Icc_phiA_phiB h
    · have hψ : 2 * Real.pi - φ ∈ Set.Icc ncPhiA ncPhiB :=
        ⟨by linarith [h.2], by linarith [h.1]⟩
      have := cos_mem_Icc_of_mem_Icc_phiA_phiB hψ
      rwa [Real.cos_two_pi_sub] at this

/-- **The open arc's `cos` range (first arc).** -/
theorem cos_mem_Ioo_of_mem_Ioo_phiA_phiB {ψ : ℝ}
    (hψ : ψ ∈ Set.Ioo ncPhiA ncPhiB) : Real.cos ψ ∈ Set.Ioo ncCosLo ncCosHi := by
  have hmemA : ncPhiA ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨le_of_lt ncPhiA_pos, le_of_lt ncPhiA_lt_pi⟩
  have hmemB : ncPhiB ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨le_of_lt ncPhiB_pos, le_of_lt ncPhiB_lt_pi⟩
  have hmemψ : ψ ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨le_trans (le_of_lt ncPhiA_pos) (le_of_lt hψ.1), le_trans (le_of_lt hψ.2) (le_of_lt ncPhiB_lt_pi)⟩
  refine ⟨?_, ?_⟩
  · have h : Real.cos ncPhiB < Real.cos ψ :=
      (Real.strictAntiOn_cos.lt_iff_gt hmemB hmemψ).mpr hψ.2
    rwa [cos_ncPhiB] at h
  · have h : Real.cos ψ < Real.cos ncPhiA :=
      (Real.strictAntiOn_cos.lt_iff_gt hmemψ hmemA).mpr hψ.1
    rwa [cos_ncPhiA] at h

/-- **The open arc's `cos` range (second arc).** -/
theorem cos_mem_Ioo_of_mem_Ioo_second (ψ : ℝ)
    (hψ : ψ ∈ Set.Ioo (2 * Real.pi - ncPhiB) (2 * Real.pi - ncPhiA)) :
    Real.cos ψ ∈ Set.Ioo ncCosLo ncCosHi := by
  have h : 2 * Real.pi - ψ ∈ Set.Ioo ncPhiA ncPhiB := ⟨by linarith [hψ.2], by linarith [hψ.1]⟩
  have := cos_mem_Ioo_of_mem_Ioo_phiA_phiB h
  rwa [Real.cos_two_pi_sub] at this

/-! ## The strict form of the threshold characterisation -/

/-- The strict form of `ncY1_mem_Icc_iff`. -/
theorem ncY1_mem_Ioo_iff (φ : ℝ) :
    (9 / 10 < ncY1 φ ∧ ncY1 φ < 29 / 10) ↔
      (ncCosLo < Real.cos φ ∧ Real.cos φ < ncCosHi) := by
  have hA : 0 < 2 + Real.cos φ := two_add_cos_pos φ
  have hnn : 0 ≤ (2 + Real.cos φ) ^ 2 - 1 / 4 := by
    rw [← ncY1_sq]; exact sq_nonneg _
  rw [ncY1_eq]
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : (53 / 50 : ℝ) < (2 + Real.cos φ) ^ 2 := by
      have h := (Real.lt_sqrt (x := 9 / 10) (y := (2 + Real.cos φ) ^ 2 - 1 / 4)
        (by norm_num)).mp h1
      nlinarith
    have h2' : (2 + Real.cos φ) ^ 2 < 433 / 50 := by
      have h := (Real.sqrt_lt (x := (2 + Real.cos φ) ^ 2 - 1 / 4) (y := 29 / 10)
        hnn (by norm_num)).mp h2
      nlinarith
    constructor
    · have h3 : Real.sqrt (53 / 50) < 2 + Real.cos φ :=
        (Real.sqrt_lt (x := 53 / 50) (y := 2 + Real.cos φ) (by norm_num) (le_of_lt hA)).mpr h1'
      rw [ncCosLo]; linarith
    · have h3 : 2 + Real.cos φ < Real.sqrt (433 / 50) :=
        (Real.lt_sqrt (x := 2 + Real.cos φ) (y := 433 / 50) (le_of_lt hA)).mpr h2'
      rw [ncCosHi]; linarith
  · rintro ⟨h1, h2⟩
    have h1' : (53 / 50 : ℝ) < (2 + Real.cos φ) ^ 2 := by
      have h3 : Real.sqrt (53 / 50) < 2 + Real.cos φ := by rw [ncCosLo] at h1; linarith
      exact (Real.sqrt_lt (x := 53 / 50) (y := 2 + Real.cos φ) (by norm_num) (le_of_lt hA)).mp h3
    have h2' : (2 + Real.cos φ) ^ 2 < 433 / 50 := by
      have h3 : 2 + Real.cos φ < Real.sqrt (433 / 50) := by rw [ncCosHi] at h2; linarith
      exact (Real.lt_sqrt (x := 2 + Real.cos φ) (y := 433 / 50) (le_of_lt hA)).mp h3
    constructor
    · rw [Real.lt_sqrt (x := 9 / 10) (y := (2 + Real.cos φ) ^ 2 - 1 / 4) (by norm_num)]
      nlinarith
    · rw [Real.sqrt_lt (x := (2 + Real.cos φ) ^ 2 - 1 / 4) (y := 29 / 10) hnn (by norm_num)]
      nlinarith

/-! ## The box norm of the arc -/

theorem boxNorm_ncArc (φ : ℝ) :
    Submission.boxNorm ncCtr ncCyc3 (ncArc φ) =
      max (max |ncY1 φ - 19 / 10| (|Real.sin φ| / (2 : ℝ) ^ (1 / 3 : ℝ)))
        (|(1 : ℝ) / 2 - 1| / (2 : ℝ) ^ (2 / 3 : ℝ)) := by
  rw [boxNorm_nc, ncArc_apply_one, ncArc_apply_two, ncArc_apply_zero]

private lemma one_lt_rpow_third : (1 : ℝ) < (2 : ℝ) ^ (1 / 3 : ℝ) := by
  have h := (Real.rpow_lt_rpow_left_iff (show (1 : ℝ) < 2 by norm_num)).mpr
    (show (0 : ℝ) < 1 / 3 by norm_num)
  simpa using h

private lemma one_lt_rpow_two_thirds : (1 : ℝ) < (2 : ℝ) ^ (2 / 3 : ℝ) := by
  have h := (Real.rpow_lt_rpow_left_iff (show (1 : ℝ) < 2 by norm_num)).mpr
    (show (0 : ℝ) < 2 / 3 by norm_num)
  simpa using h

/-- The box norm of `ncArc φ` is `< 1` exactly when the `y`-coordinate is in the window. -/
theorem boxNorm_ncArc_lt_one_iff (φ : ℝ) :
    Submission.boxNorm ncCtr ncCyc3 (ncArc φ) < 1 ↔ |ncY1 φ - 19 / 10| < 1 := by
  rw [boxNorm_ncArc, max_lt_iff, max_lt_iff]
  constructor
  · rintro ⟨⟨h1, -⟩, -⟩; exact h1
  · intro h1
    refine ⟨⟨h1, ?_⟩, ?_⟩
    · rw [div_lt_one (by positivity)]
      have h2 : |Real.sin φ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin φ, Real.sin_le_one φ⟩
      linarith [one_lt_rpow_third]
    · rw [div_lt_one (by positivity)]
      have h2 : |(1 : ℝ) / 2 - 1| = 1 / 2 := by norm_num
      rw [h2]
      linarith [one_lt_rpow_two_thirds]

/-- The box norm of `ncArc φ` is `≤ 1` exactly when the `y`-coordinate is in the closed window. -/
theorem boxNorm_ncArc_le_one_iff (φ : ℝ) :
    Submission.boxNorm ncCtr ncCyc3 (ncArc φ) ≤ 1 ↔ |ncY1 φ - 19 / 10| ≤ 1 := by
  rw [boxNorm_ncArc, max_le_iff, max_le_iff]
  constructor
  · rintro ⟨⟨h1, -⟩, -⟩; exact h1
  · intro h1
    refine ⟨⟨h1, ?_⟩, ?_⟩
    · rw [div_le_one (by positivity)]
      have h2 : |Real.sin φ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin φ, Real.sin_le_one φ⟩
      linarith [one_lt_rpow_third]
    · rw [div_le_one (by positivity)]
      have h2 : |(1 : ℝ) / 2 - 1| = 1 / 2 := by norm_num
      rw [h2]
      linarith [one_lt_rpow_two_thirds]

/-! ## The arc lies on the slice -/

/-- **Membership of `ncArc φ` in the slice.**  The plane condition holds identically on the curve and
the box condition is exactly the `y`-window, so membership is the window inequality. -/
theorem ncArc_mem_Sigma_iff (φ : ℝ) :
    ncArc φ ∈ Sigma idDiffeo ncRad ncCtr ncCyc3 ncU ↔ |ncY1 φ - 19 / 10| < 1 := by
  rw [Sigma, Work.BoxShrink.Core.mem_sliceRegion]
  constructor
  · rintro ⟨-, hbox, -⟩
    have := (Submission.mem_PBox_iff ncRad ncCtr ncCyc3 (ncArc φ)).mp hbox
    rw [ncRad_eq] at this
    exact (boxNorm_ncArc_lt_one_iff φ).mp this
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨(ncTheta φ, φ), rfl⟩
    · exact (Submission.mem_PBox_iff ncRad ncCtr ncCyc3 (ncArc φ)).mpr
        (by rw [ncRad_eq]; exact (boxNorm_ncArc_lt_one_iff φ).mpr h)
    · rw [ncCyc3_two, ncArc_apply_zero, ncCtr_zero, ncU_eq]; norm_num

/-- **The arc's open pieces lie on the slice.** -/
theorem ncArc_mem_Sigma_of_mem_Ioo {ψ : ℝ} (hψ : ψ ∈ Set.Ioo ncPhiA ncPhiB) :
    ncArc ψ ∈ Sigma idDiffeo ncRad ncCtr ncCyc3 ncU := by
  rw [ncArc_mem_Sigma_iff]
  have h := (ncY1_mem_Ioo_iff ψ).mpr (cos_mem_Ioo_of_mem_Ioo_phiA_phiB hψ)
  rw [abs_lt]
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- **The arc's open pieces lie on the slice** (second arc). -/
theorem ncArc_mem_Sigma_of_mem_Ioo_second {ψ : ℝ}
    (hψ : ψ ∈ Set.Ioo (2 * Real.pi - ncPhiB) (2 * Real.pi - ncPhiA)) :
    ncArc ψ ∈ Sigma idDiffeo ncRad ncCtr ncCyc3 ncU := by
  rw [ncArc_mem_Sigma_iff]
  have h := (ncY1_mem_Ioo_iff ψ).mpr (cos_mem_Ioo_of_mem_Ioo_second ψ hψ)
  rw [abs_lt]
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- **The closed arc lies in the closure of the slice.**  The closed interval is the closure of the
open one, on which the arc lies in the slice, and the arc is continuous. -/
theorem ncArc_image_Icc_phiA_phiB_subset_closure :
    ncArc '' Set.Icc ncPhiA ncPhiB ⊆
      closure (Sigma idDiffeo ncRad ncCtr ncCyc3 ncU) := by
  have hcl : closure (Set.Ioo ncPhiA ncPhiB) = Set.Icc ncPhiA ncPhiB :=
    closure_Ioo (ne_of_lt ncPhiA_lt_ncPhiB)
  rw [← hcl]
  refine subset_trans (image_closure_subset_closure_image continuous_ncArc) (closure_mono ?_)
  rintro _ ⟨t, ht, rfl⟩
  exact ncArc_mem_Sigma_of_mem_Ioo ht

/-- **The closed arc lies in the closure of the slice** (second arc). -/
theorem ncArc_image_Icc_second_subset_closure :
    ncArc '' Set.Icc (2 * Real.pi - ncPhiB) (2 * Real.pi - ncPhiA) ⊆
      closure (Sigma idDiffeo ncRad ncCtr ncCyc3 ncU) := by
  have hne : (2 * Real.pi - ncPhiB) ≠ (2 * Real.pi - ncPhiA) := by
    intro h; linarith [ncPhiA_lt_ncPhiB]
  have hcl : closure (Set.Ioo (2 * Real.pi - ncPhiB) (2 * Real.pi - ncPhiA)) =
      Set.Icc (2 * Real.pi - ncPhiB) (2 * Real.pi - ncPhiA) := closure_Ioo hne
  rw [← hcl]
  refine subset_trans (image_closure_subset_closure_image continuous_ncArc) (closure_mono ?_)
  rintro _ ⟨t, ht, rfl⟩
  exact ncArc_mem_Sigma_of_mem_Ioo_second ht

end

end Work.BoxShrink.PinchOff.RefuteNC
