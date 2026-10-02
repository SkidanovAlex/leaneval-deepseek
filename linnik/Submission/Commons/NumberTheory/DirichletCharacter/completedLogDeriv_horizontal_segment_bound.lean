import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.windowZeroCountC
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInStrip
import Submission.Commons.NumberTheory.Linnik.logDeriv_estimate
import Submission.Commons.NumberTheory.Linnik.partialFraction_tail

open Complex DirichletCharacter Metric
open scoped Real BigOperators
open MeasureTheory intervalIntegral

set_option maxHeartbeats 1000000

namespace Commons.NumberTheory.DirichletCharacter

private lemma hcont0 (Δ : ℝ) (hΔ : 0 < Δ) : Continuous (fun y : ℝ => (Real.sqrt (y ^ 2 + Δ ^ 2))⁻¹) := by
  apply Continuous.inv₀
  · exact Real.continuous_sqrt.comp (by continuity)
  · intro y
    exact ne_of_gt (Real.sqrt_pos.mpr (by positivity))

private lemma hnonneg0 (Δ y : ℝ) : 0 ≤ (Real.sqrt (y ^ 2 + Δ ^ 2))⁻¹ := by positivity

private lemma int_0_3_le (Δ : ℝ) (hΔ : 0 < Δ) :
    (∫ y : ℝ in (0:ℝ)..3, (Real.sqrt (y ^ 2 + Δ ^ 2))⁻¹) ≤ 3 + max 0 (Real.log (1 / Δ)) := by
  set h : ℝ → ℝ := fun y => (Real.sqrt (y ^ 2 + Δ ^ 2))⁻¹ with hh
  have hhcont : Continuous h := hcont0 Δ hΔ
  have hh0 : ∀ y, 0 ≤ h y := fun y => hnonneg0 Δ y
  by_cases hΔ3 : 3 ≤ Δ
  · have hle : (∫ y : ℝ in (0:ℝ)..3, h y) ≤ ∫ y : ℝ in (0:ℝ)..3, (Δ⁻¹ : ℝ) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
      · exact hhcont.intervalIntegrable _ _
      · exact intervalIntegrable_const
      · intro y _
        rw [hh]
        simp only
        apply inv_anti₀ hΔ
        calc Δ = Real.sqrt (Δ ^ 2) := (Real.sqrt_sq hΔ.le).symm
          _ ≤ Real.sqrt (y ^ 2 + Δ ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg y])
    rw [intervalIntegral.integral_const] at hle
    simp only [sub_zero, smul_eq_mul] at hle
    have h2 : ((3:ℝ)) * Δ⁻¹ ≤ 1 := by
      rw [inv_eq_one_div, mul_one_div, div_le_one hΔ]
      linarith
    have h3 : (0:ℝ) ≤ max 0 (Real.log (1 / Δ)) := le_max_left _ _
    linarith
  · rw [not_le] at hΔ3
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (f := h) (hhcont.intervalIntegrable 0 Δ) (hhcont.intervalIntegrable Δ 3)
    rw [← hsplit]
    have hpart1 : (∫ y : ℝ in (0:ℝ)..Δ, h y) ≤ 1 := by
      have hle : (∫ y : ℝ in (0:ℝ)..Δ, h y) ≤ ∫ y : ℝ in (0:ℝ)..Δ, (Δ⁻¹ : ℝ) := by
        apply intervalIntegral.integral_mono_on hΔ.le
        · exact hhcont.intervalIntegrable _ _
        · exact intervalIntegrable_const
        · intro y _
          rw [hh]
          simp only
          apply inv_anti₀ hΔ
          calc Δ = Real.sqrt (Δ ^ 2) := (Real.sqrt_sq hΔ.le).symm
            _ ≤ Real.sqrt (y ^ 2 + Δ ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg y])
      rw [intervalIntegral.integral_const] at hle
      simp only [sub_zero, smul_eq_mul] at hle
      have h2 : Δ * Δ⁻¹ ≤ 1 := by
        rw [inv_eq_one_div, mul_one_div, div_le_one hΔ]
      linarith
    have hpart2 : (∫ y : ℝ in Δ..3, h y) ≤ 2 + max 0 (Real.log (1 / Δ)) := by
      have hyinv : (∫ y : ℝ in Δ..3, h y) ≤ ∫ y : ℝ in Δ..3, y⁻¹ := by
        apply intervalIntegral.integral_mono_on (le_of_lt hΔ3)
        · exact hhcont.intervalIntegrable _ _
        · apply ContinuousOn.intervalIntegrable
          apply ContinuousOn.inv₀ continuousOn_id
          intro y hy
          rw [Set.uIcc_of_le (le_of_lt hΔ3), Set.mem_Icc] at hy
          exact ne_of_gt (show 0 < y by linarith [hy.1, hΔ])
        · intro y hy
          have hypos : 0 < y := by linarith [hy.1, hΔ]
          rw [hh]
          simp only
          refine inv_anti₀ (a := Real.sqrt (y ^ 2 + Δ ^ 2)) (b := y) hypos ?_
          calc y = Real.sqrt (y ^ 2) := (Real.sqrt_sq hypos.le).symm
            _ ≤ Real.sqrt (y ^ 2 + Δ ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg Δ])
      have hval : (∫ y : ℝ in Δ..3, y⁻¹) = Real.log (3 / Δ) := by
        have h0 : (0:ℝ) ∉ Set.uIcc Δ 3 := by
          rw [Set.uIcc_of_le (le_of_lt hΔ3), Set.mem_Icc]
          rintro ⟨h1, _⟩
          linarith
        rw [integral_inv h0]
      have hlog3 : Real.log (3 / Δ) ≤ 2 + max 0 (Real.log (1 / Δ)) := by
        have h1 : (3:ℝ) / Δ = 3 * (1 / Δ) := by ring
        rw [h1, Real.log_mul (by norm_num) (by positivity)]
        have h2 : Real.log 3 ≤ (2:ℝ) := by
          have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num)
          linarith
        linarith [le_max_right (0:ℝ) (Real.log (1 / Δ))]
      linarith
    linarith

private lemma int_shift_le (β Δ : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hΔ : 0 < Δ) :
    (∫ y : ℝ in (-1/2 - β)..(2 - β), (Real.sqrt (y ^ 2 + Δ ^ 2))⁻¹)
      ≤ 3 * max 0 (Real.log (1 / Δ)) + 10 := by
  set h : ℝ → ℝ := fun y => (Real.sqrt (y ^ 2 + Δ ^ 2))⁻¹ with hh
  have hhcont : Continuous h := hcont0 Δ hΔ
  have hh0 : ∀ y, 0 ≤ h y := fun y => hnonneg0 Δ y
  have ha : -1/2 - β ≤ (0:ℝ) := by linarith
  have hb : (0:ℝ) ≤ 2 - β := by linarith
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (f := h)
    (hhcont.intervalIntegrable (-1/2 - β) 0) (hhcont.intervalIntegrable (0:ℝ) (2 - β))
  rw [← hsplit]
  have hp1 : (∫ y : ℝ in (-1/2 - β)..0, h y) = ∫ y : ℝ in (0:ℝ)..β + 1/2, h y := by
    have hneg := intervalIntegral.integral_comp_neg (f := h) (a := (-1/2 - β : ℝ)) (b := 0)
    have hcongr : (∫ y : ℝ in (-1/2 - β)..0, h y) = ∫ y : ℝ in (-1/2 - β)..0, h (-y) := by
      apply intervalIntegral.integral_congr
      intro y _
      simp only [hh]
      ring_nf
    rw [hcongr, hneg]
    norm_num
  rw [hp1]
  have hle1 : (∫ y : ℝ in (0:ℝ)..2 - β, h y) ≤ ∫ y : ℝ in (0:ℝ)..3, h y := by
    have hsplit2 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (f := h) (hhcont.intervalIntegrable (0:ℝ) (2-β)) (hhcont.intervalIntegrable (2-β) 3)
    have hnn : 0 ≤ ∫ y : ℝ in (2 - β)..3, h y :=
      intervalIntegral.integral_nonneg (by linarith) (fun y _ => hh0 y)
    linarith [hsplit2]
  have hle2 : (∫ y : ℝ in (0:ℝ)..(β + 1/2), h y) ≤ ∫ y : ℝ in (0:ℝ)..3, h y := by
    have hsplit2 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (f := h) (hhcont.intervalIntegrable (0:ℝ) (β+1/2)) (hhcont.intervalIntegrable (β+1/2) 3)
    have hnn : 0 ≤ ∫ y : ℝ in (β + 1/2)..3, h y :=
      intervalIntegral.integral_nonneg (by linarith) (fun y _ => hh0 y)
    linarith [hsplit2]
  have hkey := int_0_3_le Δ hΔ
  have hmax : (0:ℝ) ≤ max 0 (Real.log (1 / Δ)) := le_max_left _ _
  linarith

private theorem integral_inv_sqrt_sq_add_le (β Δ : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hΔ : 0 < Δ) :
    (∫ x : ℝ in (-1/2)..2, (Real.sqrt ((x - β) ^ 2 + Δ ^ 2))⁻¹)
      ≤ 3 * max 0 (Real.log (1 / Δ)) + 10 := by
  set h : ℝ → ℝ := fun y => (Real.sqrt (y ^ 2 + Δ ^ 2))⁻¹ with hh
  have hrew : (∫ x : ℝ in (-1/2)..2, (Real.sqrt ((x - β) ^ 2 + Δ ^ 2))⁻¹)
      = ∫ x : ℝ in (-1/2)..2, h (x + (-β)) := by
    apply intervalIntegral.integral_congr
    intro x _
    simp only [hh]
    ring_nf
  rw [hrew]
  have hsub : (∫ x : ℝ in (-1/2)..2, h (x + (-β))) = ∫ y : ℝ in (-1/2 - β)..(2 - β), h y := by
    have h0 := intervalIntegral.integral_comp_add_right (f := h) (a := (-1/2 : ℝ)) (b := 2) (-β)
    simpa only [show (-1/2 : ℝ) + -β = -1/2 - β by ring, show (2:ℝ) + -β = 2 - β by ring] using h0
  rw [hsub]
  exact int_shift_le β Δ hβ0 hβ1 hΔ


private lemma zero_of_divisor_ne_zero {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) {u : ℂ} (hu : u ∈ U)
    (hd : MeromorphicOn.divisor f U u ≠ 0) : f u = 0 := by
  by_contra hfu
  rw [MeromorphicOn.divisor_apply hf.meromorphicOn hu] at hd
  have hAn : AnalyticAt ℂ f u := hf u hu
  rw [hAn.meromorphicOrderAt_eq] at hd
  have hord0 : analyticOrderAt f u = 0 := analyticOrderAt_eq_zero.mpr (Or.inr hfu)
  rw [hord0] at hd
  simp at hd

private theorem nearLine_zeroCount {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hχprim : χ.IsPrimitive) :
    ∃ C : ℝ, 0 < C ∧ ∀ T' : ℝ, 2 ≤ T' →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.closedBall 0 (T' + 3))) u : ℤ) : ℝ) *
          (if |u.im - T'| ≤ 1 then 1 else 0)) ≤
        C * (Real.log (T' + 3) + Real.log (N : ℝ) + 2) := by
  classical
  rcases windowZeroCountC χ hχ hχprim with ⟨c, hcpos, hc⟩
  refine ⟨8 * c, by linarith, ?_⟩
  intro T' hT'
  set Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ with hΛ
  have hΛdiff : Differentiable ℂ Λ := by
    simpa [hΛ] using DirichletCharacter.differentiable_completedLFunction hχ
  have hΛan : ∀ U : Set ℂ, AnalyticOnNhd ℂ Λ U := by
    intro U z hz; exact hΛdiff.analyticAt z
  have hΛmer : ∀ U : Set ℂ, MeromorphicOn Λ U := fun U => (hΛan U).meromorphicOn
  have hT1 : 1 ≤ T' - 1 := by linarith
  have hTle : T' - 1 ≤ T' + 1 := by linarith
  have hb := hc (T' - 1) (T' + 1) hT1 hTle
  -- pointwise comparison
  set A : ℂ → ℝ := fun u => (((MeromorphicOn.divisor Λ (Metric.closedBall 0 (T' + 3))) u : ℤ) : ℝ) *
      (if |u.im - T'| ≤ 1 then 1 else 0) with hA
  set B : ℂ → ℝ := fun u => (((MeromorphicOn.divisor Λ (Metric.closedBall 0 (T' + 2))) u : ℤ) : ℝ) *
      (if T' - 1 ≤ |u.im| ∧ |u.im| ≤ T' + 1 then 1 else 0) with hB
  have hfinA : Function.HasFiniteSupport A := by
    have h1 : (Function.support
        (fun u : ℂ => (((MeromorphicOn.divisor Λ (Metric.closedBall 0 (T' + 3))) u : ℤ) : ℝ))).Finite :=
      (MeromorphicOn.divisor_support_finite_of_subset (f := Λ) (U := Metric.closedBall 0 (T'+3))
        (hΛmer _) (isCompact_closedBall 0 (T'+3)) (fun z hz => hz)).subset (by
          intro u hu
          simp only [Function.mem_support] at hu ⊢
          intro hd0
          exact hu (by simp [hd0]))
    refine h1.subset ?_
    intro u hu
    rw [Function.mem_support] at hu ⊢
    rw [hA] at hu
    simp only at hu
    intro hd0
    exact hu (by rw [hd0]; simp)
  have hfinB : Function.HasFiniteSupport B := by
    have h1 : (Function.support
        (fun u : ℂ => (((MeromorphicOn.divisor Λ (Metric.closedBall 0 (T' + 2))) u : ℤ) : ℝ))).Finite :=
      (MeromorphicOn.divisor_support_finite_of_subset (f := Λ) (U := Metric.closedBall 0 (T'+2))
        (hΛmer _) (isCompact_closedBall 0 (T'+2)) (fun z hz => hz)).subset (by
          intro u hu
          simp only [Function.mem_support] at hu ⊢
          intro hd0
          exact hu (by simp [hd0]))
    refine h1.subset ?_
    intro u hu
    rw [Function.mem_support] at hu ⊢
    rw [hB] at hu
    simp only at hu
    intro hd0
    exact hu (by rw [hd0]; simp)
  have hpt : ∀ u : ℂ, A u ≤ B u := by
    intro u
    by_cases hid : |u.im - T'| ≤ 1
    · rw [hA, hB]
      simp only
      rw [if_pos hid]
      have hd0 : 0 ≤ ((MeromorphicOn.divisor Λ (Metric.closedBall 0 (T' + 3))) u : ℤ) :=
        MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hΛan _) u
      have hcast0 : (0:ℝ) ≤ (((MeromorphicOn.divisor Λ (Metric.closedBall 0 (T' + 3))) u : ℤ) : ℝ) := by
        exact_mod_cast hd0
      by_cases hdz : MeromorphicOn.divisor Λ (Metric.closedBall 0 (T' + 3)) u = 0
      · rw [hdz]
        simp only [Int.cast_zero, zero_mul]
        have : (0:ℝ) ≤ (((MeromorphicOn.divisor Λ (Metric.closedBall 0 (T' + 2))) u : ℤ) : ℝ) *
            (if T' - 1 ≤ |u.im| ∧ |u.im| ≤ T' + 1 then 1 else 0) := by
          apply mul_nonneg
          · exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hΛan _) u
          · split <;> norm_num
        linarith
      · -- u is a zero, inside the ball of radius T'+2
        have huB3 : u ∈ Metric.closedBall 0 (T' + 3) := by
          by_contra hnot
          exact hdz ((MeromorphicOn.divisor Λ (Metric.closedBall 0 (T'+3))).apply_eq_zero_of_notMem hnot)
        have hzero : Λ u = 0 := zero_of_divisor_ne_zero (hΛan _) huB3 hdz
        have hstrip := zerosInStrip χ hχ hχprim u (by simpa [hΛ] using hzero)
        have hule : ‖u‖ ≤ T' + 2 := by
          have h1 : u.re ^ 2 ≤ 1 := by nlinarith only [hstrip.1, hstrip.2]
          have h2 : u.im ^ 2 ≤ (T' + 1) ^ 2 := by
            have : |u.im - T'| ≤ 1 := hid
            have : u.im ≤ T' + 1 := by
              have := (abs_le.mp hid).2; linarith
            have : -(T' + 1) ≤ u.im := by
              have := (abs_le.mp hid).1; linarith
            exact sq_le_sq' ‹-(T' + 1) ≤ u.im› ‹u.im ≤ T' + 1›
          rw [Complex.norm_def, Complex.normSq_apply, Real.sqrt_le_iff]
          refine ⟨by positivity, ?_⟩
          nlinarith only [h1, h2, hT']
        have heq : MeromorphicOn.divisor Λ (Metric.closedBall 0 (T' + 3)) u =
            MeromorphicOn.divisor Λ (Metric.closedBall 0 (T' + 2)) u :=
          Commons.NumberTheory.Linnik.divisor_closedBall_eq_of_le (f := Λ) hΛmer (by linarith) hule
        have hind : T' - 1 ≤ |u.im| ∧ |u.im| ≤ T' + 1 := by
          have h1 : T' - 1 ≤ u.im := by have := (abs_le.mp hid).1; linarith
          have h2 : u.im ≤ T' + 1 := by have := (abs_le.mp hid).2; linarith
          have h3 : 0 < u.im := by linarith
          rw [abs_of_pos h3]
          exact ⟨h1, h2⟩
        rw [heq, if_pos hind]
    · rw [hA, hB]
      simp only
      rw [if_neg hid, mul_zero]
      apply mul_nonneg
      · exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hΛan _) u
      · split <;> norm_num
  have hsum := finsum_le_finsum' hfinA hfinB hpt
  refine le_trans hsum ?_
  -- rewrite B's sum as the earlier window sum
  have hb' : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (Metric.closedBall 0 (T' + 2))) u : ℤ) : ℝ) *
      (if T' - 1 ≤ |u.im| ∧ |u.im| ≤ T' + 1 then 1 else 0)) ≤
      c * 4 * (Real.log (T' + 4) + Real.log (N : ℝ) + 2) := by
    have h := hb
    have h2 : (T' + 1) - (T' - 1) + 2 = 4 := by ring
    have h3 : T' + 1 + 1 = T' + 2 := by ring
    have h4 : T' + 1 + 3 = T' + 4 := by ring
    rw [h2, h3, h4] at h
    simpa [hΛ, hB] using h
  refine le_trans hb' ?_
  have hlog : Real.log (T' + 4) ≤ 2 * Real.log (T' + 3) := by
    have h1 : T' + 4 ≤ (T' + 3) ^ 2 := by nlinarith only [hT']
    have h2 : (0:ℝ) < T' + 4 := by linarith
    calc Real.log (T' + 4) ≤ Real.log ((T' + 3) ^ 2) := Real.log_le_log h2 h1
      _ = 2 * Real.log (T' + 3) := by rw [Real.log_pow]; norm_num
  have hl3 : 0 ≤ Real.log (T' + 3) := Real.log_nonneg (by linarith)
  have hlN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by
    exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N)))
  have h8 : (8:ℝ) * c * (Real.log (T' + 3) + Real.log (N : ℝ) + 2) =
      4 * c * (2 * Real.log (T' + 3) + Real.log (N : ℝ) + 2) + 4 * c * (Real.log (N : ℝ) + 2) := by ring
  have hstep : c * 4 * (Real.log (T' + 4) + Real.log (N : ℝ) + 2) ≤
      8 * c * (Real.log (T' + 3) + Real.log (N : ℝ) + 2) := by
    have hc0 : 0 ≤ c := le_of_lt hcpos
    nlinarith only [mul_le_mul_of_nonneg_left hlog hc0, mul_nonneg hc0 hlN, hc0]
  linarith [hstep]

/-- support of `f u * ‖w-u‖⁻¹` is finite when `f` has finite support. -/
private lemma hfs_mul_inv {f : ℂ → ℝ} (hf : Function.HasFiniteSupport f) (w : ℂ) :
    Function.HasFiniteSupport (fun u : ℂ => f u * (‖w - u‖)⁻¹) := by
  refine hf.subset ?_
  intro u hu
  rw [Function.mem_support] at hu ⊢
  intro hf0
  exact hu (by rw [hf0, zero_mul])

/-- cast of a finite-support integer function to `ℝ` has finite support. -/
private lemma hfs_cast {d : ℂ → ℤ} (hd : (Function.support d).Finite) :
    Function.HasFiniteSupport (fun u : ℂ => (((d u : ℤ) : ℝ))) := by
  refine hd.subset ?_
  intro u hu
  rw [Function.mem_support] at hu ⊢
  intro h0
  exact hu (by simp [h0])

/-- One zero of the completed L-function contributes at most `3 max 0 (log (1/δ)) + 10`
to the horizontal integral. -/
private lemma integral_inv_norm_le (u : ℂ) (T' δ : ℝ) (hδ : 0 < δ)
    (hu0 : 0 ≤ u.re) (hu1 : u.re ≤ 1) (hΔ : δ ≤ |u.im - T'|) :
    (∫ x : ℝ in (-1/2)..2, (‖((x : ℂ) + (T' : ℂ) * Complex.I) - u‖)⁻¹)
      ≤ 3 * max 0 (Real.log (1 / δ)) + 10 := by
  set Δ : ℝ := |u.im - T'| with hΔdef
  have hΔpos : 0 < Δ := lt_of_lt_of_le hδ hΔ
  have hkey := integral_inv_sqrt_sq_add_le u.re Δ hu0 hu1 hΔpos
  have hid : ∀ x : ℝ, (‖((x : ℂ) + (T' : ℂ) * Complex.I) - u‖)⁻¹
      = (Real.sqrt ((x - u.re) ^ 2 + Δ ^ 2))⁻¹ := by
    intro x
    congr 1
    rw [Complex.norm_def, Complex.normSq_apply]
    congr 1
    rw [Complex.sub_re, Complex.sub_im]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, Complex.add_im, Complex.mul_im, mul_one,
      add_zero]
    rw [hΔdef, sq_abs]
    ring
  calc (∫ x : ℝ in (-1/2)..2, (‖((x : ℂ) + (T' : ℂ) * Complex.I) - u‖)⁻¹)
      = (∫ x : ℝ in (-1/2)..2, (Real.sqrt ((x - u.re) ^ 2 + Δ ^ 2))⁻¹) := by
        apply intervalIntegral.integral_congr
        intro x _
        exact hid x
    _ ≤ 3 * max 0 (Real.log (1 / Δ)) + 10 := hkey
    _ ≤ 3 * max 0 (Real.log (1 / δ)) + 10 := by
        have hle : Real.log (1 / Δ) ≤ Real.log (1 / δ) := by
          apply Real.log_le_log (by positivity)
          rw [one_div, one_div]
          exact inv_anti₀ hδ hΔ
        have := max_le_max (le_refl (0:ℝ)) hle
        linarith

/-- The divisor of the moving unit ball at a zero is bounded by the divisor of the fixed
ball of radius `T'+3`, restricted to the window `|Im - T'| ≤ 1`. -/
private lemma moving_divisor_le {Λ : ℂ → ℂ} (hΛdiff : Differentiable ℂ Λ)
    {T' : ℝ} (hT' : 2 ≤ T') {w u : ℂ} (hwim : w.im = T')
    (hstrip : ∀ ρ : ℂ, Λ ρ = 0 → 0 < ρ.re ∧ ρ.re < 1) :
    (((MeromorphicOn.divisor Λ (Metric.closedBall w 1)) u : ℤ) : ℝ) ≤
      (((MeromorphicOn.divisor Λ (Metric.closedBall 0 (T' + 3))) u : ℤ) : ℝ) *
        (if |u.im - T'| ≤ 1 then 1 else 0) := by
  have hAnw : AnalyticOnNhd ℂ Λ (Metric.closedBall w 1) := fun z _ => hΛdiff.analyticAt z
  have hAn3 : AnalyticOnNhd ℂ Λ (Metric.closedBall 0 (T' + 3)) := fun z _ => hΛdiff.analyticAt z
  by_cases hid : |u.im - T'| ≤ 1
  · rw [if_pos hid, mul_one]
    by_cases hd : MeromorphicOn.divisor Λ (Metric.closedBall w 1) u = 0
    · rw [hd, Int.cast_zero]
      exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn3 u
    · have huB : u ∈ Metric.closedBall w 1 := by
        by_contra hnot
        exact hd ((MeromorphicOn.divisor Λ (Metric.closedBall w 1)).apply_eq_zero_of_notMem hnot)
      have hzero : Λ u = 0 := zero_of_divisor_ne_zero hAnw huB hd
      have hst := hstrip u hzero
      have hule : ‖u‖ ≤ T' + 2 := by
        have h1 : u.im ≤ T' + 1 := by
          have := (abs_le.mp hid).2; linarith
        have h2 : -(T' + 1) ≤ u.im := by
          have := (abs_le.mp hid).1; linarith
        have h3 : u.re ^ 2 ≤ 1 := by nlinarith only [hst.1, hst.2]
        have h4 : u.im ^ 2 ≤ (T' + 1) ^ 2 := by
          have hab : |u.im| ≤ T' + 1 := by rw [abs_le]; exact ⟨h2, h1⟩
          exact sq_le_sq' h2 h1
        rw [Complex.norm_def, Complex.normSq_apply, Real.sqrt_le_iff]
        refine ⟨by positivity, ?_⟩
        nlinarith only [h3, h4, hT']
      have huB3 : u ∈ Metric.closedBall 0 (T' + 3) := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        simpa using le_trans hule (by linarith : T' + 2 ≤ T' + 3)
      rw [MeromorphicOn.divisor_apply hAnw.meromorphicOn huB,
        MeromorphicOn.divisor_apply hAn3.meromorphicOn huB3]
  · rw [if_neg hid]
    have hd : MeromorphicOn.divisor Λ (Metric.closedBall w 1) u = 0 := by
      by_cases huB : u ∈ Metric.closedBall w 1
      · exfalso
        have hle : ‖u - w‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using huB
        have hle' : ‖w - u‖ ≤ 1 := by rwa [norm_sub_rev] at hle
        have h1 : |w.im - u.im| ≤ ‖w - u‖ := by
          have h := Complex.abs_im_le_norm (w - u)
          rwa [Complex.sub_im] at h
        rw [hwim] at h1
        have : |u.im - T'| ≤ 1 := by rw [abs_sub_comm]; linarith
        exact hid this
      · exact (MeromorphicOn.divisor Λ (Metric.closedBall w 1)).apply_eq_zero_of_notMem huB
    rw [hd, Int.cast_zero, mul_zero]

theorem completedLogDeriv_horizontal_segment_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∃ C : ℝ, 0 < C ∧ ∀ T' : ℝ, 2 ≤ T' → ∀ δ : ℝ, 0 < δ →
      (∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 → δ ≤ |ρ.im - T'|) →
      (∫ x : ℝ in (-1/2)..2, ‖logDeriv (DirichletCharacter.completedLFunction χ)
           ((x : ℂ) + (T' : ℂ) * Complex.I)‖) ≤
        C * Real.log (N * (T' + 3)) *
          (Real.log (N * (T' + 3)) + max 0 (Real.log (1 / δ))) := by
  classical
  rcases Commons.NumberTheory.Linnik.logDeriv_estimate χ hχ hχprim with ⟨cL₀, hcL₀⟩
  rcases nearLine_zeroCount χ hχ hχprim with ⟨cW, hcWpos, hcW⟩
  set cL : ℝ := max cL₀ 0 with hcLdef
  have hcLle : cL₀ ≤ cL := by rw [hcLdef]; exact le_max_left _ _
  have hcL0 : 0 ≤ cL := by rw [hcLdef]; exact le_max_right _ _
  have hcW0 : 0 ≤ cW := le_of_lt hcWpos
  refine ⟨63 * cL + 52 * cW + 1, by positivity, ?_⟩
  intro T' hT' δ hδ hzero
  set Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ with hΛdef
  have hΛdiff : Differentiable ℂ Λ := by
    rw [hΛdef]; exact DirichletCharacter.differentiable_completedLFunction hχ
  have hAnU : ∀ U : Set ℂ, AnalyticOnNhd ℂ Λ U := fun U z _ => hΛdiff.analyticAt z
  have hmerU : ∀ U : Set ℂ, MeromorphicOn Λ U := fun U => (hAnU U).meromorphicOn
  have hstrip : ∀ ρ : ℂ, Λ ρ = 0 → 0 < ρ.re ∧ ρ.re < 1 := by
    intro ρ hρ
    exact zerosInStrip χ hχ hχprim ρ (by rw [← hΛdef]; exact hρ)
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N))
  have hlogN0 : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg hN1
  have hlog30 : 0 ≤ Real.log (T' + 3) := Real.log_nonneg (by linarith)
  set L : ℝ := Real.log ((N:ℝ) * (T' + 3)) with hLdef
  have hLval : L = Real.log (N:ℝ) + Real.log (T' + 3) := by
    rw [hLdef, Real.log_mul (by positivity) (by linarith)]
  have hlog5ge1 : (1:ℝ) ≤ Real.log 5 := by
    rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 5)]
    have := Real.exp_one_lt_d9; linarith
  have hLge1 : 1 ≤ L := by
    rw [hLval]
    have h5 : Real.log 5 ≤ Real.log (T' + 3) := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hL0 : 0 ≤ L := le_trans zero_le_one hLge1
  set mx : ℝ := max 0 (Real.log (1 / δ)) with hmxdef
  have hmx0 : 0 ≤ mx := by rw [hmxdef]; exact le_max_left _ _
  set ell : ℝ := Real.log (T' + 4) + Real.log (N:ℝ) + 2 with helldef
  have hell0 : 0 ≤ ell := by
    rw [helldef]
    have h1 : 0 ≤ Real.log (T' + 4) := Real.log_nonneg (by linarith)
    linarith
  have hlogT4 : Real.log (T' + 4) ≤ 2 * L := by
    have h1 : T' + 4 ≤ (T' + 3) ^ 2 := by nlinarith only [hT']
    have h2 : (0:ℝ) < T' + 4 := by linarith
    calc Real.log (T' + 4) ≤ Real.log ((T' + 3)^2) := Real.log_le_log h2 h1
      _ = 2 * Real.log (T' + 3) := by rw [Real.log_pow]; norm_num
      _ ≤ 2 * L := by rw [hLval]; linarith
  have hell_le : ell ≤ 5 * L := by
    rw [helldef]
    have h2 : Real.log (N:ℝ) ≤ L := by rw [hLval]; linarith
    linarith
  have hell2_le : ell^2 ≤ 25 * L^2 := by
    nlinarith only [mul_le_mul hell_le hell_le hell0 (by linarith only [hL0])]
  -- divisor, window, weight
  set d0 : ℂ → ℤ := fun u => MeromorphicOn.divisor Λ (Metric.closedBall 0 (T' + 3)) u with hd0def
  have hd0fin : (Function.support d0).Finite := by
    rw [hd0def]
    simpa using (MeromorphicOn.divisor_support_finite_of_subset (hmerU _)
      (isCompact_closedBall 0 (T' + 3)) (fun z hz => hz))
  set Z : Finset ℂ := hd0fin.toFinset.filter (fun u : ℂ => |u.im - T'| ≤ 1) with hZdef
  have hZmem : ∀ u : ℂ, u ∈ Z ↔ d0 u ≠ 0 ∧ |u.im - T'| ≤ 1 := by
    intro u
    rw [hZdef, Finset.mem_filter, Set.Finite.mem_toFinset, Function.mem_support]
  have hD0 : ∀ u : ℂ, 0 ≤ ((d0 u : ℤ) : ℝ) := by
    intro u
    simp only [hd0def]
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hAnU _) u
  have hZdata : ∀ u ∈ Z, Λ u = 0 ∧ δ ≤ |u.im - T'| := by
    intro u hu
    obtain ⟨hd0u, huim⟩ := (hZmem u).1 hu
    have huB3 : u ∈ Metric.closedBall 0 (T' + 3) := by
      by_contra hnot
      exact hd0u (by simp only [hd0def]; exact (MeromorphicOn.divisor Λ _).apply_eq_zero_of_notMem hnot)
    have hΛu : Λ u = 0 := zero_of_divisor_ne_zero (hAnU _) huB3 (by simpa only [hd0def] using hd0u)
    exact ⟨hΛu, hzero u hΛu⟩
  have hWsum : (∑ᶠ u : ℂ, (((d0 u : ℤ) : ℝ) * (if |u.im - T'| ≤ 1 then 1 else 0)))
      ≤ cW * (Real.log (T' + 3) + Real.log (N : ℝ) + 2) := by
    have h := hcW T' hT'
    simpa only [hd0def, hΛdef] using h
  have hWZ : (∑ᶠ u : ℂ, (((d0 u : ℤ) : ℝ) * (if |u.im - T'| ≤ 1 then 1 else 0)))
      = ∑ u ∈ Z, ((d0 u : ℤ) : ℝ) := by
    rw [finsum_eq_sum_of_support_subset _ ?_]
    · apply Finset.sum_congr rfl
      intro u hu
      rw [if_pos ((hZmem u).1 hu).2, mul_one]
    · intro u hu
      rw [Function.mem_support] at hu
      rw [Finset.mem_coe, hZmem]
      constructor
      · intro h0
        exact hu (by rw [h0]; simp)
      · by_contra hc
        exact hu (by rw [if_neg hc, mul_zero])
  -- per-zero integral bound
  have hper : ∀ u ∈ Z, (∫ x : ℝ in (-1/2)..2, (‖((x : ℂ) + (T' : ℂ) * Complex.I) - u‖)⁻¹)
      ≤ 3 * mx + 10 := by
    intro u hu
    obtain ⟨hΛu, hδu⟩ := hZdata u hu
    have hst := hstrip u hΛu
    have h := integral_inv_norm_le u T' δ hδ hst.1.le hst.2.le hδu
    rw [hmxdef]
    exact h
  -- pointwise bound
  have hGbound : ∀ x : ℝ, x ∈ Set.Ioc (-1/2) 2 →
      ‖logDeriv Λ ((x : ℂ) + (T' : ℂ) * Complex.I)‖ ≤
        cL * ell^2 + ∑ u ∈ Z, ((d0 u : ℤ) : ℝ) *
          (‖((x : ℂ) + (T' : ℂ) * Complex.I) - u‖)⁻¹ := by
    intro x hx
    have hxabs : |x| ≤ 2 := by
      rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
    set w : ℂ := (x : ℂ) + (T' : ℂ) * Complex.I with hwdef
    have hwre : w.re = x := by rw [hwdef]; simp
    have hwim : w.im = T' := by rw [hwdef]; simp
    have hwle : ‖w‖ ≤ T' + 2 := by
      have h := Complex.norm_le_abs_re_add_abs_im w
      rw [hwre, hwim, abs_of_nonneg (by linarith : (0:ℝ) ≤ T')] at h
      linarith
    have hR : 2 ≤ ‖w‖ := by
      have h := Complex.abs_im_le_norm w
      rw [hwim, abs_of_nonneg (by linarith : (0:ℝ) ≤ T')] at h
      linarith
    have hfin_dx : Function.HasFiniteSupport (fun u : ℂ =>
        (((MeromorphicOn.divisor Λ (Metric.closedBall w 1)) u : ℤ) : ℝ) * (‖w - u‖)⁻¹) :=
      hfs_mul_inv (hfs_cast (MeromorphicOn.divisor_support_finite_of_subset (hmerU _)
        (isCompact_closedBall w 1) (fun z hz => hz))) w
    have hfin_W : Function.HasFiniteSupport (fun u : ℂ =>
        (((d0 u : ℤ) : ℝ) * (if |u.im - T'| ≤ 1 then 1 else 0)) * (‖w - u‖)⁻¹) := by
      refine hfs_mul_inv ?_ w
      refine hd0fin.subset ?_
      intro u hu
      rw [Function.mem_support] at hu ⊢
      intro h0
      exact hu (by rw [h0]; simp)
    have hpt : ∀ u : ℂ, (((MeromorphicOn.divisor Λ (Metric.closedBall w 1)) u : ℤ) : ℝ) *
        (‖w - u‖)⁻¹ ≤
        (((d0 u : ℤ) : ℝ) * (if |u.im - T'| ≤ 1 then 1 else 0)) * (‖w - u‖)⁻¹ := by
      intro u
      refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr (norm_nonneg _))
      exact moving_divisor_le hΛdiff hT' hwim hstrip
    have hsum_le := finsum_le_finsum' hfin_dx hfin_W hpt
    have hsum_eq : (∑ᶠ u : ℂ, (((d0 u : ℤ) : ℝ) * (if |u.im - T'| ≤ 1 then 1 else 0)) *
        (‖w - u‖)⁻¹) = ∑ u ∈ Z, ((d0 u : ℤ) : ℝ) * (‖w - u‖)⁻¹ := by
      rw [finsum_eq_sum_of_support_subset _ ?_]
      · apply Finset.sum_congr rfl
        intro u hu
        rw [if_pos ((hZmem u).1 hu).2, mul_one]
      · intro u hu
        rw [Function.mem_support] at hu
        rw [Finset.mem_coe, hZmem]
        constructor
        · intro h0
          exact hu (by rw [h0]; simp)
        · by_contra hc
          exact hu (by rw [if_neg hc, mul_zero, zero_mul])
    have hmain : ‖logDeriv Λ w‖ ≤ cL * ell^2 + ∑ u ∈ Z, ((d0 u : ℤ) : ℝ) * (‖w - u‖)⁻¹ := by
      by_cases hΛw : Λ w = 0
      · have hz : ‖logDeriv Λ w‖ = 0 := by rw [logDeriv_apply, hΛw, div_zero, norm_zero]
        rw [hz]
        have h1 : 0 ≤ cL * ell^2 := mul_nonneg hcL0 (sq_nonneg ell)
        have h2 : 0 ≤ ∑ u ∈ Z, ((d0 u : ℤ) : ℝ) * (‖w - u‖)⁻¹ :=
          Finset.sum_nonneg (fun u _ => mul_nonneg (hD0 u) (by positivity))
        linarith
      · have hb := hcL₀ ‖w‖ hR w rfl hΛw
        rw [logDeriv_apply]
        have h1 : cL₀ * (Real.log (‖w‖ + 2) + Real.log (N : ℝ) + 2) ^ 2 ≤ cL * ell^2 := by
          have h0 : 0 ≤ Real.log (‖w‖ + 2) + Real.log (N : ℝ) + 2 := by
            have : 0 ≤ Real.log (‖w‖ + 2) := Real.log_nonneg (by linarith [norm_nonneg w])
            linarith
          have h2 : Real.log (‖w‖ + 2) + Real.log (N : ℝ) + 2 ≤ ell := by
            rw [helldef]
            have : Real.log (‖w‖ + 2) ≤ Real.log (T' + 4) :=
              Real.log_le_log (by positivity) (by linarith)
            linarith
          have h3 : (Real.log (‖w‖ + 2) + Real.log (N : ℝ) + 2) ^ 2 ≤ ell ^ 2 := by
            exact pow_le_pow_left₀ h0 h2 2
          exact mul_le_mul hcLle h3 (by positivity) hcL0
        have h4 : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (Metric.closedBall w 1)) u : ℤ) : ℝ) *
            (‖w - u‖)⁻¹) ≤ ∑ u ∈ Z, ((d0 u : ℤ) : ℝ) * (‖w - u‖)⁻¹ :=
          le_trans hsum_le (le_of_eq hsum_eq)
        calc ‖deriv Λ w / Λ w‖
            ≤ cL₀ * (Real.log (‖w‖ + 2) + Real.log (N : ℝ) + 2) ^ 2 +
                ∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (Metric.closedBall w 1)) u : ℤ) : ℝ) *
                  (‖w - u‖)⁻¹ := hb
          _ ≤ cL * ell^2 + ∑ u ∈ Z, ((d0 u : ℤ) : ℝ) * (‖w - u‖)⁻¹ := by linarith
    simpa [hwdef] using hmain
  -- continuity and integrability
  have hterm_cont : ∀ u ∈ Z, ContinuousOn (fun x : ℝ => ((d0 u : ℤ) : ℝ) *
      (‖((x : ℂ) + (T' : ℂ) * Complex.I) - u‖)⁻¹) (Set.uIcc (-1/2) 2) := by
    intro u hu
    by_cases hD0u : ((d0 u : ℤ) : ℝ) = 0
    · have heq : (fun x : ℝ => ((d0 u : ℤ) : ℝ) *
          (‖((x : ℂ) + (T' : ℂ) * Complex.I) - u‖)⁻¹) = fun _ : ℝ => 0 := by
        funext x
        rw [hD0u, zero_mul]
      rw [heq]
      exact continuousOn_const
    · obtain ⟨hΛu, hδu⟩ := hZdata u hu
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.inv₀
      · exact (continuous_norm.comp (by fun_prop)).continuousOn
      · intro x _
        have him : (((x : ℂ) + (T' : ℂ) * Complex.I) - u).im = T' - u.im := by simp
        have h1 : |T' - u.im| ≤ ‖((x : ℂ) + (T' : ℂ) * Complex.I) - u‖ := by
          have h := Complex.abs_im_le_norm (((x : ℂ) + (T' : ℂ) * Complex.I) - u)
          rwa [him] at h
        have h2 : δ ≤ |T' - u.im| := by rw [abs_sub_comm]; exact hδu
        exact ne_of_gt (lt_of_lt_of_le hδ (le_trans h2 h1))
  have hterm_int : ∀ u ∈ Z, IntervalIntegrable (fun x : ℝ => ((d0 u : ℤ) : ℝ) *
      (‖((x : ℂ) + (T' : ℂ) * Complex.I) - u‖)⁻¹) volume (-1/2) 2 :=
    fun u hu => (hterm_cont u hu).intervalIntegrable
  have hsum_cont : ContinuousOn (fun x : ℝ => ∑ u ∈ Z, ((d0 u : ℤ) : ℝ) *
      (‖((x : ℂ) + (T' : ℂ) * Complex.I) - u‖)⁻¹) (Set.uIcc (-1/2) 2) :=
    continuousOn_finsetSum Z hterm_cont
  have hsum_int : IntervalIntegrable (fun x : ℝ => ∑ u ∈ Z, ((d0 u : ℤ) : ℝ) *
      (‖((x : ℂ) + (T' : ℂ) * Complex.I) - u‖)⁻¹) volume (-1/2) 2 :=
    hsum_cont.intervalIntegrable
  have hGcont : ContinuousOn (fun x : ℝ => cL * ell^2 + ∑ u ∈ Z, ((d0 u : ℤ) : ℝ) *
      (‖((x : ℂ) + (T' : ℂ) * Complex.I) - u‖)⁻¹) (Set.uIcc (-1/2) 2) :=
    continuousOn_const.add hsum_cont
  have hGint : IntervalIntegrable (fun x : ℝ => cL * ell^2 + ∑ u ∈ Z, ((d0 u : ℤ) : ℝ) *
      (‖((x : ℂ) + (T' : ℂ) * Complex.I) - u‖)⁻¹) volume (-1/2) 2 :=
    hGcont.intervalIntegrable
  have hGint' : Integrable (fun x : ℝ => cL * ell^2 + ∑ u ∈ Z, ((d0 u : ℤ) : ℝ) *
      (‖((x : ℂ) + (T' : ℂ) * Complex.I) - u‖)⁻¹) (volume.restrict (Set.Ioc (-1/2) 2)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp hGint
  have hcalc : (∫ x : ℝ in (-1/2)..2, ‖logDeriv Λ ((x : ℂ) + (T' : ℂ) * Complex.I)‖)
      ≤ ∫ x : ℝ in (-1/2)..2, (cL * ell^2 + ∑ u ∈ Z, ((d0 u : ℤ) : ℝ) *
          (‖((x : ℂ) + (T' : ℂ) * Complex.I) - u‖)⁻¹) := by
    rw [intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_of_le (by norm_num)]
    refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => norm_nonneg _))
      hGint' ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hGbound x hx
  have hGval : (∫ x : ℝ in (-1/2)..2, (cL * ell^2 + ∑ u ∈ Z, ((d0 u : ℤ) : ℝ) *
        (‖((x : ℂ) + (T' : ℂ) * Complex.I) - u‖)⁻¹))
      = cL * ell^2 * (2 - (-1/2)) + ∑ u ∈ Z, ((d0 u : ℤ) : ℝ) *
        (∫ x : ℝ in (-1/2)..2, (‖((x : ℂ) + (T' : ℂ) * Complex.I) - u‖)⁻¹) := by
    rw [intervalIntegral.integral_add intervalIntegrable_const hsum_int]
    congr 1
    · rw [intervalIntegral.integral_const, smul_eq_mul]
      ring
    · rw [intervalIntegral.integral_finsetSum (fun u hu => hterm_int u hu)]
      apply Finset.sum_congr rfl
      intro u hu
      rw [intervalIntegral.integral_const_mul]
  have hper' : ∑ u ∈ Z, ((d0 u : ℤ) : ℝ) *
        (∫ x : ℝ in (-1/2)..2, (‖((x : ℂ) + (T' : ℂ) * Complex.I) - u‖)⁻¹)
      ≤ ∑ u ∈ Z, ((d0 u : ℤ) : ℝ) * (3 * mx + 10) :=
    Finset.sum_le_sum (fun u hu => mul_le_mul_of_nonneg_left (hper u hu) (hD0 u))
  have hsumZ : ∑ u ∈ Z, ((d0 u : ℤ) : ℝ) ≤ cW * (Real.log (T' + 3) + Real.log (N : ℝ) + 2) := by
    rw [← hWZ]; exact hWsum
  have htotal : (∫ x : ℝ in (-1/2)..2, ‖logDeriv Λ ((x : ℂ) + (T' : ℂ) * Complex.I)‖)
      ≤ (5/2) * cL * ell^2 +
        (cW * (Real.log (T' + 3) + Real.log (N : ℝ) + 2)) * (3 * mx + 10) := by
    have h52 : cL * ell^2 * (2 - (-1/2)) = (5/2) * cL * ell^2 := by norm_num; ring
    calc (∫ x : ℝ in (-1/2)..2, ‖logDeriv Λ ((x : ℂ) + (T' : ℂ) * Complex.I)‖)
        ≤ ∫ x : ℝ in (-1/2)..2, (cL * ell^2 + ∑ u ∈ Z, ((d0 u : ℤ) : ℝ) *
            (‖((x : ℂ) + (T' : ℂ) * Complex.I) - u‖)⁻¹) := hcalc
      _ = cL * ell^2 * (2 - (-1/2)) + ∑ u ∈ Z, ((d0 u : ℤ) : ℝ) *
            (∫ x : ℝ in (-1/2)..2, (‖((x : ℂ) + (T' : ℂ) * Complex.I) - u‖)⁻¹) := hGval
      _ ≤ cL * ell^2 * (2 - (-1/2)) + ∑ u ∈ Z, ((d0 u : ℤ) : ℝ) * (3 * mx + 10) :=
            add_le_add (le_refl _) hper'
      _ = (5/2) * cL * ell^2 + (∑ u ∈ Z, ((d0 u : ℤ) : ℝ)) * (3 * mx + 10) := by
            rw [h52, Finset.sum_mul]
      _ ≤ (5/2) * cL * ell^2 +
            (cW * (Real.log (T' + 3) + Real.log (N : ℝ) + 2)) * (3 * mx + 10) := by
            have h3 : 0 ≤ 3 * mx + 10 := by linarith
            exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hsumZ h3)
  have hconst : (5/2) * cL * ell^2 +
        (cW * (Real.log (T' + 3) + Real.log (N : ℝ) + 2)) * (3 * mx + 10)
      ≤ (63 * cL + 52 * cW) * L * (L + mx) := by
    have hb1 : Real.log (T' + 3) + Real.log (N : ℝ) + 2 ≤ 4 * L := by
      have h1 : Real.log (T' + 3) ≤ L := by rw [hLval]; linarith
      have h2 : Real.log (N : ℝ) ≤ L := by rw [hLval]; linarith
      have h3 : (2:ℝ) ≤ 2 * L := by linarith
      linarith
    have hK0 : 0 ≤ 3 * mx + 10 := by linarith
    have hA : L ^ 2 ≤ L * (L + mx) := by nlinarith only [mul_nonneg hL0 hmx0]
    have hA' : L * mx ≤ L * (L + mx) := by nlinarith only [mul_nonneg hL0 hL0]
    have hB : L ≤ L * (L + mx) := by
      nlinarith only [mul_nonneg hL0 hmx0, mul_nonneg hL0 (sub_nonneg.mpr hLge1)]
    have e1 : (5/2) * cL * ell^2 ≤ 62.5 * cL * (L * (L + mx)) := by
      have hC : ell ^ 2 ≤ 25 * (L * (L + mx)) := by nlinarith only [hell2_le, hA]
      nlinarith only [mul_le_mul_of_nonneg_left hC hcL0]
    have e2 : (cW * (Real.log (T' + 3) + Real.log (N : ℝ) + 2)) * (3 * mx + 10)
        ≤ 52 * cW * (L * (L + mx)) := by
      have h1 : cW * (Real.log (T' + 3) + Real.log (N : ℝ) + 2) ≤ 4 * cW * L := by
        nlinarith only [mul_le_mul_of_nonneg_left hb1 hcW0]
      have h2 : (cW * (Real.log (T' + 3) + Real.log (N : ℝ) + 2)) * (3 * mx + 10)
          ≤ (4 * cW * L) * (3 * mx + 10) := mul_le_mul_of_nonneg_right h1 hK0
      nlinarith only [h2, mul_le_mul_of_nonneg_left hA' hcW0, mul_le_mul_of_nonneg_left hB hcW0]
    have e3 : (5/2) * cL * ell^2 +
          (cW * (Real.log (T' + 3) + Real.log (N : ℝ) + 2)) * (3 * mx + 10)
        ≤ 62.5 * cL * (L * (L + mx)) + 52 * cW * (L * (L + mx)) := add_le_add e1 e2
    have e4 : 62.5 * cL * (L * (L + mx)) + 52 * cW * (L * (L + mx))
        = (62.5 * cL + 52 * cW) * (L * (L + mx)) := by ring
    have e5 : (62.5 * cL + 52 * cW) * (L * (L + mx)) ≤ (63 * cL + 52 * cW) * (L * (L + mx)) := by
      have h6 : 0 ≤ L * (L + mx) := mul_nonneg hL0 (by linarith)
      nlinarith only [mul_nonneg hcL0 h6]
    have e6 : (63 * cL + 52 * cW) * (L * (L + mx)) = (63 * cL + 52 * cW) * L * (L + mx) := by ring
    linarith [e3, e4, e5, e6]
  have hfinal : (∫ x : ℝ in (-1/2)..2, ‖logDeriv Λ ((x : ℂ) + (T' : ℂ) * Complex.I)‖)
      ≤ (63 * cL + 52 * cW + 1) * L * (L + mx) := by
    refine le_trans htotal (le_trans hconst ?_)
    have h6 : 0 ≤ L * (L + mx) := mul_nonneg hL0 (by linarith)
    nlinarith only [h6]
  simpa only [hLdef, hmxdef, hΛdef] using hfinal

end Commons.NumberTheory.DirichletCharacter
