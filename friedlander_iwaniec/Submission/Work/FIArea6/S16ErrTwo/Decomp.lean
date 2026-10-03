import Mathlib
import Submission.Work.FIArea6.S16ErrTwo.Defs
import Submission.Work.FIArea6.S16ErrTwo.Pointwise

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.FIArea6.S16ErrTwo

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The three "low" summands of the §16 error (diagonal, near-diagonal, non-coprime) at a fixed
pair `(z1,z2)`. -/
def lowT (Pa : Work.FITop.Params) (X d : ℕ) (β : GaussianInt → ℂ) (z1 z2 : GaussianInt) : ℝ :=
  (if Work.FIPlan.Delta z1 z2 = 0 then ‖β z1‖ * ‖β z2‖ else 0)
    + (if 0 < Work.FIPlan.absDelta z1 z2 ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2
        ∧ ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ≤ Mthr Pa X
      then ‖β z1‖ * ‖β z2‖ else 0)
    + (if ¬ Work.FIPlan.GaussCoprime z1 z2 ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2
      then ‖β z1‖ * ‖β z2‖ else 0)

/-- The far summand at a fixed pair. -/
def farT (Pa : Work.FITop.Params) (X d : ℕ) (β : GaussianInt → ℂ) (z1 z2 : GaussianInt) : ℝ :=
  if Work.FIPlan.GaussCoprime z1 z2 ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2
      ∧ Mthr Pa X < ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
    then ‖β z1‖ * ‖β z2‖
      * (8 * Pa.N / ((Kcut X : ℝ) * ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)))
    else 0

lemma ifterm_nonneg (c : Prop) [Decidable c] {w : ℝ} (hw : 0 ≤ w) :
    0 ≤ (if c then w else 0) := by
  split_ifs
  · exact hw
  · exact le_refl 0

/-- The diagonal, near and non-coprime cases together dominate the full weight. -/
lemma lowT_ge {Pa : Work.FITop.Params} {X d : ℕ} {β : GaussianInt → ℂ} {z1 z2 : GaussianInt}
    (h : Work.FIPlan.Delta z1 z2 = 0 ∨
      (0 < Work.FIPlan.absDelta z1 z2 ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2
        ∧ ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ≤ Mthr Pa X) ∨
      (¬ Work.FIPlan.GaussCoprime z1 z2 ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2)) :
    ‖β z1‖ * ‖β z2‖ ≤ lowT Pa X d β z1 z2 := by
  have hw : 0 ≤ ‖β z1‖ * ‖β z2‖ := by positivity
  have hnn1 := ifterm_nonneg (c := (0 < Work.FIPlan.absDelta z1 z2 ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2
      ∧ ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ≤ Mthr Pa X)) hw
  have hnn2 := ifterm_nonneg (c := (Work.FIPlan.Delta z1 z2 = 0)) hw
  have hnn3 := ifterm_nonneg (c := (¬ Work.FIPlan.GaussCoprime z1 z2
      ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2)) hw
  rcases h with h | h | h
  · have h1 : (if Work.FIPlan.Delta z1 z2 = 0 then ‖β z1‖ * ‖β z2‖ else 0)
        = ‖β z1‖ * ‖β z2‖ := if_pos h
    simp only [lowT, h1]; linarith
  · obtain ⟨h1, h2, h3⟩ := h
    have h4 : (if 0 < Work.FIPlan.absDelta z1 z2 ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2
        ∧ ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ≤ Mthr Pa X
        then ‖β z1‖ * ‖β z2‖ else 0) = ‖β z1‖ * ‖β z2‖ := if_pos ⟨h1, h2, h3⟩
    simp only [lowT, h4]; linarith
  · obtain ⟨h1, h2⟩ := h
    have h4 : (if ¬ Work.FIPlan.GaussCoprime z1 z2 ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2
        then ‖β z1‖ * ‖β z2‖ else 0) = ‖β z1‖ * ‖β z2‖ := if_pos ⟨h1, h2⟩
    simp only [lowT, h4]; linarith

/-- The "low" pointwise error bound. -/
lemma err_low_le {Pa : Work.FITop.Params} {X : ℕ} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) (hX : 1 ≤ X)
    (hXN : (X : ℝ) ≤ Pa.N) {z1 z2 : GaussianInt}
    (hz1 : β z1 ≠ 0) (hz2 : β z2 ≠ 0) :
    ‖((if Work.FIPlan.GaussCoprime z1 z2 then (Work.FITop4.logFac6 z1 z2 : ℂ) else 0)
        - Work.FIArea7.logFac6Series z1 z2 (Kcut X))‖ ≤ Bc Pa := by
  have h1 : ‖(Work.FITop4.logFac6 z1 z2 : ℂ)‖ ≤ Real.log (16 * Pa.N) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact logFac6_abs_le hβ hz1 hz2
  have h2 : ‖Work.FIArea7.logFac6Series z1 z2 (Kcut X)‖ ≤ 8 + 8 * Real.log (2 + X) :=
    series_norm_le X hX z1 z2
  have h4 : ‖(if Work.FIPlan.GaussCoprime z1 z2 then (Work.FITop4.logFac6 z1 z2 : ℂ) else 0)‖
      ≤ Real.log (16 * Pa.N) := by
    split_ifs with hc
    · exact h1
    · simp only [norm_zero]
      exact Real.log_nonneg (by linarith [Pa.hN1])
  have h3 : ‖((if Work.FIPlan.GaussCoprime z1 z2 then (Work.FITop4.logFac6 z1 z2 : ℂ) else 0)
        - Work.FIArea7.logFac6Series z1 z2 (Kcut X))‖
      ≤ ‖(if Work.FIPlan.GaussCoprime z1 z2 then (Work.FITop4.logFac6 z1 z2 : ℂ) else 0)‖
        + ‖Work.FIArea7.logFac6Series z1 z2 (Kcut X)‖ := norm_sub_le _ _
  have h5 : Real.log (16 * Pa.N) ≤ Bc Pa := by
    rw [Bc]
    have h16 : Real.log 16 ≤ 4 := by
      have h2' : Real.log 16 = 4 * Real.log 2 := by
        rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
        norm_num
      have h3' := Real.log_two_lt_d9
      linarith
    have hm : Real.log (16 * Pa.N) = Real.log 16 + Real.log Pa.N :=
      Real.log_mul (by norm_num) (by linarith [Pa.hN1])
    have hN : Real.log Pa.N ≤ Real.log (2 + Pa.N) :=
      Real.log_le_log (by linarith [Pa.hN1]) (by linarith [Pa.hN1])
    have h0 : 0 ≤ Real.log (2 + Pa.N) := Real.log_nonneg (by linarith [Pa.hN1])
    rw [hm]; linarith
  have h6 : 8 + 8 * Real.log (2 + X) ≤ Bc Pa := by
    rw [Bc]
    have hlogX : Real.log (2 + X) ≤ Real.log (2 + Pa.N) :=
      Real.log_le_log (by linarith) (by linarith)
    have h0 : 0 ≤ Real.log (2 + Pa.N) := Real.log_nonneg (by linarith [Pa.hN1])
    linarith
  have h56 : Real.log (16 * Pa.N) + (8 + 8 * Real.log (2 + X)) ≤ Bc Pa := by
    rw [Bc] at h5 h6 ⊢
    have h0 : 0 ≤ Real.log (2 + Pa.N) := Real.log_nonneg (by linarith [Pa.hN1])
    have h16 : Real.log 16 ≤ 4 := by
      have h2' : Real.log 16 = 4 * Real.log 2 := by
        rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
        norm_num
      have h3' := Real.log_two_lt_d9
      linarith
    have hm : Real.log (16 * Pa.N) ≤ 4 + Real.log (2 + Pa.N) := by
      rw [Real.log_mul (by norm_num) (by linarith [Pa.hN1])]
      have hN : Real.log Pa.N ≤ Real.log (2 + Pa.N) :=
        Real.log_le_log (by linarith [Pa.hN1]) (by linarith [Pa.hN1])
      linarith
    have hlogX : Real.log (2 + X) ≤ Real.log (2 + Pa.N) :=
      Real.log_le_log (by linarith) (by linarith)
    linarith
  linarith [h3, h4, h2, h56]

/-- The "low" conclusion: once the pair weight is dominated by `lowT`, the pointwise error by
`Bc Pa` and `farT ≥ 0`, the pair bound follows. -/
lemma low_case_le {Pa : Work.FITop.Params} {X d : ℕ} {β : GaussianInt → ℂ} {z1 z2 : GaussianInt}
    (hBc0 : 0 ≤ Bc Pa) (hfar0 : 0 ≤ farT Pa X d β z1 z2)
    (hlow_ge : ‖β z1‖ * ‖β z2‖ ≤ lowT Pa X d β z1 z2)
    {E : ℂ} (hE_le : ‖E‖ ≤ Bc Pa) :
    ‖β z1‖ * ‖β z2‖ * ‖E‖ ≤ Bc Pa * lowT Pa X d β z1 z2 + farT Pa X d β z1 z2 := by
  have hw : 0 ≤ ‖β z1‖ * ‖β z2‖ := by positivity
  calc ‖β z1‖ * ‖β z2‖ * ‖E‖ ≤ ‖β z1‖ * ‖β z2‖ * Bc Pa :=
        mul_le_mul_of_nonneg_left hE_le hw
    _ ≤ Bc Pa * lowT Pa X d β z1 z2 := by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_left hlow_ge hBc0
    _ ≤ Bc Pa * lowT Pa X d β z1 z2 + farT Pa X d β z1 z2 := le_add_of_nonneg_right hfar0

/-- **The per-pair bound**: the summand of `Vd − MainSum` is bounded by the low summands
(weighted by `Bc Pa`) plus the far summand. -/
lemma pair_le {Pa : Work.FITop.Params} {X d : ℕ} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) (hd : 1 ≤ d) (hdX : d ≤ X)
    (hX : 1 ≤ X) (hPz : 4 * X ≤ Pa.Pz) (hXN : (X : ℝ) ≤ Pa.N) (z1 z2 : GaussianInt) :
    ‖β z1 * star (β z2) * (Work.FITop4.ratioSym z1 z2 d : ℂ) *
        (if 4 * d ∣ Work.FIPlan.absDelta z1 z2 then
          ((if Work.FIPlan.GaussCoprime z1 z2 then (Work.FITop4.logFac6 z1 z2 : ℂ) else 0)
            - Work.FIArea7.logFac6Series z1 z2 (Kcut X)) else 0)‖
      ≤ Bc Pa * lowT Pa X d β z1 z2 + farT Pa X d β z1 z2 := by
  have hBc0 : 0 ≤ Bc Pa := Bc_nonneg Pa
  have hw : 0 ≤ ‖β z1‖ * ‖β z2‖ := by positivity
  have hlow : 0 ≤ lowT Pa X d β z1 z2 := by
    rw [lowT]
    have h1 := ifterm_nonneg (c := (Work.FIPlan.Delta z1 z2 = 0)) hw
    have h2 := ifterm_nonneg (c := (0 < Work.FIPlan.absDelta z1 z2
      ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2
      ∧ ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ≤ Mthr Pa X)) hw
    have h3 := ifterm_nonneg (c := (¬ Work.FIPlan.GaussCoprime z1 z2
      ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2)) hw
    linarith
  have hfar0 : 0 ≤ farT Pa X d β z1 z2 := by
    rw [farT]
    refine ifterm_nonneg _ ?_
    have h1 : (0 : ℝ) ≤ 8 * Pa.N := by
      have : (0 : ℝ) ≤ Pa.N := by linarith [Pa.hN1]
      linarith
    have h2 : (0 : ℝ) ≤ (Kcut X : ℝ) * ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) := by positivity
    exact mul_nonneg hw (div_nonneg h1 h2)
  set E : ℂ := (if 4 * d ∣ Work.FIPlan.absDelta z1 z2 then
      ((if Work.FIPlan.GaussCoprime z1 z2 then (Work.FITop4.logFac6 z1 z2 : ℂ) else 0)
        - Work.FIArea7.logFac6Series z1 z2 (Kcut X)) else 0) with hEdef
  have hstep1 : ‖β z1 * star (β z2) * (Work.FITop4.ratioSym z1 z2 d : ℂ) * E‖
      ≤ ‖β z1‖ * ‖β z2‖ * ‖E‖ := by
    calc ‖β z1 * star (β z2) * (Work.FITop4.ratioSym z1 z2 d : ℂ) * E‖
        = ‖β z1‖ * ‖star (β z2)‖ * ‖(Work.FITop4.ratioSym z1 z2 d : ℂ)‖ * ‖E‖ := by
          rw [norm_mul, norm_mul, norm_mul]
      _ = ‖β z1‖ * ‖β z2‖ * ‖(Work.FITop4.ratioSym z1 z2 d : ℂ)‖ * ‖E‖ := by rw [norm_star]
      _ ≤ ‖β z1‖ * ‖β z2‖ * 1 * ‖E‖ := by
          gcongr
          exact Work.FIArea6.sc_norm_ratioSym_le_one z1 z2 d
      _ = ‖β z1‖ * ‖β z2‖ * ‖E‖ := by ring
  have hRHS : 0 ≤ Bc Pa * lowT Pa X d β z1 z2 + farT Pa X d β z1 z2 :=
    add_nonneg (mul_nonneg hBc0 hlow) hfar0
  refine le_trans hstep1 ?_
  by_cases hdvd : 4 * d ∣ Work.FIPlan.absDelta z1 z2
  · rw [hEdef, if_pos hdvd]
    by_cases hcop : Work.FIPlan.GaussCoprime z1 z2
    · rw [if_pos hcop]
      by_cases hgt : Mthr Pa X < ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
      · -- far case
        have hfar_eq : farT Pa X d β z1 z2
            = ‖β z1‖ * ‖β z2‖
              * (8 * Pa.N / ((Kcut X : ℝ) * ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ))) :=
          if_pos ⟨hcop, hdvd, hgt⟩
        by_cases hz2 : β z2 = 0
        · rw [hz2]; simp only [norm_zero, mul_zero]; linarith
        by_cases hz1 : β z1 = 0
        · rw [hz1]; simp only [norm_zero, zero_mul]; linarith
        have hD0 : Work.FIPlan.absDelta z1 z2 ≠ 0 := by
          intro h0
          rw [h0] at hgt
          simp only [Nat.cast_zero] at hgt
          exact absurd hgt (not_lt.mpr (Mthr_nonneg Pa X))
        have hΔ : Work.FIPlan.Delta z1 z2 ≠ 0 := fun h0 => hD0 (by rw [Work.FIPlan.absDelta, h0]; simp)
        have hfar_le := Work.FIArea6.sc_error_le_far hβ X hX hz1 hz2 hΔ
        rw [hfar_eq] at hRHS ⊢
        have hprod := mul_le_mul_of_nonneg_left hfar_le hw
        have hBclow := mul_nonneg hBc0 hlow
        linarith [hprod, hBclow]
      · -- near or diagonal case
        have hlow_ge : ‖β z1‖ * ‖β z2‖ ≤ lowT Pa X d β z1 z2 := by
          rcases Nat.eq_zero_or_pos (Work.FIPlan.absDelta z1 z2) with h0 | hpos
          · refine lowT_ge (Or.inl ?_)
            rw [Work.FIPlan.absDelta] at h0
            exact Int.natAbs_eq_zero.mp h0
          · exact lowT_ge (Or.inr (Or.inl ⟨hpos, hdvd, not_lt.mp hgt⟩))
        by_cases hz1 : β z1 = 0
        · rw [hz1]; simp only [norm_zero, zero_mul]; linarith [hRHS]
        by_cases hz2 : β z2 = 0
        · rw [hz2]; simp only [norm_zero, mul_zero]; linarith [hRHS]
        have hE_le := err_low_le hβ hX hXN hz1 hz2
        rw [if_pos hcop] at hE_le
        exact low_case_le hBc0 hfar0 hlow_ge hE_le
    · rw [if_neg hcop]
      have hlow_ge : ‖β z1‖ * ‖β z2‖ ≤ lowT Pa X d β z1 z2 :=
        lowT_ge (Or.inr (Or.inr ⟨hcop, hdvd⟩))
      have hE_le : ‖(0 : ℂ) - Work.FIArea7.logFac6Series z1 z2 (Kcut X)‖ ≤ Bc Pa := by
        rw [zero_sub, norm_neg]
        have h2 : ‖Work.FIArea7.logFac6Series z1 z2 (Kcut X)‖ ≤ 8 + 8 * Real.log (2 + X) :=
          series_norm_le X hX z1 z2
        have h6 : 8 + 8 * Real.log (2 + X) ≤ Bc Pa := by
          rw [Bc]
          have hlogX : Real.log (2 + X) ≤ Real.log (2 + Pa.N) :=
            Real.log_le_log (by linarith) (by linarith)
          have h0 : 0 ≤ Real.log (2 + Pa.N) := Real.log_nonneg (by linarith [Pa.hN1])
          linarith
        linarith
      exact low_case_le hBc0 hfar0 hlow_ge hE_le
  · rw [hEdef, if_neg hdvd]
    simp only [norm_zero, mul_zero]
    linarith [hRHS]

/-- **The per-modulus decomposition of the §16 error.** -/
theorem norm_Vd_sub_MainSum_le {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β)
    {X d : ℕ} (hd : 1 ≤ d) (hdX : d ≤ X) (hX : 1 ≤ X) (hPz : 4 * X ≤ Pa.Pz)
    (hXN : (X : ℝ) ≤ Pa.N) :
    ‖Work.FIArea6.Vd Pa d β - Work.FIArea6.MainSum Pa X d β‖
      ≤ Bc Pa * (diagMass Pa β + nearMass Pa X d β + ncMass Pa d β)
        + ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa, farT Pa X d β z1 z2 := by
  rw [Work.FIArea6.sc_Vd_sub_MainSum_eq Pa X d φ z0 β hβ hd hdX hPz]
  refine le_trans (norm_sum_le _ _) ?_
  have hinner : ∀ z1 ∈ Work.FITop.boxN Pa,
      ‖∑ z2 ∈ Work.FITop.boxN Pa,
          (β z1 * star (β z2) * (Work.FITop4.ratioSym z1 z2 d : ℂ) *
            (if 4 * d ∣ Work.FIPlan.absDelta z1 z2 then
              ((if Work.FIPlan.GaussCoprime z1 z2 then (Work.FITop4.logFac6 z1 z2 : ℂ) else 0)
                - Work.FIArea7.logFac6Series z1 z2 (Kcut X)) else 0))‖
        ≤ ∑ z2 ∈ Work.FITop.boxN Pa,
            (Bc Pa * lowT Pa X d β z1 z2 + farT Pa X d β z1 z2) := by
    intro z1 _
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun z2 _ => ?_))
    exact pair_le hβ hd hdX hX hPz hXN z1 z2
  refine le_trans (Finset.sum_le_sum hinner) ?_
  have hsum_lowT : (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
        lowT Pa X d β z1 z2)
      = diagMass Pa β + nearMass Pa X d β + ncMass Pa d β := by
    simp only [lowT, diagMass, nearMass, ncMass, Finset.sum_add_distrib]
  have hsplit1 : (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
        (Bc Pa * lowT Pa X d β z1 z2 + farT Pa X d β z1 z2))
      = (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa, Bc Pa * lowT Pa X d β z1 z2)
        + (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa, farT Pa X d β z1 z2) := by
    simp only [Finset.sum_add_distrib]
  have hsplit2 : (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
        Bc Pa * lowT Pa X d β z1 z2)
      = Bc Pa * (diagMass Pa β + nearMass Pa X d β + ncMass Pa d β) := by
    simp only [← Finset.mul_sum, hsum_lowT]
  rw [hsplit1, hsplit2]

end

end Work.FIArea6.S16ErrTwo
