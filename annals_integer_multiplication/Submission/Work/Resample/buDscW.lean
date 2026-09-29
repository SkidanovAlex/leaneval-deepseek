import Mathlib
import Submission.Work.Resample.buDefs
import Submission.Work.Resample.buDscKey
import Submission.Work.Resample.buDscTdiv
import Submission.Work.Resample.buDscDiag
import Submission.Work.Resample.buFixed

namespace Work.Resample

theorem buDscW (RM : HvdH.ResMath1DProp) (p α s t : ℕ) (hα : 2 ≤ α) (hp : 100 ≤ p)
    (hD : ∀ ℓ : Fin s, ‖HvdH.diagD' s t α ℓ ℓ‖ ≤ 7 / 8)
    (Wd : ℤ → ℤ) (ε : ℝ) (hε0 : 0 ≤ ε) (hε2 : ε ≤ 2)
    (hWd : ∀ ℓ : Fin s, |(Wd (ℓ : ℤ) : ℝ) / (2 : ℝ) ^ p - (HvdH.diagD' s t α ℓ ℓ).re|
      ≤ ε / (2 : ℝ) ^ p)
    (X : Fin s → ℤ × ℤ) (hX : ∀ ℓ, HvdH.inDisc p (X ℓ))
    (B : ℝ) (hB : ∀ ℓ, ‖HvdH.fxC p (X ℓ)‖ ≤ B)
    (y : Fin s → ℂ) (e : ℝ) (he : ∀ ℓ, (2 : ℝ) ^ p * ‖HvdH.fxC p (X ℓ) - y ℓ‖ ≤ e) :
    (∀ ℓ, HvdH.inDisc p (Work.Resample.buDsc Wd p s X ℓ)) ∧
    (∀ ℓ, (2 : ℝ) ^ p * ‖HvdH.fxC p (Work.Resample.buDsc Wd p s X ℓ)
        - (HvdH.diagD' s t α).mulVec y ℓ‖ ≤ 2 + e + ε * B) := by
  have h2p_pos : (0 : ℝ) < (2 : ℝ) ^ p := by positivity
  have h2p_ne : ((2 : ℝ) ^ p) ≠ 0 := ne_of_gt h2p_pos
  have h2p_int : ((2 : ℤ) ^ p).natAbs = 2 ^ p := by
    rw [Int.natAbs_pow]; rfl
  have hq_ne : ((2 : ℤ) ^ p) ≠ 0 := by positivity
  -- ### The tabulated weight is bounded by `2^p`
  have hWabs : ∀ ℓ : Fin s, |(Wd (ℓ : ℤ) : ℝ)| ≤ (2 : ℝ) ^ p := by
    intro ℓ
    have hDℓ : |(HvdH.diagD' s t α ℓ ℓ).re| ≤ 7 / 8 :=
      le_trans (Complex.abs_re_le_norm _) (hD ℓ)
    have hstep : |(Wd (ℓ : ℤ) : ℝ) / (2 : ℝ) ^ p| ≤ 7 / 8 + 2 / (2 : ℝ) ^ p := by
      have h1 : |(Wd (ℓ : ℤ) : ℝ) / (2 : ℝ) ^ p|
          ≤ |(Wd (ℓ : ℤ) : ℝ) / (2 : ℝ) ^ p - (HvdH.diagD' s t α ℓ ℓ).re|
            + |(HvdH.diagD' s t α ℓ ℓ).re| := by
        have heq : (Wd (ℓ : ℤ) : ℝ) / (2 : ℝ) ^ p
            = ((Wd (ℓ : ℤ) : ℝ) / (2 : ℝ) ^ p - (HvdH.diagD' s t α ℓ ℓ).re)
              + (HvdH.diagD' s t α ℓ ℓ).re := by ring
        conv_lhs => rw [heq]
        exact abs_add_le _ _
      have h2 : ε / (2 : ℝ) ^ p ≤ 2 / (2 : ℝ) ^ p :=
        div_le_div_of_nonneg_right hε2 h2p_pos.le
      linarith [hWd ℓ, h2]
    have h16 : (16 : ℝ) ≤ (2 : ℝ) ^ p := by
      have hpow : (2 : ℝ) ^ 4 ≤ (2 : ℝ) ^ p :=
        pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 4 ≤ p)
      have h4 : (2 : ℝ) ^ 4 = (16 : ℝ) := by norm_num
      linarith
    have hfin : (2 : ℝ) ^ p * (7 / 8 + 2 / (2 : ℝ) ^ p) = (2 : ℝ) ^ p * (7 / 8) + 2 := by
      field_simp
    calc |(Wd (ℓ : ℤ) : ℝ)|
        = |(2 : ℝ) ^ p * ((Wd (ℓ : ℤ) : ℝ) / (2 : ℝ) ^ p)| := by
          rw [mul_div_cancel₀ _ h2p_ne]
      _ = (2 : ℝ) ^ p * |(Wd (ℓ : ℤ) : ℝ) / (2 : ℝ) ^ p| := by
          rw [abs_mul, abs_of_nonneg h2p_pos.le]
      _ ≤ (2 : ℝ) ^ p * (7 / 8 + 2 / (2 : ℝ) ^ p) :=
          mul_le_mul_of_nonneg_left hstep h2p_pos.le
      _ = (2 : ℝ) ^ p * (7 / 8) + 2 := hfin
      _ ≤ (2 : ℝ) ^ p := by linarith
  -- ### Integer form of the weight bound
  have hWnat : ∀ ℓ : Fin s, (Wd (ℓ : ℤ)).natAbs ≤ 2 ^ p := by
    intro ℓ
    have h1 : (((Wd (ℓ : ℤ)).natAbs : ℤ) : ℝ) = |((Wd (ℓ : ℤ)) : ℝ)| := by
      rw [Int.natCast_natAbs, Int.cast_abs]
    have h2 : ((Wd (ℓ : ℤ)).natAbs : ℝ) ≤ ((2 : ℕ) ^ p : ℝ) := by
      have h3 := hWabs ℓ
      rw [← h1] at h3
      exact_mod_cast h3
    exact_mod_cast h2
  -- ### Truncated division does not increase `natAbs` when the numerator is scaled by `|W| ≤ q`
  have hTdiv : ∀ ℓ : Fin s, (Int.tdiv (Wd (ℓ : ℤ) * (X ℓ).1) ((2 : ℤ) ^ p)).natAbs
      ≤ (X ℓ).1.natAbs := by
    intro ℓ
    rw [Int.natAbs_tdiv, Int.natAbs_mul, h2p_int]
    have hqpos : 0 < 2 ^ p := by positivity
    calc (Wd (ℓ : ℤ)).natAbs * (X ℓ).1.natAbs / 2 ^ p
        ≤ (2 ^ p) * (X ℓ).1.natAbs / 2 ^ p :=
          Nat.div_le_div_right (Nat.mul_le_mul_right _ (hWnat ℓ))
      _ = (X ℓ).1.natAbs := Nat.mul_div_cancel_left _ hqpos
  have hTdiv2 : ∀ ℓ : Fin s, (Int.tdiv (Wd (ℓ : ℤ) * (X ℓ).2) ((2 : ℤ) ^ p)).natAbs
      ≤ (X ℓ).2.natAbs := by
    intro ℓ
    rw [Int.natAbs_tdiv, Int.natAbs_mul, h2p_int]
    have hqpos : 0 < 2 ^ p := by positivity
    calc (Wd (ℓ : ℤ)).natAbs * (X ℓ).2.natAbs / 2 ^ p
        ≤ (2 ^ p) * (X ℓ).2.natAbs / 2 ^ p :=
          Nat.div_le_div_right (Nat.mul_le_mul_right _ (hWnat ℓ))
      _ = (X ℓ).2.natAbs := Nat.mul_div_cancel_left _ hqpos
  -- ### The weight rounding error in `2^p`-scaled units
  have hWclose : ∀ ℓ : Fin s,
      |((Wd (ℓ : ℤ) : ℝ) - (2 : ℝ) ^ p * (HvdH.diagD' s t α ℓ ℓ).re)| ≤ ε := by
    intro ℓ
    have h1 : (Wd (ℓ : ℤ) : ℝ) - (2 : ℝ) ^ p * (HvdH.diagD' s t α ℓ ℓ).re
        = (2 : ℝ) ^ p * ((Wd (ℓ : ℤ) : ℝ) / (2 : ℝ) ^ p
            - (HvdH.diagD' s t α ℓ ℓ).re) := by
      field_simp
    rw [h1, abs_mul, abs_of_nonneg h2p_pos.le]
    calc (2 : ℝ) ^ p * |(Wd (ℓ : ℤ) : ℝ) / (2 : ℝ) ^ p - (HvdH.diagD' s t α ℓ ℓ).re|
        ≤ (2 : ℝ) ^ p * (ε / (2 : ℝ) ^ p) :=
          mul_le_mul_of_nonneg_left (hWd ℓ) h2p_pos.le
      _ = ε := by field_simp
  constructor
  · -- ### Membership in the disc `C̃◦`
    intro ℓ
    have hfour : (4 : ℤ) ^ p = ((2 : ℤ) ^ p) ^ 2 := by
      rw [show (4 : ℤ) = 2 * 2 by norm_num, mul_pow]
      ring
    have h1 : (Int.tdiv (Wd (ℓ : ℤ) * (X ℓ).1) ((2 : ℤ) ^ p)) ^ 2 ≤ ((X ℓ).1) ^ 2 := by
      have := (Int.natAbs_le_iff_mul_self_le).mp (hTdiv ℓ)
      simpa [pow_two] using this
    have h2 : (Int.tdiv (Wd (ℓ : ℤ) * (X ℓ).2) ((2 : ℤ) ^ p)) ^ 2 ≤ ((X ℓ).2) ^ 2 := by
      have := (Int.natAbs_le_iff_mul_self_le).mp (hTdiv2 ℓ)
      simpa [pow_two] using this
    have hXℓ : (X ℓ).1 ^ 2 + (X ℓ).2 ^ 2 ≤ ((2 : ℤ) ^ p) ^ 2 := by
      have := hX ℓ
      simp only [HvdH.inDisc] at this
      rwa [hfour] at this
    show (Int.tdiv (Wd (ℓ : ℤ) * (X ℓ).1) ((2 : ℤ) ^ p)) ^ 2
        + (Int.tdiv (Wd (ℓ : ℤ) * (X ℓ).2) ((2 : ℤ) ^ p)) ^ 2 ≤ 4 ^ p
    rw [hfour]
    linarith
  · -- ### The `2^p`-scaled error of the scaled output
    intro ℓ
    have hDℓ : |(HvdH.diagD' s t α ℓ ℓ).re| ≤ 1 := by
      have h1 := Complex.abs_re_le_norm (HvdH.diagD' s t α ℓ ℓ)
      have h2 := hD ℓ
      linarith
    set S1 : ℂ := (((Int.tdiv (Wd (ℓ : ℤ) * (X ℓ).1) ((2 : ℤ) ^ p) : ℤ) : ℂ)
        + ((Int.tdiv (Wd (ℓ : ℤ) * (X ℓ).2) ((2 : ℤ) ^ p) : ℤ) : ℂ) * Complex.I)
        - (Wd (ℓ : ℤ) : ℂ) * (((X ℓ).1 : ℂ) + ((X ℓ).2 : ℂ) * Complex.I)
          / ((2 : ℂ) ^ p) with hS1
    set S2 : ℂ := ((Wd (ℓ : ℤ) : ℂ)
        - ((((2 : ℝ) ^ p) * (HvdH.diagD' s t α ℓ ℓ).re : ℝ) : ℂ)) * HvdH.fxC p (X ℓ) with hS2
    set S3 : ℂ := ((((2 : ℝ) ^ p) * (HvdH.diagD' s t α ℓ ℓ).re : ℝ) : ℂ)
        * (HvdH.fxC p (X ℓ) - y ℓ) with hS3
    have hkey : (((2 : ℝ) ^ p : ℝ) : ℂ) *
        (HvdH.fxC p (Work.Resample.buDsc Wd p s X ℓ)
          - (((HvdH.diagD' s t α ℓ ℓ).re : ℝ) : ℂ) * y ℓ)
        = S1 + S2 + S3 := by
      simp only [Work.Resample.buDsc]
      rw [hS1, hS2, hS3]
      exact buDscKey p (Wd (ℓ : ℤ)) (X ℓ) ((HvdH.diagD' s t α ℓ ℓ).re) (y ℓ)
    have hb1 : ‖S1‖ ≤ 2 := by
      rw [hS1]
      exact buDscTdiv (Wd (ℓ : ℤ)) (X ℓ) p
    have hb2 : ‖S2‖ ≤ ε * B := by
      rw [hS2, norm_mul]
      have hcast : ((Wd (ℓ : ℤ) : ℂ)
          - ((((2 : ℝ) ^ p) * (HvdH.diagD' s t α ℓ ℓ).re : ℝ) : ℂ))
          = ((((Wd (ℓ : ℤ) : ℝ) - (2 : ℝ) ^ p * (HvdH.diagD' s t α ℓ ℓ).re) : ℝ) : ℂ) := by
        push_cast; ring
      rw [hcast, Complex.norm_real, Real.norm_eq_abs]
      calc |((Wd (ℓ : ℤ) : ℝ) - (2 : ℝ) ^ p * (HvdH.diagD' s t α ℓ ℓ).re)|
            * ‖HvdH.fxC p (X ℓ)‖
          ≤ ε * ‖HvdH.fxC p (X ℓ)‖ :=
            mul_le_mul_of_nonneg_right (hWclose ℓ) (norm_nonneg _)
        _ ≤ ε * B := mul_le_mul_of_nonneg_left (hB ℓ) hε0
    have hb3 : ‖S3‖ ≤ e := by
      rw [hS3, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have habs : |(2 : ℝ) ^ p * (HvdH.diagD' s t α ℓ ℓ).re| ≤ (2 : ℝ) ^ p := by
        rw [abs_mul, abs_of_nonneg h2p_pos.le]
        exact mul_le_of_le_one_right h2p_pos.le hDℓ
      calc |(2 : ℝ) ^ p * (HvdH.diagD' s t α ℓ ℓ).re| * ‖HvdH.fxC p (X ℓ) - y ℓ‖
          ≤ (2 : ℝ) ^ p * ‖HvdH.fxC p (X ℓ) - y ℓ‖ :=
            mul_le_mul_of_nonneg_right habs (norm_nonneg _)
        _ ≤ e := he ℓ
    have hsum : ‖S1 + S2 + S3‖ ≤ 2 + ε * B + e := by
      have h1 := norm_add_le S1 S2
      have h2 := norm_add_le (S1 + S2) S3
      linarith only [h1, h2, hb1, hb2, hb3]
    calc (2 : ℝ) ^ p * ‖HvdH.fxC p (Work.Resample.buDsc Wd p s X ℓ)
          - (HvdH.diagD' s t α).mulVec y ℓ‖
        = (2 : ℝ) ^ p * ‖HvdH.fxC p (Work.Resample.buDsc Wd p s X ℓ)
            - (((HvdH.diagD' s t α ℓ ℓ).re : ℝ) : ℂ) * y ℓ‖ := by
          rw [buDscDiag s t α y ℓ]
      _ = ‖(((2 : ℝ) ^ p : ℝ) : ℂ) * (HvdH.fxC p (Work.Resample.buDsc Wd p s X ℓ)
            - (((HvdH.diagD' s t α ℓ ℓ).re : ℝ) : ℂ) * y ℓ)‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h2p_pos.le]
      _ = ‖S1 + S2 + S3‖ := by rw [hkey]
      _ ≤ 2 + ε * B + e := hsum
      _ = 2 + e + ε * B := by ring

end Work.Resample
