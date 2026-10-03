import Mathlib

namespace Work.Horn.FatouQ

/-- The Taylor remainder of `(1 + v)^q` up to order `2`: for `‖v‖ ≤ 1` the
expression `(1+v)^q - 1 - q v - (q(q-1)/2) v²` is bounded by a constant times
`‖v‖³`.  This is proved by induction on `q` using
`R(q+1,v) = (1+v) R(q,v) + (q(q-1)/2) v³`. -/
lemma taylor_remainder (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℂ, ‖v‖ ≤ 1 →
      ‖(1 + v)^q - 1 - (q:ℂ)*v - ((q:ℂ)*((q:ℂ)-1)/2)*v^2‖ ≤ C * ‖v‖^3 := by
  induction q with
  | zero =>
      refine ⟨0, le_refl 0, ?_⟩
      intro v _
      simp
  | succ n ih =>
      obtain ⟨C, hC, hbound⟩ := ih
      refine ⟨2*C + ‖(n:ℂ)*((n:ℂ)-1)/2‖, ?_, ?_⟩
      · positivity
      · intro v hv
        have hrec : (1 + v)^(n+1) - 1 - ((n+1:ℕ):ℂ)*v
              - (((n+1:ℕ):ℂ)*(((n+1:ℕ):ℂ)-1)/2)*v^2
            = (1+v) * ((1+v)^n - 1 - (n:ℂ)*v - ((n:ℂ)*((n:ℂ)-1)/2)*v^2)
              + ((n:ℂ)*((n:ℂ)-1)/2)*v^3 := by
          rw [pow_succ]
          push_cast
          ring
        rw [hrec]
        have h1v : ‖(1:ℂ) + v‖ ≤ 2 := by
          calc ‖(1:ℂ) + v‖ ≤ ‖(1:ℂ)‖ + ‖v‖ := norm_add_le _ _
            _ = 1 + ‖v‖ := by simp
            _ ≤ 2 := by linarith
        calc ‖(1+v) * ((1+v)^n - 1 - (n:ℂ)*v - ((n:ℂ)*((n:ℂ)-1)/2)*v^2)
                + ((n:ℂ)*((n:ℂ)-1)/2)*v^3‖
            ≤ ‖(1+v) * ((1+v)^n - 1 - (n:ℂ)*v - ((n:ℂ)*((n:ℂ)-1)/2)*v^2)‖
                + ‖((n:ℂ)*((n:ℂ)-1)/2)*v^3‖ := norm_add_le _ _
          _ = ‖(1:ℂ)+v‖ * ‖(1+v)^n - 1 - (n:ℂ)*v - ((n:ℂ)*((n:ℂ)-1)/2)*v^2‖
                + ‖(n:ℂ)*((n:ℂ)-1)/2‖ * ‖v‖^3 := by
                rw [norm_mul, norm_mul, norm_pow]
          _ ≤ 2 * (C * ‖v‖^3) + ‖(n:ℂ)*((n:ℂ)-1)/2‖ * ‖v‖^3 := by
                apply add_le_add
                · exact mul_le_mul h1v (hbound v hv) (norm_nonneg _) (by norm_num)
                · exact le_refl _
          _ = (2*C + ‖(n:ℂ)*((n:ℂ)-1)/2‖) * ‖v‖^3 := by ring

theorem inv_pow_sub_quadratic (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℂ, ‖t‖ ≤ 1 / 2 →
      ‖(1 + t)⁻¹ ^ q - 1 + (q : ℂ) * t - ((q : ℂ) * ((q : ℂ) + 1) / 2) * t ^ 2‖ ≤
        C * ‖t‖ ^ 3 := by
  obtain ⟨C, hC, hbound⟩ := taylor_remainder q
  refine ⟨8*C + 2*(q:ℝ) + 6*‖(q:ℂ)*((q:ℂ)-1)/2‖, ?_, ?_⟩
  · have := hC; positivity
  · intro t ht
    -- the substitution `v = -t/(1+t)`, so that `(1+t)⁻¹ = 1 + v`
    set v : ℂ := -(t * ((1:ℂ) + t)⁻¹) with hvdef
    have hlow : (1:ℝ)/2 ≤ ‖(1:ℂ) + t‖ := by
      have h := norm_add_le ((1:ℂ) + t) (-t)
      have h2 : ((1:ℂ) + t) + (-t) = 1 := by ring
      rw [h2, norm_one, norm_neg] at h
      linarith
    have hne : (1:ℂ) + t ≠ 0 := by
      intro h
      have : ‖(1:ℂ) + t‖ = 0 := by rw [h, norm_zero]
      linarith
    have hinv : ‖((1:ℂ) + t)⁻¹‖ ≤ 2 := by
      rw [norm_inv, inv_le_iff_one_le_mul₀ (by linarith : (0:ℝ) < ‖(1:ℂ)+t‖)]
      linarith
    have hvnorm : ‖v‖ ≤ 2 * ‖t‖ := by
      rw [hvdef]
      simp only [norm_neg, norm_mul]
      calc ‖t‖ * ‖((1:ℂ) + t)⁻¹‖ ≤ ‖t‖ * 2 :=
              mul_le_mul_of_nonneg_left hinv (norm_nonneg t)
        _ = 2 * ‖t‖ := by ring
    have hv1 : (1:ℂ) + v = ((1:ℂ) + t)⁻¹ := by
      rw [hvdef]; field_simp; ring
    have hv2 : v + t - t^2 = -(t^3 * ((1:ℂ)+t)⁻¹) := by
      rw [hvdef]; field_simp; ring
    have hv3 : v + t = t^2 * ((1:ℂ)+t)⁻¹ := by
      rw [hvdef]; field_simp; ring
    have hv4 : v - t = -(2*t) + t^2 * ((1:ℂ)+t)⁻¹ := by
      rw [hvdef]; field_simp; ring
    -- `v + t - t² = -t³/(1+t)` is of size `2‖t‖³`
    have hb1 : ‖v + t - t^2‖ ≤ 2 * ‖t‖^3 := by
      rw [hv2, norm_neg, norm_mul, norm_pow]
      calc ‖t‖^3 * ‖((1:ℂ) + t)⁻¹‖ ≤ ‖t‖^3 * 2 :=
              mul_le_mul_of_nonneg_left hinv (by positivity)
        _ = 2 * ‖t‖^3 := by ring
    -- `v² - t² = (v+t)(v-t)` is of size `6‖t‖³`
    have hb2 : ‖v^2 - t^2‖ ≤ 6 * ‖t‖^3 := by
      have hfac : v^2 - t^2 = (v+t)*(v-t) := by ring
      rw [hfac, norm_mul]
      have h2a : ‖v + t‖ ≤ 2 * ‖t‖^2 := by
        rw [hv3, norm_mul, norm_pow]
        calc ‖t‖^2 * ‖((1:ℂ) + t)⁻¹‖ ≤ ‖t‖^2 * 2 :=
                mul_le_mul_of_nonneg_left hinv (by positivity)
          _ = 2 * ‖t‖^2 := by ring
      have h2b : ‖v - t‖ ≤ 3 * ‖t‖ := by
        rw [hv4]
        calc ‖-(2*t) + t^2 * ((1:ℂ)+t)⁻¹‖
              ≤ ‖-(2*t)‖ + ‖t^2*((1:ℂ)+t)⁻¹‖ := norm_add_le _ _
          _ = 2 * ‖t‖ + ‖t‖^2 * ‖((1:ℂ)+t)⁻¹‖ := by
                congr 1
                · rw [norm_neg, norm_mul, Complex.norm_ofNat]
                · rw [norm_mul, norm_pow]
          _ ≤ 2 * ‖t‖ + ‖t‖^2 * 2 := by
                exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hinv (by positivity))
          _ ≤ 3 * ‖t‖ := by nlinarith [norm_nonneg t, ht]
      calc ‖v+t‖*‖v-t‖ ≤ (2*‖t‖^2) * (3*‖t‖) :=
              mul_le_mul h2a h2b (norm_nonneg _) (by positivity)
        _ = 6 * ‖t‖^3 := by ring
    -- the exact decomposition of the expression into three pieces
    have hkey : ((1:ℂ)+t)⁻¹ ^ q - 1 + (q:ℂ)*t - ((q:ℂ)*((q:ℂ)+1)/2)*t^2
        = ((1+v)^q - 1 - (q:ℂ)*v - ((q:ℂ)*((q:ℂ)-1)/2)*v^2)
          + (q:ℂ)*(v + t - t^2) + ((q:ℂ)*((q:ℂ)-1)/2)*(v^2 - t^2) := by
      rw [← hv1]
      ring
    rw [hkey]
    have hE : ‖(1+v)^q - 1 - (q:ℂ)*v - ((q:ℂ)*((q:ℂ)-1)/2)*v^2‖ ≤ C * ‖v‖^3 :=
      hbound v (by linarith [hvnorm, ht])
    have hv3le : ‖v‖^3 ≤ 8 * ‖t‖^3 := by
      have h : ‖v‖^3 ≤ (2*‖t‖)^3 := pow_le_pow_left₀ (norm_nonneg v) hvnorm 3
      nlinarith [h]
    have hq : ‖(q:ℂ)*(v + t - t^2)‖ ≤ (q:ℝ) * (2 * ‖t‖^3) := by
      rw [norm_mul, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left hb1 (by positivity)
    have hcc : ‖((q:ℂ)*((q:ℂ)-1)/2)*(v^2 - t^2)‖
        ≤ ‖(q:ℂ)*((q:ℂ)-1)/2‖ * (6 * ‖t‖^3) := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hb2 (norm_nonneg _)
    have hmain : ‖((1+v)^q - 1 - (q:ℂ)*v - ((q:ℂ)*((q:ℂ)-1)/2)*v^2)
          + (q:ℂ)*(v + t - t^2) + ((q:ℂ)*((q:ℂ)-1)/2)*(v^2 - t^2)‖
        ≤ C*‖v‖^3 + (q:ℝ)*(2*‖t‖^3) + ‖(q:ℂ)*((q:ℂ)-1)/2‖*(6*‖t‖^3) := by
      have ha := norm_add_le
        ((1+v)^q - 1 - (q:ℂ)*v - ((q:ℂ)*((q:ℂ)-1)/2)*v^2 + (q:ℂ)*(v + t - t^2))
        (((q:ℂ)*((q:ℂ)-1)/2)*(v^2 - t^2))
      have hb := norm_add_le
        ((1+v)^q - 1 - (q:ℂ)*v - ((q:ℂ)*((q:ℂ)-1)/2)*v^2)
        ((q:ℂ)*(v + t - t^2))
      linarith
    calc ‖((1+v)^q - 1 - (q:ℂ)*v - ((q:ℂ)*((q:ℂ)-1)/2)*v^2)
          + (q:ℂ)*(v + t - t^2) + ((q:ℂ)*((q:ℂ)-1)/2)*(v^2 - t^2)‖
        ≤ C*‖v‖^3 + (q:ℝ)*(2*‖t‖^3) + ‖(q:ℂ)*((q:ℂ)-1)/2‖*(6*‖t‖^3) := hmain
      _ ≤ C*(8*‖t‖^3) + (q:ℝ)*(2*‖t‖^3) + ‖(q:ℂ)*((q:ℂ)-1)/2‖*(6*‖t‖^3) := by
            have hm : C * ‖v‖^3 ≤ C * (8 * ‖t‖^3) := mul_le_mul_of_nonneg_left hv3le hC
            linarith
      _ = (8*C + 2*(q:ℝ) + 6*‖(q:ℂ)*((q:ℂ)-1)/2‖) * ‖t‖^3 := by ring

end Work.Horn.FatouQ
