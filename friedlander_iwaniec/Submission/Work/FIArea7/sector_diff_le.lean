import Mathlib

namespace Work.FIArea7

/-- Norm of a real coercion to `ℂ`. -/
private lemma norm_ofRealC (x : ℝ) : ‖((x : ℝ) : ℂ)‖ = |x| := by simp

/-- Norm of an integer coercion to `ℂ`. -/
private lemma norm_intCastC (n : ℤ) : ‖(((n : ℤ)) : ℂ)‖ = |(n : ℝ)| := by
  rw [← Complex.ofReal_intCast, norm_ofRealC]

/-- Powers of two vectors of norm at most `1` differ by at most `n` times the distance
(geometric series / triangle inequality by induction). -/
private lemma norm_pow_sub_pow_le (u w : ℂ) (hu : ‖u‖ ≤ 1) (hw : ‖w‖ ≤ 1) (n : ℕ) :
    ‖u ^ n - w ^ n‖ ≤ (n : ℝ) * ‖u - w‖ := by
  induction n with
  | zero => simp
  | succ m ih =>
    have hsplit : u ^ (m + 1) - w ^ (m + 1) = u * (u ^ m - w ^ m) + (u - w) * w ^ m := by
      ring
    have hwm : ‖w ^ m‖ ≤ 1 := by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg w) hw
    calc ‖u ^ (m + 1) - w ^ (m + 1)‖
        = ‖u * (u ^ m - w ^ m) + (u - w) * w ^ m‖ := by rw [hsplit]
      _ ≤ ‖u * (u ^ m - w ^ m)‖ + ‖(u - w) * w ^ m‖ := norm_add_le _ _
      _ = ‖u‖ * ‖u ^ m - w ^ m‖ + ‖u - w‖ * ‖w ^ m‖ := by rw [norm_mul, norm_mul]
      _ ≤ 1 * ((m : ℝ) * ‖u - w‖) + ‖u - w‖ * 1 := by
          gcongr
      _ = ((m + 1 : ℕ) : ℝ) * ‖u - w‖ := by push_cast; ring

/-- Inversion is an isometry on the unit circle. -/
private lemma norm_inv_sub_inv_eq (u w : ℂ) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) :
    ‖u⁻¹ - w⁻¹‖ = ‖u - w‖ := by
  have hu0 : u ≠ 0 := by
    intro h; rw [h, norm_zero] at hu; norm_num at hu
  have hw0 : w ≠ 0 := by
    intro h; rw [h, norm_zero] at hw; norm_num at hw
  have hid : u⁻¹ - w⁻¹ = u⁻¹ * (w - u) * w⁻¹ := by field_simp
  rw [hid, norm_mul, norm_mul, norm_inv, norm_inv, hu, hw, inv_one, mul_one, one_mul,
    norm_sub_rev]

/-- `|u^k - w^k| ≤ |k| |u - w|` for `u, w` of norm one and any integer `k`
(the case `k < 0` reduces to `k > 0` by inverting). -/
private lemma norm_zpow_sub_le (u w : ℂ) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (k : ℤ) :
    ‖u ^ k - w ^ k‖ ≤ |(k : ℝ)| * ‖u - w‖ := by
  obtain ⟨n, hn | hn⟩ := Int.eq_nat_or_neg k
  · rw [hn, zpow_natCast, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n)]
    exact norm_pow_sub_pow_le u w (le_of_eq hu) (le_of_eq hw) n
  · rw [hn, Int.cast_neg, Int.cast_natCast, abs_neg, abs_of_nonneg (Nat.cast_nonneg n)]
    have h1 : u ^ (-(n : ℤ)) - w ^ (-(n : ℤ)) = (u⁻¹) ^ n - (w⁻¹) ^ n := by
      rw [zpow_neg, zpow_natCast, inv_pow, zpow_neg, zpow_natCast, inv_pow]
    rw [h1]
    have hu' : ‖u⁻¹‖ ≤ 1 := by rw [norm_inv, hu, inv_one]
    have hw' : ‖w⁻¹‖ ≤ 1 := by rw [norm_inv, hw, inv_one]
    calc ‖(u⁻¹) ^ n - (w⁻¹) ^ n‖ ≤ (n : ℝ) * ‖u⁻¹ - w⁻¹‖ :=
          norm_pow_sub_pow_le _ _ hu' hw' n
      _ = (n : ℝ) * ‖u - w‖ := by rw [norm_inv_sub_inv_eq u w hu hw]

/-- Normalized vectors move at most twice as fast as the vectors themselves:
`|A/|A| - B/|B|| ≤ 2 |A - B| / |A|` for `A ≠ 0 ≠ B`. -/
private lemma norm_div_norm_sub_div_norm_le (A B : ℂ) (hA : A ≠ 0) (hB : B ≠ 0) :
    ‖A / (‖A‖ : ℂ) - B / (‖B‖ : ℂ)‖ ≤ 2 * ‖A - B‖ / ‖A‖ := by
  have hc : (0 : ℝ) < ‖A‖ := norm_pos_iff.mpr hA
  have hd : (0 : ℝ) < ‖B‖ := norm_pos_iff.mpr hB
  have hcC : ((‖A‖ : ℝ) : ℂ) ≠ 0 := by simpa [Complex.ofReal_eq_zero] using ne_of_gt hc
  have hdC : ((‖B‖ : ℝ) : ℂ) ≠ 0 := by simpa [Complex.ofReal_eq_zero] using ne_of_gt hd
  have hdecomp : A * ((‖B‖ : ℝ) : ℂ) - ((‖A‖ : ℝ) : ℂ) * B
      = (A - B) * ((‖B‖ : ℝ) : ℂ) + B * (((‖B‖ : ℝ) : ℂ) - ((‖A‖ : ℝ) : ℂ)) := by
    ring
  have hnum : ‖A * ((‖B‖ : ℝ) : ℂ) - ((‖A‖ : ℝ) : ℂ) * B‖ ≤ 2 * ‖B‖ * ‖A - B‖ := by
    rw [hdecomp]
    calc ‖(A - B) * ((‖B‖ : ℝ) : ℂ) + B * (((‖B‖ : ℝ) : ℂ) - ((‖A‖ : ℝ) : ℂ))‖
        ≤ ‖(A - B) * ((‖B‖ : ℝ) : ℂ)‖ + ‖B * (((‖B‖ : ℝ) : ℂ) - ((‖A‖ : ℝ) : ℂ))‖ :=
          norm_add_le _ _
      _ = ‖A - B‖ * ‖B‖ + ‖B‖ * |‖B‖ - ‖A‖| := by
          simp only [norm_mul, norm_ofRealC, ← Complex.ofReal_sub,
            abs_of_nonneg (norm_nonneg B)]
      _ ≤ ‖A - B‖ * ‖B‖ + ‖B‖ * ‖A - B‖ := by
          gcongr
          simpa [norm_sub_rev] using abs_norm_sub_norm_le B A
      _ = 2 * ‖B‖ * ‖A - B‖ := by ring
  rw [div_sub_div A B hcC hdC, norm_div]
  have hden : ‖((‖A‖ : ℝ) : ℂ) * ((‖B‖ : ℝ) : ℂ)‖ = ‖A‖ * ‖B‖ := by
    rw [norm_mul, norm_ofRealC, norm_ofRealC, abs_of_nonneg (norm_nonneg A),
      abs_of_nonneg (norm_nonneg B)]
  rw [hden]
  calc ‖A * ((‖B‖ : ℝ) : ℂ) - ((‖A‖ : ℝ) : ℂ) * B‖ / (‖A‖ * ‖B‖)
      ≤ (2 * ‖B‖ * ‖A - B‖) / (‖A‖ * ‖B‖) := div_le_div_of_nonneg_right hnum (by positivity)
    _ = 2 * ‖A - B‖ / ‖A‖ := by field_simp

/-- **Pointwise difference of the sector character**: for `r ≠ 0` and the points
`z_v = r + i (b + L v)`, all on the vertical line `Re = r`, the unit vectors `z_v/|z_v|` satisfy

  `‖(z_{v+1}/|z_{v+1}|)^k - (z_v/|z_v|)^k‖ ≤ |k|·2|L|/|r|`   (`k ∈ ℤ`).

Proof: `|u^k - w^k| ≤ |k|·|u - w|` for unit `u, w` (geometric series; for `k < 0` use
`|u⁻¹ - w⁻¹| = |u - w|`), and `|A/|A| - B/|B|| ≤ 2|A-B|/|A|`, with `|z_{v+1} - z_v| = |L|` and
`|z_v| ≥ |r|`.  This is the loss of the sector factor `ψ(z) = χ(z)(z/|z|)^k` in *FI* (22.3): it
enters through summation by parts (`Work.FIArea7.abel_bound`) with `D = |k|·2|L|/|r|`, and summing
`D` over the class segments reproduces the factor `|k| + 1`. -/
theorem sector_diff_le (r b L k : ℤ) (hr : r ≠ 0) :
    ∀ v : ℤ,
      ‖(((⟨r, b + L * (v + 1)⟩ : GaussianInt) : ℂ)
            / ((‖((⟨r, b + L * (v + 1)⟩ : GaussianInt) : ℂ)‖ : ℝ) : ℂ)) ^ k
          - (((⟨r, b + L * v⟩ : GaussianInt) : ℂ)
            / ((‖((⟨r, b + L * v⟩ : GaussianInt) : ℂ)‖ : ℝ) : ℂ)) ^ k‖
        ≤ |(k : ℝ)| * (2 * |(L : ℝ)| / |(r : ℝ)|) := by
  intro v
  set A : ℂ := ((⟨r, b + L * (v + 1)⟩ : GaussianInt) : ℂ) with hA
  set B : ℂ := ((⟨r, b + L * v⟩ : GaussianInt) : ℂ) with hB
  have hAre : A.re = (r : ℝ) := by
    rw [hA]; exact GaussianInt.re_toComplex r (b + L * (v + 1))
  have hBre : B.re = (r : ℝ) := by
    rw [hB]; exact GaussianInt.re_toComplex r (b + L * v)
  have hA0 : A ≠ 0 := by
    intro h
    have h' : (r : ℝ) = 0 := by
      have := congrArg Complex.re h
      simpa [hAre] using this
    exact hr (Int.cast_eq_zero.mp h')
  have hB0 : B ≠ 0 := by
    intro h
    have h' : (r : ℝ) = 0 := by
      have := congrArg Complex.re h
      simpa [hBre] using this
    exact hr (Int.cast_eq_zero.mp h')
  have hAeq : A = (r : ℂ) + (((b + L * (v + 1) : ℤ)) : ℂ) * Complex.I := by
    rw [hA, GaussianInt.toComplex_def']
  have hBeq : B = (r : ℂ) + (((b + L * v : ℤ)) : ℂ) * Complex.I := by
    rw [hB, GaussianInt.toComplex_def']
  have hAB : ‖A - B‖ = |(L : ℝ)| := by
    have hdiff : A - B = ((L : ℤ) : ℂ) * Complex.I := by
      rw [hAeq, hBeq]
      push_cast
      ring
    rw [hdiff, norm_mul, Complex.norm_I, mul_one, norm_intCastC]
  have hrle : |(r : ℝ)| ≤ ‖A‖ := by
    rw [← hAre]
    exact Complex.abs_re_le_norm A
  have hcu : ‖A / ((‖A‖ : ℝ) : ℂ)‖ = 1 := by
    rw [norm_div, norm_ofRealC, abs_of_nonneg (norm_nonneg A),
      div_self (ne_of_gt (norm_pos_iff.mpr hA0))]
  have hdu : ‖B / ((‖B‖ : ℝ) : ℂ)‖ = 1 := by
    rw [norm_div, norm_ofRealC, abs_of_nonneg (norm_nonneg B),
      div_self (ne_of_gt (norm_pos_iff.mpr hB0))]
  have h1 := norm_zpow_sub_le (A / ((‖A‖ : ℝ) : ℂ)) (B / ((‖B‖ : ℝ) : ℂ)) hcu hdu k
  have h2 := norm_div_norm_sub_div_norm_le A B hA0 hB0
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr
  calc ‖(A / ((‖A‖ : ℝ) : ℂ)) ^ k - (B / ((‖B‖ : ℝ) : ℂ)) ^ k‖
      ≤ |(k : ℝ)| * ‖A / ((‖A‖ : ℝ) : ℂ) - B / ((‖B‖ : ℝ) : ℂ)‖ := h1
    _ ≤ |(k : ℝ)| * (2 * ‖A - B‖ / ‖A‖) :=
        mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    _ = |(k : ℝ)| * (2 * |(L : ℝ)| / ‖A‖) := by rw [hAB]
    _ ≤ |(k : ℝ)| * (2 * |(L : ℝ)| / |(r : ℝ)|) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact div_le_div_of_nonneg_left (by positivity) (abs_pos.mpr hrR) hrle

end Work.FIArea7
