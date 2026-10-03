import Mathlib

/-!
# The nearest member of the `τ_C`-fibre over `p` is close to `τ₀ p = -1/p`

For `σ u₀ = 1 - exp (2πi α)` and `w = σ/p = σ * p⁻¹` one has, for the principal branch,

  `ζ₀ + 1/p = -log (1 - w)/(2πiα) + 1/p`,

which is exactly the `k = 0` member of the fibre `ζ = -Log(1-σ/p)/(2πiα) - k/α` of solutions of
`τ_C σ α ζ = p`, compared with the reference point `τ₀ p = -1/p`.  We prove

  `‖ζ₀ + 1/p‖ ≤ 48 (‖u₀-1‖ + ‖α‖‖1/p‖) ‖1/p‖`

in the *moderate regime* `64 ‖α‖ ‖1/p‖ ≤ 1`, `‖1/p‖ ≥ 1`, `‖α‖ ≤ 1/64`, `‖u₀‖ ≥ 1/2`.

The proof splits `-log(1-w)/(2πiα) + 1/p` into

* `(log((1-w)⁻¹) - w)/(2πiα)`, bounded by the logarithm Taylor remainder
  `Complex.norm_log_one_sub_inv_sub_self_le`, and
* `w/(2πiα) + 1/p = (1/p)(σ + 2πiα)/(2πiα)`, which is pure algebra once
  `σ = (1 - exp (2πiα))/u₀` is substituted, giving the `‖u₀-1‖` factor.

Both terms are `O((‖u₀-1‖ + ‖α‖‖1/p‖)‖1/p‖)` with constants far below `48`.
-/

namespace Work.PertCrux

theorem norm_log_preimage_sub_tau0_le {α u0 σ p : ℂ}
    (hα : α ≠ 0) (hu0 : 1 / 2 ≤ ‖u0‖) (hσ : σ ≠ 0) (hp : p ≠ 0) (hσp : σ ≠ p)
    (hσu : σ * u0 = 1 - Complex.exp (2 * Real.pi * Complex.I * α))
    (hα64 : ‖α‖ ≤ 1 / 64) (hsmall : 64 * ‖α‖ * ‖1 / p‖ ≤ 1) (ht : 1 ≤ ‖1 / p‖) :
    ‖-(Complex.log (1 - σ / p)) / (2 * Real.pi * Complex.I * α) + 1 / p‖
      ≤ 48 * (‖u0 - 1‖ + ‖α‖ * ‖1 / p‖) * ‖1 / p‖ := by
  rw [div_eq_mul_inv σ p, one_div p]
  set T : ℂ := p⁻¹ with hTdef
  set z : ℂ := 2 * Real.pi * Complex.I * α with hzdef
  have htT : 1 ≤ ‖T‖ := by rw [hTdef]; simpa [one_div] using ht
  have hsmallT : 64 * ‖α‖ * ‖T‖ ≤ 1 := by rw [hTdef]; simpa [one_div] using hsmall
  have hTnn : 0 ≤ ‖T‖ := le_trans zero_le_one htT
  have hapos : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have ha : 0 ≤ ‖α‖ := le_of_lt hapos
  have hUt : 0 ≤ ‖u0 - 1‖ := norm_nonneg _
  have hznorm : ‖z‖ = 2 * Real.pi * ‖α‖ := by
    rw [hzdef, norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
  have hzle1 : ‖z‖ ≤ 1 := by
    rw [hznorm]; nlinarith [Real.pi_lt_d2, hα64, ha]
  have hzpos : 0 < ‖z‖ := by rw [hznorm]; positivity
  have hzne : z ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hzpos)
  have hu0pos : 0 < ‖u0‖ := by linarith [hu0]
  have hu0ne : u0 ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hu0pos)
  -- Shape of `σ` from the defining relation.
  have hσ_bound : ‖σ‖ ≤ 14 * ‖α‖ := by
    have hn : ‖σ‖ * ‖u0‖ = ‖1 - Complex.exp z‖ := by rw [← Complex.norm_mul, hσu]
    have h2 : ‖1 - Complex.exp z‖ ≤ ‖z‖ + ‖z‖ ^ 2 := by
      have h3 : Complex.exp z - 1 = z + (Complex.exp z - 1 - z) := by ring
      have h4 : ‖Complex.exp z - 1‖ ≤ ‖z‖ + ‖z‖ ^ 2 := by
        rw [h3]
        exact (norm_add_le _ _).trans (by linarith [Complex.norm_exp_sub_one_sub_id_le hzle1])
      rw [norm_sub_rev]; exact h4
    rw [hznorm] at h2
    have hb : ‖σ‖ * (1 / 2) ≤ ‖σ‖ * ‖u0‖ := mul_le_mul_of_nonneg_left hu0 (norm_nonneg σ)
    have key : ‖σ‖ ≤ 4 * Real.pi * ‖α‖ + 8 * Real.pi ^ 2 * ‖α‖ ^ 2 := by
      nlinarith [hn, hb, h2]
    have hfin : 4 * Real.pi * ‖α‖ + 8 * Real.pi ^ 2 * ‖α‖ ^ 2 ≤ 14 * ‖α‖ := by
      nlinarith [Real.pi_lt_d2, Real.pi_pos, hα64, ha]
    linarith [key, hfin]
  have hw_le : ‖σ * T‖ ≤ 14 * ‖α‖ * ‖T‖ := by
    rw [Complex.norm_mul]; exact mul_le_mul_of_nonneg_right hσ_bound hTnn
  have hαT : ‖α‖ * ‖T‖ ≤ 1 / 64 := by linarith [hsmallT]
  have hw_half : ‖σ * T‖ ≤ 1 / 2 := by
    have h1 : (14:ℝ) * (‖α‖ * ‖T‖) ≤ 14 * (1/64) := mul_le_mul_of_nonneg_left hαT (by norm_num)
    nlinarith [hw_le]
  have hw_lt1 : ‖σ * T‖ < 1 := by linarith [hw_half]
  -- The argument `1 - w` stays in the slit plane.
  have harg : (1 - σ * T).arg ≠ Real.pi := by
    refine Complex.slitPlane_arg_ne_pi ?_
    have hmem : 1 + -(σ * T) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_of_norm_lt_one (by simpa using hw_lt1)
    simpa [sub_eq_add_neg] using hmem
  -- Taylor remainder for the logarithm.
  have hrem : ‖Complex.log ((1 - σ * T)⁻¹) - σ * T‖ ≤ ‖σ * T‖ ^ 2 := by
    have h := Complex.norm_log_one_sub_inv_sub_self_le (z := σ * T) hw_lt1
    have hpos : 0 < 1 - ‖σ * T‖ := by linarith [hw_half]
    have hinv : (1 - ‖σ * T‖)⁻¹ ≤ 2 := by
      rw [inv_le_iff_one_le_mul₀ hpos]; linarith [hw_half]
    nlinarith [h, hinv, norm_nonneg (σ * T)]
  -- Term A: `(log ((1-w)⁻¹) - w)/(2πiα)`.
  have hA : ‖(Complex.log ((1 - σ * T)⁻¹) - σ * T) / z‖ ≤ 32 * ‖α‖ * ‖T‖ ^ 2 := by
    rw [norm_div, hznorm]
    have hnum : ‖Complex.log ((1 - σ * T)⁻¹) - σ * T‖ ≤ (14 * ‖α‖ * ‖T‖) ^ 2 := by
      nlinarith [hrem, hw_le, norm_nonneg (σ * T), ha, hTnn]
    have hden : 0 < 2 * Real.pi * ‖α‖ := by positivity
    have hstep : ‖Complex.log ((1 - σ * T)⁻¹) - σ * T‖ / (2 * Real.pi * ‖α‖)
        ≤ (14 * ‖α‖ * ‖T‖) ^ 2 / (2 * Real.pi * ‖α‖) :=
      div_le_div_of_nonneg_right hnum (le_of_lt hden)
    have hid : (14 * ‖α‖ * ‖T‖) ^ 2 / (2 * Real.pi * ‖α‖) = (98 / Real.pi) * ‖α‖ * ‖T‖ ^ 2 := by
      field_simp; ring
    have hπ : (98:ℝ) / Real.pi ≤ 32 := by
      rw [div_le_iff₀ Real.pi_pos]; nlinarith [Real.pi_gt_d2]
    calc ‖Complex.log ((1 - σ * T)⁻¹) - σ * T‖ / (2 * Real.pi * ‖α‖)
        ≤ (14 * ‖α‖ * ‖T‖) ^ 2 / (2 * Real.pi * ‖α‖) := hstep
      _ = (98 / Real.pi) * ‖α‖ * ‖T‖ ^ 2 := hid
      _ ≤ 32 * ‖α‖ * ‖T‖ ^ 2 := by
            rw [show (98 / Real.pi) * ‖α‖ * ‖T‖ ^ 2 = (98 / Real.pi) * (‖α‖ * ‖T‖ ^ 2) by ring,
                show 32 * ‖α‖ * ‖T‖ ^ 2 = 32 * (‖α‖ * ‖T‖ ^ 2) by ring]
            exact mul_le_mul_of_nonneg_right hπ (by positivity)
  -- Term B: `w/(2πiα) + 1/p = (1/p)(σ + 2πiα)/(2πiα)`.
  have hσeq : σ = (1 - Complex.exp z) / u0 := by
    rw [eq_div_iff hu0ne]; exact hσu
  have hsz_eq : σ + z = (1 - Complex.exp z + z * u0) / u0 := by
    rw [hσeq]; field_simp
  have hnum_eq : 1 - Complex.exp z + z * u0 = -(Complex.exp z - 1 - z) + z * (u0 - 1) := by ring
  have hnum_bound : ‖1 - Complex.exp z + z * u0‖ ≤ ‖z‖ ^ 2 + ‖z‖ * ‖u0 - 1‖ := by
    rw [hnum_eq]
    calc ‖-(Complex.exp z - 1 - z) + z * (u0 - 1)‖
        ≤ ‖-(Complex.exp z - 1 - z)‖ + ‖z * (u0 - 1)‖ := norm_add_le _ _
      _ = ‖Complex.exp z - 1 - z‖ + ‖z‖ * ‖u0 - 1‖ := by rw [norm_neg, norm_mul]
      _ ≤ ‖z‖ ^ 2 + ‖z‖ * ‖u0 - 1‖ := by linarith [Complex.norm_exp_sub_one_sub_id_le hzle1]
  have hσz : ‖σ + z‖ ≤ 2 * (‖z‖ ^ 2 + ‖z‖ * ‖u0 - 1‖) := by
    rw [hsz_eq, norm_div, div_le_iff₀ hu0pos]
    have hS : 0 ≤ ‖z‖ ^ 2 + ‖z‖ * ‖u0 - 1‖ := by positivity
    have h2u : (1:ℝ) ≤ 2 * ‖u0‖ := by linarith [hu0]
    have h2 := mul_le_mul_of_nonneg_right h2u hS
    linarith [hnum_bound, h2]
  have hB : ‖σ * T / z + T‖ ≤ 2 * ‖u0 - 1‖ * ‖T‖ + 4 * Real.pi * ‖α‖ * ‖T‖ := by
    have hd : σ * T / z + T = T * (σ + z) / z := by field_simp
    rw [hd, norm_div, norm_mul, hznorm]
    have hden : 0 < 2 * Real.pi * ‖α‖ := by positivity
    calc ‖T‖ * ‖σ + z‖ / (2 * Real.pi * ‖α‖)
        ≤ ‖T‖ * (2 * (‖z‖ ^ 2 + ‖z‖ * ‖u0 - 1‖)) / (2 * Real.pi * ‖α‖) := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hden)
          exact mul_le_mul_of_nonneg_left hσz hTnn
      _ = 2 * ‖u0 - 1‖ * ‖T‖ + 4 * Real.pi * ‖α‖ * ‖T‖ := by
          rw [hznorm]; field_simp; ring
  -- Assembly.
  have hloginv : Complex.log ((1 - σ * T)⁻¹) = -Complex.log (1 - σ * T) := Complex.log_inv _ harg
  have hsplit : -Complex.log (1 - σ * T) / z + T
      = (Complex.log ((1 - σ * T)⁻¹) - σ * T) / z + (σ * T / z + T) := by
    rw [hloginv]; ring
  rw [hsplit]
  have h1 : 4 * Real.pi * ‖α‖ * ‖T‖ ≤ 16 * ‖α‖ * ‖T‖ ^ 2 := by
    have htt : ‖T‖ ≤ ‖T‖ ^ 2 := by nlinarith [htT]
    have h4pi : 4 * Real.pi ≤ 16 := by linarith [Real.pi_lt_four]
    calc 4 * Real.pi * ‖α‖ * ‖T‖ = (4 * Real.pi) * (‖α‖ * ‖T‖) := by ring
      _ ≤ 16 * (‖α‖ * ‖T‖) := mul_le_mul_of_nonneg_right h4pi (mul_nonneg ha hTnn)
      _ ≤ 16 * (‖α‖ * ‖T‖ ^ 2) := by
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htt ha) (by norm_num)
      _ = 16 * ‖α‖ * ‖T‖ ^ 2 := by ring
  have h2 : 2 * ‖u0 - 1‖ * ‖T‖ ≤ 48 * ‖u0 - 1‖ * ‖T‖ := by nlinarith [hUt, hTnn]
  calc ‖(Complex.log ((1 - σ * T)⁻¹) - σ * T) / z + (σ * T / z + T)‖
      ≤ ‖(Complex.log ((1 - σ * T)⁻¹) - σ * T) / z‖ + ‖σ * T / z + T‖ := norm_add_le _ _
    _ ≤ 32 * ‖α‖ * ‖T‖ ^ 2 + (2 * ‖u0 - 1‖ * ‖T‖ + 4 * Real.pi * ‖α‖ * ‖T‖) := add_le_add hA hB
    _ ≤ 48 * (‖u0 - 1‖ + ‖α‖ * ‖T‖) * ‖T‖ := by nlinarith [h1, h2, ha, hTnn, htT]

end Work.PertCrux
