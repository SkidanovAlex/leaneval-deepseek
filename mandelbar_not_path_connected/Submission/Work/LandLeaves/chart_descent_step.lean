/-
Copyright: subproject `Submission/Work/LandLeaves/` of `mandelbar_not_path_connected`.

The quantitative "descent step" for the chart `w ↦ 1/(n c w^n) - 1` around a non-zero `z`,
for a map `h` which is tangent to `z ↦ z + c z^{n+1}` up to order `n + 2`.
-/
import Mathlib
import Submission.Work.LandLeaves.chart_descent_prelim

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

/-- Algebraic identity behind the descent step: writing `h z = z + d`, the defect of the chart
`w ↦ 1/(n c w^n) - 1` along `h` splits as the `(n+1)`-st jet term `-c⁻¹ z^{-(n+1)} (d - c z^{n+1})`
plus the second-order remainder `((z+d)^n)⁻¹ - (z^n)⁻¹ + n z^{-(n+1)} d` (scaled by `(n c)⁻¹`). -/
lemma step_identity (n : ℕ) (hn : 1 ≤ n) (c z : ℂ) (hc : c ≠ 0) (hz : z ≠ 0) (d : ℂ)
    (hzd : z + d ≠ 0) :
    (1/((n:ℂ)*c*(z+d)^n)) - ((1/((n:ℂ)*c*z^n)) - 1)
      = -c⁻¹ * (z^(n+1))⁻¹ * (d - c*z^(n+1))
        + ((n:ℂ)*c)⁻¹ * (((z+d)^n)⁻¹ - (z^n)⁻¹ + (n:ℂ)*(z^(n+1))⁻¹*d) := by
  have hn' : (n:ℂ) ≠ 0 := by
    exact_mod_cast (Nat.pos_iff_ne_zero.mp (by omega : 0 < n))
  have hzn : (z^n) ≠ 0 := pow_ne_zero _ hz
  have hzdn : ((z+d)^n) ≠ 0 := pow_ne_zero _ hzd
  have hzpn : (z^(n+1)) ≠ 0 := pow_ne_zero _ hz
  field_simp
  ring

theorem chart_descent_step (n : ℕ) (hn : 1 ≤ n) (c : ℂ) (hc : c ≠ 0) (A : ℝ) (hA : 0 ≤ A)
    (h : ℂ → ℂ) (δ : ℝ) (hδpos : 0 < δ) (hδ1 : δ ≤ 1)
    (hδB : (‖c‖ + A) * δ ≤ 1 / 2)
    (happ : ∀ z : ℂ, ‖z‖ ≤ δ → ‖h z - z - c * z ^ (n + 1)‖ ≤ A * ‖z‖ ^ (n + 2)) :
    ∀ z : ℂ, z ≠ 0 → ‖z‖ ≤ δ →
      ‖(1 : ℂ) / ((n : ℂ) * c * (h z) ^ n)
          - ((1 : ℂ) / ((n : ℂ) * c * z ^ n) - 1)‖
        ≤ (A / ‖c‖ + (4 : ℝ) ^ n * (‖c‖ + A) ^ 2 / ((n : ℝ) * ‖c‖)) * ‖z‖ := by
  intro z hz hzδ
  have hznorm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hznorm_nonneg : 0 ≤ ‖z‖ := le_of_lt hznorm_pos
  have hznorm_ne : ‖z‖ ≠ 0 := ne_of_gt hznorm_pos
  have hznorm_le_one : ‖z‖ ≤ 1 := le_trans hzδ hδ1
  have hcnorm_pos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hcnorm_nonneg : 0 ≤ ‖c‖ := le_of_lt hcnorm_pos
  have hnR_pos : (0:ℝ) < (n:ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hcA_nonneg : 0 ≤ ‖c‖ + A := add_nonneg hcnorm_nonneg hA
  set d : ℂ := h z - z with hd_def
  set r0 : ℂ := h z - z - c * z^(n+1) with hr0_def
  set e : ℂ := ((z+d)^n)⁻¹ - (z^n)⁻¹ + (n:ℂ)*(z^(n+1))⁻¹*d with he_def
  have hr0bound : ‖r0‖ ≤ A * ‖z‖^(n+2) := by
    rw [hr0_def]; exact happ z hzδ
  have hd_eq : d = c*z^(n+1) + r0 := by rw [hd_def, hr0_def]; ring
  have hhd : h z = z + d := by rw [hd_def]; ring
  have hr0_eq : d - c*z^(n+1) = r0 := by rw [hd_def, hr0_def]
  have hzpow_le : ‖z‖^(n+2) ≤ ‖z‖^(n+1) :=
    pow_le_pow_of_le_one hznorm_nonneg hznorm_le_one (show n+1 ≤ n+2 by omega)
  have hd_bound : ‖d‖ ≤ ‖z‖^(n+1) * (‖c‖ + A) := by
    have h1 : ‖d‖ ≤ ‖c * z^(n+1)‖ + ‖r0‖ := by
      calc ‖d‖ = ‖c*z^(n+1) + r0‖ := by rw [hd_eq]
        _ ≤ ‖c*z^(n+1)‖ + ‖r0‖ := norm_add_le _ _
    have h2 : ‖c * z^(n+1)‖ = ‖c‖ * ‖z‖^(n+1) := by rw [norm_mul, norm_pow]
    have h3 : ‖r0‖ ≤ A * ‖z‖^(n+1) :=
      le_trans hr0bound (mul_le_mul_of_nonneg_left hzpow_le hA)
    calc ‖d‖ ≤ ‖c * z^(n+1)‖ + ‖r0‖ := h1
      _ ≤ ‖c‖ * ‖z‖^(n+1) + A * ‖z‖^(n+1) := add_le_add (le_of_eq h2) h3
      _ = ‖z‖^(n+1) * (‖c‖ + A) := by ring
  have hzn_le_delta : ‖z‖^n ≤ δ := by
    have h1 : ‖z‖^n ≤ ‖z‖^1 := pow_le_pow_of_le_one hznorm_nonneg hznorm_le_one hn
    rw [pow_one] at h1
    exact le_trans h1 hzδ
  have hd_shrink : ‖d‖ ≤ ‖z‖ / 2 := by
    have hA1 : ‖z‖^n * (‖c‖ + A) ≤ 1/2 := by
      have h2 : ‖z‖^n * (‖c‖+A) ≤ δ * (‖c‖+A) :=
        mul_le_mul_of_nonneg_right hzn_le_delta hcA_nonneg
      have h3 : δ * (‖c‖+A) ≤ 1/2 := by linarith [hδB]
      linarith
    calc ‖d‖ ≤ ‖z‖^(n+1) * (‖c‖ + A) := hd_bound
      _ = ‖z‖ * (‖z‖^n * (‖c‖ + A)) := by rw [pow_succ']; ring
      _ ≤ ‖z‖ * (1/2) := mul_le_mul_of_nonneg_left hA1 hznorm_nonneg
      _ = ‖z‖ / 2 := by ring
  have hzd_ne : z + d ≠ 0 := by
    intro hzero
    have hlow : ‖z‖ / 2 ≤ ‖z + d‖ := by
      have h := norm_sub_le (z+d) d
      have hzeq : (z+d) - d = z := by ring
      rw [hzeq] at h
      linarith [hd_shrink]
    rw [hzero, norm_zero] at hlow
    linarith [hznorm_pos]
  have hlin : ‖e‖ ≤ (4:ℝ)^n * ‖d‖^2 / ‖z‖^(n+2) := by
    rw [he_def]; exact norm_pow_inv_sub_linear n z d hz hd_shrink
  have he_bound : ‖e‖ ≤ (4:ℝ)^n * ‖z‖^n * (‖c‖+A)^2 := by
    have hd2 : ‖d‖^2 ≤ (‖z‖^(n+1))^2 * (‖c‖+A)^2 := by
      calc ‖d‖^2 ≤ (‖z‖^(n+1) * (‖c‖+A))^2 :=
            pow_le_pow_left₀ (norm_nonneg d) hd_bound 2
        _ = (‖z‖^(n+1))^2 * (‖c‖+A)^2 := by ring
    have h4n : 0 ≤ (4:ℝ)^n := by positivity
    have hzpowpos : 0 < ‖z‖^(n+2) := pow_pos hznorm_pos _
    calc ‖e‖ ≤ (4:ℝ)^n * ‖d‖^2 / ‖z‖^(n+2) := hlin
      _ ≤ (4:ℝ)^n * ((‖z‖^(n+1))^2 * (‖c‖+A)^2) / ‖z‖^(n+2) := by
            apply div_le_div_of_nonneg_right _ (le_of_lt hzpowpos)
            exact mul_le_mul_of_nonneg_left hd2 h4n
      _ = (4:ℝ)^n * ‖z‖^n * (‖c‖+A)^2 := by
            have hB : ‖z‖^(n+2) ≠ 0 := pow_ne_zero _ hznorm_ne
            rw [div_eq_iff hB]
            have hmul : (‖z‖^(n+1))^2 = ‖z‖^n * ‖z‖^(n+2) := by
              rw [← pow_mul, ← pow_add]; congr 1; omega
            rw [hmul]; ring
  have hterm1 : ‖c‖⁻¹ * (‖z‖^(n+1))⁻¹ * ‖r0‖ ≤ (A/‖c‖)*‖z‖ := by
    have h1 : ‖c‖⁻¹ * (‖z‖^(n+1))⁻¹ * ‖r0‖
        ≤ ‖c‖⁻¹ * (‖z‖^(n+1))⁻¹ * (A*‖z‖^(n+2)) := by
      apply mul_le_mul_of_nonneg_left hr0bound
      positivity
    have h2 : ‖c‖⁻¹ * (‖z‖^(n+1))⁻¹ * (A*‖z‖^(n+2)) = (A/‖c‖)*‖z‖ := by
      have hzpow : (‖z‖^(n+1))⁻¹ * ‖z‖^(n+2) = ‖z‖ := by
        have hzneq : ‖z‖^(n+1) ≠ 0 := pow_ne_zero _ hznorm_ne
        have hsplit : ‖z‖^(n+2) = ‖z‖^(n+1) * ‖z‖ := by
          rw [show n+2 = (n+1)+1 by omega]
          exact pow_succ _ _
        rw [hsplit, inv_mul_cancel_left₀ hzneq]
      calc ‖c‖⁻¹ * (‖z‖^(n+1))⁻¹ * (A*‖z‖^(n+2))
          = ‖c‖⁻¹ * A * ((‖z‖^(n+1))⁻¹ * ‖z‖^(n+2)) := by ring
        _ = ‖c‖⁻¹ * A * ‖z‖ := by rw [hzpow]
        _ = (A/‖c‖)*‖z‖ := by ring
    linarith [h1, h2]
  have hzpow_le_z : ‖z‖^n ≤ ‖z‖ := by
    have h : ‖z‖^n ≤ ‖z‖^1 := pow_le_pow_of_le_one hznorm_nonneg hznorm_le_one hn
    simpa using h
  have hterm2 : ((n:ℝ)*‖c‖)⁻¹ * ‖e‖ ≤ (4^n*(‖c‖+A)^2/((n:ℝ)*‖c‖))*‖z‖ := by
    have hnn : 0 ≤ ((n:ℝ)*‖c‖)⁻¹ := by positivity
    have h1 : ((n:ℝ)*‖c‖)⁻¹ * ‖e‖
        ≤ ((n:ℝ)*‖c‖)⁻¹ * ((4:ℝ)^n * ‖z‖^n * (‖c‖+A)^2) :=
      mul_le_mul_of_nonneg_left he_bound hnn
    have hstep : ((4:ℝ)^n * ‖z‖^n * (‖c‖+A)^2) ≤ ((4:ℝ)^n * ‖z‖ * (‖c‖+A)^2) := by
      have h0 : (4:ℝ)^n * ‖z‖^n ≤ (4:ℝ)^n * ‖z‖ :=
        mul_le_mul_of_nonneg_left hzpow_le_z (by positivity)
      exact mul_le_mul_of_nonneg_right h0 (sq_nonneg (‖c‖+A))
    have h2 : ((n:ℝ)*‖c‖)⁻¹ * ‖e‖
        ≤ ((n:ℝ)*‖c‖)⁻¹ * ((4:ℝ)^n * ‖z‖ * (‖c‖+A)^2) :=
      le_trans h1 (mul_le_mul_of_nonneg_left hstep hnn)
    have h3 : ((n:ℝ)*‖c‖)⁻¹ * ((4:ℝ)^n * ‖z‖ * (‖c‖+A)^2)
        = (4^n*(‖c‖+A)^2/((n:ℝ)*‖c‖))*‖z‖ := by
      rw [div_eq_mul_inv]; ring
    linarith [h2, h3]
  rw [hhd]
  rw [step_identity n hn c z hc hz d hzd_ne]
  rw [hr0_eq, ← he_def]
  calc ‖-c⁻¹*(z^(n+1))⁻¹*r0 + ((n:ℂ)*c)⁻¹*e‖
      ≤ ‖-c⁻¹*(z^(n+1))⁻¹*r0‖ + ‖((n:ℂ)*c)⁻¹*e‖ := norm_add_le _ _
      _ = ‖c‖⁻¹ * (‖z‖^(n+1))⁻¹ * ‖r0‖ + ((n:ℝ)*‖c‖)⁻¹ * ‖e‖ := by
            simp only [norm_mul, norm_neg, norm_inv, norm_pow, Complex.norm_natCast]
      _ ≤ (A/‖c‖)*‖z‖ + (4^n*(‖c‖+A)^2/((n:ℝ)*‖c‖))*‖z‖ :=
            add_le_add hterm1 hterm2
      _ = (A/‖c‖ + (4:ℝ)^n*(‖c‖+A)^2/((n:ℝ)*‖c‖))*‖z‖ := by ring

end Work.LandLeaves
