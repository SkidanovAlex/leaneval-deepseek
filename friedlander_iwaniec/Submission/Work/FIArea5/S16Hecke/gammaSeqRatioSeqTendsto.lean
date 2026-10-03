import Mathlib

namespace Work.FIArea5.S16Hecke

/-- Norm of the `j`-th factor appearing in the `n`-th Gamma sequence term for `s = u + iT`. -/
lemma gammaSeqRatio_norm_factor_u (u T : ℝ) (j : ℕ) :
    ‖((u : ℂ) + (T : ℂ) * Complex.I) + (j : ℂ)‖ = Real.sqrt (T ^ 2 + ((j : ℝ) + u) ^ 2) := by
  rw [show ((u : ℂ) + (T : ℂ) * Complex.I) + (j : ℂ)
        = ((u + (j : ℝ) : ℝ) : ℂ) + ((T : ℝ) : ℂ) * Complex.I by
    apply Complex.ext <;> simp]
  rw [Complex.norm_add_mul_I]
  congr 1
  ring

/-- Norm of the `j`-th factor for `s = 1/2 + iT`. -/
lemma gammaSeqRatio_norm_factor_h (T : ℝ) (j : ℕ) :
    ‖((1 / 2 : ℂ) + (T : ℂ) * Complex.I) + (j : ℂ)‖
      = Real.sqrt (T ^ 2 + ((j : ℝ) + 1 / 2) ^ 2) := by
  rw [show ((1 / 2 : ℂ) + (T : ℂ) * Complex.I) + (j : ℂ)
        = (((1 / 2 : ℝ) + (j : ℝ) : ℝ) : ℂ) + ((T : ℝ) : ℂ) * Complex.I by
    apply Complex.ext <;> simp]
  rw [Complex.norm_add_mul_I]
  congr 1
  ring

/-- Norm of the `n`-th term of the Gamma sequence for `s = u + iT`, as an explicit product. -/
lemma gammaSeqRatio_norm_u (u T : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖Complex.GammaSeq ((u : ℂ) + (T : ℂ) * Complex.I) n‖ =
      (n : ℝ) ^ u * (n.factorial : ℝ) /
        Finset.prod (Finset.range (n + 1)) (fun j => Real.sqrt (T ^ 2 + ((j : ℝ) + u) ^ 2)) := by
  rw [Complex.GammaSeq, norm_div, norm_mul, Complex.norm_natCast, Complex.norm_prod]
  rw [show ((n : ℂ)) = ((n : ℝ) : ℂ) by simp]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < n)]
  have hre : ((u : ℂ) + (T : ℂ) * Complex.I).re = u := by simp
  rw [hre]
  congr 1
  exact Finset.prod_congr rfl (fun j _ => gammaSeqRatio_norm_factor_u u T j)

/-- Norm of the `n`-th term of the Gamma sequence for `s = 1/2 + iT`. -/
lemma gammaSeqRatio_norm_h (T : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖Complex.GammaSeq ((1 / 2 : ℂ) + (T : ℂ) * Complex.I) n‖ =
      (n : ℝ) ^ ((1 : ℝ) / 2) * (n.factorial : ℝ) /
        Finset.prod (Finset.range (n + 1)) (fun j => Real.sqrt (T ^ 2 + ((j : ℝ) + 1 / 2) ^ 2)) := by
  rw [Complex.GammaSeq, norm_div, norm_mul, Complex.norm_natCast, Complex.norm_prod]
  rw [show ((n : ℂ)) = ((n : ℝ) : ℂ) by simp]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < n)]
  have hre : ((1 / 2 : ℂ) + (T : ℂ) * Complex.I).re = (1 : ℝ) / 2 := by simp
  rw [hre]
  congr 1
  exact Finset.prod_congr rfl (fun j _ => gammaSeqRatio_norm_factor_h T j)

/-- The key identity: for `n ≥ 1`, the ratio of the norms of the two Gamma sequence terms
equals the product in the statement. -/
lemma gammaSeqRatio_ratio_eq (u T : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖Complex.GammaSeq ((u : ℂ) + (T : ℂ) * Complex.I) n‖ /
        ‖Complex.GammaSeq ((1 / 2 : ℂ) + (T : ℂ) * Complex.I) n‖
      = (n : ℝ) ^ (u - 1 / 2) * Finset.prod (Finset.range (n + 1))
          (fun j => Real.sqrt ((T ^ 2 + ((j : ℝ) + 1 / 2) ^ 2) / (T ^ 2 + ((j : ℝ) + u) ^ 2))) := by
  rw [gammaSeqRatio_norm_u u T hn, gammaSeqRatio_norm_h T hn]
  set A := Finset.prod (Finset.range (n + 1)) (fun j => Real.sqrt (T ^ 2 + ((j : ℝ) + u) ^ 2)) with hA
  set B := Finset.prod (Finset.range (n + 1))
      (fun j => Real.sqrt (T ^ 2 + ((j : ℝ) + 1 / 2) ^ 2)) with hB
  have hprod : Finset.prod (Finset.range (n + 1))
        (fun j => Real.sqrt ((T ^ 2 + ((j : ℝ) + 1 / 2) ^ 2) / (T ^ 2 + ((j : ℝ) + u) ^ 2)))
        = B / A := by
    have h1 : ∀ j : ℕ, Real.sqrt ((T ^ 2 + ((j : ℝ) + 1 / 2) ^ 2) / (T ^ 2 + ((j : ℝ) + u) ^ 2))
        = Real.sqrt (T ^ 2 + ((j : ℝ) + 1 / 2) ^ 2) / Real.sqrt (T ^ 2 + ((j : ℝ) + u) ^ 2) :=
      fun j => Real.sqrt_div (by positivity) _
    simp_rw [h1]
    rw [Finset.prod_div_distrib, hB, hA]
  rw [hprod]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hC : (n : ℝ) ^ ((1 : ℝ) / 2) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hn' _)
  have hnf : (n.factorial : ℝ) ≠ 0 := by simp [Nat.factorial_ne_zero]
  have hpow : (n : ℝ) ^ u = (n : ℝ) ^ (u - 1 / 2) * (n : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_add hn']
    ring_nf
  rcases eq_or_ne A 0 with hA0 | hA0
  · simp [hA0]
  · rw [hpow]
    field_simp

/-- `Γ(1/2 + iT)` never vanishes (Gamma has no zeros). -/
lemma gammaSeqRatio_gamma_half_ne_zero (T : ℝ) :
    Complex.Gamma ((1 / 2 : ℂ) + (T : ℂ) * Complex.I) ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro m hm
  have hre := congr_arg Complex.re hm
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, Complex.neg_re] at hre
  norm_num at hre
  have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

theorem gammaSeqRatioSeqTendsto (u T : ℝ) :
    Filter.Tendsto (fun n : ℕ =>
        (n : ℝ) ^ (u - 1 / 2) * Finset.prod (Finset.range (n + 1))
          (fun j : ℕ => Real.sqrt ((T ^ 2 + ((j : ℝ) + 1 / 2) ^ 2) / (T ^ 2 + ((j : ℝ) + u) ^ 2))))
      Filter.atTop
      (nhds (‖Complex.Gamma ((u : ℂ) + (T : ℂ) * Complex.I)‖ /
           ‖Complex.Gamma ((1 / 2 : ℂ) + (T : ℂ) * Complex.I)‖)) := by
  have hne : ‖Complex.Gamma ((1 / 2 : ℂ) + (T : ℂ) * Complex.I)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (gammaSeqRatio_gamma_half_ne_zero T)
  have h1 : Filter.Tendsto (fun n => ‖Complex.GammaSeq ((u : ℂ) + (T : ℂ) * Complex.I) n‖)
      Filter.atTop (nhds ‖Complex.Gamma ((u : ℂ) + (T : ℂ) * Complex.I)‖) :=
    (Complex.GammaSeq_tendsto_Gamma _).norm
  have h2 : Filter.Tendsto (fun n => ‖Complex.GammaSeq ((1 / 2 : ℂ) + (T : ℂ) * Complex.I) n‖)
      Filter.atTop (nhds ‖Complex.Gamma ((1 / 2 : ℂ) + (T : ℂ) * Complex.I)‖) :=
    (Complex.GammaSeq_tendsto_Gamma _).norm
  refine Filter.Tendsto.congr' ?_ (h1.div h2 hne)
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  exact gammaSeqRatio_ratio_eq u T (by omega)

end Work.FIArea5.S16Hecke
