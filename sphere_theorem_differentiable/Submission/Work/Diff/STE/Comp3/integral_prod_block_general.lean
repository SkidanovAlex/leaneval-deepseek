import Mathlib
import Submission.Work.Diff.STE.CSq_comp_le
import Submission.Work.Diff.STE.Comp.young_conv_lp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Comp3

open MeasureTheory BigOperators

/-- The reciprocals of the Young exponents attached to a weight family `β : Fin r → ℕ` with
`∑ i, β i = s` sum to `r - 1/2`; this is the exponent condition of Young's inequality
`Comp.young_conv_lp` for the block sizes `β`. -/
lemma sum_yExp_inv_fin {r : ℕ} (s : ℕ) (hs : 0 < s) (β : Fin r → ℕ)
    (hβsum : ∑ i : Fin r, β i = s) :
    ∑ i : Fin r, (Work.Diff.STE.yExp s (β i))⁻¹ = (r : ℝ) - 1 / 2 := by
  have h1 : ∀ i : Fin r, (Work.Diff.STE.yExp s (β i))⁻¹
      = 1 - (β i : ℝ) / (2 * (s : ℝ)) := by
    intro i
    rw [Work.Diff.STE.yExp_inv]
    field_simp
  rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, ← Finset.sum_div]
  rw [show ∑ i : Fin r, ((β i : ℕ) : ℝ) = (s : ℝ) from by rw [← Nat.cast_sum, hβsum]]
  field_simp

/-- **General per-block estimate.**  Let `γ` be a coefficient family with all moments and the
weighted `ℓ¹`/`ℓ²` norms finite, and let `d i` be families whose norms are dominated by the
multipliers of order `β i`, `∑ i, β i = s`, `r ≤ s`.  Then the `L²`-norm over the unit cube of
the product of the Fourier series `seriesFun (d i)` is bounded by
`((2π)^s (1+Λ)^s)^2 (1 + CSq s γ)`.

This is the generalisation of `integral_prod_blockFam_le` to an arbitrary block structure `β`:
the harmonic-analytic content is Young's inequality for the `r`-fold convolution
(`Comp.young_conv_lp`) with the exponents `p i = 2s/(2s-β i)`, whose reciprocals sum to
`r - 1/2` because `∑ i, β i = s`, together with the weighted `ℓ^p` interpolation bound
`Comp.weighted_lp_le` for each factor. -/
theorem integral_prod_block_general {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℕ) (hs : 0 < s) (γ : (ι → ℤ) → ℂ)
    (hmom : ∀ N : ℕ, Summable fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ N * ‖γ k‖)
    (hΛ : Summable fun k : ι → ℤ => ‖γ k‖)
    (hQ : Summable fun k : ι → ℤ => (‖k‖ : ℝ) ^ (2 * s) * ‖γ k‖ ^ 2)
    {r : ℕ} (hr : 1 ≤ r) (hrs : r ≤ s) (d : Fin r → (ι → ℤ) → ℂ) (β : Fin r → ℕ)
    (hβ : ∀ i, β i ≤ s) (hβsum : ∑ i, β i = s)
    (hd : ∀ i k, ‖d i k‖ ≤ (2 * Real.pi * ‖k‖) ^ (β i) * ‖γ k‖)
    (hsm : ∀ i, Summable fun k : ι → ℤ => ‖d i k‖ ^ (Work.Diff.STE.yExp s (β i))) :
    ∫ x in Work.Diff.STE.unitCube, ‖∏ i, Work.Diff.STE.seriesFun (d i) x‖ ^ 2
      ≤ (((2 * Real.pi) ^ s * (1 + ∑' k : ι → ℤ, ‖γ k‖) ^ s) ^ 2) *
          (1 + Work.Diff.STE.CSq s γ) := by
  classical
  set Λ : ℝ := ∑' k : ι → ℤ, ‖γ k‖ with hΛdef
  set Q : ℝ := ∑' k : ι → ℤ, (‖k‖ : ℝ) ^ (2 * s) * ‖γ k‖ ^ 2 with hQdef
  have hΛ0 : (0 : ℝ) ≤ Λ := tsum_nonneg fun k => norm_nonneg (γ k)
  have hQ0 : (0 : ℝ) ≤ Q :=
    tsum_nonneg fun k => mul_nonneg (pow_nonneg (norm_nonneg k) _) (sq_nonneg _)
  have hCSq0 : (0 : ℝ) ≤ Work.Diff.STE.CSq s γ :=
    tsum_nonneg fun k => mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) s) (sq_nonneg _)
  have hΛ1 : 1 ≤ 1 + Λ := by linarith
  have hQ_le : Q ≤ Work.Diff.STE.CSq s γ := by
    rw [hQdef, Work.Diff.STE.CSq]
    refine Summable.tsum_le_tsum (fun k => ?_) hQ
      (Work.Diff.STE.summable_wt_pow_mul_norm_sq γ hmom s)
    have h1 : (‖k‖ : ℝ) ^ (2 * s) ≤ (Work.Diff.STE.wt k) ^ s := by
      have h2 : (‖k‖ : ℝ) ^ 2 ≤ Work.Diff.STE.wt k := Work.Diff.STE.sq_norm_le_wt k
      calc (‖k‖ : ℝ) ^ (2 * s) = ((‖k‖ : ℝ) ^ 2) ^ s := by rw [← pow_mul]
        _ ≤ (Work.Diff.STE.wt k) ^ s := pow_le_pow_left₀ (sq_nonneg _) h2 s
    exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  -- the exponent family `p i = 2s/(2s - β i)` and the Young condition
  have hp : ∀ i : Fin r, 1 ≤ Work.Diff.STE.yExp s (β i) :=
    fun i => Work.Diff.STE.one_le_yExp s hs (β i) (hβ i)
  have hsum_exp : ∑ i : Fin r, (Work.Diff.STE.yExp s (β i))⁻¹ = (r : ℝ) - 1 / 2 :=
    sum_yExp_inv_fin s hs β hβsum
  obtain ⟨_hiConv_summ, hyoung⟩ :=
    Work.Diff.STE.Comp.young_conv_lp hr d (fun i => Work.Diff.STE.yExp s (β i)) hp hsum_exp hsm
  -- ℓ¹ summability of each factor family, from the single moment bound
  have hdnorm : ∀ i : Fin r, Summable fun k : ι → ℤ => ‖d i k‖ := by
    intro i
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
      ((Work.Diff.STE.summable_moment_mul γ hmom (β i)).mul_left ((2 * Real.pi) ^ (β i)))
    calc ‖d i k‖ ≤ (2 * Real.pi * ‖k‖) ^ (β i) * ‖γ k‖ := hd i k
      _ = (2 * Real.pi) ^ (β i) * ((‖k‖ : ℝ) ^ (β i) * ‖γ k‖) := by rw [mul_pow]; ring
      _ ≤ (2 * Real.pi) ^ (β i) * ((1 + ‖k‖) ^ (β i) * ‖γ k‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (norm_nonneg k) (by linarith) _) (norm_nonneg _)
  have hprod := Work.Diff.STE.prod_seriesFun_iConv r d hr hdnorm
  -- the per-factor bound
  have hfac : ∀ i : Fin r,
      (∑' k : ι → ℤ, ‖d i k‖ ^ (Work.Diff.STE.yExp s (β i)))
          ^ ((Work.Diff.STE.yExp s (β i))⁻¹)
        ≤ (2 * Real.pi) ^ (β i) * (1 + Λ) ^ (1 - (β i : ℝ) / s)
          * (1 + Work.Diff.STE.CSq s γ) ^ ((β i : ℝ) / (2 * s)) := by
    intro i
    have hβi : β i ≤ s := hβ i
    have hpi : 1 ≤ Work.Diff.STE.yExp s (β i) := hp i
    have hmaj : Summable fun k : ι → ℤ =>
        ((‖k‖ : ℝ) ^ (β i) * ‖γ k‖) ^ (Work.Diff.STE.yExp s (β i)) :=
      Work.Diff.STE.summable_majorant_rpow γ hmom hΛ (β i) _ hpi
    have hpt : ∀ k : ι → ℤ, ‖d i k‖ ^ (Work.Diff.STE.yExp s (β i))
        ≤ (2 * Real.pi) ^ ((β i : ℝ) * (Work.Diff.STE.yExp s (β i)))
          * ((‖k‖ : ℝ) ^ (β i) * ‖γ k‖) ^ (Work.Diff.STE.yExp s (β i)) := by
      intro k
      have hdom2 : ‖d i k‖
          ≤ (2 * Real.pi) ^ (β i) * ((‖k‖ : ℝ) ^ (β i) * ‖γ k‖) := by
        have h := hd i k
        rw [mul_pow] at h
        calc ‖d i k‖ ≤ (2 * Real.pi) ^ (β i) * (‖k‖ : ℝ) ^ (β i) * ‖γ k‖ := h
          _ = (2 * Real.pi) ^ (β i) * ((‖k‖ : ℝ) ^ (β i) * ‖γ k‖) := by ring
      have h := Real.rpow_le_rpow (norm_nonneg _) hdom2
        (x := ‖d i k‖)
        (y := (2 * Real.pi) ^ (β i) * ((‖k‖ : ℝ) ^ (β i) * ‖γ k‖))
        (z := Work.Diff.STE.yExp s (β i)) (by linarith [hpi])
      rw [Real.mul_rpow (x := (2 * Real.pi) ^ (β i))
          (y := (‖k‖ : ℝ) ^ (β i) * ‖γ k‖) (z := Work.Diff.STE.yExp s (β i))
          (by positivity) (by positivity),
        ← Real.rpow_natCast (2 * Real.pi) (β i),
        ← Real.rpow_mul (x := 2 * Real.pi) (by positivity) (β i : ℝ)
          (Work.Diff.STE.yExp s (β i))] at h
      exact h
    have hcmp : (∑' k : ι → ℤ, ‖d i k‖ ^ (Work.Diff.STE.yExp s (β i)))
        ≤ (2 * Real.pi) ^ ((β i : ℝ) * (Work.Diff.STE.yExp s (β i)))
          * ∑' k : ι → ℤ, ((‖k‖ : ℝ) ^ (β i) * ‖γ k‖) ^ (Work.Diff.STE.yExp s (β i)) := by
      rw [← tsum_mul_left]
      exact Summable.tsum_le_tsum hpt (hsm i) (hmaj.mul_left _)
    have h2 : ((2 * Real.pi) ^ ((β i : ℝ) * (Work.Diff.STE.yExp s (β i)))
          * ∑' k : ι → ℤ, ((‖k‖ : ℝ) ^ (β i) * ‖γ k‖) ^ (Work.Diff.STE.yExp s (β i)))
          ^ ((Work.Diff.STE.yExp s (β i))⁻¹)
        = (2 * Real.pi) ^ (β i)
          * (∑' k : ι → ℤ, ((‖k‖ : ℝ) ^ (β i) * ‖γ k‖) ^ (Work.Diff.STE.yExp s (β i)))
              ^ ((Work.Diff.STE.yExp s (β i))⁻¹) := by
      rw [Real.mul_rpow (x := (2 * Real.pi) ^ ((β i : ℝ) * (Work.Diff.STE.yExp s (β i))))
          (y := ∑' k : ι → ℤ, ((‖k‖ : ℝ) ^ (β i) * ‖γ k‖) ^ (Work.Diff.STE.yExp s (β i)))
          (z := (Work.Diff.STE.yExp s (β i))⁻¹) (by positivity)
          (tsum_nonneg fun k => Real.rpow_nonneg (by positivity) _),
        ← Real.rpow_mul (x := 2 * Real.pi) (by positivity) ((β i : ℝ) * (Work.Diff.STE.yExp s (β i)))
          ((Work.Diff.STE.yExp s (β i))⁻¹)]
      congr 1
      have hyne : Work.Diff.STE.yExp s (β i) ≠ 0 :=
        Work.Diff.STE.yExp_ne_zero s hs _ hβi
      field_simp
      rw [Real.rpow_natCast]
    have hstep := (Real.rpow_le_rpow
        (tsum_nonneg fun k => Real.rpow_nonneg (norm_nonneg _) _) hcmp
      (y := (2 * Real.pi) ^ ((β i : ℝ) * (Work.Diff.STE.yExp s (β i)))
          * ∑' k : ι → ℤ, ((‖k‖ : ℝ) ^ (β i) * ‖γ k‖) ^ (Work.Diff.STE.yExp s (β i)))
      (z := (Work.Diff.STE.yExp s (β i))⁻¹)
      (inv_nonneg.mpr (by linarith [hpi]))).trans (le_of_eq h2)
    have hw := Work.Diff.STE.Comp.weighted_lp_le s (β i) hβi hs γ hΛ hQ
    have heq1 : (∑' k : ι → ℤ, ((‖k‖ : ℝ) ^ (β i) * ‖γ k‖) ^ (Work.Diff.STE.yExp s (β i)))
        = (∑' k : ι → ℤ, (‖γ k‖ * (‖k‖ : ℝ) ^ (β i))
            ^ ((2 * (s : ℝ)) / (2 * (s : ℝ) - (β i : ℝ)))) := by
      refine tsum_congr fun k => ?_
      rw [Work.Diff.STE.yExp_eq, mul_comm]
    have hw' : (∑' k : ι → ℤ, ((‖k‖ : ℝ) ^ (β i) * ‖γ k‖) ^ (Work.Diff.STE.yExp s (β i)))
          ^ ((Work.Diff.STE.yExp s (β i))⁻¹)
        ≤ (1 + Λ) ^ (1 - (β i : ℝ) / s) * (1 + Q) ^ ((β i : ℝ) / (2 * s)) := by
      rw [heq1, Work.Diff.STE.yExp_inv]
      exact hw
    have hle1 : (1 + Q) ^ ((β i : ℝ) / (2 * s))
        ≤ (1 + Work.Diff.STE.CSq s γ) ^ ((β i : ℝ) / (2 * s)) :=
      Real.rpow_le_rpow (by positivity) (by linarith [hQ_le]) (by positivity)
    have hfin : (2 * Real.pi) ^ (β i)
          * ((1 + Λ) ^ (1 - (β i : ℝ) / s) * (1 + Q) ^ ((β i : ℝ) / (2 * s)))
        ≤ (2 * Real.pi) ^ (β i)
          * ((1 + Λ) ^ (1 - (β i : ℝ) / s)
            * (1 + Work.Diff.STE.CSq s γ) ^ ((β i : ℝ) / (2 * s))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hle1 (Real.rpow_nonneg (by linarith [hΛ0]) _)) (by positivity)
    refine hstep.trans ((mul_le_mul_of_nonneg_left hw' (by positivity)).trans ?_)
    exact hfin.trans (le_of_eq (by ring))
  -- the product of the per-factor bounds
  have hmul : ∏ i : Fin r,
        ((2 * Real.pi) ^ (β i) * (1 + Λ) ^ (1 - (β i : ℝ) / s)
          * (1 + Work.Diff.STE.CSq s γ) ^ ((β i : ℝ) / (2 * s)))
      = (2 * Real.pi) ^ s * (1 + Λ) ^ (r - 1) * (1 + Work.Diff.STE.CSq s γ) ^ (1 / 2 : ℝ) := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    have h1 : ∏ i : Fin r, (2 * Real.pi) ^ (β i) = (2 * Real.pi) ^ s := by
      rw [Finset.prod_pow_eq_pow_sum, hβsum]
    have h2 : ∏ i : Fin r, (1 + Λ) ^ (1 - (β i : ℝ) / s) = (1 + Λ) ^ ((r : ℝ) - 1) := by
      rw [← Real.rpow_sum_of_pos (by linarith : (0 : ℝ) < 1 + Λ)]
      congr 1
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one, ← Finset.sum_div,
        show ∑ i : Fin r, ((β i : ℕ) : ℝ) = (s : ℝ) from by rw [← Nat.cast_sum, hβsum]]
      field_simp
    have h3 : ∏ i : Fin r, (1 + Work.Diff.STE.CSq s γ) ^ ((β i : ℝ) / (2 * s))
        = (1 + Work.Diff.STE.CSq s γ) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_sum_of_pos (by linarith : (0 : ℝ) < 1 + Work.Diff.STE.CSq s γ)]
      congr 1
      rw [← Finset.sum_div,
        show ∑ i : Fin r, ((β i : ℕ) : ℝ) = (s : ℝ) from by rw [← Nat.cast_sum, hβsum]]
      field_simp
    have hc : (↑r - 1 : ℝ) = ↑(r - 1) := by rw [Nat.cast_sub hr, Nat.cast_one]
    rw [h1, h2, h3, hc, Real.rpow_natCast]
  have hy2 : (∑' k : ι → ℤ, ‖Work.Diff.STE.Comp.iConv r d k‖ ^ 2) ^ (1 / 2 : ℝ)
      ≤ (2 * Real.pi) ^ s * (1 + Λ) ^ (r - 1) * (1 + Work.Diff.STE.CSq s γ) ^ (1 / 2 : ℝ) := by
    refine hyoung.trans ?_
    rw [← hmul]
    exact Finset.prod_le_prod₀ (fun i _ => Real.rpow_nonneg (tsum_nonneg fun k =>
      Real.rpow_nonneg (norm_nonneg _) _) _) fun i _ => hfac i
  have hsq : ∑' k : ι → ℤ, ‖Work.Diff.STE.Comp.iConv r d k‖ ^ 2
      ≤ ((2 * Real.pi) ^ s * (1 + Λ) ^ s) ^ 2 * (1 + Work.Diff.STE.CSq s γ) := by
    set A : ℝ := ∑' k : ι → ℤ, ‖Work.Diff.STE.Comp.iConv r d k‖ ^ 2 with hA
    have hA0 : 0 ≤ A := tsum_nonneg fun k => sq_nonneg _
    set B : ℝ := (2 * Real.pi) ^ s * (1 + Λ) ^ (r - 1) * (1 + Work.Diff.STE.CSq s γ) ^ (1 / 2 : ℝ)
      with hB
    have hA_sq : (A ^ (1 / 2 : ℝ)) ^ 2 = A := by
      rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hA0]
    have hZ : ((1 + Work.Diff.STE.CSq s γ) ^ (1 / 2 : ℝ)) ^ 2 = 1 + Work.Diff.STE.CSq s γ := by
      have h0 : (0 : ℝ) ≤ 1 + Work.Diff.STE.CSq s γ := by linarith [hCSq0]
      rw [← Real.sqrt_eq_rpow, Real.sq_sqrt h0]
    have hB_sq : B ^ 2 = ((2 * Real.pi) ^ s * (1 + Λ) ^ (r - 1)) ^ 2
        * (1 + Work.Diff.STE.CSq s γ) := by
      rw [hB, mul_pow, mul_pow, hZ]
    have hAB : A ^ (1 / 2 : ℝ) ≤ B := by rw [hA, hB]; exact hy2
    calc A = (A ^ (1 / 2 : ℝ)) ^ 2 := hA_sq.symm
      _ ≤ B ^ 2 := pow_le_pow_left₀ (Real.rpow_nonneg hA0 _) hAB 2
      _ = ((2 * Real.pi) ^ s * (1 + Λ) ^ (r - 1)) ^ 2 * (1 + Work.Diff.STE.CSq s γ) := hB_sq
      _ ≤ ((2 * Real.pi) ^ s * (1 + Λ) ^ s) ^ 2 * (1 + Work.Diff.STE.CSq s γ) := by
          refine mul_le_mul_of_nonneg_right ?_ (by linarith [hCSq0])
          refine pow_le_pow_left₀ (by positivity) ?_ 2
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hΛ1 ((Nat.sub_le _ _).trans hrs))
            (pow_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi) s)
  have hpt : ∀ x : ι → ℝ, ‖∏ i : Fin r, Work.Diff.STE.seriesFun (d i) x‖ ^ 2
      = ‖Work.Diff.STE.seriesFun (Work.Diff.STE.Comp.iConv r d) x‖ ^ 2 := by
    intro x
    rw [show (∏ i : Fin r, Work.Diff.STE.seriesFun (d i) x)
        = Work.Diff.STE.seriesFun (Work.Diff.STE.Comp.iConv r d) x from congrFun hprod x]
  calc ∫ x in Work.Diff.STE.unitCube, ‖∏ i : Fin r, Work.Diff.STE.seriesFun (d i) x‖ ^ 2
      = ∫ x in Work.Diff.STE.unitCube,
          ‖Work.Diff.STE.seriesFun (Work.Diff.STE.Comp.iConv r d) x‖ ^ 2 :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ∑' k : ι → ℤ, ‖Work.Diff.STE.Comp.iConv r d k‖ ^ 2 :=
        Work.Diff.STE.ens_integral_normSq_seriesFun _ (Work.Diff.STE.summable_iConv r d hdnorm)
    _ ≤ ((2 * Real.pi) ^ s * (1 + Λ) ^ s) ^ 2 * (1 + Work.Diff.STE.CSq s γ) := hsq

end Work.Diff.STE.Comp3
