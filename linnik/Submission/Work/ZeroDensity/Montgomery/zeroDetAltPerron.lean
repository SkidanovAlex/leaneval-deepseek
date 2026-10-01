import Mathlib
import Submission.Work.ZeroDensity.Montgomery.zeroDetAltDefs
import Submission.Work.ZeroDensity.Montgomery.zeroDetAltPerronAux
import Submission.Work.ZeroDensity.Montgomery.muTrunc_LSeries
import Submission.Work.ZeroDensity.Montgomery.convolution_charSeq_muTrunc
import Submission.Work.ZeroDensity.Montgomery.perronTerm_bounds
import Submission.Work.ZeroDensity.Montgomery.integral_perronTerm

namespace Work.ZeroDensity.Montgomery

open scoped Classical BigOperators
open MeasureTheory

/-- **Perron's formula (inverse Mellin transform of the exponential kernel) for the smoothed
Möbius sum.**  With `mCoef X n = Σ_{d | n, d ≤ X} μ(d)` and
`MX χ X s = Σ_{n ≤ ⌊X⌋₊} μ(n)χ(n)n^{-s}`, for `c > 0` and `c > 1 - Re ρ`,
`(1/2π) ∫_ℝ L(ρ+c+iu,χ)·M_X(ρ+c+iu,χ)·Γ(c+iu)·Y^{c+iu} du = Σ_{n≥1} m_n χ(n) n^{-ρ} e^{-n/Y}`.
The integrand is `PhiNaive χ ρ X Y` at `w = c + iu` (the vertical line `Re w = c`, `dw = i du`),
and the line lies in `Re s > 1`, so everything converges absolutely.

Sketch: `L(s,χ) = LSeries (χ ·) s` for `Re s > 1`
(`DirichletCharacter.LFunction_eq_LSeries`), `MX χ X s` is a finite sum, so the product is the
absolutely convergent series `Σ_n mCoef X n χ(n) n^{-s}`; integrate termwise against the inverse
Mellin transform of `Γ` (`Work.LinnikAreas.Density4.mellin_kernel_exp`, which says
`(1/2π)∫_ℝ y^{-(c+iu)}Γ(c+iu)du = e^{-y}` for `y > 0`), with `y = n/Y`; the exchange of sum and
integral is justified by `|mCoef X n| ≤ n.divisors.card` and `Re ρ + c > 1`. -/
theorem zeroDetAltPerron {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ)
    (hρ : 0 < ρ.re) (X Y c : ℝ) (hc : 0 < c) (hc2 : 1 - ρ.re < c) (hY : 0 < Y) :
    (1 / (2 * Real.pi)) * ∫ u : ℝ,
        Work.ZeroDensity.Montgomery.PhiNaive χ ρ X Y ((c : ℂ) + (u : ℂ) * Complex.I)
      = ∑' n : ℕ, Work.ZeroDensity.Montgomery.mCoef X n * χ (n : ZMod q) * (n : ℂ) ^ (-ρ)
          * Complex.exp (-(n : ℂ) / (Y : ℂ)) := by
  classical
  -- ### Step 1: the integrand is the absolutely convergent Dirichlet series `Σ_n perronTerm n u`.
  have hpt : ∀ u : ℝ, PhiNaive χ ρ X Y ((c : ℂ) + (u : ℂ) * Complex.I)
      = ∑' n : ℕ, perronTerm χ ρ X Y c n u := by
    intro u
    have hsw : 1 < (ρ + ((c : ℂ) + (u : ℂ) * Complex.I)).re := by
      have hre : (ρ + ((c : ℂ) + (u : ℂ) * Complex.I)).re = ρ.re + c := by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
          Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
      rw [hre]; linarith
    have hbχ : LSeriesSummable (charSeq χ) (ρ + ((c : ℂ) + (u : ℂ) * Complex.I)) :=
      LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => by
        rw [charSeq]; exact χ.norm_le_one (n : ZMod q)) hsw
    have hbμ : LSeriesSummable (muTrunc χ X) (ρ + ((c : ℂ) + (u : ℂ) * Complex.I)) :=
      LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => by
        rw [muTrunc]; split_ifs with h
        · rw [norm_mul]
          have hmob : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
            rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
          calc ‖(ArithmeticFunction.moebius n : ℂ)‖ * ‖χ (n : ZMod q)‖
              ≤ 1 * 1 := by
                exact mul_le_mul hmob (χ.norm_le_one (n : ZMod q)) (norm_nonneg _) zero_le_one
            _ = 1 := mul_one 1
        · simp) hsw
    have hconv : LSeries.convolution (charSeq χ) (muTrunc χ X)
        = fun n : ℕ => mCoef X n * χ (n : ZMod q) :=
      funext (convolution_charSeq_muTrunc χ X)
    have hprod : DirichletCharacter.LFunction χ (ρ + ((c : ℂ) + (u : ℂ) * Complex.I))
          * MX χ X (ρ + ((c : ℂ) + (u : ℂ) * Complex.I))
        = ∑' n : ℕ, mCoef X n * χ (n : ZMod q)
            * (n : ℂ) ^ (-(ρ + ((c : ℂ) + (u : ℂ) * Complex.I))) := by
      rw [DirichletCharacter.LFunction_eq_LSeries χ hsw, ← charSeq_def χ]
      rw [← muTrunc_LSeries χ X (ρ + ((c : ℂ) + (u : ℂ) * Complex.I))]
      rw [← LSeries_convolution' hbχ hbμ, hconv, LSeries]
      refine tsum_congr fun n => ?_
      rw [LSeries.term_def₀ (by simp [mCoef_zero])]
    rw [PhiNaive, hprod]
    rw [← tsum_mul_right, ← tsum_mul_right]
    refine tsum_congr fun n => ?_
    simp only [perronTerm]
  -- ### Step 2: exchange the sum and the vertical integral.
  obtain ⟨hInt, hSumm⟩ := perronTerm_bounds χ ρ X Y c hc hc2 hY
  have hswap : (∫ u : ℝ, ∑' n : ℕ, perronTerm χ ρ X Y c n u)
      = ∑' n : ℕ, (∫ u : ℝ, perronTerm χ ρ X Y c n u) :=
    (MeasureTheory.integral_tsum_of_summable_integral_norm hInt hSumm).symm
  have hcongr : (∫ u : ℝ, PhiNaive χ ρ X Y ((c : ℂ) + (u : ℂ) * Complex.I))
      = ∫ u : ℝ, ∑' n : ℕ, perronTerm χ ρ X Y c n u :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
  -- ### Step 3: evaluate each term by the inverse Mellin transform of `Γ`.
  have hterm : ∀ n : ℕ, (∫ u : ℝ, perronTerm χ ρ X Y c n u)
      = 2 * Real.pi * (mCoef X n * χ (n : ZMod q) * (n : ℂ) ^ (-ρ)
          * Complex.exp (-(n : ℂ) / (Y : ℂ))) := by
    intro n
    rcases eq_or_ne n 0 with hn | hn
    · subst hn
      have hρne : ρ ≠ 0 := fun h => by rw [h] at hρ; simp at hρ
      have hz : (fun u : ℝ => perronTerm χ ρ X Y c 0 u) = fun _ => (0 : ℂ) := by
        funext u
        simp [perronTerm, mCoef_zero]
      have h0pow : (0 : ℂ) ^ (-ρ) = 0 := Complex.zero_cpow (neg_ne_zero.mpr hρne)
      rw [hz, integral_zero]
      simp [mCoef_zero, h0pow]
    · have := integral_perronTerm χ ρ X Y c hc hY hn
      simpa only [perronTerm] using this
  have htsum : (∑' n : ℕ, (∫ u : ℝ, perronTerm χ ρ X Y c n u))
      = ∑' n : ℕ, 2 * Real.pi * (mCoef X n * χ (n : ZMod q) * (n : ℂ) ^ (-ρ)
          * Complex.exp (-(n : ℂ) / (Y : ℂ))) :=
    tsum_congr hterm
  -- ### Step 4: the scalar `1/(2π)` cancels the `2π`.
  have h2pi : (2 : ℂ) * (Real.pi : ℂ) ≠ 0 := by
    refine mul_ne_zero (by norm_num) ?_
    exact_mod_cast Real.pi_ne_zero
  calc (1 / (2 * Real.pi)) * ∫ u : ℝ, PhiNaive χ ρ X Y ((c : ℂ) + (u : ℂ) * Complex.I)
      = (1 / (2 * Real.pi)) * ∑' n : ℕ, (∫ u : ℝ, perronTerm χ ρ X Y c n u) := by
        rw [hcongr, hswap]
    _ = (1 / (2 * Real.pi)) * ∑' n : ℕ, 2 * Real.pi *
          (mCoef X n * χ (n : ZMod q) * (n : ℂ) ^ (-ρ)
            * Complex.exp (-(n : ℂ) / (Y : ℂ))) := by rw [htsum]
    _ = ∑' n : ℕ, mCoef X n * χ (n : ZMod q) * (n : ℂ) ^ (-ρ)
          * Complex.exp (-(n : ℂ) / (Y : ℂ)) := by
        rw [← tsum_mul_left]
        refine tsum_congr fun n => ?_
        rw [one_div, ← mul_assoc, inv_mul_cancel₀ h2pi, one_mul]

end Work.ZeroDensity.Montgomery
