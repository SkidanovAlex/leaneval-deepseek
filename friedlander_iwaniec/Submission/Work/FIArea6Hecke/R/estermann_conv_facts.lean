/-
# `Submission.Work.FIArea6Hecke.R.estermann_conv_facts`

Facts about the four-fold Dirichlet convolution
`Conv χ₁ χ₂ = λ_1 ⍟ λ_{χ₁} ⍟ λ_{χ₂} ⍟ λ_{χ₁χ₂}` of Hecke eigenvalue sequences of `ℚ(i)`, the
coefficient sequence of the product `L(s,1)·L(s,χ₁)·L(s,χ₂)·L(s,χ₁χ₂)`:

* `Conv χ₁ χ₂ 1 = 1`;
* `0 ≤ (Conv χ₁ χ₂ n).re` for `n > 0`;
* the abscissa of absolute convergence of the real coefficient sequence is `< 2` (in fact `≤ 1`,
  since `Conv` is a Dirichlet convolution of four sequences each summable for `re s > 1`);
* the Dirichlet series of the real coefficients is the four-fold product of Hecke `L`-series.

The first two and the Dirichlet-series identity are the content of
`S16Hecke.hecke_prod_coeff_nonneg`; the abscissa statement is proved here from the summability of
the four Hecke eigenvalue sequences (`S16Hecke.summable_heckeLam`) and closure of `LSeriesSummable`
under Dirichlet convolution.
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.hecke_prod_coeff_nonneg

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open LSeries
open scoped BigOperators
open Work.FIArea5.S16Hecke

noncomputable section

/-! ## The abscissa of absolute convergence -/

/-- The abscissa of absolute convergence of the real-part coefficients of `Conv χ₁ χ₂` is at
most `1`.  Indeed `Conv` is the four-fold Dirichlet convolution of Hecke eigenvalue sequences,
each of which is summable for `re s > 1` (`summable_heckeLam`), and taking real parts only
decreases the absolute values of the coefficients. -/
theorem estermannConv_abscissa_le_one {chi₁ chi₂ : GaussianInt → ℂ}
    (hb₁ : ∀ z : GaussianInt, ‖chi₁ z‖ ≤ 1) (hb₂ : ∀ z : GaussianInt, ‖chi₂ z‖ ≤ 1) :
    LSeries.abscissaOfAbsConv (fun n : ℕ => ((Conv chi₁ chi₂ n).re : ℂ)) ≤ 1 := by
  refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (fun y hy => ?_)
  have hyre : (1 : ℝ) < ((y : ℂ)).re := by simpa using hy
  have h0 : LSeriesSummable (heckeLam (fun _ => (1 : ℂ)) 0) (y : ℂ) :=
    summable_heckeLam _ (fun z => by simp) hyre
  have h1 : LSeriesSummable (heckeLam chi₁ 0) (y : ℂ) :=
    summable_heckeLam _ hb₁ hyre
  have h2 : LSeriesSummable (heckeLam chi₂ 0) (y : ℂ) :=
    summable_heckeLam _ hb₂ hyre
  have h3 : LSeriesSummable (heckeLam (fun z => chi₁ z * chi₂ z) 0) (y : ℂ) :=
    summable_heckeLam _
      (fun z => by rw [norm_mul]; exact mul_le_one₀ (hb₁ z) (norm_nonneg _) (hb₂ z)) hyre
  have hConv : LSeriesSummable (Conv chi₁ chi₂) (y : ℂ) :=
    ((h0.convolution h1).convolution h2).convolution h3
  rw [LSeriesSummable] at hConv ⊢
  refine Summable.of_norm_bounded hConv.norm (fun n => ?_)
  exact LSeries.norm_term_le (↑y)
    (by rw [Complex.norm_real, Real.norm_eq_abs]; exact Complex.abs_re_le_norm _)

/-! ## The Dirichlet-series identity -/

/-- The Dirichlet series of the real coefficients of `Conv χ₁ χ₂` factors as the four-fold
product of the Hecke `L`-series of `1`, `χ₁`, `χ₂` and `χ₁χ₂` on `re s > 1`. -/
theorem estermannConv_tsum_eq {chi₁ chi₂ : GaussianInt → ℂ}
    (hre₁ : ∀ z : GaussianInt, chi₁ z = star (chi₁ z))
    (hre₂ : ∀ z : GaussianInt, chi₂ z = star (chi₂ z))
    (hb₁ : ∀ z : GaussianInt, ‖chi₁ z‖ ≤ 1) (hb₂ : ∀ z : GaussianInt, ‖chi₂ z‖ ≤ 1)
    (s : ℂ) (hs : 1 < s.re) :
    (∑' n : ℕ, ((Conv chi₁ chi₂ n).re : ℂ) * (n : ℂ) ^ (-s))
      = heckeLSeries (fun _ => (1 : ℂ)) 0 s * heckeLSeries chi₁ 0 s * heckeLSeries chi₂ 0 s *
        heckeLSeries (fun z => chi₁ z * chi₂ z) 0 s := by
  have hConv0 : Conv chi₁ chi₂ 0 = 0 := by simp [Conv, LSeries.convolution_def]
  have hre : ∀ n, (Conv chi₁ chi₂ n) = (((Conv chi₁ chi₂ n).re) : ℂ) :=
    fun n => Complex.ext rfl (by rw [Complex.ofReal_im, Conv_im chi₁ chi₂ hre₁ hre₂ n])
  have hterm : (∑' n : ℕ, ((Conv chi₁ chi₂ n).re : ℂ) * (n : ℂ) ^ (-s))
      = LSeries (Conv chi₁ chi₂) s := by
    rw [show LSeries (Conv chi₁ chi₂) s = ∑' n, Conv chi₁ chi₂ n * (n : ℂ) ^ (-s) from by
          rw [LSeries]; exact tsum_congr (fun n => LSeries.term_def₀ hConv0 s n)]
    exact tsum_congr (fun n => by rw [hre n, Complex.ofReal_re])
  rw [hterm]
  have hsumm0 : LSeriesSummable (heckeLam (fun _ => (1 : ℂ)) 0) s :=
    summable_heckeLam _ (by intro z; simp) hs
  have hsumm1 : LSeriesSummable (heckeLam chi₁ 0) s := summable_heckeLam _ hb₁ hs
  have hsumm2 : LSeriesSummable (heckeLam chi₂ 0) s := summable_heckeLam _ hb₂ hs
  have hsumm3 : LSeriesSummable (heckeLam (fun z => chi₁ z * chi₂ z) 0) s :=
    summable_heckeLam _
      (fun z => by rw [norm_mul]; exact mul_le_one₀ (hb₁ z) (norm_nonneg _) (hb₂ z)) hs
  have e1 := LSeries_convolution' hsumm0 hsumm1
  have e2 := LSeries_convolution' (hsumm0.convolution hsumm1) hsumm2
  have e3 := LSeries_convolution' ((hsumm0.convolution hsumm1).convolution hsumm2) hsumm3
  rw [Conv, e3, e2, e1]
  simp only [heckeLSeries]

/-! ## The main theorem -/

/-- The Dirichlet-convolution coefficients `Conv χ₁ χ₂` of the fourfold Hecke product
`L(s,1)·L(s,χ₁)·L(s,χ₂)·L(s,χ₁χ₂)`: value `1` at `n = 1`, non-negative real part, abscissa of
absolute convergence `< 2`, and the Dirichlet-series identity on `re s > 1`. -/
theorem estermann_conv_facts {chi₁ chi₂ : GaussianInt → ℂ}
    (h1₁ : chi₁ 1 = 1) (h1₂ : chi₂ 1 = 1)
    (hre₁ : ∀ z : GaussianInt, chi₁ z = star (chi₁ z))
    (hre₂ : ∀ z : GaussianInt, chi₂ z = star (chi₂ z))
    (hmul₁ : ∀ z w : GaussianInt, chi₁ (z * w) = chi₁ z * chi₁ w)
    (hmul₂ : ∀ z w : GaussianInt, chi₂ (z * w) = chi₂ z * chi₂ w)
    (hb₁ : ∀ z : GaussianInt, ‖chi₁ z‖ ≤ 1) (hb₂ : ∀ z : GaussianInt, ‖chi₂ z‖ ≤ 1) :
    Work.FIArea5.S16Hecke.Conv chi₁ chi₂ 1 = 1 ∧
      (∀ n : ℕ, 0 < n → 0 ≤ (Work.FIArea5.S16Hecke.Conv chi₁ chi₂ n).re) ∧
      LSeries.abscissaOfAbsConv (fun n : ℕ => ((Work.FIArea5.S16Hecke.Conv chi₁ chi₂ n).re : ℂ)) < 2 ∧
      ∀ s : ℂ, 1 < s.re →
        (∑' n : ℕ, ((Work.FIArea5.S16Hecke.Conv chi₁ chi₂ n).re : ℂ) * (n : ℂ) ^ (-s))
          = Work.FIArea5.S16Hecke.heckeLSeries (fun _ => (1 : ℂ)) 0 s *
            Work.FIArea5.S16Hecke.heckeLSeries chi₁ 0 s *
            Work.FIArea5.S16Hecke.heckeLSeries chi₂ 0 s *
            Work.FIArea5.S16Hecke.heckeLSeries (fun z => chi₁ z * chi₂ z) 0 s := by
  refine ⟨Conv_one chi₁ chi₂ h1₁ h1₂, ?_, ?_, ?_⟩
  · intro n hn
    exact Conv_re_nonneg chi₁ chi₂ h1₁ h1₂ hre₁ hre₂ hmul₁ hmul₂ hb₁ hb₂ n hn
  · exact lt_of_le_of_lt (estermannConv_abscissa_le_one hb₁ hb₂) (by norm_num)
  · intro s hs
    exact estermannConv_tsum_eq hre₁ hre₂ hb₁ hb₂ s hs

end

end Work.FIArea6Hecke.R
