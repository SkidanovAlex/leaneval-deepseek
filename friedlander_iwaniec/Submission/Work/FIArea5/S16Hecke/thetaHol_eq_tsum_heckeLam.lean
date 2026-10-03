import Mathlib
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIArea5.S16Hecke.Basic
import Submission.Work.FIArea5.S16Hecke.thetaSph_eq_tsum_heckeLam
import Submission.Work.FIArea5.S16Hecke.rpow_mul_exp_neg_bounded
import Submission.Work.FIArea5.S16.summable_int_prod_exp_neg_sq_add

set_option autoImplicit false

namespace Work.FIArea5.S16Hecke

open Finset
open scoped BigOperators
open Work.FIPlan

noncomputable section

/-! ## Auxiliary facts -/

/-- **The exponent bookkeeping of the holomorphic theta series.**  For natural `n, m` one has
`n^{m/2} = (√n)^m` (a `ℂ`-power on the left, an ordinary power on the right).  This is the identity
that converts the `ψ`-normalised Hecke eigenvalue sum into the `z^m`-weighted sum of `thetaHol`. -/
lemma cpow_half_eq_sqrt_pow (n m : ℕ) :
    (n : ℂ) ^ ((m : ℂ) / 2) = (((Real.sqrt (n : ℝ)) : ℝ) : ℂ) ^ m := by
  have hnR : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have hreal : (Real.sqrt (n:ℝ))^m = (n:ℝ)^((m:ℝ)/2) := by
    rw [← Real.rpow_natCast (Real.sqrt (n:ℝ)) m]
    rw [Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul hnR (1/2) (↑m)]
    rw [show (1/2:ℝ) * (↑m) = (m:ℝ)/2 by ring]
  calc (n : ℂ) ^ ((m : ℂ) / 2)
      = ((n:ℝ):ℂ) ^ (((m:ℝ)/2 : ℝ) : ℂ) := by
        rw [Complex.ofReal_natCast]
        congr 1
        push_cast; ring
    _ = Complex.ofReal ((n:ℝ)^((m:ℝ)/2)) := (Complex.ofReal_cpow hnR ((m:ℝ)/2)).symm
    _ = Complex.ofReal ((Real.sqrt (n:ℝ))^m) := by rw [hreal]
    _ = (((Real.sqrt (n : ℝ)) : ℝ) : ℂ) ^ m := Complex.ofReal_pow _ _

/-- **The pointwise identity underlying `thetaHol_eq_tsum_heckeLam`.**  For `n > 0`, a Gaussian
integer `z` with `|z|² = n`, and `‖χ‖ ≤ 1` (not needed here), one has
`n^{m/2}·ψ(z) = χ(z)·z^m`, because `z/|z| = z/√n` and `n^{m/2} = (√n)^m`. -/
lemma cpow_half_mul_psi (chi : GaussianInt → ℂ) (m : ℕ) {n : ℕ} (hn : 0 < n)
    {z : GaussianInt} (hz : gnorm z = n) :
    (n : ℂ) ^ ((m : ℂ) / 2) * psi chi (m : ℤ) z = chi z * (z.toComplex) ^ m := by
  have hnR : (0:ℝ) < (n:ℝ) := Nat.cast_pos.mpr hn
  have hS : (((Real.sqrt (n:ℝ)) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    exact ne_of_gt (Real.sqrt_pos_of_pos hnR)
  have hkey : (((Real.sqrt (n:ℝ)) : ℝ) : ℂ)
      * (z.toComplex / (((Real.sqrt (n:ℝ)) : ℝ) : ℂ)) = z.toComplex := by
    rw [mul_div_assoc', mul_div_cancel_left₀ z.toComplex hS]
  calc (n : ℂ) ^ ((m : ℂ) / 2) * psi chi (m : ℤ) z
      = (n : ℂ) ^ ((m : ℂ) / 2)
          * (chi z * (z.toComplex / (((Real.sqrt (n:ℝ)) : ℝ) : ℂ))^m) := by
          rw [psi, hz, zpow_natCast]
    _ = ((((Real.sqrt (n:ℝ)) : ℝ) : ℂ))^m
          * (chi z * (z.toComplex / (((Real.sqrt (n:ℝ)) : ℝ) : ℂ))^m) := by
          rw [cpow_half_eq_sqrt_pow n m]
    _ = chi z * ((((Real.sqrt (n:ℝ)) : ℝ) : ℂ)^m
          * (z.toComplex / (((Real.sqrt (n:ℝ)) : ℝ) : ℂ))^m) := by ring
    _ = chi z * ((((Real.sqrt (n:ℝ)) : ℝ) : ℂ)
          * (z.toComplex / (((Real.sqrt (n:ℝ)) : ℝ) : ℂ)))^m := by rw [mul_pow]
    _ = chi z * (z.toComplex)^m := by rw [hkey]

/-- Summability over `ℤ[i]` of the polynomial-weighted Gaussian
`e^{-πu|z|²}(1+|z|²)^m`, the majorant for the terms of the holomorphic theta series. -/
lemma summable_gnorm_weight {u : ℝ} (hu : 0 < u) (m : ℕ) :
    Summable (fun z : GaussianInt =>
      Real.exp (-(Real.pi * u * (gnorm z : ℝ))) * (1 + (gnorm z : ℝ))^m) := by
  have hgauss : Summable (fun p : ℤ × ℤ =>
      Real.exp (-(Real.pi * u) * ((p.1 : ℝ)^2 + (p.2 : ℝ)^2)) *
      (1 + (p.1 : ℝ)^2 + (p.2 : ℝ)^2)^m) := by
    refine (Work.FIArea5.S16.summable_int_prod_exp_neg_sq_add (c := Real.pi * u)
      (by positivity) 0 m).congr (fun p => ?_)
    obtain ⟨a, b⟩ := p
    simp only [zero_mul, add_zero]
  rw [summable_gaussian_iff]
  refine hgauss.congr (fun p => ?_)
  obtain ⟨a, b⟩ := p
  rw [gnorm_mk_cast]
  have harg : -(Real.pi * u) * ((a:ℝ)^2 + (b:ℝ)^2)
      = -(Real.pi * u * ((a:ℝ)^2 + (b:ℝ)^2)) := by ring
  rw [harg]
  congr 1
  ring

/-- A primary Gaussian integer has positive norm (its norm is odd). -/
lemma gnorm_pos_of_isPrimary {z : GaussianInt} (hz : IsPrimary z) : 0 < gnorm z := by
  obtain ⟨k, hk⟩ := isPrimary_odd_gnorm hz
  omega

/-! ## The theorem -/

/-- **The holomorphic theta series is the generating function of the Hecke eigenvalues.**
`H(u) = Σ_{z primary} χ(z) z^m e^{-πu|z|²} = Σ_n n^{m/2} λ(n) e^{-πun}`; this is the identity
through which the Mellin transform of `thetaHol` becomes the Hecke `L`-function at `s - m/2`
(`mellin_thetaHol`). -/
theorem thetaHol_eq_tsum_heckeLam (chi : GaussianInt → ℂ) (m : ℕ)
    (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {u : ℝ} (hu : 0 < u) :
    thetaHol chi m u
      = ∑' n : ℕ, (n : ℂ) ^ ((m : ℂ) / 2) * heckeLam chi (m : ℤ) n
          * Complex.exp (-(Real.pi * u * (n : ℝ))) := by
  classical
  have hg : Summable (fun z : GaussianInt =>
      Real.exp (-(Real.pi * u * (gnorm z : ℝ))) * (1 + (gnorm z : ℝ))^m) :=
    summable_gnorm_weight hu m
  set f : GaussianInt → ℂ := fun z =>
    if IsPrimary z then chi z * (z.toComplex)^m * Complex.exp (-Real.pi * u * (gnorm z : ℝ))
    else 0 with hf
  have hfsum : Summable f := by
    refine Summable.of_norm_bounded hg (fun z => ?_)
    have hfz : f z = (if IsPrimary z then chi z * (z.toComplex)^m
        * Complex.exp (-Real.pi * u * (gnorm z : ℝ)) else 0) := rfl
    rw [hfz]
    by_cases hz : IsPrimary z
    · rw [if_pos hz]
      have h1 : ‖chi z‖ ≤ 1 := hchi z
      have h2 : ‖(z.toComplex)^m‖ ≤ (1 + (gnorm z : ℝ))^m := by
        rw [norm_pow, norm_toComplex]
        apply pow_le_pow_left₀ (Real.sqrt_nonneg _)
        nlinarith [Real.sq_sqrt (Nat.cast_nonneg (gnorm z) : (0:ℝ) ≤ (gnorm z : ℝ)),
          sq_nonneg (Real.sqrt (gnorm z : ℝ) - 1/2), Real.sqrt_nonneg (gnorm z : ℝ)]
      calc ‖chi z * (z.toComplex)^m * Complex.exp (-Real.pi * u * (gnorm z : ℝ))‖
          = ‖chi z‖ * ‖(z.toComplex)^m‖
              * Real.exp (-(Real.pi * u * (gnorm z : ℝ))) := by
            rw [norm_mul, norm_mul, norm_exp_theta]
        _ ≤ 1 * (1 + (gnorm z : ℝ))^m * Real.exp (-(Real.pi * u * (gnorm z : ℝ))) := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (by positivity) zero_le_one)
              (Real.exp_nonneg _)
        _ = Real.exp (-(Real.pi * u * (gnorm z : ℝ))) * (1 + (gnorm z : ℝ))^m := by ring
    · rw [if_neg hz, norm_zero]
      positivity
  have htheta : thetaHol chi m u = ∑' z : GaussianInt, f z := rfl
  rw [htheta, ← (hfsum.hasSum.tsum_fiberwise (gnorm : GaussianInt → ℕ)).tsum_eq]
  refine tsum_congr (fun n => ?_)
  rw [_root_.tsum_subtype (gnorm ⁻¹' {n}) f]
  have hstep1 : (∑' z : GaussianInt, (gnorm ⁻¹' {n}).indicator f z)
      = ∑' z : GaussianInt,
          (if IsPrimary z ∧ gnorm z = n then
            chi z * (z.toComplex)^m * Complex.exp (-Real.pi * u * (gnorm z : ℝ)) else 0) := by
    refine tsum_congr (fun z => ?_)
    rw [Set.indicator_apply]
    simp only [Set.mem_preimage, Set.mem_singleton_iff, hf]
    by_cases hp : IsPrimary z <;> by_cases hgn : gnorm z = n <;> simp [hp, hgn]
  rw [hstep1]
  set S : Finset GaussianInt := (gBox (n : ℤ)).filter (fun z => IsPrimary z ∧ gnorm z = n) with hS
  have hbound0 : ∀ z ∉ S,
      (if IsPrimary z ∧ gnorm z = n then
        chi z * (z.toComplex)^m * Complex.exp (-Real.pi * u * (gnorm z : ℝ)) else 0) = 0 := by
    intro z hz
    rw [if_neg]
    intro h
    apply hz
    rw [hS, Finset.mem_filter]
    refine ⟨?_, h⟩
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have hz0 : z = 0 := by
        have h1 : z.re ^ 2 + z.im ^ 2 = 0 := by
          have h2' := gnorm_cast_eq z
          rw [h.2] at h2'
          simpa using h2'.symm
        have hre : z.re = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
        have him : z.im = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
        exact Zsqrtd.ext hre him
      rw [hz0]
      rw [mem_gBox_iff]
      simp
    · exact mem_gBox_of_gnorm_le (by exact_mod_cast hn) (by rw [h.2])
  rw [tsum_eq_sum (s := S) hbound0]
  have hSval : ∀ z ∈ S, IsPrimary z ∧ gnorm z = n := by
    intro z hz
    rw [hS, Finset.mem_filter] at hz
    exact hz.2
  have hnpos : ∀ z ∈ S, 0 < n := by
    intro z hz
    rw [← (hSval z hz).2]
    exact gnorm_pos_of_isPrimary (hSval z hz).1
  -- simplify the indicator `if`
  trans ∑ z ∈ S, chi z * (z.toComplex)^m * Complex.exp (-Real.pi * u * (n : ℝ))
  · refine Finset.sum_congr rfl (fun z hz => ?_)
    rw [if_pos (hSval z hz), (hSval z hz).2]
  -- factor out the exponential
  rw [← Finset.sum_mul]
  have hkey : ∑ z ∈ S, chi z * (z.toComplex)^m = (n : ℂ) ^ ((m : ℂ) / 2) * heckeLam chi (m : ℤ) n := by
    rw [show heckeLam chi (m : ℤ) n = ∑ z ∈ S, psi chi (m : ℤ) z from by rw [hS]; rfl]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun z hz => ?_)
    rw [← cpow_half_mul_psi chi m (hnpos z hz) (hSval z hz).2]
  rw [hkey]
  congr 1
  congr 1
  ring

end
end Work.FIArea5.S16Hecke
