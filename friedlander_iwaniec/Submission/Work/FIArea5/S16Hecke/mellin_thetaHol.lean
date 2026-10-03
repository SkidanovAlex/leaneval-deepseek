/-
# `Submission.Work.FIArea5.S16Hecke.mellin_thetaHol`

The **Mellin step** of Hecke's proof of the functional equation of the Hecke `L`-function of
`ℚ(i)` (*FI* §16, step (2.4) of the theta chapter; see `FIArea5/ROADMAP_HeckeL.md`):

  `∫_0^∞ thetaHol χ m u · u^{s-1} du = Γ(s)·π^{-s}·L(s - m/2, ψ)`,  `ψ(z) = χ(z)(z/|z|)^m`,

for `re s > 1 + m/2`.

The integral is written as a Mellin transform.  The proof has three inputs:

* `thetaHol_eq_tsum_heckeLam` — the holomorphic theta series is the generating function
  `Σ_n n^{m/2}λ(n)e^{-πun}` of the Hecke eigenvalues (`λ(n) = Σ_{|z|²=n, z primary} ψ(z)`,
  and `z^m = |z|^m ψ(z)/χ(z) = n^{m/2}(z/|z|)^m` on primary `z` of norm `n`);
* `mellin_tsum_exp` — the term-by-term Mellin transform of a Dirichlet-type exponential series
  `Σ_n w_n e^{-cun}`: `∫_0^∞ (Σ_n w_n e^{-cun})u^{s-1}du = Γ(s)c^{-s}Σ_n w_n n^{-s}`,
  valid whenever `Σ_n ‖w_n‖n^{-σ}` converges (`σ = re s > 0`);
* the elementary summability of `‖λ(n)‖n^{m/2-σ} ≪ τ(n)n^{m/2-σ}` for `σ > 1 + m/2`
  (`heckeLam_bound`, `summable_card_divisors_mul_rpow_neg`).
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea5.S16Hecke.Basic
import Submission.Work.FIArea5.S16Hecke.heckeLam_bound
import Submission.Work.FIArea5.S16Hecke.summable_card_divisors_mul_rpow_neg
import Submission.Work.FIArea5.S16Hecke.rpow_mul_exp_neg_bounded
import Submission.Work.FIArea5.S16Hecke.mellin_tsum_exp
import Submission.Work.FIArea5.S16Hecke.thetaHol_eq_tsum_heckeLam

namespace Work.FIArea5.S16Hecke

open Finset
open scoped BigOperators
open Work.FIPlan

noncomputable section

/-! ## Elementary auxiliary facts -/


/-- `‖(n : ℂ)^{m/2}‖ = n^{m/2}` for `n > 0`: the complex power of a positive real number has
modulus the real power of its real part. -/
private lemma norm_cpow_half (n : ℕ) (hn : 0 < n) (m : ℕ) :
    ‖(n : ℂ) ^ ((m : ℂ) / 2)‖ = (n : ℝ) ^ ((m : ℝ) / 2) := by
  have hmain : ‖(((n : ℝ) : ℂ)) ^ ((m : ℂ) / 2)‖ = (n : ℝ) ^ ((m : ℝ) / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr hn) ((m : ℂ) / 2)]
    congr 1
    simp
  simpa only [Complex.ofReal_natCast] using hmain

/-- The exponent bookkeeping `n^{m/2}·n^{-s} = n^{-(s-m/2)}` for `n ≠ 0`. -/
private lemma cpow_half_mul_cpow_neg {n : ℕ} (hn : 0 < n) (m : ℕ) (s : ℂ) :
    (n : ℂ) ^ ((m : ℂ) / 2) * (n : ℂ) ^ (-s) = (n : ℂ) ^ (-(s - (m : ℂ) / 2)) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hn
  rw [← Complex.cpow_add _ _ hnC]
  congr 1
  ring

/-- **Absolute convergence of the weighted Hecke series.**  For `‖χ‖ ≤ 1` and `re s > 1 + m/2`
one has `Σ_n ‖n^{m/2}λ(n)‖·n^{-re s} < ∞`, by `‖λ(n)‖ ≤ 4τ(n)` (`heckeLam_bound`) and the
convergence of `Σ_n τ(n)n^{-σ'}` for `σ' = re s - m/2 > 1`
(`summable_card_divisors_mul_rpow_neg`). -/
private lemma summable_holWeight (chi : GaussianInt → ℂ) (m : ℕ)
    (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {s : ℂ} (hs : 1 + (m : ℝ) / 2 < s.re) :
    Summable (fun n : ℕ => ‖(n : ℂ) ^ ((m : ℂ) / 2) * heckeLam chi (m : ℤ) n‖ *
      (n : ℝ) ^ (-s.re)) := by
  have hm2 : (0 : ℝ) ≤ (m : ℝ) / 2 := by positivity
  have hs0 : 0 < s.re := by linarith
  have hσ : 1 < s.re - (m : ℝ) / 2 := by linarith
  have hbase : Summable (fun n : ℕ =>
      4 * ((n.divisors.card : ℝ) * (n : ℝ) ^ (-(s.re - (m : ℝ) / 2)))) :=
    (summable_card_divisors_mul_rpow_neg (σ := s.re - (m : ℝ) / 2) hσ).mul_left 4
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hbase
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    rw [heckeLam_zero]
    simp
  · have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hnpos
    have hlam : ‖heckeLam chi (m : ℤ) n‖ ≤ 4 * ((n.divisors.card : ℕ) : ℝ) :=
      heckeLam_bound chi (m : ℤ) hchi (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hnpos))
    have h1 : (n : ℝ) ^ ((m : ℝ) / 2) * (n : ℝ) ^ (-s.re)
        = (n : ℝ) ^ (-(s.re - (m : ℝ) / 2)) := by
      rw [← Real.rpow_add hnR]
      congr 1
      ring
    calc ‖(n : ℂ) ^ ((m : ℂ) / 2) * heckeLam chi (m : ℤ) n‖ * (n : ℝ) ^ (-s.re)
        = (‖(n : ℂ) ^ ((m : ℂ) / 2)‖ * ‖heckeLam chi (m : ℤ) n‖) * (n : ℝ) ^ (-s.re) := by
          rw [norm_mul]
      _ ≤ ((n : ℝ) ^ ((m : ℝ) / 2) * (4 * ((n.divisors.card : ℕ) : ℝ))) * (n : ℝ) ^ (-s.re) := by
          rw [norm_cpow_half n hnpos m]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hlam (Real.rpow_nonneg (le_of_lt hnR) _))
            (Real.rpow_nonneg (le_of_lt hnR) _)
      _ = ((n : ℝ) ^ ((m : ℝ) / 2) * (n : ℝ) ^ (-s.re)) * (4 * ((n.divisors.card : ℕ) : ℝ)) := by
          ring
      _ = (n : ℝ) ^ (-(s.re - (m : ℝ) / 2)) * (4 * ((n.divisors.card : ℕ) : ℝ)) := by rw [h1]
      _ = 4 * ((n.divisors.card : ℝ) * (n : ℝ) ^ (-(s.re - (m : ℝ) / 2))) := by ring

/-- **Pointwise absolute convergence of the exponential series.**  For `u > 0` the series
`Σ_n ‖n^{m/2}λ(n)‖e^{-πun}` converges, by comparison with `Σ_n ‖n^{m/2}λ(n)‖n^{-re s}`
(`summable_holWeight`): the polynomial power `n^{re s}` is dominated by a constant multiple of
`e^{πun}` (`rpow_mul_exp_neg_bounded`). -/
private lemma summable_holWeight_exp (chi : GaussianInt → ℂ) (m : ℕ)
    (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {s : ℂ} (hs : 1 + (m : ℝ) / 2 < s.re)
    {u : ℝ} (hu : 0 < u) :
    Summable (fun n : ℕ => ‖(n : ℂ) ^ ((m : ℂ) / 2) * heckeLam chi (m : ℤ) n‖ *
      Real.exp (-(Real.pi * u * (n : ℝ)))) := by
  obtain ⟨C, hC0, hC⟩ := rpow_mul_exp_neg_bounded (Real.pi * u) (by positivity) s.re
    (by have : (0:ℝ) ≤ (m:ℝ)/2 := by positivity
        linarith)
  have hsum := summable_holWeight chi m hchi hs
  refine Summable.of_nonneg_of_le
    (f := fun n : ℕ => C * (‖(n : ℂ) ^ ((m : ℂ) / 2) * heckeLam chi (m : ℤ) n‖ *
      (n : ℝ) ^ (-s.re))) (fun n => by positivity) (fun n => ?_) (hsum.mul_left C)
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    simp [heckeLam_zero]
  · have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hnpos
    have hb : (n : ℝ) ^ s.re * Real.exp (-(Real.pi * u * (n : ℝ))) ≤ C := hC (n : ℝ) (le_of_lt hnR)
    have h1 : (n : ℝ) ^ (-s.re) * (n : ℝ) ^ s.re = 1 := by
      rw [← Real.rpow_add hnR, neg_add_cancel, Real.rpow_zero]
    calc ‖(n : ℂ) ^ ((m : ℂ) / 2) * heckeLam chi (m : ℤ) n‖ *
          Real.exp (-(Real.pi * u * (n : ℝ)))
        = (‖(n : ℂ) ^ ((m : ℂ) / 2) * heckeLam chi (m : ℤ) n‖ *
            ((n : ℝ) ^ (-s.re) * (n : ℝ) ^ s.re)) * Real.exp (-(Real.pi * u * (n : ℝ))) := by
          rw [h1, mul_one]
      _ = (‖(n : ℂ) ^ ((m : ℂ) / 2) * heckeLam chi (m : ℤ) n‖ * (n : ℝ) ^ (-s.re)) *
            ((n : ℝ) ^ s.re * Real.exp (-(Real.pi * u * (n : ℝ)))) := by ring
      _ ≤ (‖(n : ℂ) ^ ((m : ℂ) / 2) * heckeLam chi (m : ℤ) n‖ * (n : ℝ) ^ (-s.re)) * C :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = C * (‖(n : ℂ) ^ ((m : ℂ) / 2) * heckeLam chi (m : ℤ) n‖ * (n : ℝ) ^ (-s.re)) := by ring

/-! ## The theorem -/

theorem mellin_thetaHol (chi : GaussianInt → ℂ) (m : ℕ)
    (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {s : ℂ} (hs : 1 + (m : ℝ) / 2 < s.re) :
    (∫ u in Set.Ioi (0 : ℝ), thetaHol chi m u * ((u : ℂ) ^ (s - 1)))
      = Complex.Gamma s * ((Real.pi : ℂ) ^ (-s)) *
          heckeLSeries chi (m : ℤ) (s - (m : ℂ) / 2) := by
  have hm2 : (0 : ℝ) ≤ (m : ℝ) / 2 := by positivity
  have hs0 : 0 < s.re := by linarith
  set w : ℕ → ℂ := fun n => (n : ℂ) ^ ((m : ℂ) / 2) * heckeLam chi (m : ℤ) n with hw
  have hw0 : w 0 = 0 := by simp [hw, heckeLam_zero]
  have hpoint : ∀ u : ℝ, 0 < u →
      Summable (fun n : ℕ => ‖w n‖ * Real.exp (-(Real.pi * u * (n : ℝ)))) := by
    intro u hu
    simpa only [hw] using summable_holWeight_exp chi m hchi hs hu
  have hsum : Summable (fun n : ℕ => ‖w n‖ * (n : ℝ) ^ (-s.re)) := by
    simpa only [hw] using summable_holWeight chi m hchi hs
  -- (1) the holomorphic theta series is the generating function of `w`
  have hD : ∀ u : ℝ, 0 < u →
      thetaHol chi m u = ∑' n : ℕ, w n * Complex.exp (-(Real.pi * u * (n : ℝ))) := by
    intro u hu
    simpa only [hw] using thetaHol_eq_tsum_heckeLam chi m hchi hu
  -- (2) term-by-term Mellin transform
  have hC : mellin (fun u : ℝ => ∑' n : ℕ, w n * Complex.exp (-(Real.pi * u * (n : ℝ)))) s
      = Complex.Gamma s * ((Real.pi : ℂ) ^ (-s)) * ∑' n : ℕ, w n * (n : ℂ) ^ (-s) :=
    mellin_tsum_exp w Real.pi Real.pi_pos hw0 hs0 hpoint hsum
  -- (3) identify `Σ_n w_n n^{-s}` with the Hecke `L`-series at `s - m/2`
  have hRHS : (∑' n : ℕ, w n * (n : ℂ) ^ (-s)) =
      heckeLSeries chi (m : ℤ) (s - (m : ℂ) / 2) := by
    rw [heckeLSeries, LSeries_def₀ (heckeLam_zero chi (m : ℤ))]
    refine tsum_congr (fun n => ?_)
    rcases eq_or_ne n 0 with hn | hn
    · subst hn
      simp [hw, heckeLam_zero]
    · calc w n * (n : ℂ) ^ (-s)
          = (n : ℂ) ^ ((m : ℂ) / 2) * heckeLam chi (m : ℤ) n * (n : ℂ) ^ (-s) := by rw [hw]
        _ = heckeLam chi (m : ℤ) n * ((n : ℂ) ^ ((m : ℂ) / 2) * (n : ℂ) ^ (-s)) := by ring
        _ = heckeLam chi (m : ℤ) n * (n : ℂ) ^ (-(s - (m : ℂ) / 2)) := by
              rw [cpow_half_mul_cpow_neg (Nat.pos_of_ne_zero hn) m s]
        _ = heckeLam chi (m : ℤ) n / (n : ℂ) ^ (s - (m : ℂ) / 2) := by
              simp only [div_eq_mul_inv, Complex.cpow_neg]
  -- (4) rewrite the integral as the Mellin transform
  have hLHS : (∫ u in Set.Ioi (0 : ℝ), thetaHol chi m u * ((u : ℂ) ^ (s - 1)))
      = mellin (fun u : ℝ => ∑' n : ℕ, w n * Complex.exp (-(Real.pi * u * (n : ℝ)))) s := by
    rw [mellin]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
    rw [smul_eq_mul, ← hD u hu]
    ring
  rw [hLHS, hC, hRHS]

end

end Work.FIArea5.S16Hecke
