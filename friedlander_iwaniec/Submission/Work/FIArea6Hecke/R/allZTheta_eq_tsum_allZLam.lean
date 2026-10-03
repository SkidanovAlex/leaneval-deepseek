import Mathlib
import Submission.Work.FIArea6Hecke.R.AllZThetaDefs

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open Finset
open scoped BigOperators
open Work.FIPlan

noncomputable section

/-- The pointwise exponent identity for `n = 0`: `0^{m/2}·ψ(0) = χ(0)·0^m`. -/
lemma cpow_half_mul_psi_zero (chi₀ : GaussianInt → ℂ) (m : ℕ) :
    (0:ℂ)^((m:ℂ)/2) * Work.FIArea5.S16Hecke.psi chi₀ (m:ℤ) 0 = chi₀ 0 * (0:ℂ)^m := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [Work.FIArea5.S16Hecke.psi, GaussianInt.toComplex_zero]
    simp
  · have hmz : (m:ℤ) ≠ 0 := by omega
    have hmc : ((m:ℂ)/2 : ℂ) ≠ 0 := by
      simp only [ne_eq, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false]
      exact_mod_cast hm.ne'
    rw [Work.FIArea5.S16Hecke.psi, GaussianInt.toComplex_zero]
    simp only [gnorm, Zsqrtd.norm_zero, Int.natAbs_zero, Nat.cast_zero, Real.sqrt_zero,
      Complex.ofReal_zero, div_zero]
    rw [Complex.zero_cpow hmc, zero_zpow (m:ℤ) hmz, zero_pow hm.ne']
    ring

/-- **The pointwise identity `n^{m/2}·ψ(z) = χ(z)·z^m`** for `n = |z|²`, valid for all `z`
(including `z = 0`): it combines the positive-norm case `cpow_half_mul_psi` with the
degenerate `z = 0` computation. -/
lemma cpow_half_mul_psi_all (chi₀ : GaussianInt → ℂ) (m : ℕ) (z : GaussianInt) :
    ((gnorm z : ℕ) : ℂ) ^ ((m : ℂ) / 2) * Work.FIArea5.S16Hecke.psi chi₀ (m : ℤ) z
      = chi₀ z * (z.toComplex) ^ m := by
  rcases Nat.eq_zero_or_pos (gnorm z) with h0 | hpos
  · have hz0 : z = 0 := eq_zero_of_gnorm_eq_zero h0
    subst hz0
    simpa [gnorm, Zsqrtd.norm_zero, GaussianInt.toComplex_zero] using cpow_half_mul_psi_zero chi₀ m
  · exact Work.FIArea5.S16Hecke.cpow_half_mul_psi chi₀ m hpos rfl

/-- **The norm fibre identity**: grouping the (absolutely convergent) `allZSummand` sum over the
norm fibre `{|z|² = n}` reproduces the `allZ` Hecke eigenvalue sum, weighted by `n^{m/2}` and the
exponential factor. -/
lemma allZSummand_fiber_eq (chi₀ : GaussianInt → ℂ) (m : ℕ) (u : ℝ) (n : ℕ) :
    (∑ z ∈ (gBox (n : ℤ)).filter (fun z => gnorm z = n), allZSummand chi₀ m u z)
      = (n : ℂ) ^ ((m : ℂ) / 2) * allZLam chi₀ (m : ℤ) n
          * Complex.exp (-(Real.pi * u * (n : ℝ))) := by
  classical
  set S : Finset GaussianInt := (gBox (n : ℤ)).filter (fun z => gnorm z = n) with hS
  have hsummand : ∀ z ∈ S, allZSummand chi₀ m u z
      = chi₀ z * (z.toComplex) ^ m * Complex.exp (-(Real.pi * u * (n : ℝ))) := by
    intro z hz
    have hg : gnorm z = n := (Finset.mem_filter.mp hz).2
    rw [allZSummand, hg]
  rw [Finset.sum_congr rfl hsummand, ← Finset.sum_mul]
  have hkey : (∑ z ∈ S, chi₀ z * (z.toComplex) ^ m)
      = (n : ℂ) ^ ((m : ℂ) / 2)
          * ∑ z ∈ S, Work.FIArea5.S16Hecke.psi chi₀ (m : ℤ) z := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun z hz => ?_)
    have hg : gnorm z = n := (Finset.mem_filter.mp hz).2
    have h := cpow_half_mul_psi_all chi₀ m z
    rw [hg] at h
    exact h.symm
  rw [hkey]
  rw [show allZLam chi₀ (m : ℤ) n
      = ∑ z ∈ S, Work.FIArea5.S16Hecke.psi chi₀ (m : ℤ) z from by rw [hS]; rfl]

theorem allZTheta_eq_tsum_allZLam (chi₀ : GaussianInt → ℂ) (m : ℕ)
    (hchi : ∀ z : GaussianInt, ‖chi₀ z‖ ≤ 1) {u : ℝ} (hu : 0 < u) :
    Work.FIArea6Hecke.R.allZTheta chi₀ m u =
      ∑' n : ℕ, (n : ℂ) ^ ((m : ℂ) / 2) * Work.FIArea6Hecke.R.allZLam chi₀ (m : ℤ) n *
        Complex.exp (-(Real.pi * u * (n : ℝ))) := by
  rw [allZTheta_eq_tsum_summand,
    tsum_gnorm_fiberwise (fun z => allZSummand chi₀ m u z) (summable_allZSummand hu hchi)]
  exact tsum_congr (fun n => allZSummand_fiber_eq chi₀ m u n)

end

end Work.FIArea6Hecke.R
