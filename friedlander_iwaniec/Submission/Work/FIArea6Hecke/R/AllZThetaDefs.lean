/-
# `Work.FIArea6Hecke.R.AllZThetaDefs`

Auxiliary vocabulary for the **all-`z` theta series** `allZTheta` and the **all-`z` Hecke
`L`-series `fullHeckeLSeries` of `Work.FIArea6Hecke.R.ConductorThetaDefs.

The summand, the "all-`z` Hecke eigenvalue" `allZLam`, and the elementary norm bound /
summability of the summand, together with the regrouping lemma `tsum_gnorm_fiberwise` that
rewrites any summable lattice sum over `ℤ[i]` as a sum over the norms `n = |z|²` of the finite
box sums `Σ_{z ∈ gBox n, |z|² = n}`.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.ConductorThetaDefs
import Submission.Work.FIArea5.S16Hecke.thetaSph_eq_tsum_heckeLam
import Submission.Work.FIArea5.S16Hecke.thetaHol_eq_tsum_heckeLam
import Submission.Work.FIArea5.S16Hecke.primaryAux
import Submission.Work.FIArea5.S16Hecke.heckeLam_bound

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea6Hecke.R

open Finset
open scoped BigOperators
open Work.FIPlan

noncomputable section

/-- The summand of the all-`z` theta series: `z ↦ χ₀(z)·z^m·e^{-πu|z|²}`. -/
def allZSummand (chi₀ : GaussianInt → ℂ) (m : ℕ) (u : ℝ) (z : GaussianInt) : ℂ :=
  chi₀ z * (z.toComplex) ^ m * Complex.exp (-(Real.pi * u * (gnorm z : ℝ)))

lemma allZTheta_eq_tsum_summand (chi₀ : GaussianInt → ℂ) (m : ℕ) (u : ℝ) :
    allZTheta chi₀ m u = ∑' z : GaussianInt, allZSummand chi₀ m u z := rfl

/-- The **all-`z` Hecke eigenvalue** `Σ_{|z|² = n} ψ(z)`, the sum running over all (not just the
primary) Gaussian integers of norm `n`, inside the finite box `gBox n`. -/
def allZLam (chi₀ : GaussianInt → ℂ) (k : ℤ) (n : ℕ) : ℂ :=
  ∑ z ∈ (gBox (n : ℤ)).filter (fun z => gnorm z = n), Work.FIArea5.S16Hecke.psi chi₀ k z

/-- A Gaussian integer of norm `0` is `0`. -/
lemma eq_zero_of_gnorm_eq_zero {z : GaussianInt} (h : gnorm z = 0) : z = 0 := by
  have h1 : z.re ^ 2 + z.im ^ 2 = 0 := by
    have hc := Work.FIArea5.S16Hecke.gnorm_cast_eq z
    rw [h] at hc
    simpa using hc.symm
  have hr : z.re = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
  have hi : z.im = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
  exact Zsqrtd.ext hr hi

/-- Pointwise majorant for the summand of `allZTheta`. -/
lemma allZSummand_norm_le {chi₀ : GaussianInt → ℂ} {m : ℕ}
    (hchi : ∀ z : GaussianInt, ‖chi₀ z‖ ≤ 1) (u : ℝ) (z : GaussianInt) :
    ‖allZSummand chi₀ m u z‖
      ≤ Real.exp (-(Real.pi * u * (gnorm z : ℝ))) * (1 + (gnorm z : ℝ)) ^ m := by
  rw [allZSummand, norm_mul, norm_mul]
  have hexp : ‖Complex.exp (-(Real.pi * u * (gnorm z : ℝ)))‖
      = Real.exp (-(Real.pi * u * (gnorm z : ℝ))) := by
    have h : (-(Real.pi * u * (gnorm z : ℝ))) = ((-(Real.pi * u * (gnorm z : ℝ)) : ℝ) : ℂ) := by
      simp
    rw [h, Complex.norm_exp_ofReal]
  rw [hexp]
  have h1 : ‖chi₀ z‖ ≤ 1 := hchi z
  have h2 : ‖(z.toComplex) ^ m‖ ≤ (1 + (gnorm z : ℝ)) ^ m := by
    rw [norm_pow, Work.FIArea5.S16Hecke.norm_toComplex]
    apply pow_le_pow_left₀ (Real.sqrt_nonneg _)
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (gnorm z) : (0:ℝ) ≤ (gnorm z : ℝ)),
      sq_nonneg (Real.sqrt (gnorm z : ℝ) - 1/2), Real.sqrt_nonneg (gnorm z : ℝ)]
  calc ‖chi₀ z‖ * ‖(z.toComplex) ^ m‖ * Real.exp (-(Real.pi * u * (gnorm z : ℝ)))
      ≤ 1 * (1 + (gnorm z : ℝ)) ^ m * Real.exp (-(Real.pi * u * (gnorm z : ℝ))) := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul h1 h2 (by positivity) zero_le_one) (Real.exp_nonneg _)
    _ = Real.exp (-(Real.pi * u * (gnorm z : ℝ))) * (1 + (gnorm z : ℝ)) ^ m := by ring

/-- Absolute convergence of the all-`z` theta series for `u > 0`. -/
lemma summable_allZSummand {u : ℝ} (hu : 0 < u) {chi₀ : GaussianInt → ℂ} {m : ℕ}
    (hchi : ∀ z : GaussianInt, ‖chi₀ z‖ ≤ 1) :
    Summable (fun z : GaussianInt => allZSummand chi₀ m u z) :=
  Summable.of_norm_bounded (Work.FIArea5.S16Hecke.summable_gnorm_weight hu m)
    (fun z => allZSummand_norm_le hchi u z)

/-- **Regrouping a summable lattice sum by the norm.**  For a summable `f : ℤ[i] → ℂ`,

  `Σ'_z f z = Σ'_n Σ_{z ∈ gBox n, |z|² = n} f z`,

because the norm fibres of `ℤ[i]` are exactly the finite box sections (a fibre is a singleton for
`n = 0` and is contained in `gBox n` for `n ≥ 1`). -/
theorem tsum_gnorm_fiberwise (f : GaussianInt → ℂ) (hf : Summable f) :
    (∑' z : GaussianInt, f z)
      = ∑' n : ℕ, ∑ z ∈ (gBox (n : ℤ)).filter (fun z => gnorm z = n), f z := by
  classical
  rw [← (hf.hasSum.tsum_fiberwise (gnorm : GaussianInt → ℕ)).tsum_eq]
  refine tsum_congr (fun n => ?_)
  rw [tsum_subtype (gnorm ⁻¹' ({n} : Set ℕ)) f]
  have hbound : ∀ z, z ∉ (gBox (n : ℤ)).filter (fun w => gnorm w = n) →
      (gnorm ⁻¹' ({n} : Set ℕ)).indicator f z = 0 := by
    intro z hz
    rw [Set.indicator_apply]
    by_cases hgn : gnorm z = n
    · rw [if_pos (by simpa [Set.mem_preimage] using hgn)]
      exfalso
      apply hz
      rw [Finset.mem_filter]
      refine ⟨?_, hgn⟩
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        rw [eq_zero_of_gnorm_eq_zero hgn]
        rw [Work.FIArea5.S16Hecke.mem_gBox_iff]
        simp
      · exact Work.FIArea5.S16Hecke.mem_gBox_of_gnorm_le (by exact_mod_cast hn) (by rw [hgn])
    · rw [if_neg (by simpa [Set.mem_preimage] using hgn)]
  rw [tsum_eq_sum hbound]
  refine Finset.sum_congr rfl (fun z hz => ?_)
  have hgn : gnorm z = n := (Finset.mem_filter.mp hz).2
  rw [Set.indicator_apply, if_pos (by simpa [Set.mem_preimage] using hgn)]

end

end Work.FIArea6Hecke.R
