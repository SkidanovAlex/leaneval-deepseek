import Mathlib
import Submission.Work.FIArea6Hecke.R.AllZThetaDefs
import Submission.Work.FIArea6Hecke.R.summable_primary_chi_div_gnorm_cpow

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open scoped BigOperators

noncomputable section

/-- Splitting the complex power `n^{-(s-m/2)}` as `n^{m/2}·n^{-s}` for the natural number `n`
(this is where the weight `m/2` of the Größencharacter is undone). -/
private lemma cpow_neg_sub_eq (m : ℕ) {s : ℂ} (hσ : 1 < (s - (m : ℂ) / 2).re) (n : ℕ) :
    (n : ℂ) ^ (-(s - (m : ℂ) / 2)) = (n : ℂ) ^ ((m : ℂ) / 2) * (n : ℂ) ^ (-s) := by
  have h1 : (s - (m : ℂ) / 2).re = s.re - (m : ℝ) / 2 := by simp
  have hsre : 0 < s.re := by
    have h2 : (0 : ℝ) ≤ (m : ℝ) / 2 := by positivity
    linarith [hσ, h1, h2]
  have hsne : s ≠ 0 := by
    intro h0
    rw [h0] at hsre
    simp at hsre
  rcases eq_or_ne n 0 with hn | hn
  · subst hn
    rw [Nat.cast_zero]
    have h3 : (-(s - (m : ℂ) / 2)) ≠ 0 := by
      intro hc
      have h0 : s - (m : ℂ) / 2 = 0 := neg_eq_zero.mp hc
      rw [h0] at hσ
      norm_num at hσ
    rw [Complex.zero_cpow h3, Complex.zero_cpow (neg_ne_zero.mpr hsne), mul_zero]
  · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hexp : -(s - (m : ℂ) / 2) = (m : ℂ) / 2 + (-s) := by ring
    rw [hexp, Complex.cpow_add _ _ hnC]

/-- **Absolute convergence of the lattice sum defining `fullHeckeLSeries`.**  For `re σ > 1` the
summand `ψ(z)·N(z)^{-σ}` is dominated by `N(z)^{-re σ}`, which is summable over `ℤ[i]` by
`summable_gnorm_rpow_neg`; `‖ψ‖ ≤ 1` is used through `norm_psi_le_one`. -/
private lemma summable_psi_mul_gnorm_cpow (chi₀ : GaussianInt → ℂ) (m : ℕ)
    (hchi : ∀ z : GaussianInt, ‖chi₀ z‖ ≤ 1) {σ : ℂ} (hσ : 1 < σ.re) :
    Summable (fun z : GaussianInt => Work.FIArea5.S16Hecke.psi chi₀ (m : ℤ) z *
      (((Work.FIPlan.gnorm z : ℕ)) : ℂ) ^ (-σ)) := by
  have hbase : Summable (fun z : GaussianInt => (Work.FIPlan.gnorm z : ℝ) ^ (-σ.re)) :=
    Work.FIArea6Hecke.R.summable_gnorm_rpow_neg hσ
  refine Summable.of_norm_bounded hbase (fun z => ?_)
  rw [norm_mul]
  have h2 : ‖(((Work.FIPlan.gnorm z : ℕ)) : ℂ) ^ (-σ)‖
      ≤ ((Work.FIPlan.gnorm z : ℕ) : ℝ) ^ (-σ.re) := by
    rcases eq_or_ne (Work.FIPlan.gnorm z) 0 with hz | hz
    · rw [hz, Nat.cast_zero]
      have hσne : (-σ) ≠ 0 := by
        intro hc
        have h0 : σ = 0 := neg_eq_zero.mp hc
        rw [h0] at hσ
        norm_num at hσ
      have hσrene : (-σ.re) ≠ 0 := by
        intro hc
        have h0 : σ.re = 0 := neg_eq_zero.mp hc
        linarith
      rw [Complex.zero_cpow hσne, Nat.cast_zero, Real.zero_rpow hσrene, norm_zero]
    · have hp : (0 : ℝ) < ((Work.FIPlan.gnorm z : ℕ) : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hz
      have hcast : (((Work.FIPlan.gnorm z : ℕ)) : ℂ)
          = ((((Work.FIPlan.gnorm z : ℕ)) : ℝ) : ℂ) := by simp
      rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hp, Complex.neg_re]
  calc ‖Work.FIArea5.S16Hecke.psi chi₀ (m : ℤ) z‖ *
        ‖(((Work.FIPlan.gnorm z : ℕ)) : ℂ) ^ (-σ)‖
      ≤ 1 * ((Work.FIPlan.gnorm z : ℕ) : ℝ) ^ (-σ.re) :=
        mul_le_mul (Work.FIArea5.S16Hecke.norm_psi_le_one chi₀ (m : ℤ) hchi z) h2
          (norm_nonneg _) zero_le_one
    _ = ((Work.FIPlan.gnorm z : ℕ) : ℝ) ^ (-σ.re) := one_mul _

theorem fullHeckeLSeries_eq_tsum_allZLam (chi₀ : GaussianInt → ℂ) (m : ℕ)
    (hchi : ∀ z : GaussianInt, ‖chi₀ z‖ ≤ 1) {s : ℂ}
    (hs : 1 + (m : ℝ) / 2 < s.re) :
    Work.FIArea6Hecke.R.fullHeckeLSeries chi₀ (m : ℤ) (s - (m : ℂ) / 2) =
      ∑' n : ℕ, (n : ℂ) ^ ((m : ℂ) / 2) * Work.FIArea6Hecke.R.allZLam chi₀ (m : ℤ) n *
        (n : ℂ) ^ (-s) := by
  have hσ : 1 < (s - (m : ℂ) / 2).re := by
    have h1 : (s - (m : ℂ) / 2).re = s.re - (m : ℝ) / 2 := by simp
    rw [h1]; linarith
  have hsumm : Summable (fun z : GaussianInt => Work.FIArea5.S16Hecke.psi chi₀ (m : ℤ) z *
      (((Work.FIPlan.gnorm z : ℕ)) : ℂ) ^ (-(s - (m : ℂ) / 2))) :=
    summable_psi_mul_gnorm_cpow chi₀ m hchi hσ
  rw [show Work.FIArea6Hecke.R.fullHeckeLSeries chi₀ (m : ℤ) (s - (m : ℂ) / 2) =
      ∑' z : GaussianInt, Work.FIArea5.S16Hecke.psi chi₀ (m : ℤ) z *
        (((Work.FIPlan.gnorm z : ℕ)) : ℂ) ^ (-(s - (m : ℂ) / 2)) from rfl]
  rw [tsum_gnorm_fiberwise _ hsumm]
  refine tsum_congr (fun n => ?_)
  have h1 : ∀ z ∈ (Work.FIPlan.gBox (n : ℤ)).filter (fun z => Work.FIPlan.gnorm z = n),
      Work.FIArea5.S16Hecke.psi chi₀ (m : ℤ) z *
          (((Work.FIPlan.gnorm z : ℕ)) : ℂ) ^ (-(s - (m : ℂ) / 2))
        = Work.FIArea5.S16Hecke.psi chi₀ (m : ℤ) z * (n : ℂ) ^ (-(s - (m : ℂ) / 2)) := by
    intro z hz
    rw [(Finset.mem_filter.mp hz).2]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_mul]
  rw [show (∑ z ∈ (Work.FIPlan.gBox (n : ℤ)).filter (fun z => Work.FIPlan.gnorm z = n),
        Work.FIArea5.S16Hecke.psi chi₀ (m : ℤ) z) =
      Work.FIArea6Hecke.R.allZLam chi₀ (m : ℤ) n from rfl]
  rw [cpow_neg_sub_eq m hσ n]
  ring

end

end Work.FIArea6Hecke.R
