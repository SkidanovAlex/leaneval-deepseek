import Mathlib
import Submission.Work.FIArea6Hecke.R.AllZThetaDefs
import Submission.Work.FIArea5.S16Hecke.heckeLam_bound
import Submission.Work.FIArea5.S16Hecke.summable_card_divisors_mul_rpow_neg

namespace Work.FIArea6Hecke.R

open Finset
open scoped BigOperators
open Work.FIPlan

noncomputable section

/-- **Size of the all-`z` Hecke eigenvalue.**  For `‖χ₀‖ ≤ 1`, the all-`z` eigenvalue
`allZLam χ₀ k n = Σ_{z ∈ gBox n, |z|² = n} ψ(z)` is bounded by the number of Gaussian integers of
norm `n`, which is at most `r₂(n) ≤ 4·τ(n)`.  This is the "all-`z`" counterpart of
`Work.FIArea5.S16Hecke.heckeLam_bound`. -/
theorem allZLam_bound (chi₀ : GaussianInt → ℂ) (k : ℤ)
    (hchi : ∀ z : GaussianInt, ‖chi₀ z‖ ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    ‖allZLam chi₀ k n‖ ≤ 4 * ((n.divisors.card : ℕ) : ℝ) := by
  classical
  set S : Finset GaussianInt :=
    (gBox (n : ℤ)).filter (fun z => gnorm z = n) with hS
  have hsum : ‖allZLam chi₀ k n‖ ≤ ∑ z ∈ S, ‖Work.FIArea5.S16Hecke.psi chi₀ k z‖ := by
    rw [hS]
    exact norm_sum_le _ _
  have hone : ∑ z ∈ S, ‖Work.FIArea5.S16Hecke.psi chi₀ k z‖ ≤ (S.card : ℝ) := by
    calc ∑ z ∈ S, ‖Work.FIArea5.S16Hecke.psi chi₀ k z‖ ≤ ∑ _z ∈ S, (1 : ℝ) :=
          Finset.sum_le_sum (fun z _ => Work.FIArea5.S16Hecke.norm_psi_le_one chi₀ k hchi z)
      _ = (S.card : ℝ) := by simp
  have hcount : (S.card : ℝ) ≤ 4 * ((n.divisors.card : ℕ) : ℝ) := by
    let U : Finset (ℤ × ℤ) :=
      ((Finset.Icc (-(n : ℤ)) (n : ℤ)) ×ˢ (Finset.Icc (-(n : ℤ)) (n : ℤ))).filter
        (fun p => p.1 ^ 2 + p.2 ^ 2 = (n : ℤ))
    have hsub : S.image (fun z : GaussianInt => (z.re, z.im)) ⊆ U := by
      intro p hp
      rw [Finset.mem_image] at hp
      obtain ⟨z, hz, rfl⟩ := hp
      rw [hS, Finset.mem_filter] at hz
      obtain ⟨hzbox, hgn⟩ := hz
      rw [Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_product]
        exact Work.FIArea5.S16Hecke.mem_gBox_iff.mp hzbox
      · have h : ((gnorm z : ℕ) : ℤ) = (n : ℤ) := by rw [hgn]
        rw [Work.FIArea5.S16Hecke.gnorm_cast_eq z] at h
        exact h
    have himg : (S.image (fun z : GaussianInt => (z.re, z.im))).card = S.card :=
      Finset.card_image_of_injective S Work.FIArea5.S16Hecke.re_im_injective
    have hle : (S.image (fun z : GaussianInt => (z.re, z.im))).card ≤ U.card :=
      Finset.card_le_card hsub
    have hU : (U.card : ℤ) ≤ 4 * ((Nat.divisors n).card : ℤ) :=
      Commons.NumberTheory.GaussianInt.two_squares_repr_count_le_tau_of_pos n hn
    have hleR : (S.card : ℝ) ≤ (U.card : ℝ) := by
      have h : ((S.image (fun z : GaussianInt => (z.re, z.im))).card : ℝ) ≤ (U.card : ℝ) := by
        exact_mod_cast hle
      rwa [himg] at h
    have hU' : (U.card : ℝ) ≤ 4 * ((Nat.divisors n).card : ℝ) := by
      have h2 : ((U.card : ℤ) : ℝ) ≤ ((4 * ((Nat.divisors n).card : ℤ) : ℤ) : ℝ) := by
        exact_mod_cast hU
      simpa using h2
    linarith
  linarith

theorem summable_allZLam_weight (chi₀ : GaussianInt → ℂ) (m : ℕ)
    (hchi : ∀ z : GaussianInt, ‖chi₀ z‖ ≤ 1) {σ : ℝ} (hσ : 1 + (m : ℝ) / 2 < σ) :
    Summable (fun n : ℕ => ‖(n : ℂ) ^ ((m : ℂ) / 2) * Work.FIArea6Hecke.R.allZLam chi₀ (m : ℤ) n‖ *
      (n : ℝ) ^ (-σ)) := by
  have hσ' : (1 : ℝ) < σ - (m : ℝ) / 2 := by linarith
  have hmaj : Summable (fun n : ℕ =>
      4 * ((n.divisors.card : ℝ) * (n : ℝ) ^ (-(σ - (m : ℝ) / 2)))) :=
    (Work.FIArea5.S16Hecke.summable_card_divisors_mul_rpow_neg hσ').mul_left 4
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hmaj
  · positivity
  · rcases eq_or_ne n 0 with rfl | hn
    · norm_num
      have hσpos : (0 : ℝ) < σ := by
        have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        linarith
      rw [Real.zero_rpow (show (-σ) ≠ 0 from ne_of_lt (neg_lt_zero.mpr hσpos)), mul_zero]
    · have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn
      have hbound := allZLam_bound chi₀ (m : ℤ) hchi hn1
      have hcpow : ‖(n : ℂ) ^ ((m : ℂ) / 2)‖ = (n : ℝ) ^ ((m : ℝ) / 2) := by
        rw [show (n : ℂ) = ((n : ℝ) : ℂ) by simp,
          Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
        simp
      have hexp : (n : ℝ) ^ ((m : ℝ) / 2) * (n : ℝ) ^ (-σ)
          = (n : ℝ) ^ (-(σ - (m : ℝ) / 2)) := by
        rw [← Real.rpow_add hnpos]
        congr 1
        ring
      rw [norm_mul, hcpow]
      calc (n : ℝ) ^ ((m : ℝ) / 2) * ‖allZLam chi₀ (m : ℤ) n‖ * (n : ℝ) ^ (-σ)
          = ((n : ℝ) ^ ((m : ℝ) / 2) * (n : ℝ) ^ (-σ)) * ‖allZLam chi₀ (m : ℤ) n‖ := by
            ring
        _ = (n : ℝ) ^ (-(σ - (m : ℝ) / 2)) * ‖allZLam chi₀ (m : ℤ) n‖ := by rw [hexp]
        _ ≤ (n : ℝ) ^ (-(σ - (m : ℝ) / 2)) * (4 * (n.divisors.card : ℝ)) :=
            mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        _ = 4 * ((n.divisors.card : ℝ) * (n : ℝ) ^ (-(σ - (m : ℝ) / 2))) := by ring

end

end Work.FIArea6Hecke.R
