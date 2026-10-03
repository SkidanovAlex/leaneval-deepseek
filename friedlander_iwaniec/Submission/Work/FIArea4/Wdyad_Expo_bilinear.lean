import Mathlib
import Submission.Work.FIArea4.WdyadBilinearDefs
import Submission.Work.FIArea4.WdyadDefs2
import Submission.Work.FIArea4.WdyadSetup
import Submission.Commons.Analysis.Fourier.summable_of_isBigO_cocompact_rpow

namespace Work.FIArea4

open Finset
open scoped BigOperators FourierTransform

noncomputable section

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! ## Elementary helpers -/

/-- `‖exp (2 π i r k a / Q)‖ = 1` for real `Q`. -/
lemma norm_exp_unit (Q : ℝ) (r a : ℕ) (k : ℤ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (r : ℝ) * (k : ℝ) * (a : ℝ) / Q)‖ = 1 := by
  have harg : 2 * Real.pi * Complex.I * (r : ℝ) * (k : ℝ) * (a : ℝ) / Q
      = ((2 * Real.pi * (r : ℝ) * (k : ℝ) * (a : ℝ) / Q : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.norm_exp_ofReal_mul_I]

/-- The Fourier transform of the degenerate majorant `gmajorC 0` vanishes: the integrand is a
constant of modulus `exp (π/4)`, which is not integrable. -/
lemma fourier_gmajorC_zero : FourierTransform.fourier (gmajorC (0 : ℝ)) = 0 := by
  have hgm : gmajorC (0 : ℝ) = fun _ : ℝ => ((Real.exp (Real.pi / 4) : ℝ) : ℂ) := by
    funext x; simp [gmajorC, gmajor]
  funext ξ
  rw [Real.fourier_real_eq_integral_exp_smul, hgm]
  exact MeasureTheory.integral_undef (by
    intro h
    have h1 : MeasureTheory.Integrable
        (fun v : ℝ => ‖Complex.exp (↑(-2 * Real.pi * v * ξ) * Complex.I) •
          ((Real.exp (Real.pi / 4) : ℝ) : ℂ)‖) MeasureTheory.volume := h.norm
    have h2 : (fun v : ℝ => ‖Complex.exp (↑(-2 * Real.pi * v * ξ) * Complex.I) •
          ((Real.exp (Real.pi / 4) : ℝ) : ℂ)‖)
        = (fun _ : ℝ => Real.exp (Real.pi / 4)) := by
      funext v
      rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    rw [h2, MeasureTheory.integrable_const_iff] at h1
    rcases h1 with h1 | h1
    · exact absurd h1 (ne_of_gt (Real.exp_pos _))
    · exact absurd h1 (MeasureTheory.not_isFiniteMeasure_iff.mpr Real.volume_univ))

/-- Multiplying a summable family by a uniformly bounded family keeps it summable. -/
lemma summable_fourier_mul {F : ℝ → ℂ} {Q : ℝ} (hF : Summable fun k : ℤ => F ((k : ℝ) / Q))
    {b : ℤ → ℂ} {C : ℝ} (hb : ∀ k, ‖b k‖ ≤ C) :
    Summable fun k : ℤ => F ((k : ℝ) / Q) * b k :=
  (hF.norm.mul_right C).of_norm_bounded (fun k => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hb k) (norm_nonneg _))

/-! ## The finite-sum / `tsum` interchange -/

lemma block_swap {G : ℝ → ℂ} {Q : ℝ} {W : ℕ → ℂ} {ga : ℕ → ℂ} {E : ℕ → ℤ → ℕ → ℂ}
    (hsumL : ∀ r a : ℕ, Summable fun k : ℤ => G ((k : ℝ) / Q) * (ga a * E r k a))
    (s t : Finset ℕ) :
    (∑ r ∈ s, W r * ((1 / Q) * ∑' k : ℤ, G ((k : ℝ) / Q) * (∑ a ∈ t, ga a * E r k a)))
      = ∑ r ∈ s, ∑ a ∈ t, ∑' k : ℤ, (1 / Q) * W r * G ((k : ℝ) / Q) * ga a * E r k a := by
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [show (∑' k : ℤ, G ((k : ℝ) / Q) * (∑ a ∈ t, ga a * E r k a))
      = ∑ a ∈ t, ∑' k : ℤ, G ((k : ℝ) / Q) * (ga a * E r k a) from by
    rw [show (∑' k : ℤ, G ((k : ℝ) / Q) * (∑ a ∈ t, ga a * E r k a))
        = ∑' k : ℤ, ∑ a ∈ t, G ((k : ℝ) / Q) * (ga a * E r k a) from
          tsum_congr (fun k => Finset.mul_sum _ _ _)]
    exact Summable.tsum_finsetSum (fun a _ => hsumL r a)]
  rw [show W r * ((1 / Q) * (∑ a ∈ t, ∑' k : ℤ, G ((k : ℝ) / Q) * (ga a * E r k a)))
      = ∑ a ∈ t, W r * ((1 / Q) * ∑' k : ℤ, G ((k : ℝ) / Q) * (ga a * E r k a)) from by
    simp only [Finset.mul_sum]]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← tsum_mul_left, ← tsum_mul_left]
  exact tsum_congr (fun k => by ring)

lemma block_swap' {G : ℝ → ℂ} {Q : ℝ} {W : ℕ → ℂ} {ga : ℕ → ℂ} {E : ℕ → ℤ → ℕ → ℂ}
    (hsumR : ∀ r a : ℕ, Summable fun k : ℤ => G ((k : ℝ) / Q) * (W r * E r k a))
    (s t : Finset ℕ) :
    (∑ a ∈ t, ga a * ((1 / Q) * ∑' k : ℤ, G ((k : ℝ) / Q) * (∑ r ∈ s, W r * E r k a)))
      = ∑ r ∈ s, ∑ a ∈ t, ∑' k : ℤ, (1 / Q) * W r * G ((k : ℝ) / Q) * ga a * E r k a := by
  have key : ∀ a ∈ t, ga a * ((1 / Q) * ∑' k : ℤ, G ((k : ℝ) / Q) * (∑ r ∈ s, W r * E r k a))
      = ∑ r ∈ s, ∑' k : ℤ, (1 / Q) * W r * G ((k : ℝ) / Q) * ga a * E r k a := by
    intro a _
    rw [show (∑' k : ℤ, G ((k : ℝ) / Q) * (∑ r ∈ s, W r * E r k a))
        = ∑ r ∈ s, ∑' k : ℤ, G ((k : ℝ) / Q) * (W r * E r k a) from by
      rw [show (∑' k : ℤ, G ((k : ℝ) / Q) * (∑ r ∈ s, W r * E r k a))
          = ∑' k : ℤ, ∑ r ∈ s, G ((k : ℝ) / Q) * (W r * E r k a) from
            tsum_congr (fun k => Finset.mul_sum _ _ _)]
      exact Summable.tsum_finsetSum (fun r _ => hsumR r a)]
    rw [show ga a * ((1 / Q) * (∑ r ∈ s, ∑' k : ℤ, G ((k : ℝ) / Q) * (W r * E r k a)))
        = ∑ r ∈ s, ga a * ((1 / Q) * ∑' k : ℤ, G ((k : ℝ) / Q) * (W r * E r k a)) from by
      simp only [Finset.mul_sum]]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [← tsum_mul_left, ← tsum_mul_left]
    exact tsum_congr (fun k => by ring)
  rw [Finset.sum_congr rfl key]
  exact Finset.sum_comm

/-- The `(d₁,d₂)` block of the expansion. -/
lemma expo_block (F : ℝ → ℂ) (R : ℕ) (γ : ℕ → ℕ → ℂ) {d1 d2 : ℕ}
    (hd1 : 1 ≤ d1) (hd2 : 1 ≤ d2)
    (hFsum : Summable fun k : ℤ => F ((k : ℝ) / ((Nat.lcm d1 d2 : ℕ) : ℝ))) :
    (∑ r ∈ Finset.Ioc R (2 * R),
      (if Nat.Coprime r (d1 * d2) then
        ((jacobiSym (r : ℤ) (Work.FIPlan.oddPart d1) : ℤ) : ℂ) *
          ((jacobiSym (r : ℤ) (Work.FIPlan.oddPart d2) : ℤ) : ℂ) *
          ((1 / ((Nat.lcm d1 d2 : ℕ) : ℝ)) *
            ∑' k : ℤ, F ((k : ℝ) / ((Nat.lcm d1 d2 : ℕ) : ℝ)) *
              (∑ a ∈ Finset.range (Nat.lcm d1 d2),
                γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) *
                  Complex.exp (2 * Real.pi * Complex.I * (r : ℝ) * (k : ℝ) * (a : ℝ) /
                    ((Nat.lcm d1 d2 : ℕ) : ℝ))))
      else 0))
    = ∑ a ∈ Finset.range (Nat.lcm d1 d2),
        γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) * KK F R d1 d2 a := by
  haveI : NeZero (Work.FIPlan.oddPart d1) := ⟨(Nat.ordCompl_pos 2 (by omega)).ne'⟩
  haveI : NeZero (Work.FIPlan.oddPart d2) := ⟨(Nat.ordCompl_pos 2 (by omega)).ne'⟩
  have hsumL : ∀ r a : ℕ, Summable fun k : ℤ =>
      F ((k : ℝ) / ((Nat.lcm d1 d2 : ℕ) : ℝ)) *
        (γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) *
          Complex.exp (2 * Real.pi * Complex.I * (r : ℝ) * (k : ℝ) * (a : ℝ) /
            ((Nat.lcm d1 d2 : ℕ) : ℝ))) := by
    intro r a
    refine summable_fourier_mul hFsum
      (C := ‖γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2)‖) (fun k => ?_)
    rw [norm_mul, norm_exp_unit, mul_one]
  have hsumR : ∀ r a : ℕ, Summable fun k : ℤ =>
      F ((k : ℝ) / ((Nat.lcm d1 d2 : ℕ) : ℝ)) *
        (wChar d1 d2 r * Complex.exp (2 * Real.pi * Complex.I * (r : ℝ) * (k : ℝ) * (a : ℝ) /
          ((Nat.lcm d1 d2 : ℕ) : ℝ))) := by
    intro r a
    refine summable_fourier_mul hFsum (C := ‖wChar d1 d2 r‖) (fun k => ?_)
    rw [norm_mul, norm_exp_unit, mul_one]
  have step1 : (∑ r ∈ Finset.Ioc R (2 * R),
      (if Nat.Coprime r (d1 * d2) then
        ((jacobiSym (r : ℤ) (Work.FIPlan.oddPart d1) : ℤ) : ℂ) *
          ((jacobiSym (r : ℤ) (Work.FIPlan.oddPart d2) : ℤ) : ℂ) *
          ((1 / ((Nat.lcm d1 d2 : ℕ) : ℝ)) *
            ∑' k : ℤ, F ((k : ℝ) / ((Nat.lcm d1 d2 : ℕ) : ℝ)) *
              (∑ a ∈ Finset.range (Nat.lcm d1 d2),
                γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) *
                  Complex.exp (2 * Real.pi * Complex.I * (r : ℝ) * (k : ℝ) * (a : ℝ) /
                    ((Nat.lcm d1 d2 : ℕ) : ℝ))))
      else 0))
      = ∑ r ∈ Finset.Ioc R (2 * R), wChar d1 d2 r *
          ((1 / ((Nat.lcm d1 d2 : ℕ) : ℝ)) *
            ∑' k : ℤ, F ((k : ℝ) / ((Nat.lcm d1 d2 : ℕ) : ℝ)) *
              (∑ a ∈ Finset.range (Nat.lcm d1 d2),
                γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) *
                  Complex.exp (2 * Real.pi * Complex.I * (r : ℝ) * (k : ℝ) * (a : ℝ) /
                    ((Nat.lcm d1 d2 : ℕ) : ℝ)))) := by
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [wChar_eq]
    by_cases hc : Nat.Coprime r (d1 * d2)
    · simp [if_pos hc]
    · simp [if_neg hc]
  rw [step1]
  simp only [KK]
  rw [block_swap (G := F) (Q := ((Nat.lcm d1 d2 : ℕ) : ℝ)) (W := wChar d1 d2)
        (ga := fun a => γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2))
        (E := fun r k a => Complex.exp (2 * Real.pi * Complex.I * (r : ℝ) * (k : ℝ) * (a : ℝ) /
          ((Nat.lcm d1 d2 : ℕ) : ℝ)))
        hsumL (Finset.Ioc R (2 * R)) (Finset.range (Nat.lcm d1 d2))]
  rw [block_swap' (G := F) (Q := ((Nat.lcm d1 d2 : ℕ) : ℝ)) (W := wChar d1 d2)
        (ga := fun a => γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2))
        (E := fun r k a => Complex.exp (2 * Real.pi * Complex.I * (r : ℝ) * (k : ℝ) * (a : ℝ) /
          ((Nat.lcm d1 d2 : ℕ) : ℝ)))
        hsumR (Finset.Ioc R (2 * R)) (Finset.range (Nat.lcm d1 d2))]

/-! ## The sum over `r` and `a` commute -/

lemma sum_comm_three (s1 s2 s3 : Finset ℕ) (f : ℕ → ℕ → ℕ → ℂ) :
    (∑ r ∈ s1, ∑ d1 ∈ s2, ∑ d2 ∈ s3, f r d1 d2)
      = ∑ d1 ∈ s2, ∑ d2 ∈ s3, ∑ r ∈ s1, f r d1 d2 := by
  rw [Finset.sum_comm (s := s1) (t := s2) (f := fun r d1 => ∑ d2 ∈ s3, f r d1 d2)]
  exact Finset.sum_congr rfl (fun d1 _ => Finset.sum_comm)

/-! ## The main theorem -/

end

end Work.FIArea4
