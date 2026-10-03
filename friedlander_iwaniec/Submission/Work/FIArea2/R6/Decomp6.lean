/-
# `FIArea2/R6/Decomp6.lean` — the round-6 pair-sum decomposition of `D* − D₀`

*FI* (9.10) is the statement that `D*(M,N) − D₀(M,N)` is small; by (9.11) and (5.26) this
difference is the `β_{z₁}β̄_{z₂}`-weighted sum of the per-pair errors `C(z₁,z₂) − C₀(z₁,z₂)` of
(9.1).  This file performs that reduction at the round-6 objects (`Work.FITop4.D0`, `C0`, `G0`
built on the count kernel (6.12) with the log `log(8|z₁z₂|/|Δ|)` of (7.10) in the `|w|²`-convention
of `Fhat`), together with the two algebraic facts the reduction needs:

* `Ccount` and the kernel `C₀` are *symmetric* in `(z₁,z₂)` (`Cnt_swap`, `C0_6_swap`);
* the antisymmetric part of `β_{z₁}β̄_{z₂}` against the symmetric kernel sums to `0`
  (`sum_antisym_mul_symm`), which is why `D₀` is real (`D0_6_im_eq_zero`) and why the complex
  pair-sum identity below holds without an `i`-term.

The results are copied/adapted from `Submission/Work/FIArea2/D0formMod_im_eq_zero.lean` (the frozen
`D0formMod` version, which is the same algebra at the frozen kernel).
-/
import Mathlib
import Submission.Work.FITop4.Areas6
import Submission.Work.FIArea2.G0_fix
import Submission.Work.FIArea2.D0formMod_im_eq_zero
import Submission.Work.FIArea2.Sec9AggDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The kernel is symmetric -/

/-- `Cnt` (6.12) is symmetric: the bijection `(γ₁,γ₂) ↦ (γ₂,γ₁)` reverses the congruence. -/
lemma Cnt_swap (z1 z2 : GaussianInt) : Cnt z1 z2 = Cnt z2 z1 := by
  unfold Cnt
  rw [Work.FIArea2.D0modAux.absDelta_swap z1 z2]
  refine Finset.card_bij (fun (p : ℕ × ℕ) (_ : p ∈ _) => (p.2, p.1)) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
    obtain ⟨hpS, hc1, hc2⟩ := hp
    refine ⟨⟨hpS.2, hpS.1⟩, ?_, ?_⟩
    · rw [← Int.dvd_iff_emod_eq_zero] at hc1 ⊢
      rw [show ((p.2 : ℤ)) ^ 2 * z1.re - ((p.1 : ℤ)) ^ 2 * z2.re
        = -(((p.1 : ℤ)) ^ 2 * z2.re - ((p.2 : ℤ)) ^ 2 * z1.re) by ring]
      exact dvd_neg.mpr hc1
    · rw [← Int.dvd_iff_emod_eq_zero] at hc2 ⊢
      rw [show ((p.2 : ℤ)) ^ 2 * z1.im - ((p.1 : ℤ)) ^ 2 * z2.im
        = -(((p.1 : ℤ)) ^ 2 * z2.im - ((p.2 : ℤ)) ^ 2 * z1.im) by ring]
      exact dvd_neg.mpr hc2
  · intro p1 hp1 p2 hp2 heq
    have h1 : p1.1 = p2.1 := by simpa using congrArg Prod.snd heq
    have h2 : p1.2 = p2.2 := by simpa using congrArg Prod.fst heq
    exact Prod.ext h1 h2
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hq
    obtain ⟨hqS, hc1, hc2⟩ := hq
    refine ⟨(q.2, q.1), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      refine ⟨⟨hqS.2, hqS.1⟩, ?_, ?_⟩
      · rw [← Int.dvd_iff_emod_eq_zero] at hc1 ⊢
        rw [show ((q.2 : ℤ)) ^ 2 * z2.re - ((q.1 : ℤ)) ^ 2 * z1.re
          = -(((q.1 : ℤ)) ^ 2 * z1.re - ((q.2 : ℤ)) ^ 2 * z2.re) by ring]
        exact dvd_neg.mpr hc1
      · rw [← Int.dvd_iff_emod_eq_zero] at hc2 ⊢
        rw [show ((q.2 : ℤ)) ^ 2 * z2.im - ((q.1 : ℤ)) ^ 2 * z1.im
          = -(((q.1 : ℤ)) ^ 2 * z1.im - ((q.2 : ℤ)) ^ 2 * z2.im) by ring]
        exact dvd_neg.mpr hc2
    · rfl

/-- The round-6 count kernel `G₀ = Cnt/|Δ|` is symmetric. -/
lemma G0_6_swap (z1 z2 : GaussianInt) :
    Work.FITop4.G0 z1 z2 = Work.FITop4.G0 z2 z1 := by
  unfold Work.FITop4.G0
  rw [Cnt_swap z1 z2, Work.FIArea2.D0modAux.absDelta_swap z1 z2]

/-- The (7.10) log of the round-6 main term is symmetric. -/
lemma logFac6_swap (z1 z2 : GaussianInt) :
    Work.FITop4.logFac6 z1 z2 = Work.FITop4.logFac6 z2 z1 := by
  unfold Work.FITop4.logFac6
  rw [mul_comm z1 z2, Work.FIArea2.D0modAux.absDelta_swap z1 z2]

/-- The (6.13) kernel `C₀` of the round-6 contract is symmetric. -/
lemma C0_6_swap (fhat : ℝ) (z1 z2 : GaussianInt) :
    Work.FITop4.C0 fhat z1 z2 = Work.FITop4.C0 fhat z2 z1 := by
  unfold Work.FITop4.C0
  rw [mul_comm z1 z2, logFac6_swap z1 z2, G0_6_swap z1 z2]

/-- `Ccount` (6.9) is symmetric in the pair. -/
lemma Ccount_swap (Pa : Work.FITop.Params) (f : ℤ → ℝ) (z1 z2 : GaussianInt) :
    Ccount Pa f z1 z2 = Ccount Pa f z2 z1 := by
  unfold Ccount
  refine Finset.sum_congr rfl fun w _ => ?_
  have h : (Work.FITop3.Zc w z1 * Work.FITop3.Zc w z2).re
      = (Work.FITop3.Zc w z2 * Work.FITop3.Zc w z1).re := by
    rw [mul_comm (Work.FITop3.Zc w z2) (Work.FITop3.Zc w z1)]
  rw [h, mul_comm]

/-! ## 2. The antisymmetric part vanishes -/

/-- A double sum of an antisymmetric factor times a symmetric one vanishes. -/
lemma sum_antisym_mul_symm {ι : Type*} [DecidableEq ι] (s : Finset ι) (g w : ι → ι → ℝ)
    (hg : ∀ a b, g a b = - g b a) (hw : ∀ a b, w a b = w b a) :
    ∑ a ∈ s, ∑ b ∈ s, g a b * w a b = 0 := by
  have h2' : ∀ a b : ι, g b a * w b a = - (g a b * w a b) := by
    intro a b
    rw [hg a b, hw a b]
    ring
  have h1 : (∑ a ∈ s, ∑ b ∈ s, g a b * w a b)
      = ∑ a ∈ s, ∑ b ∈ s, g b a * w b a := by
    rw [Finset.sum_comm, Finset.sum_comm]
  have h2 : (∑ a ∈ s, ∑ b ∈ s, g b a * w b a)
      = - (∑ a ∈ s, ∑ b ∈ s, g a b * w a b) := by
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => h2' a b))]
    simp only [Finset.sum_neg_distrib]
  linarith [h1, h2]

/-- The antisymmetry of `(β_{z₁}β̄_{z₂}).im` (with the coprimality indicator) against the
symmetric `Ccount`. -/
lemma im_antisymm (Pa : Work.FITop.Params) (f : ℤ → ℝ) (β : GaussianInt → ℂ) :
    ∀ a b : GaussianInt,
      (if Work.FIPlan.GaussCoprime a b then (β a * star (β b)).im else 0)
        = - (if Work.FIPlan.GaussCoprime b a then (β b * star (β a)).im else 0) := by
  intro a b
  by_cases h : Work.FIPlan.GaussCoprime a b
  · have h' : Work.FIPlan.GaussCoprime b a := IsCoprime.symm h
    rw [if_pos h, if_pos h']
    simp only [Complex.mul_im, Complex.mul_re, Complex.conj_im, Complex.conj_re,
      Complex.star_def]
    ring
  · have h' : ¬ Work.FIPlan.GaussCoprime b a := fun hc => h (IsCoprime.symm hc)
    rw [if_neg h, if_neg h']; ring

/-- The imaginary part of `β_{z₁}β̄_{z₂}` against the symmetric `Ccount`, restricted to coprime
pairs, vanishes. -/
lemma sum_im_vanishes (Pa : Work.FITop.Params) (f : ℤ → ℝ) (β : GaussianInt → ℂ) :
    ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
        (if Work.FIPlan.GaussCoprime z1 z2 then
          (β z1 * star (β z2)).im * Ccount Pa f z1 z2 else 0) = 0 := by
  have hA := im_antisymm Pa f β
  have hB : ∀ a b : GaussianInt, Ccount Pa f a b = Ccount Pa f b a := fun a b =>
    Ccount_swap Pa f a b
  have h := sum_antisym_mul_symm (Work.FITop.boxN Pa)
    (fun a b => if Work.FIPlan.GaussCoprime a b then (β a * star (β b)).im else 0)
    (fun a b => Ccount Pa f a b) hA hB
  have hpoint : ∀ z1 z2 : GaussianInt,
      (if Work.FIPlan.GaussCoprime z1 z2 then (β z1 * star (β z2)).im * Ccount Pa f z1 z2 else 0)
        = (if Work.FIPlan.GaussCoprime z1 z2 then (β z1 * star (β z2)).im else 0)
            * Ccount Pa f z1 z2 := by
    intro z1 z2
    by_cases hc : Work.FIPlan.GaussCoprime z1 z2
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc]; ring
  calc ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
        (if Work.FIPlan.GaussCoprime z1 z2 then
          (β z1 * star (β z2)).im * Ccount Pa f z1 z2 else 0)
      = ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          ((if Work.FIPlan.GaussCoprime z1 z2 then (β z1 * star (β z2)).im else 0)
            * Ccount Pa f z1 z2) := by
        simp only [hpoint]
    _ = 0 := h

/-! ## 3. `D₀` is real, and the pair-sum identity -/

/-- The round-6 main term `D₀` of (9.11) is real. -/
theorem D0_6_im_eq_zero (Rz : ℤ) (fhat : ℝ) (β : GaussianInt → ℂ) :
    (Work.FITop4.D0 Rz fhat β).im = 0 := by
  have hconj : star (Work.FITop4.D0 Rz fhat β) = Work.FITop4.D0 Rz fhat β := by
    rw [Work.FITop4.D0]
    refine Work.FIArea2.D0modAux.star_double_sum_eq_of_swap (Work.FIPlan.gBox Rz) _
      (fun z1 z2 => ?_)
    by_cases h : Work.FIPlan.GaussCoprime z1 z2
    · have h' : Work.FIPlan.GaussCoprime z2 z1 := IsCoprime.symm h
      rw [if_pos h, if_pos h', C0_6_swap fhat z1 z2]
      simp only [star_mul, star_star, Work.FIArea2.D0modAux.star_coe_real]
      ring
    · have h' : ¬ Work.FIPlan.GaussCoprime z2 z1 := fun hc => h (IsCoprime.symm hc)
      rw [if_neg h, if_neg h', star_zero]
  exact Complex.conj_eq_iff_im.mp (by simpa using hconj)

/-- **(5.26) vs (9.11)**, real form: pushing `re` into the pair sum. -/
theorem D0_6_re_eq (Pa : Work.FITop.Params) (f : ℤ → ℝ) (β : GaussianInt → ℂ) :
    (Work.FITop4.D0 (Work.FITop.radN Pa) (Work.FITop3.Fhat Pa f) β).re
      = ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          if Work.FIPlan.GaussCoprime z1 z2 then
            (β z1 * star (β z2)).re * Work.FITop4.C0 (Work.FITop3.Fhat Pa f) z1 z2
          else 0 := by
  unfold Work.FITop4.D0 Work.FITop.boxN
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun z1 _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun z2 _ => ?_
  by_cases hc : Work.FIPlan.GaussCoprime z1 z2
  · simp only [hc, if_true]
    rw [Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re]
    ring
  · simp [hc, Complex.zero_re]

/-- **(5.26) vs (9.11)** at the round-6 objects: the frozen `D*` minus the real part of the
round-6 `D₀` is the `(β_{z₁}β̄_{z₂}).re`-weighted sum of the per-pair errors of (9.1). -/
theorem Dstar_sub_D0_6_re (Pa : Work.FITop.Params) (f : ℤ → ℝ) (β : GaussianInt → ℂ) :
    Work.FITop3.Dstar Pa f β
        - (Work.FITop4.D0 (Work.FITop.radN Pa) (Work.FITop3.Fhat Pa f) β).re
      = ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          if Work.FIPlan.GaussCoprime z1 z2 then
            (β z1 * star (β z2)).re
              * (Ccount Pa f z1 z2 - Work.FITop4.C0 (Work.FITop3.Fhat Pa f) z1 z2)
          else 0 := by
  rw [Dstar_eq_pairSum, D0_6_re_eq, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun z1 _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun z2 _ => ?_
  by_cases hc : Work.FIPlan.GaussCoprime z1 z2 <;> simp [hc, mul_sub]

/-- The norm bound: `D* − D₀` is controlled by `‖β z₁‖‖β z₂‖` times the per-pair error of (9.1).
(`D₀` is real by `D0_6_im_eq_zero`, so this bounds the complex distance.) -/
theorem norm_Dstar_sub_D0_6_le (Pa : Work.FITop.Params) (f : ℤ → ℝ) (β : GaussianInt → ℂ) :
    ‖((Work.FITop3.Dstar Pa f β : ℝ) : ℂ)
        - Work.FITop4.D0 (Work.FITop.radN Pa) (Work.FITop3.Fhat Pa f) β‖
      ≤ ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          if Work.FIPlan.GaussCoprime z1 z2 then
            ‖β z1‖ * ‖β z2‖
              * |Ccount Pa f z1 z2 - Work.FITop4.C0 (Work.FITop3.Fhat Pa f) z1 z2|
          else 0 := by
  have him := D0_6_im_eq_zero (Work.FITop.radN Pa) (Work.FITop3.Fhat Pa f) β
  have hcz : ((Work.FITop3.Dstar Pa f β : ℝ) : ℂ)
      - Work.FITop4.D0 (Work.FITop.radN Pa) (Work.FITop3.Fhat Pa f) β
      = ((Work.FITop3.Dstar Pa f β
          - (Work.FITop4.D0 (Work.FITop.radN Pa) (Work.FITop3.Fhat Pa f) β).re : ℝ) : ℂ) := by
    refine Complex.ext ?_ ?_ <;> simp [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, him]
  rw [hcz, Complex.norm_real, Real.norm_eq_abs, Dstar_sub_D0_6_re]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine Finset.sum_le_sum fun z1 _ => ?_
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine Finset.sum_le_sum fun z2 _ => ?_
  by_cases hc : Work.FIPlan.GaussCoprime z1 z2
  · have h3 : |(β z1 * star (β z2)).re| ≤ ‖β z1‖ * ‖β z2‖ := by
      calc |(β z1 * star (β z2)).re| ≤ ‖β z1 * star (β z2)‖ :=
            Complex.abs_re_le_norm (β z1 * star (β z2))
        _ = ‖β z1‖ * ‖β z2‖ := by rw [norm_mul, norm_star]
    have h4 : |(β z1 * star (β z2)).re
            * (Ccount Pa f z1 z2 - Work.FITop4.C0 (Work.FITop3.Fhat Pa f) z1 z2)|
        ≤ ‖β z1‖ * ‖β z2‖
            * |Ccount Pa f z1 z2 - Work.FITop4.C0 (Work.FITop3.Fhat Pa f) z1 z2| := by
      calc |(β z1 * star (β z2)).re
              * (Ccount Pa f z1 z2 - Work.FITop4.C0 (Work.FITop3.Fhat Pa f) z1 z2)|
          = |(β z1 * star (β z2)).re|
              * |Ccount Pa f z1 z2 - Work.FITop4.C0 (Work.FITop3.Fhat Pa f) z1 z2| := abs_mul _ _
        _ ≤ (‖β z1‖ * ‖β z2‖)
              * |Ccount Pa f z1 z2 - Work.FITop4.C0 (Work.FITop3.Fhat Pa f) z1 z2| :=
            mul_le_mul_of_nonneg_right h3 (abs_nonneg _)
        _ = ‖β z1‖ * ‖β z2‖
              * |Ccount Pa f z1 z2 - Work.FITop4.C0 (Work.FITop3.Fhat Pa f) z1 z2| := by ring
    simpa [hc] using h4
  · simp [hc]

end

end Work.FIArea2.R6
