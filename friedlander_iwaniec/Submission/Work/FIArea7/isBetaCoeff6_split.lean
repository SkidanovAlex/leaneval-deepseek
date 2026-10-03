
/-
# `Submission.Work.FIArea7.isBetaCoeff6_split` — the A2 algebraic bridge of *FI* §17
-/
import Mathlib
import Submission.Work.FIArea7.Bridge17Defs
import Submission.Work.FIArea7.UniCharTerm6
import Submission.Work.FIArea4.arg_sub_bounds

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. Elementary helpers -/

/-- `z.toComplex`'s imaginary part is `z.im` read in `ℝ`. -/
lemma toComplex_im_eq (z : GaussianInt) : z.toComplex.im = (z.im : ℝ) :=
  (GaussianInt.intCast_im z).symm

/-- A mollifier that has no mass at negative angles vanishes at `0` (by continuity). -/
lemma moll_zero_of_support {q : ℝ → ℝ} (hcont : ContDiff ℝ 2 q)
    (hsupp : ∀ α, q α ≠ 0 → 0 ≤ α) : q 0 = 0 := by
  have hzero : ∀ α < (0 : ℝ), q α = 0 := by
    intro α hα
    by_contra hne
    exact absurd (hsupp α hne) (not_le.mpr hα)
  have hclosed : IsClosed {x : ℝ | q x = 0} := isClosed_eq hcont.continuous continuous_const
  have hsub : Set.Iio (0 : ℝ) ⊆ {x : ℝ | q x = 0} := fun x hx => hzero x hx
  have h0 : (0 : ℝ) ∈ closure (Set.Iio (0 : ℝ)) := by
    rw [closure_Iio]; simp
  exact closure_minimal hsub hclosed h0

/-- `2πθ√(1+θ) < ϑ` under the hypothesis `9θ ≤ ϑ` of the contract. -/
lemma two_pi_theta_mul_sqrt_lt (Pa : Work.FITop.Params) (hθϑ : 9 * Pa.θ ≤ Pa.ϑ) :
    2 * Real.pi * Pa.θ * Real.sqrt (1 + Pa.θ) < Pa.ϑ := by
  have hθ0 : 0 ≤ Pa.θ := le_of_lt Pa.hθ0
  have hθ8 : Pa.θ ≤ 1 / 8 := Work.FIArea4.theta_le_eighth Pa
  have hϑ0 : 0 < Pa.ϑ := Pa.hϑ0
  have hs : Real.sqrt (1 + Pa.θ) ≤ 9 / 8 := by
    have h1 : Real.sqrt (1 + Pa.θ) ≤ Real.sqrt ((9 / 8) ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 9 / 8)] at h1
  have hθ : Pa.θ ≤ Pa.ϑ / 9 := by linarith
  have hle : 2 * Real.pi * Pa.θ * Real.sqrt (1 + Pa.θ)
      ≤ 2 * Real.pi * (Pa.ϑ / 9) * (9 / 8) := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hθ (by positivity)
    · exact hs
    · positivity
    · positivity
  have hval : 2 * Real.pi * (Pa.ϑ / 9) * (9 / 8) = Real.pi / 4 * Pa.ϑ := by ring
  rw [hval] at hle
  nlinarith [Real.pi_lt_four, hϑ0]

/-- **The sector is trivial when it is not normalised.** -/
lemma abs_im_lt_of_inPolarBox_not_normalized {Pa : Work.FITop.Params} {φ : ℝ} {z : GaussianInt}
    (hB : Work.FITop4.InPolarBox Pa φ z)
    (hφ : ¬ (-Real.pi ≤ φ ∧ φ ≤ Real.pi - 2 * Real.pi * Pa.θ))
    (hθϑ : 9 * Pa.θ ≤ Pa.ϑ) :
    |(z.im : ℝ)| < Pa.ϑ * Real.sqrt Pa.N := by
  obtain ⟨-, hradlo, hradhi, hanglo, hanghi⟩ := hB
  have hπθ : 2 * Real.pi * Pa.θ ≤ 1 := Work.FIArea4.two_pi_theta_le_one Pa
  have him : |(z.im : ℝ)| = ‖z.toComplex‖ * |Real.sin z.toComplex.arg| := by
    rw [GaussianInt.intCast_im z, ← Complex.norm_mul_sin_arg z.toComplex, abs_mul,
      abs_of_nonneg (norm_nonneg _)]
  have hnorm : ‖z.toComplex‖ ≤ Real.sqrt ((1 + Pa.θ) * Pa.N) := by
    rw [← Work.FIArea4.sqrt_gnorm z]
    exact Real.sqrt_le_sqrt hradhi
  have hnum : 2 * Real.pi * Pa.θ * Real.sqrt (1 + Pa.θ) < Pa.ϑ :=
    two_pi_theta_mul_sqrt_lt Pa hθϑ
  have hcases : φ < -Real.pi ∨ Real.pi - 2 * Real.pi * Pa.θ < φ := by
    by_contra h
    push Not at h
    exact hφ ⟨h.1, h.2⟩
  have hsin : |Real.sin z.toComplex.arg| < 2 * Real.pi * Pa.θ := by
    have harggt : -Real.pi < z.toComplex.arg := Complex.neg_pi_lt_arg _
    have hargle : z.toComplex.arg ≤ Real.pi := Complex.arg_le_pi _
    rcases hcases with hlt | hgt
    · have ht0 : 0 < z.toComplex.arg + Real.pi := by linarith
      have ht1 : z.toComplex.arg + Real.pi < 2 * Real.pi * Pa.θ := by linarith
      have hsinarg : Real.sin z.toComplex.arg
          = -Real.sin (z.toComplex.arg + Real.pi) := by
        rw [Real.sin_add_pi, neg_neg]
      have hnn : 0 ≤ Real.sin (z.toComplex.arg + Real.pi) := by
        refine Real.sin_nonneg_of_mem_Icc ⟨le_of_lt ht0, ?_⟩
        linarith [Real.pi_gt_three]
      rw [hsinarg, abs_neg, abs_of_nonneg hnn]
      linarith [Real.sin_le (le_of_lt ht0)]
    · have ht0 : 0 ≤ Real.pi - z.toComplex.arg := by linarith
      have ht1 : Real.pi - z.toComplex.arg < 2 * Real.pi * Pa.θ := by linarith
      have hsinarg : Real.sin z.toComplex.arg
          = Real.sin (Real.pi - z.toComplex.arg) := by rw [Real.sin_pi_sub]
      have hnn : 0 ≤ Real.sin (Real.pi - z.toComplex.arg) := by
        refine Real.sin_nonneg_of_mem_Icc ⟨ht0, ?_⟩
        linarith [Real.pi_gt_three]
      rw [hsinarg, abs_of_nonneg hnn]
      linarith [Real.sin_le ht0]
  have hNpos : (0 : ℝ) < Pa.N := by linarith [Pa.hN1]
  calc |(z.im : ℝ)| = ‖z.toComplex‖ * |Real.sin z.toComplex.arg| := him
    _ ≤ Real.sqrt ((1 + Pa.θ) * Pa.N) * (2 * Real.pi * Pa.θ) :=
        mul_le_mul hnorm (le_of_lt hsin) (abs_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt Pa.N * (2 * Real.pi * Pa.θ * Real.sqrt (1 + Pa.θ)) := by
        rw [Real.sqrt_mul (by linarith [Pa.hθ0] : (0 : ℝ) ≤ 1 + Pa.θ)]
        ring
    _ < Real.sqrt Pa.N * Pa.ϑ :=
        mul_lt_mul_of_pos_left hnum (Real.sqrt_pos.mpr hNpos)
    _ = Pa.ϑ * Real.sqrt Pa.N := by ring

/-! ## 2. The bridge -/

/-- **A2: the algebraic §17 bridge** — every round-6 coefficient on an axis-free box is, up to the
divisor condition (5.9), the coefficient `betaTilde` of `Bridge17Defs` (*FI* p. 1015 "we no longer
need the angle mollifier"; p. 1009 "(5.7) … detected by characters"; (10.4) "(5.9) removed").
See `Submission/Work/FIArea7/AREA7_ROUTE_LEAD.md` §2.2 (A2). -/
theorem isBetaCoeff6_split {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt} {β : GaussianInt → ℂ}
    (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β)
    (hfar : ∀ z, Work.FITop4.InPolarBox Pa φ z → Work.FITop4.IsAxisFree Pa z)
    (hθϑ : 9 * Pa.θ ≤ Pa.ϑ) :
    (∀ z, β z = 0) ∨
    ∃ q p : ℝ → ℝ, Work.FIArea7.IsMollPair Pa q p ∧
      -Real.pi ≤ φ ∧ φ ≤ Real.pi - 2 * Real.pi * Pa.θ ∧
      ∀ z, β z = Work.FIArea7.betaTilde Pa q p φ z0 z
                 * (if (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ then 1 else 0) := by
  obtain ⟨q, p, hqcd, hpcd, hq0, hq1, hqsup, hqder, hp0, hp1, hpsup, hpder, hβf⟩ := hβ
  have hq00 : q 0 = 0 := moll_zero_of_support hqcd (fun α h => (hqsup α h).1)
  by_cases hφ : -Real.pi ≤ φ ∧ φ ≤ Real.pi - 2 * Real.pi * Pa.θ
  · right
    refine ⟨q, p, ?_, hφ.1, hφ.2, ?_⟩
    · exact ⟨hqcd, hpcd, fun α => ⟨hq0 α, hq1 α⟩, hqsup, hqder,
        fun u => ⟨hp0 u, hp1 u⟩, hpsup, hpder⟩
    · intro z
      set α : ℝ := Complex.arg z.toComplex - φ with hα
      set n : ℕ := Work.FIPlan.gnorm z with hn
      rw [hβf z]
      rw [Work.FIArea7.betaTilde, Work.FIArea7.radBetaCls, Work.FIArea7.radBeta]
      rw [← hn, ← hα]
      set c1 : Prop := Work.FITop4.InPolarBox Pa φ z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
          (((n.divisors.card : ℕ) : ℝ) ≤ Pa.τ) ∧ Work.FITop4.SameClass8 z z0 ∧
          Work.FITop4.IsAxisFree Pa z with hc1
      set c2 : Prop := Work.FITop4.SameClass8 z z0 ∧
          (Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z) ∧
          (((n.divisors.card : ℕ) : ℝ) ≤ Pa.τ) with hc2
      by_cases hq : q α = 0
      · have hVz : ((q α * p (n : ℝ) : ℝ) : ℂ) * (ArithmeticFunction.moebius n : ℂ)
            * ((Work.FIPlan.gammaTrunc Pa.C n : ℝ) : ℂ) = 0 := by
          rw [show q α * p (n : ℝ) = 0 by simp [hq], Complex.ofReal_zero, zero_mul, zero_mul]
        have hqz : ((q α : ℝ) : ℂ) = 0 := by simp [hq]
        rw [hVz, hqz]
        simp
      by_cases hp : p (n : ℝ) = 0
      · have hVz : ((q α * p (n : ℝ) : ℝ) : ℂ) * (ArithmeticFunction.moebius n : ℂ)
            * ((Work.FIPlan.gammaTrunc Pa.C n : ℝ) : ℂ) = 0 := by
          rw [show q α * p (n : ℝ) = 0 by rw [hp, mul_zero], Complex.ofReal_zero,
            zero_mul, zero_mul]
        have hpz : ((p (n : ℝ) : ℝ) : ℂ) = 0 := by simp [hp]
        rw [hVz, hpz]
        simp
      have hiffc : c1 ↔ c2 := by
        rw [hc1, hc2]
        constructor
        · rintro ⟨hB, hNp, hT, hS, -⟩
          exact ⟨hS, ⟨hB.1, hNp⟩, hT⟩
        · rintro ⟨hS, ⟨hP, hNp⟩, hT⟩
          have hqsup' := hqsup α hq
          have hαne : α ≠ 0 := by
            intro h0
            exact hq (by rw [h0]; exact hq00)
          have hαpos : 0 < α := lt_of_le_of_ne' hqsup'.1 hαne
          have hp' := hpsup (n : ℝ) hp
          rw [hn] at hp'
          have hB : Work.FITop4.InPolarBox Pa φ z := by
            refine ⟨hP, hp'.1, hp'.2, ?_, ?_⟩
            · rw [hα] at hαpos
              linarith
            · rw [hα] at hqsup'
              linarith [hqsup'.2]
          exact ⟨hB, hNp, hT, hS, hfar z hB⟩
      by_cases h1 : c1
      · have h2 := hiffc.mp h1
        rw [hc2] at h2
        obtain ⟨hS, hPN, hT⟩ := h2
        rw [if_pos h1, if_pos hS, if_pos hPN, if_pos hT]
        rw [Complex.ofReal_mul]
        ring
      · rw [if_neg h1]
        have h2 : ¬ c2 := fun h => h1 (hiffc.mpr h)
        rw [hc2] at h2
        by_cases hS : Work.FITop4.SameClass8 z z0 <;>
          by_cases hPN : (Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z) <;>
          by_cases hT : (((n.divisors.card : ℕ) : ℝ) ≤ Pa.τ)
        · exact absurd ⟨hS, hPN, hT⟩ h2
        · simp [hS, hPN, hT]
        · simp [hS, hPN, hT]
        · simp [hS, hPN, hT]
        · simp [hS, hPN, hT]
        · simp [hS, hPN, hT]
        · simp [hS, hPN, hT]
        · simp [hS, hPN, hT]
  · left
    intro z
    rw [hβf z]
    by_cases hc : (Work.FITop4.InPolarBox Pa φ z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
        (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ ∧
        Work.FITop4.SameClass8 z z0 ∧ Work.FITop4.IsAxisFree Pa z)
    · exfalso
      have him := abs_im_lt_of_inPolarBox_not_normalized hc.1 hφ hθϑ
      have hfar' := hfar z hc.1
      linarith [hfar'.2, him]
    · rw [if_neg hc]

end

end Work.FIArea7
