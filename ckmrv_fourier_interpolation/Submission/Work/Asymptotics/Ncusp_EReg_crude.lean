import Mathlib
import Submission.Work.Asymptotics.KMinusCuspBallLimit
import Submission.Work.Asymptotics.KMinusFunnelZBounds
import Submission.Work.Asymptotics.KMinusFunnelZBoundsLS
import Submission.Work.Asymptotics.ERegDefs
import Submission.Work.Asymptotics.EReg_atom_bounds
import Submission.Work.Asymptotics.EReg_alpha8_bound
import Submission.Work.Asymptotics.EReg_alpha24_bound

/-!
# The crude `E`-region bound for the cleared `K_-` numerator `Ncusp`

On the cusp-`0` tile `E = {τ : ℍ | 3/2 ≤ (S • τ).im}` the cleared numerator
`Ncusp ℓ d τ z = Δ(z)(j(τ)-j(z))z^{-(2-d/2)}K_-(τ,S•z)` is bounded by `(scale τ)^N e^{π Im z}`,
uniformly for `z` with `Im z ≥ 1`.

The `τ`-side input is the polynomial control of the cusp coefficients `αᵢ = Alpha ℓ d i τ` on
`E` (`EReg_alpha8_bound`, `EReg_alpha24_bound`) together with the `j`-bounds of
`EReg_atom_bounds`; for `d = 8` the relevant τ-coefficient is
`α₁ + α₂(1728 - j) = (α₁ - α₂ j) + 1728 α₂`, whose first summand is the `E`-order cancellation
combination bounded by `EReg_alpha8_bound`.  The `z`-side input is the pair of bounds
`KMinusFunnelZBounds`, `KMinusFunnelZBoundsLS` on the atoms `E₈V`, `E₆(U²-W²)`, `V`, `jV`,
`(E₁₀/Δ)(U²-W²)`, `E₁₀𝓛_S` and `(E₁₄/Δ)𝓛_S` for `Im z ≥ 1/3`.
-/

namespace Work.Asymptotics

open UpperHalfPlane
open Work.Kernels

set_option maxHeartbeats 32000000

noncomputable section

/-- Norm of a product, from bounds on the factors. -/
private lemma n2 {a b : ℂ} {A B : ℝ} (hA : 0 ≤ A) (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) :
    ‖a * b‖ ≤ A * B := by
  rw [norm_mul]
  exact mul_le_mul ha hb (norm_nonneg _) hA

/-- Norm of a sum of three terms. -/
private lemma nadd3 (a b c : ℂ) : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
  have h1 := norm_add_le (a + b) c
  have h2 := norm_add_le a b
  linarith [h1, h2, norm_nonneg (a + b), norm_nonneg a, norm_nonneg b, norm_nonneg c]

/-- Norm of a sum of four terms. -/
private lemma nadd4 (a b c d : ℂ) : ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  have h1 := norm_add_le (a + b + c) d
  have h2 := nadd3 (a + b) c d
  rw [show a + b + c = (a + b) + c from rfl] at h2
  have h3 := norm_add_le a b
  linarith [h1, h2, h3, norm_nonneg (a + b + c), norm_nonneg (a + b), norm_nonneg a,
    norm_nonneg b, norm_nonneg c, norm_nonneg d]

/-- **The crude `E`-region bound, `d = 8`.** -/
theorem Ncusp_EReg_crude_8 (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ z : UpperHalfPlane), τ ∈ Work.Asymptotics.EReg → 1 ≤ z.im →
      ‖Work.Asymptotics.Ncusp ℓ 8 τ z‖
        ≤ C * (Work.Kernels.scale τ) ^ N * Real.exp (Real.pi * z.im) := by
  obtain ⟨Ca, Na, hCa, hNa, hAll⟩ := EReg_alpha8_bound ℓ
  obtain ⟨Cz1, hCz1, hz1⟩ := KMinusFunnelZBounds
  obtain ⟨Cz2, hCz2, hz2⟩ := KMinusFunnelZBoundsLS ℓ
  set K : ℝ := (Ca + 1) * (Cz1 + Cz2 + 1) + 1 with hK
  have hK0 : 0 < K := by rw [hK]; positivity
  have hCaK : Ca ≤ K := by rw [hK]; nlinarith [hCa, hCz1, hCz2]
  refine ⟨‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ *
    (3456 * K * (Cz2 + 1) + (K + 1728 * K) * (2 * (Cz1 + 1)) + K * (2 * (Cz1 + 1))) + 1,
    Na, by positivity, hNa, fun τ z hτ hz => ?_⟩
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hsN1 : (1 : ℝ) ≤ (Work.Kernels.scale τ) ^ Na := Real.one_le_rpow hs1 hNa
  have hsN0 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ Na := by positivity
  have hz3 : (1 : ℝ) / 3 ≤ z.im := by linarith
  have hexp1 : (1 : ℝ) ≤ Real.exp (Real.pi * z.im) := Real.one_le_exp (by positivity)
  have hexpnn : (0 : ℝ) ≤ Real.exp (Real.pi * z.im) := Real.exp_nonneg _
  -- `τ`-side
  have hA0 : ‖Work.Asymptotics.Alpha ℓ 8 0 τ‖ ≤ K * (Work.Kernels.scale τ) ^ Na :=
    le_trans (hAll τ hτ).1 (mul_le_mul_of_nonneg_right hCaK hsN0)
  have hA2 : ‖Work.Asymptotics.Alpha ℓ 8 2 τ‖ ≤ K * (Work.Kernels.scale τ) ^ Na :=
    le_trans (hAll τ hτ).2.1 (mul_le_mul_of_nonneg_right hCaK hsN0)
  have hAc : ‖Work.Asymptotics.Alpha ℓ 8 1 τ
      - Work.Asymptotics.Alpha ℓ 8 2 τ * Work.Kernels.jInvariantFun τ‖
      ≤ K * (Work.Kernels.scale τ) ^ Na :=
    le_trans (hAll τ hτ).2.2 (mul_le_mul_of_nonneg_right hCaK hsN0)
  have hA12 : ‖Work.Asymptotics.Alpha ℓ 8 1 τ
      + Work.Asymptotics.Alpha ℓ 8 2 τ * (1728 - Work.Kernels.jInvariantFun τ)‖
      ≤ K * (Work.Kernels.scale τ) ^ Na + 1728 * (K * (Work.Kernels.scale τ) ^ Na) := by
    have heq : Work.Asymptotics.Alpha ℓ 8 1 τ
        + Work.Asymptotics.Alpha ℓ 8 2 τ * (1728 - Work.Kernels.jInvariantFun τ)
        = (Work.Asymptotics.Alpha ℓ 8 1 τ
            - Work.Asymptotics.Alpha ℓ 8 2 τ * Work.Kernels.jInvariantFun τ)
          + 1728 * Work.Asymptotics.Alpha ℓ 8 2 τ := by ring
    rw [heq]
    refine le_trans (norm_add_le _ _) ?_
    have h2 : ‖(1728 : ℂ) * Work.Asymptotics.Alpha ℓ 8 2 τ‖
        = 1728 * ‖Work.Asymptotics.Alpha ℓ 8 2 τ‖ := by
      rw [norm_mul]; norm_num
    rw [h2]
    linarith [hAc, hA2]
  -- `z`-side
  have hZ1 : ‖Work.Kernels.E8Fun z * Work.Kernels.VFun z‖ ≤ Cz1 + 1 := by
    linarith [(hz1 z hz3).2.1, hCz1]
  have hZ2 : ‖Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2)‖
      ≤ 2 * (Cz1 + 1) := by
    have h1 := (hz1 z hz3).1
    have h2 := (hz1 z hz3).2.1
    have h1' : ‖Work.Kernels.E8Fun z * Work.Kernels.VFun z
        + Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2)‖ ≤ Cz1 := h1
    have h3 : ‖Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2)‖
        ≤ ‖Work.Kernels.E8Fun z * Work.Kernels.VFun z
            + Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2)‖
          + ‖Work.Kernels.E8Fun z * Work.Kernels.VFun z‖ := by
      have h4 := norm_add_le (Work.Kernels.E8Fun z * Work.Kernels.VFun z
          + Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2))
        (-(Work.Kernels.E8Fun z * Work.Kernels.VFun z))
      have h5 : Work.Kernels.E8Fun z * Work.Kernels.VFun z
          + Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2)
          + -(Work.Kernels.E8Fun z * Work.Kernels.VFun z)
          = Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2) := by ring
      rw [h5, norm_neg] at h4
      exact h4
    linarith [h1', h2, h3, hCz1]
  have hZ3 : ‖Work.Kernels.E10Fun z * ℓ.L_S z‖ ≤ Cz2 + 1 := by
    linarith [(hz2 z hz3).1, hCz2]
  -- the three pieces of `T8`
  have hfk0 : Work.Kernels.fk (Work.Asymptotics.ulen 8 0) z = Work.Kernels.E10Fun z := by
    simp [Work.Asymptotics.ulen, Work.Kernels.fk]
  have hfk1 : Work.Kernels.fk (Work.Asymptotics.ulen 8 1) z = Work.Kernels.E8Fun z := by
    simp [Work.Asymptotics.ulen, Work.Kernels.fk, Work.Kernels.E8Fun]
  have hfk2 : Work.Kernels.fk (Work.Asymptotics.ulen 8 2) z = Work.Kernels.E6Fun z := by
    simp [Work.Asymptotics.ulen, Work.Kernels.fk]
  have hp1 : ‖(-3456 : ℂ) * Work.Asymptotics.Alpha ℓ 8 0 τ
      * (Work.Kernels.fk (Work.Asymptotics.ulen 8 0) z * ℓ.L_S z)‖
      ≤ (3456 * K * (Cz2 + 1)) * (Work.Kernels.scale τ) ^ Na := by
    have hA : ‖(-3456 : ℂ) * Work.Asymptotics.Alpha ℓ 8 0 τ‖
        ≤ 3456 * (K * (Work.Kernels.scale τ) ^ Na) := by
      rw [norm_mul]
      norm_num
      exact hA0
    have hB : ‖Work.Kernels.fk (Work.Asymptotics.ulen 8 0) z * ℓ.L_S z‖ ≤ Cz2 + 1 := by
      rw [hfk0]; exact hZ3
    calc ‖(-3456 : ℂ) * Work.Asymptotics.Alpha ℓ 8 0 τ
          * (Work.Kernels.fk (Work.Asymptotics.ulen 8 0) z * ℓ.L_S z)‖
        = ‖(-3456 : ℂ) * Work.Asymptotics.Alpha ℓ 8 0 τ‖
          * ‖Work.Kernels.fk (Work.Asymptotics.ulen 8 0) z * ℓ.L_S z‖ := norm_mul _ _
      _ ≤ (3456 * (K * (Work.Kernels.scale τ) ^ Na)) * (Cz2 + 1) :=
          mul_le_mul hA hB (norm_nonneg _) (by positivity)
      _ = (3456 * K * (Cz2 + 1)) * (Work.Kernels.scale τ) ^ Na := by ring
  have hp2 : ‖(Work.Asymptotics.Alpha ℓ 8 1 τ
        + Work.Asymptotics.Alpha ℓ 8 2 τ * (1728 - Work.Kernels.jInvariantFun τ))
      * (Work.Kernels.fk (Work.Asymptotics.ulen 8 1) z * (-(Work.Kernels.VFun z)))‖
      ≤ ((K + 1728 * K) * (2 * (Cz1 + 1))) * (Work.Kernels.scale τ) ^ Na := by
    have hA : ‖Work.Asymptotics.Alpha ℓ 8 1 τ
        + Work.Asymptotics.Alpha ℓ 8 2 τ * (1728 - Work.Kernels.jInvariantFun τ)‖
        ≤ (K + 1728 * K) * (Work.Kernels.scale τ) ^ Na := by
      have he : K * (Work.Kernels.scale τ) ^ Na + 1728 * (K * (Work.Kernels.scale τ) ^ Na)
          = (K + 1728 * K) * (Work.Kernels.scale τ) ^ Na := by ring
      rw [he] at hA12
      exact hA12
    have hB : ‖Work.Kernels.fk (Work.Asymptotics.ulen 8 1) z * (-(Work.Kernels.VFun z))‖
        ≤ 2 * (Cz1 + 1) := by
      rw [hfk1, show Work.Kernels.E8Fun z * (-(Work.Kernels.VFun z))
          = -(Work.Kernels.E8Fun z * Work.Kernels.VFun z) by ring, norm_neg]
      linarith [hZ1]
    calc ‖(Work.Asymptotics.Alpha ℓ 8 1 τ
          + Work.Asymptotics.Alpha ℓ 8 2 τ * (1728 - Work.Kernels.jInvariantFun τ))
        * (Work.Kernels.fk (Work.Asymptotics.ulen 8 1) z * (-(Work.Kernels.VFun z)))‖
        = ‖Work.Asymptotics.Alpha ℓ 8 1 τ
            + Work.Asymptotics.Alpha ℓ 8 2 τ * (1728 - Work.Kernels.jInvariantFun τ)‖
          * ‖Work.Kernels.fk (Work.Asymptotics.ulen 8 1) z * (-(Work.Kernels.VFun z))‖ :=
          norm_mul _ _
      _ ≤ ((K + 1728 * K) * (Work.Kernels.scale τ) ^ Na) * (2 * (Cz1 + 1)) :=
          mul_le_mul hA hB (norm_nonneg _) (by positivity)
      _ = ((K + 1728 * K) * (2 * (Cz1 + 1))) * (Work.Kernels.scale τ) ^ Na := by ring
  have hp3 : ‖(-(Work.Asymptotics.Alpha ℓ 8 1 τ)
        + Work.Asymptotics.Alpha ℓ 8 2 τ * Work.Kernels.jInvariantFun τ)
      * (Work.Kernels.fk (Work.Asymptotics.ulen 8 2) z
          * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2))‖
      ≤ (K * (2 * (Cz1 + 1))) * (Work.Kernels.scale τ) ^ Na := by
    have hneg : ‖-(Work.Asymptotics.Alpha ℓ 8 1 τ)
        + Work.Asymptotics.Alpha ℓ 8 2 τ * Work.Kernels.jInvariantFun τ‖
        = ‖Work.Asymptotics.Alpha ℓ 8 1 τ
            - Work.Asymptotics.Alpha ℓ 8 2 τ * Work.Kernels.jInvariantFun τ‖ := by
      rw [show -(Work.Asymptotics.Alpha ℓ 8 1 τ)
          + Work.Asymptotics.Alpha ℓ 8 2 τ * Work.Kernels.jInvariantFun τ
          = -(Work.Asymptotics.Alpha ℓ 8 1 τ
              - Work.Asymptotics.Alpha ℓ 8 2 τ * Work.Kernels.jInvariantFun τ) by ring,
        norm_neg]
    have hA : ‖-(Work.Asymptotics.Alpha ℓ 8 1 τ)
        + Work.Asymptotics.Alpha ℓ 8 2 τ * Work.Kernels.jInvariantFun τ‖
        ≤ K * (Work.Kernels.scale τ) ^ Na := by
      rw [hneg]; exact hAc
    have hB : ‖Work.Kernels.fk (Work.Asymptotics.ulen 8 2) z
        * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2)‖ ≤ 2 * (Cz1 + 1) := by
      rw [hfk2]; exact hZ2
    calc ‖(-(Work.Asymptotics.Alpha ℓ 8 1 τ)
          + Work.Asymptotics.Alpha ℓ 8 2 τ * Work.Kernels.jInvariantFun τ)
        * (Work.Kernels.fk (Work.Asymptotics.ulen 8 2) z
            * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2))‖
        = ‖-(Work.Asymptotics.Alpha ℓ 8 1 τ)
            + Work.Asymptotics.Alpha ℓ 8 2 τ * Work.Kernels.jInvariantFun τ‖
          * ‖Work.Kernels.fk (Work.Asymptotics.ulen 8 2) z
            * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2)‖ := norm_mul _ _
      _ ≤ (K * (Work.Kernels.scale τ) ^ Na) * (2 * (Cz1 + 1)) :=
          mul_le_mul hA hB (norm_nonneg _) (by positivity)
      _ = (K * (2 * (Cz1 + 1))) * (Work.Kernels.scale τ) ^ Na := by ring
  have hT8 : ‖Work.Asymptotics.T8 ℓ τ z‖
      ≤ (3456 * K * (Cz2 + 1) + (K + 1728 * K) * (2 * (Cz1 + 1))
          + K * (2 * (Cz1 + 1))) * (Work.Kernels.scale τ) ^ Na := by
    rw [Work.Asymptotics.T8]
    have hsplit : ‖-3456 * Work.Asymptotics.Alpha ℓ 8 0 τ
          * Work.Kernels.fk (Work.Asymptotics.ulen 8 0) z * ℓ.L_S z
        + (Work.Asymptotics.Alpha ℓ 8 1 τ
            + Work.Asymptotics.Alpha ℓ 8 2 τ * (1728 - Work.Kernels.jInvariantFun τ))
          * Work.Kernels.fk (Work.Asymptotics.ulen 8 1) z * (-(Work.Kernels.VFun z))
        + (-(Work.Asymptotics.Alpha ℓ 8 1 τ)
            + Work.Asymptotics.Alpha ℓ 8 2 τ * Work.Kernels.jInvariantFun τ)
          * Work.Kernels.fk (Work.Asymptotics.ulen 8 2) z
          * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2)‖
        = ‖((-3456 : ℂ) * Work.Asymptotics.Alpha ℓ 8 0 τ
              * (Work.Kernels.fk (Work.Asymptotics.ulen 8 0) z * ℓ.L_S z))
            + ((Work.Asymptotics.Alpha ℓ 8 1 τ
                + Work.Asymptotics.Alpha ℓ 8 2 τ * (1728 - Work.Kernels.jInvariantFun τ))
              * (Work.Kernels.fk (Work.Asymptotics.ulen 8 1) z * (-(Work.Kernels.VFun z))))
            + ((-(Work.Asymptotics.Alpha ℓ 8 1 τ)
                + Work.Asymptotics.Alpha ℓ 8 2 τ * Work.Kernels.jInvariantFun τ)
              * (Work.Kernels.fk (Work.Asymptotics.ulen 8 2) z
                * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2)))‖ := by
      congr 1
      ring
    rw [hsplit]
    have htri := nadd3 ((-3456 : ℂ) * Work.Asymptotics.Alpha ℓ 8 0 τ
              * (Work.Kernels.fk (Work.Asymptotics.ulen 8 0) z * ℓ.L_S z))
            ((Work.Asymptotics.Alpha ℓ 8 1 τ
                + Work.Asymptotics.Alpha ℓ 8 2 τ * (1728 - Work.Kernels.jInvariantFun τ))
              * (Work.Kernels.fk (Work.Asymptotics.ulen 8 1) z * (-(Work.Kernels.VFun z))))
            ((-(Work.Asymptotics.Alpha ℓ 8 1 τ)
                + Work.Asymptotics.Alpha ℓ 8 2 τ * Work.Kernels.jInvariantFun τ)
              * (Work.Kernels.fk (Work.Asymptotics.ulen 8 2) z
                * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2)))
    refine le_trans htri ?_
    have hsum : (3456 * K * (Cz2 + 1)) * (Work.Kernels.scale τ) ^ Na
        + ((K + 1728 * K) * (2 * (Cz1 + 1))) * (Work.Kernels.scale τ) ^ Na
        + (K * (2 * (Cz1 + 1))) * (Work.Kernels.scale τ) ^ Na
        = (3456 * K * (Cz2 + 1) + (K + 1728 * K) * (2 * (Cz1 + 1))
            + K * (2 * (Cz1 + 1))) * (Work.Kernels.scale τ) ^ Na := by ring
    linarith [hp1, hp2, hp3, hsum.le, hsum.ge]
  have hfin : ‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * ‖Work.Asymptotics.T8 ℓ τ z‖
      ≤ (‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ *
          (3456 * K * (Cz2 + 1) + (K + 1728 * K) * (2 * (Cz1 + 1))
            + K * (2 * (Cz1 + 1))) + 1) * (Work.Kernels.scale τ) ^ Na := by
    have h1 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ Na := hsN0
    have h2 : ‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * ‖Work.Asymptotics.T8 ℓ τ z‖
        ≤ ‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ *
          ((3456 * K * (Cz2 + 1) + (K + 1728 * K) * (2 * (Cz1 + 1))
            + K * (2 * (Cz1 + 1))) * (Work.Kernels.scale τ) ^ Na) :=
      mul_le_mul_of_nonneg_left hT8 (norm_nonneg _)
    have h3 : ‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ *
          ((3456 * K * (Cz2 + 1) + (K + 1728 * K) * (2 * (Cz1 + 1))
            + K * (2 * (Cz1 + 1))) * (Work.Kernels.scale τ) ^ Na)
        = (‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ *
          (3456 * K * (Cz2 + 1) + (K + 1728 * K) * (2 * (Cz1 + 1))
            + K * (2 * (Cz1 + 1)))) * (Work.Kernels.scale τ) ^ Na := by ring
    have h4 : (‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ *
          (3456 * K * (Cz2 + 1) + (K + 1728 * K) * (2 * (Cz1 + 1))
            + K * (2 * (Cz1 + 1)))) * (Work.Kernels.scale τ) ^ Na
        ≤ (‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ *
          (3456 * K * (Cz2 + 1) + (K + 1728 * K) * (2 * (Cz1 + 1))
            + K * (2 * (Cz1 + 1))) + 1) * (Work.Kernels.scale τ) ^ Na :=
      mul_le_mul_of_nonneg_right (by linarith [norm_nonneg ((2 : ℂ) * Work.Kernels.c1728
        * (Real.pi : ℂ))⁻¹]) h1
    linarith [h2, h3.le, h3.ge, h4]
  calc ‖Work.Asymptotics.Ncusp ℓ 8 τ z‖
      = ‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹ * Work.Asymptotics.T8 ℓ τ z‖ := by
        rw [Work.Asymptotics.Ncusp_eight_expansion ℓ τ z]
    _ = ‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * ‖Work.Asymptotics.T8 ℓ τ z‖ :=
        norm_mul _ _
    _ ≤ (‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ *
          (3456 * K * (Cz2 + 1) + (K + 1728 * K) * (2 * (Cz1 + 1))
            + K * (2 * (Cz1 + 1))) + 1) * (Work.Kernels.scale τ) ^ Na := hfin
    _ ≤ (‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ *
          (3456 * K * (Cz2 + 1) + (K + 1728 * K) * (2 * (Cz1 + 1))
            + K * (2 * (Cz1 + 1))) + 1) * (Work.Kernels.scale τ) ^ Na
          * Real.exp (Real.pi * z.im) :=
        le_mul_of_one_le_right (by positivity) hexp1


end

end Work.Asymptotics
