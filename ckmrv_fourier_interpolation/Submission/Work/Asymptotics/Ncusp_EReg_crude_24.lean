import Mathlib
import Submission.Work.Asymptotics.KMinusCuspBallLimit
import Submission.Work.Asymptotics.KMinusFunnelZBounds
import Submission.Work.Asymptotics.KMinusFunnelZBoundsLS
import Submission.Work.Asymptotics.ERegDefs
import Submission.Work.Asymptotics.EReg_atom_bounds
import Submission.Work.Asymptotics.EReg_alpha24_bound

/-!
# The crude `E`-region bound for the cleared `K_-` numerator, `d = 24`

On the cusp-`0` tile `E = {τ : ℍ | 3/2 ≤ (S • τ).im}` the numerator
`Ncusp ℓ 24 τ z = Δ(z)(j(τ)-j(z))z^{10}K_-(τ,S•z)` is bounded by `C (scale τ)^N e^{π Im z}`
uniformly for `Im z ≥ 1`.

The `τ`-side input is `EReg_alpha24_bound` (the CKMRV `E`-order cancellation combinations
`α₀`, `α₂`, `α₁ - α₂`, `j(α₁ - α₂)`) and the `j`-bounds of `EReg_atom_bounds`; the `z`-side
input is `KMinusFunnelZBounds`/`KMinusFunnelZBoundsLS`.
-/

namespace Work.Asymptotics

open UpperHalfPlane
open Work.Kernels

set_option maxHeartbeats 8000000

noncomputable section

/-- The norm of a sum of three terms. -/
private lemma nadd3 (a b c : ℂ) : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
  have h1 := norm_add_le (a + b) c
  have h2 := norm_add_le a b
  linarith [h1, h2, norm_nonneg (a + b), norm_nonneg a, norm_nonneg b, norm_nonneg c]

/-- **The crude `E`-region bound, `d = 24`.** -/
theorem Ncusp_EReg_crude_24 (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ z : UpperHalfPlane),
      τ ∈ Work.Asymptotics.EReg → 1 ≤ z.im →
      ‖Work.Asymptotics.Ncusp ℓ 24 τ z‖
        ≤ C * (Work.Kernels.scale τ) ^ N * Real.exp (Real.pi * z.im) := by
  obtain ⟨Ca, Na, hCa, hNa, hAllA⟩ := EReg_alpha24_bound ℓ
  obtain ⟨Ca2, Na2, hCa2, hNa2, hAll2⟩ := EReg_atom_bounds ℓ
  obtain ⟨Cz1, hCz1, hz1⟩ := KMinusFunnelZBounds
  obtain ⟨Cz2, hCz2, hz2⟩ := KMinusFunnelZBoundsLS ℓ
  set M : ℝ := max (max Ca Ca2) (max (Cz1 + 1) (Cz2 + 1)) + 1 with hM
  set E : ℝ := Na + Na2 + 1 with hE
  have hM1 : (1 : ℝ) ≤ M := by
    rw [hM]
    have h0 : (0 : ℝ) ≤ max (max Ca Ca2) (max (Cz1 + 1) (Cz2 + 1)) :=
      le_trans (le_trans hCa.le (le_max_left Ca Ca2)) (le_max_left _ _)
    linarith
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM1
  have hMn : (0 : ℝ) ≤ M := hM0.le
  have hE0 : 0 ≤ E := by rw [hE]; linarith
  have hNaE : Na ≤ E := by rw [hE]; linarith
  have hNa2E : Na2 ≤ E := by rw [hE]; linarith
  have hCaM : Ca ≤ M := by
    rw [hM]
    have h1 : Ca ≤ max Ca Ca2 := le_max_left _ _
    have h2 : max Ca Ca2 ≤ max (max Ca Ca2) (max (Cz1 + 1) (Cz2 + 1)) := le_max_left _ _
    linarith
  have hCa2M : Ca2 ≤ M := by
    rw [hM]
    have h1 : Ca2 ≤ max Ca Ca2 := le_max_right _ _
    have h2 : max Ca Ca2 ≤ max (max Ca Ca2) (max (Cz1 + 1) (Cz2 + 1)) := le_max_left _ _
    linarith
  have hCz1M : Cz1 + 1 ≤ M := by
    rw [hM]
    have h1 : Cz1 + 1 ≤ max (Cz1 + 1) (Cz2 + 1) := le_max_left _ _
    have h2 : max (Cz1 + 1) (Cz2 + 1)
        ≤ max (max Ca Ca2) (max (Cz1 + 1) (Cz2 + 1)) := le_max_right _ _
    linarith
  have hCz2M : Cz2 + 1 ≤ M := by
    rw [hM]
    have h1 : Cz2 + 1 ≤ max (Cz1 + 1) (Cz2 + 1) := le_max_right _ _
    have h2 : max (Cz1 + 1) (Cz2 + 1)
        ≤ max (max Ca Ca2) (max (Cz1 + 1) (Cz2 + 1)) := le_max_right _ _
    linarith
  have hCpos : 0 < ‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * (12102 * M * M) + 1 := by
    have h1 : (0 : ℝ) ≤ 12102 * M * M := mul_nonneg (mul_nonneg (by norm_num) hMn) hMn
    have h2 : (0 : ℝ) ≤ ‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ := norm_nonneg _
    have h3 : (0 : ℝ) ≤ ‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * (12102 * M * M) :=
      mul_nonneg h2 h1
    linarith
  refine ⟨‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * (12102 * M * M) + 1, E,
    hCpos, hE0, ?_⟩
  intro τ z hτ hz
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hspos : (0 : ℝ) < Work.Kernels.scale τ := Work.Kernels.scale_pos τ
  have hSg0 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ E := Real.rpow_nonneg hspos.le E
  have hP1 : (1 : ℝ) ≤ Real.exp (Real.pi * z.im) :=
    Real.one_le_exp (by nlinarith [Real.pi_pos, hz])
  have hP0 : (0 : ℝ) ≤ Real.exp (Real.pi * z.im) := Real.exp_nonneg _
  have hz3 : (1 : ℝ) / 3 ≤ z.im := by linarith
  have hMM0 : (0 : ℝ) ≤ M * M := mul_nonneg hMn hMn
  have hMMS0 : (0 : ℝ) ≤ M * M * (Work.Kernels.scale τ) ^ E := mul_nonneg hMM0 hSg0
  have hMErr0 : (0 : ℝ) ≤ M * (Work.Kernels.scale τ) ^ E := mul_nonneg hMn hSg0
  have hstep : ∀ {c n : ℝ} {f : ℂ}, c ≤ M → n ≤ E → ‖f‖ ≤ c * (Work.Kernels.scale τ) ^ n →
      ‖f‖ ≤ M * (Work.Kernels.scale τ) ^ E := by
    intro c n f hc hn h
    refine le_trans h ?_
    exact mul_le_mul hc (Real.rpow_le_rpow_of_exponent_le hs1 hn)
      (Real.rpow_nonneg hspos.le n) hMn
  have hDelta : ‖Work.Kernels.DeltaFun τ‖ ≤ M * (Work.Kernels.scale τ) ^ E := by
    refine hstep (c := Ca2) (n := Na2) hCa2M hNa2E ?_
    have ht1 : tS τ ≤ 1 := tS_le_one τ
    have ht0 : 0 ≤ tS τ := tS_nonneg τ
    have h3 : (0 : ℝ) ≤ Ca2 * (Work.Kernels.scale τ) ^ Na2 :=
      mul_nonneg hCa2.le (Real.rpow_nonneg hspos.le Na2)
    calc ‖Work.Kernels.DeltaFun τ‖
        ≤ Ca2 * (Work.Kernels.scale τ) ^ Na2 * tS τ ^ 2 := (hAll2 τ hτ).2.2.2.2.2.1
      _ ≤ Ca2 * (Work.Kernels.scale τ) ^ Na2 * 1 :=
          mul_le_mul_of_nonneg_left (by nlinarith [ht1, ht0]) h3
      _ = Ca2 * (Work.Kernels.scale τ) ^ Na2 := by rw [mul_one]
  have hJD : ‖Work.Kernels.jInvariantFun τ * Work.Kernels.DeltaFun τ‖
      ≤ M * (Work.Kernels.scale τ) ^ E :=
    hstep (c := Ca2) (n := Na2) hCa2M hNa2E (hAll2 τ hτ).2.2.2.2.2.2.2.2.2.2
  have hA0 : ‖Alpha ℓ 24 0 τ‖ ≤ M * (Work.Kernels.scale τ) ^ E :=
    hstep (c := Ca) (n := Na) hCaM hNaE (hAllA τ hτ).1
  have hA2 : ‖Alpha ℓ 24 2 τ‖ ≤ M * (Work.Kernels.scale τ) ^ E :=
    hstep (c := Ca) (n := Na) hCaM hNaE (hAllA τ hτ).2.1
  have hA12 : ‖Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ‖ ≤ M * (Work.Kernels.scale τ) ^ E :=
    hstep (c := Ca) (n := Na) hCaM hNaE (hAllA τ hτ).2.2.1
  have hJA12 : ‖Work.Kernels.jInvariantFun τ * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)‖
      ≤ M * (Work.Kernels.scale τ) ^ E :=
    hstep (c := Ca) (n := Na) hCaM hNaE (hAllA τ hτ).2.2.2
  -- `z`-side
  have hV : ‖Work.Kernels.VFun z‖ ≤ M := by
    have h := (hz1 z hz3).2.2.1
    linarith [h, hCz1M]
  have hjV : ‖Work.Kernels.jInvariantFun z * Work.Kernels.VFun z‖
      ≤ M * Real.exp (Real.pi * z.im) := by
    refine le_trans (hz1 z hz3).2.2.2.1 ?_
    exact mul_le_mul_of_nonneg_right (by linarith [hCz1M]) hP0
  have hZE10 : ‖Work.Kernels.E10Fun z / Work.Kernels.DeltaFun z
      * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2)‖
      ≤ M * Real.exp (Real.pi * z.im) := by
    refine le_trans (hz1 z hz3).2.2.2.2 ?_
    exact mul_le_mul_of_nonneg_right (by linarith [hCz1M]) hP0
  have hZE14 : ‖Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z * ℓ.L_S z‖
      ≤ M * Real.exp (Real.pi * z.im) := by
    refine le_trans (hz2 z hz3).2 ?_
    exact mul_le_mul_of_nonneg_right (by linarith [hCz2M]) hP0
  -- `Alpha ℓ 24 0 τ = Δ τ`
  have hAlpha0eq : Alpha ℓ 24 0 τ = Work.Kernels.DeltaFun τ := by
    rw [Alpha]
    simp [Work.Kernels.psiVec, vlen, Work.Kernels.fk]
  -- the bracket
  have hbr : ‖(((-3456 : ℂ) * Alpha ℓ 24 0 τ + 2 * Alpha ℓ 24 1 τ - 2 * Alpha ℓ 24 2 τ)
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)
      + (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * Work.Kernels.jInvariantFun τ
      + 1728 * Alpha ℓ 24 2 τ) * Work.Kernels.VFun z‖
      ≤ 8645 * M * M * (Work.Kernels.scale τ) ^ E * Real.exp (Real.pi * z.im) := by
    have hsplit : (((-3456 : ℂ) * Alpha ℓ 24 0 τ + 2 * Alpha ℓ 24 1 τ - 2 * Alpha ℓ 24 2 τ)
          * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)
        + (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * Work.Kernels.jInvariantFun τ
        + 1728 * Alpha ℓ 24 2 τ) * Work.Kernels.VFun z
      = ((-3456 : ℂ) * (Work.Kernels.jInvariantFun τ * Work.Kernels.DeltaFun τ)
            + 3 * (Work.Kernels.jInvariantFun τ * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)))
          * Work.Kernels.VFun z
        + ((3456 : ℂ) * Work.Kernels.DeltaFun τ - 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ))
          * (Work.Kernels.jInvariantFun z * Work.Kernels.VFun z)
        + 1728 * Alpha ℓ 24 2 τ * Work.Kernels.VFun z := by
      rw [hAlpha0eq]; ring
    rw [hsplit]
    refine le_trans (nadd3 _ _ _) ?_
    have hI : ‖((-3456 : ℂ) * (Work.Kernels.jInvariantFun τ * Work.Kernels.DeltaFun τ)
          + 3 * (Work.Kernels.jInvariantFun τ * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)))
          * Work.Kernels.VFun z‖
        ≤ 3459 * M * M * (Work.Kernels.scale τ) ^ E * Real.exp (Real.pi * z.im) := by
      have h1 : ‖(-3456 : ℂ) * (Work.Kernels.jInvariantFun τ * Work.Kernels.DeltaFun τ)‖
          ≤ 3456 * (M * (Work.Kernels.scale τ) ^ E) := by
        calc ‖(-3456 : ℂ) * (Work.Kernels.jInvariantFun τ * Work.Kernels.DeltaFun τ)‖
            = ‖(-3456 : ℂ)‖ * ‖Work.Kernels.jInvariantFun τ * Work.Kernels.DeltaFun τ‖ :=
              norm_mul _ _
          _ = 3456 * ‖Work.Kernels.jInvariantFun τ * Work.Kernels.DeltaFun τ‖ := by
              norm_num
          _ ≤ 3456 * (M * (Work.Kernels.scale τ) ^ E) :=
              mul_le_mul_of_nonneg_left hJD (by norm_num)
      have h2 : ‖(3 : ℂ) * (Work.Kernels.jInvariantFun τ
            * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ))‖ ≤ 3 * (M * (Work.Kernels.scale τ) ^ E) := by
        calc ‖(3 : ℂ) * (Work.Kernels.jInvariantFun τ
              * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ))‖
            = ‖(3 : ℂ)‖ * ‖Work.Kernels.jInvariantFun τ
                * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)‖ := norm_mul _ _
          _ = 3 * ‖Work.Kernels.jInvariantFun τ
                * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)‖ := by norm_num
          _ ≤ 3 * (M * (Work.Kernels.scale τ) ^ E) :=
              mul_le_mul_of_nonneg_left hJA12 (by norm_num)
      have hsum : ‖(-3456 : ℂ) * (Work.Kernels.jInvariantFun τ * Work.Kernels.DeltaFun τ)
          + 3 * (Work.Kernels.jInvariantFun τ * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ))‖
          ≤ 3459 * (M * (Work.Kernels.scale τ) ^ E) := by
        refine le_trans (norm_add_le _ _) ?_
        linarith [h1, h2]
      calc ‖((-3456 : ℂ) * (Work.Kernels.jInvariantFun τ * Work.Kernels.DeltaFun τ)
            + 3 * (Work.Kernels.jInvariantFun τ * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)))
            * Work.Kernels.VFun z‖
          = ‖(-3456 : ℂ) * (Work.Kernels.jInvariantFun τ * Work.Kernels.DeltaFun τ)
              + 3 * (Work.Kernels.jInvariantFun τ * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ))‖
            * ‖Work.Kernels.VFun z‖ := norm_mul _ _
        _ ≤ (3459 * (M * (Work.Kernels.scale τ) ^ E)) * M :=
            mul_le_mul hsum hV (norm_nonneg _) (mul_nonneg (by norm_num) hMErr0)
        _ = 3459 * M * M * (Work.Kernels.scale τ) ^ E := by ring
        _ ≤ 3459 * M * M * (Work.Kernels.scale τ) ^ E * Real.exp (Real.pi * z.im) :=
            le_mul_of_one_le_right (by positivity) hP1
    have hII : ‖((3456 : ℂ) * Work.Kernels.DeltaFun τ
          - 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ))
          * (Work.Kernels.jInvariantFun z * Work.Kernels.VFun z)‖
        ≤ 3458 * M * M * (Work.Kernels.scale τ) ^ E * Real.exp (Real.pi * z.im) := by
      have h1 : ‖(3456 : ℂ) * Work.Kernels.DeltaFun τ‖
          ≤ 3456 * (M * (Work.Kernels.scale τ) ^ E) := by
        calc ‖(3456 : ℂ) * Work.Kernels.DeltaFun τ‖
            = ‖(3456 : ℂ)‖ * ‖Work.Kernels.DeltaFun τ‖ := norm_mul _ _
          _ = 3456 * ‖Work.Kernels.DeltaFun τ‖ := by norm_num
          _ ≤ 3456 * (M * (Work.Kernels.scale τ) ^ E) :=
              mul_le_mul_of_nonneg_left hDelta (by norm_num)
      have h2 : ‖(2 : ℂ) * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)‖
          ≤ 2 * (M * (Work.Kernels.scale τ) ^ E) := by
        calc ‖(2 : ℂ) * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)‖
            = ‖(2 : ℂ)‖ * ‖Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ‖ := norm_mul _ _
          _ = 2 * ‖Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ‖ := by norm_num
          _ ≤ 2 * (M * (Work.Kernels.scale τ) ^ E) :=
              mul_le_mul_of_nonneg_left hA12 (by norm_num)
      have hsum : ‖(3456 : ℂ) * Work.Kernels.DeltaFun τ
          - 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)‖
          ≤ 3458 * (M * (Work.Kernels.scale τ) ^ E) := by
        refine le_trans (norm_sub_le _ _) ?_
        linarith [h1, h2]
      calc ‖((3456 : ℂ) * Work.Kernels.DeltaFun τ
            - 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ))
            * (Work.Kernels.jInvariantFun z * Work.Kernels.VFun z)‖
          = ‖(3456 : ℂ) * Work.Kernels.DeltaFun τ
              - 2 * (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ)‖
            * ‖Work.Kernels.jInvariantFun z * Work.Kernels.VFun z‖ := norm_mul _ _
        _ ≤ (3458 * (M * (Work.Kernels.scale τ) ^ E)) * (M * Real.exp (Real.pi * z.im)) :=
            mul_le_mul hsum hjV (norm_nonneg _) (mul_nonneg (by norm_num) hMErr0)
        _ = 3458 * M * M * (Work.Kernels.scale τ) ^ E * Real.exp (Real.pi * z.im) := by ring
    have hIII : ‖(1728 : ℂ) * Alpha ℓ 24 2 τ * Work.Kernels.VFun z‖
        ≤ 1728 * M * M * (Work.Kernels.scale τ) ^ E * Real.exp (Real.pi * z.im) := by
      have h1 : ‖(1728 : ℂ) * Alpha ℓ 24 2 τ‖ ≤ 1728 * (M * (Work.Kernels.scale τ) ^ E) := by
        calc ‖(1728 : ℂ) * Alpha ℓ 24 2 τ‖
            = ‖(1728 : ℂ)‖ * ‖Alpha ℓ 24 2 τ‖ := norm_mul _ _
          _ = 1728 * ‖Alpha ℓ 24 2 τ‖ := by norm_num
          _ ≤ 1728 * (M * (Work.Kernels.scale τ) ^ E) :=
              mul_le_mul_of_nonneg_left hA2 (by norm_num)
      calc ‖(1728 : ℂ) * Alpha ℓ 24 2 τ * Work.Kernels.VFun z‖
          = ‖(1728 : ℂ) * Alpha ℓ 24 2 τ‖ * ‖Work.Kernels.VFun z‖ := norm_mul _ _
        _ ≤ (1728 * (M * (Work.Kernels.scale τ) ^ E)) * M :=
            mul_le_mul h1 hV (norm_nonneg _) (mul_nonneg (by norm_num) hMErr0)
        _ = 1728 * M * M * (Work.Kernels.scale τ) ^ E := by ring
        _ ≤ 1728 * M * M * (Work.Kernels.scale τ) ^ E * Real.exp (Real.pi * z.im) :=
            le_mul_of_one_le_right (by positivity) hP1
    have hsum : 3459 * M * M * (Work.Kernels.scale τ) ^ E * Real.exp (Real.pi * z.im)
        + 3458 * M * M * (Work.Kernels.scale τ) ^ E * Real.exp (Real.pi * z.im)
        + 1728 * M * M * (Work.Kernels.scale τ) ^ E * Real.exp (Real.pi * z.im)
        = 8645 * M * M * (Work.Kernels.scale τ) ^ E * Real.exp (Real.pi * z.im) := by ring
    linarith [hI, hII, hIII, hsum.le, hsum.ge]
  -- the three pieces of `T24`
  have hterm1 : ‖(-3456 : ℂ) * Alpha ℓ 24 0 τ
      * (Work.Kernels.fk 2 z * ℓ.L_S z)‖
      ≤ 3456 * M * M * (Work.Kernels.scale τ) ^ E * Real.exp (Real.pi * z.im) := by
    have hA : ‖(-3456 : ℂ) * Alpha ℓ 24 0 τ‖ ≤ 3456 * (M * (Work.Kernels.scale τ) ^ E) := by
      calc ‖(-3456 : ℂ) * Alpha ℓ 24 0 τ‖
          = ‖(-3456 : ℂ)‖ * ‖Alpha ℓ 24 0 τ‖ := norm_mul _ _
        _ = 3456 * ‖Alpha ℓ 24 0 τ‖ := by norm_num
        _ ≤ 3456 * (M * (Work.Kernels.scale τ) ^ E) :=
            mul_le_mul_of_nonneg_left hA0 (by norm_num)
    have hB : ‖Work.Kernels.fk 2 z * ℓ.L_S z‖ ≤ M * Real.exp (Real.pi * z.im) := by
      rw [fk_two_eq]; exact hZE14
    calc ‖(-3456 : ℂ) * Alpha ℓ 24 0 τ * (Work.Kernels.fk 2 z * ℓ.L_S z)‖
        = ‖(-3456 : ℂ) * Alpha ℓ 24 0 τ‖ * ‖Work.Kernels.fk 2 z * ℓ.L_S z‖ := norm_mul _ _
      _ ≤ (3456 * (M * (Work.Kernels.scale τ) ^ E)) * (M * Real.exp (Real.pi * z.im)) :=
          mul_le_mul hA hB (norm_nonneg _) (mul_nonneg (by norm_num) hMErr0)
      _ = 3456 * M * M * (Work.Kernels.scale τ) ^ E * Real.exp (Real.pi * z.im) := by ring
  have hterm2 : ‖-((((-3456 : ℂ) * Alpha ℓ 24 0 τ + 2 * Alpha ℓ 24 1 τ - 2 * Alpha ℓ 24 2 τ)
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)
      + (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * Work.Kernels.jInvariantFun τ
      + 1728 * Alpha ℓ 24 2 τ) * Work.Kernels.VFun z)‖
      ≤ 8645 * M * M * (Work.Kernels.scale τ) ^ E * Real.exp (Real.pi * z.im) := by
    rw [norm_neg]
    exact hbr
  have hterm3 : ‖(Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * (Work.Kernels.fk (-2) z
      * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2))‖
      ≤ M * M * (Work.Kernels.scale τ) ^ E * Real.exp (Real.pi * z.im) := by
    have hA : ‖Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ‖ ≤ M * (Work.Kernels.scale τ) ^ E := by
      rw [show Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ
          = -(Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) by ring, norm_neg]
      exact hA12
    have hB : ‖Work.Kernels.fk (-2) z
        * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2)‖
        ≤ M * Real.exp (Real.pi * z.im) := by
      rw [fk_neg_two_eq]; exact hZE10
    calc ‖(Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * (Work.Kernels.fk (-2) z
          * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2))‖
        = ‖Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ‖
          * ‖Work.Kernels.fk (-2) z
            * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2)‖ := norm_mul _ _
      _ ≤ (M * (Work.Kernels.scale τ) ^ E) * (M * Real.exp (Real.pi * z.im)) :=
          mul_le_mul hA hB (norm_nonneg _) hMErr0
      _ = M * M * (Work.Kernels.scale τ) ^ E * Real.exp (Real.pi * z.im) := by ring
  have hT24 : ‖T24 ℓ τ z‖
      ≤ 12102 * M * M * (Work.Kernels.scale τ) ^ E * Real.exp (Real.pi * z.im) := by
    have hdef : T24 ℓ τ z
        = (-3456 : ℂ) * Alpha ℓ 24 0 τ * (Work.Kernels.fk 2 z * ℓ.L_S z)
          + (-((((-3456 : ℂ) * Alpha ℓ 24 0 τ + 2 * Alpha ℓ 24 1 τ - 2 * Alpha ℓ 24 2 τ)
                * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)
              + (Alpha ℓ 24 1 τ - Alpha ℓ 24 2 τ) * Work.Kernels.jInvariantFun τ
              + 1728 * Alpha ℓ 24 2 τ) * Work.Kernels.VFun z))
          + (Alpha ℓ 24 2 τ - Alpha ℓ 24 1 τ) * (Work.Kernels.fk (-2) z
              * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2)) := by
      rw [T24]; ring
    rw [hdef]
    refine le_trans (nadd3 _ _ _) ?_
    have hsum : 3456 * M * M * (Work.Kernels.scale τ) ^ E * Real.exp (Real.pi * z.im)
        + 8645 * M * M * (Work.Kernels.scale τ) ^ E * Real.exp (Real.pi * z.im)
        + M * M * (Work.Kernels.scale τ) ^ E * Real.exp (Real.pi * z.im)
        = 12102 * M * M * (Work.Kernels.scale τ) ^ E * Real.exp (Real.pi * z.im) := by ring
    linarith [hterm1, hterm2, hterm3, hsum.le, hsum.ge]
  calc ‖Work.Asymptotics.Ncusp ℓ 24 τ z‖
      = ‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹ * T24 ℓ τ z‖ := by
        rw [Ncusp_twentyfour_expansion]
    _ = ‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * ‖T24 ℓ τ z‖ := norm_mul _ _
    _ ≤ ‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖
          * (12102 * M * M * (Work.Kernels.scale τ) ^ E * Real.exp (Real.pi * z.im)) :=
        mul_le_mul_of_nonneg_left hT24 (norm_nonneg _)
    _ = (‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * (12102 * M * M))
          * (Work.Kernels.scale τ) ^ E * Real.exp (Real.pi * z.im) := by ring
    _ ≤ (‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * (12102 * M * M) + 1)
          * (Work.Kernels.scale τ) ^ E * Real.exp (Real.pi * z.im) := by
        apply mul_le_mul_of_nonneg_right _ hP0
        apply mul_le_mul_of_nonneg_right _ hSg0
        linarith [norm_nonneg ((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹]

end

end Work.Asymptotics
