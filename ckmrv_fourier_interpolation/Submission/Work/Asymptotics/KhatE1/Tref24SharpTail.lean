/-
# The sharp tail of the `K₋`-reference bracket on the strip `0 ≤ Re z ≤ 1`

`Compact.Tref24 = Ept z · Compact.R24` is the reference part of the `K₋`-bracket
(`Compact.Tref24_eq`).  Its first term `Ept z · R24_p0` is exactly the leading `E(z)¹`-term of
the deviation (`R24_p0 = E1combo24`, bounded by `C ‖q(τ)‖ (scale τ)^N`, `E1combo24_bound`),
so the *tail*

  `T2 := Ept z · (R24 ℓ τ z - R24_p0 ℓ τ)
      = Σ_{k=1}^{5} Ept z^{k+1} (Xc R24_qk + R24_pk)`

is what enters the sharp `d = 24` bracket.  Here it is bounded on the funnel strip at the
*natural* weight `‖q(τ)‖⁻¹ ‖Ept z‖²`:

  `‖T2‖ ≤ C ‖q(τ)‖⁻¹ (scale τ)^N (1+t)^M e^{-2πt}`,

the other pieces of the sharp `d = 24` bracket (`Submission/Work/Asymptotics/KhatE1/
Kdev24Lead.lean`, `KPlus24SharpStrip.lean`) having the same weight.

Since `Xc ℓ z = πi z + c`, one has `Xc ℓ z = Xc ℓ (i t) + πi Re z`, so the axis bound
`Funnel24Tail.coeff_bounds` (proved for `z = i t`) transfers to the strip, using also the
bounds `‖Δ(τ)‖ ≤ 2`, `‖j(τ)Δ(τ)‖ ≤ 27/8` (`Funnel24.norm_Delta_funnel`,
`Funnel24.norm_j_mul_Delta_funnel`) for the two nonvanishing `R24_q•`.
-/
import Mathlib
import Submission.Work.Asymptotics.Funnel24Tail.Tref24FunnelBound
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.KhatE1Defs

set_option maxHeartbeats 1000000

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-- The point `i t` of the imaginary axis. -/
private def axPt (t : ℝ) (ht : 0 < t) : ℍ := ⟨(t : ℂ) * Complex.I, by
  simpa [Complex.mul_im] using ht⟩

private lemma axPt_coe (t : ℝ) (ht : 0 < t) : (axPt t ht : ℂ) = (t : ℂ) * Complex.I := rfl

/-- `Xc` is affine in `z`: on the strip, `Xc ℓ z = Xc ℓ (i t) + πi Re z`. -/
private lemma Xc_axPt (ℓ : Work.Kernels.LogLambdaData) (z : ℍ) (t : ℝ) (ht : 0 < t)
    (hzim : z.im = t) :
    Work.Asymptotics.Compact.Xc ℓ z
      = Work.Asymptotics.Compact.Xc ℓ (axPt t ht) + (Real.pi : ℂ) * Complex.I * (z.re : ℂ) := by
  have hz : (z : ℂ) = (z.re : ℂ) + ((z.im : ℝ) : ℂ) * Complex.I :=
    (Complex.re_add_im z).symm
  simp only [Work.Asymptotics.Compact.Xc, axPt_coe]
  rw [hz, hzim]
  ring

/-- **The exact `Ept z`-expansion of the `K₋`-reference tail.**  This pins the coefficients of
`Ept z^{k+1}` in `Ept z · (R24 - R24_p0)`; it is the input needed by the second-order
`E²`-coefficient identity of the sharp `d = 24` bracket
(`Submission/Work/Asymptotics/KhatE1/Kdev24Lead.lean`). -/
theorem Tref24_tail_expansion (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) :
    Work.Residues.Ept z * (Work.Asymptotics.Compact.R24 ℓ τ z
        - Work.Asymptotics.Compact.R24_p0 ℓ τ)
      = (Work.Residues.Ept z) ^ 2
          * (Work.Asymptotics.Compact.Xc ℓ z * Work.Asymptotics.Compact.R24_q1 ℓ τ
              + Work.Asymptotics.Compact.R24_p1 ℓ τ)
        + (Work.Residues.Ept z) ^ 3
          * (Work.Asymptotics.Compact.Xc ℓ z * Work.Asymptotics.Compact.R24_q2 ℓ τ
              + Work.Asymptotics.Compact.R24_p2 ℓ τ)
        + (Work.Residues.Ept z) ^ 4
          * (Work.Asymptotics.Compact.Xc ℓ z * Work.Asymptotics.Compact.R24_q3 ℓ τ
              + Work.Asymptotics.Compact.R24_p3 ℓ τ)
        + (Work.Residues.Ept z) ^ 5
          * (Work.Asymptotics.Compact.Xc ℓ z * Work.Asymptotics.Compact.R24_q4 ℓ τ
              + Work.Asymptotics.Compact.R24_p4 ℓ τ)
        + (Work.Residues.Ept z) ^ 6
          * (Work.Asymptotics.Compact.Xc ℓ z * Work.Asymptotics.Compact.R24_q5 ℓ τ
              + Work.Asymptotics.Compact.R24_p5 ℓ τ) := by
  rw [Work.Asymptotics.Compact.R24]
  simp only [Work.Asymptotics.Compact.R24_q0]
  ring

/-- **The sharp tail of the `K₋`-reference bracket on the strip.** -/
theorem Tref24SharpTail (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖Work.Residues.Ept z * (Work.Asymptotics.Compact.R24 ℓ τ z
            - Work.Asymptotics.Compact.R24_p0 ℓ τ)‖
          ≤ C * (‖Work.Kernels.qParamFun τ‖)⁻¹ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(2 * Real.pi * t)) := by
  obtain ⟨Cc, Nc, hCc, hNc, hcoef⟩ := Work.Asymptotics.Funnel24Tail.coeff_bounds ℓ
  have hΔ : ∀ τ : ℍ, Work.Asymptotics.Funnel τ → ‖Work.Kernels.DeltaFun τ‖ ≤ 2 := by
    intro τ hτ
    have h := Work.Asymptotics.Funnel24.norm_Delta_funnel τ hτ
    have he : Real.exp (-(2 * Real.pi * τ.im)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, τ.im_pos]
    linarith
  have hjΔ : ∀ τ : ℍ, Work.Asymptotics.Funnel τ →
      ‖Work.Kernels.jInvariantFun τ * Work.Kernels.DeltaFun τ‖ ≤ 27 / 8 :=
    fun τ hτ => Work.Asymptotics.Funnel24.norm_j_mul_Delta_funnel τ hτ
  have h1e8 : (1990656 : ℝ) * 2 ≤ 100000000000 := by norm_num
  have h1e9 : (1433272320 : ℝ) * 2 + 1990656 * (27 / 8) ≤ 100000000000 := by norm_num
  refine ⟨5 * (Cc + Real.pi * 100000000000 + 1) * 2 + 1, Nc, 1,
    by positivity, hNc, by norm_num, ?_⟩
  intro τ z t hτ ht hz0 hz1 hzim
  have ht3 : (3 : ℝ) ≤ t := by have h2 := Work.Asymptotics.Funnel.im_two hτ; linarith
  have ht0 : (0 : ℝ) < t := by linarith
  have hΔτ : ‖Work.Kernels.DeltaFun τ‖ ≤ 2 := hΔ τ hτ
  have hjDτ : ‖Work.Kernels.jInvariantFun τ * Work.Kernels.DeltaFun τ‖ ≤ 27 / 8 := hjΔ τ hτ
  have hax := hcoef τ (axPt t ht0) t hτ ht (axPt_coe t ht0)
  obtain ⟨hc1, hc2, hc3, hc4, hc5⟩ := hax
  -- bounds for the `R24_q•` (only `q1`, `q3` are nonzero)
  have hQ1 : ‖Work.Asymptotics.Compact.R24_q1 ℓ τ‖ ≤ 100000000000 := by
    have hnorm : ‖(1990656 : ℂ)‖ = 1990656 := by norm_num
    have h : ‖Work.Asymptotics.Compact.R24_q1 ℓ τ‖ ≤ 1990656 * 2 := by
      rw [show Work.Asymptotics.Compact.R24_q1 ℓ τ
        = (1990656 : ℂ) * Work.Kernels.DeltaFun τ from rfl, norm_mul, hnorm]
      have := mul_le_mul_of_nonneg_left hΔτ (by norm_num : (0:ℝ) ≤ 1990656)
      linarith [this]
    linarith
  have hQ3 : ‖Work.Asymptotics.Compact.R24_q3 ℓ τ‖ ≤ 100000000000 := by
    have hnorm : ‖(-1433272320 : ℂ)‖ = 1433272320 := by norm_num
    have hnorm2 : ‖(1990656 : ℂ)‖ = 1990656 := by norm_num
    have h : ‖Work.Asymptotics.Compact.R24_q3 ℓ τ‖
        ≤ 1433272320 * 2 + 1990656 * (27 / 8) := by
      rw [show Work.Asymptotics.Compact.R24_q3 ℓ τ
          = (-1433272320 : ℂ) * Work.Kernels.DeltaFun τ
            + (1990656 : ℂ)
                * (Work.Kernels.jInvariantFun τ * Work.Kernels.DeltaFun τ) from rfl]
      refine le_trans (norm_add_le _ _) ?_
      have hA : ‖(-1433272320 : ℂ) * Work.Kernels.DeltaFun τ‖
          = 1433272320 * ‖Work.Kernels.DeltaFun τ‖ := by rw [norm_mul, hnorm]
      have hB : ‖(1990656 : ℂ) * (Work.Kernels.jInvariantFun τ * Work.Kernels.DeltaFun τ)‖
          = 1990656 * ‖Work.Kernels.jInvariantFun τ * Work.Kernels.DeltaFun τ‖ := by
        rw [norm_mul, hnorm2]
      rw [hA, hB]
      have h1 := mul_le_mul_of_nonneg_left hΔτ (by norm_num : (0:ℝ) ≤ 1433272320)
      have h2 := mul_le_mul_of_nonneg_left hjDτ (by norm_num : (0:ℝ) ≤ 1990656)
      linarith [h1, h2]
    linarith
  have hQ0 : ‖Work.Asymptotics.Compact.R24_q2 ℓ τ‖ ≤ 100000000000 := by
    rw [show Work.Asymptotics.Compact.R24_q2 ℓ τ = 0 from rfl, norm_zero]; norm_num
  have hQ4 : ‖Work.Asymptotics.Compact.R24_q4 ℓ τ‖ ≤ 100000000000 := by
    rw [show Work.Asymptotics.Compact.R24_q4 ℓ τ = 0 from rfl, norm_zero]; norm_num
  have hQ5 : ‖Work.Asymptotics.Compact.R24_q5 ℓ τ‖ ≤ 100000000000 := by
    rw [show Work.Asymptotics.Compact.R24_q5 ℓ τ = 0 from rfl, norm_zero]; norm_num
  -- the shape of every bound
  set shape : ℝ := (Work.Kernels.scale τ) ^ Nc
      * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t) with hshape
  have hsN : (1 : ℝ) ≤ (Work.Kernels.scale τ) ^ Nc :=
    Real.one_le_rpow (Work.Kernels.one_le_scale τ) hNc
  have hsexp : (1 : ℝ) ≤ 1 + Real.exp (2 * Real.pi * τ.im) := by
    have := Real.exp_pos (2 * Real.pi * τ.im); linarith
  have ht1 : (1 : ℝ) ≤ 1 + t := by linarith
  have hshape1 : (1 : ℝ) ≤ shape := by
    rw [hshape]
    calc (1 : ℝ) = 1 * (1 * 1) := by ring
      _ ≤ (Work.Kernels.scale τ) ^ Nc
            * ((1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t)) :=
          mul_le_mul hsN (mul_le_mul hsexp ht1 (by norm_num) (by positivity))
            (by norm_num) (by positivity)
      _ = (Work.Kernels.scale τ) ^ Nc
            * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t) := by ring
  have hshape0 : (0 : ℝ) ≤ shape := le_trans zero_le_one hshape1
  have hshaperw : Cc * (Work.Kernels.scale τ) ^ Nc
      * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t) = Cc * shape := by
    rw [hshape]; ring
  -- transfer of the axis bounds to the strip
  have hstrip : ∀ (Q P : ℂ),
      ‖Work.Asymptotics.Compact.Xc ℓ (axPt t ht0) * Q + P‖ ≤ Cc * shape →
      ‖Q‖ ≤ 100000000000 →
      ‖Work.Asymptotics.Compact.Xc ℓ z * Q + P‖
        ≤ (Cc + Real.pi * 100000000000 + 1) * shape := by
    intro Q P hP hQ
    have hsplit : Work.Asymptotics.Compact.Xc ℓ z * Q + P
        = (Work.Asymptotics.Compact.Xc ℓ (axPt t ht0) * Q + P)
          + ((Real.pi : ℂ) * Complex.I * (z.re : ℂ)) * Q := by
      rw [Xc_axPt ℓ z t ht0 hzim]; ring
    have hqz : |z.re| ≤ 1 := by rw [abs_of_nonneg hz0]; exact hz1
    have hcoefπ : ‖((Real.pi : ℂ) * Complex.I * (z.re : ℂ)) * Q‖
        ≤ Real.pi * 100000000000 := by
      have h1 : ‖((Real.pi : ℂ) * Complex.I * (z.re : ℂ))‖ ≤ Real.pi := by
        have h2 : ((Real.pi : ℂ) * Complex.I * (z.re : ℂ))
            = (((Real.pi * z.re : ℝ)) : ℂ) * Complex.I := by push_cast; ring
        rw [h2, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg Real.pi_pos.le hz0)]
        nlinarith [hz1, Real.pi_pos]
      rw [norm_mul]
      exact mul_le_mul h1 hQ (norm_nonneg _) Real.pi_pos.le
    have hsum : ‖Work.Asymptotics.Compact.Xc ℓ z * Q + P‖
        ≤ Cc * shape + Real.pi * 100000000000 := by
      rw [hsplit]
      have h2 := norm_add_le (Work.Asymptotics.Compact.Xc ℓ (axPt t ht0) * Q + P)
        (((Real.pi : ℂ) * Complex.I * (z.re : ℂ)) * Q)
      linarith [h2, hP, hcoefπ]
    have hmain : Cc * shape + Real.pi * 100000000000
        ≤ (Cc + Real.pi * 100000000000 + 1) * shape := by
      have hπCq0 : (0 : ℝ) ≤ Real.pi * 100000000000 := by positivity
      have h1 : Cc * shape ≤ (Cc + Real.pi * 100000000000 + 1) * shape :=
        mul_le_mul_of_nonneg_right (by linarith [hπCq0]) hshape0
      have h2 : Real.pi * 100000000000 ≤ Real.pi * 100000000000 * shape := by
        calc Real.pi * 100000000000 = Real.pi * 100000000000 * 1 := by ring
          _ ≤ Real.pi * 100000000000 * shape := mul_le_mul_of_nonneg_left hshape1 hπCq0
      have h3 : Real.pi * 100000000000 * shape
          ≤ (Cc + Real.pi * 100000000000 + 1) * shape :=
        mul_le_mul_of_nonneg_right (by linarith [hπCq0]) hshape0
      linarith [h1, h2, h3]
    linarith [hsum, hmain]
  have hB1 := hstrip _ _ (by rw [← hshaperw]; exact hc1) hQ1
  have hB2 := hstrip _ _ (by rw [← hshaperw]; exact hc2) hQ0
  have hB3 := hstrip _ _ (by rw [← hshaperw]; exact hc3) hQ3
  have hB4 := hstrip _ _ (by rw [← hshaperw]; exact hc4) hQ4
  have hB5 := hstrip _ _ (by rw [← hshaperw]; exact hc5) hQ5
  -- the exact expansion of the tail
  have hexp : Work.Residues.Ept z * (Work.Asymptotics.Compact.R24 ℓ τ z
        - Work.Asymptotics.Compact.R24_p0 ℓ τ)
      = (Work.Residues.Ept z) ^ 2
          * (Work.Asymptotics.Compact.Xc ℓ z * Work.Asymptotics.Compact.R24_q1 ℓ τ
              + Work.Asymptotics.Compact.R24_p1 ℓ τ)
        + (Work.Residues.Ept z) ^ 3
          * (Work.Asymptotics.Compact.Xc ℓ z * Work.Asymptotics.Compact.R24_q2 ℓ τ
              + Work.Asymptotics.Compact.R24_p2 ℓ τ)
        + (Work.Residues.Ept z) ^ 4
          * (Work.Asymptotics.Compact.Xc ℓ z * Work.Asymptotics.Compact.R24_q3 ℓ τ
              + Work.Asymptotics.Compact.R24_p3 ℓ τ)
        + (Work.Residues.Ept z) ^ 5
          * (Work.Asymptotics.Compact.Xc ℓ z * Work.Asymptotics.Compact.R24_q4 ℓ τ
              + Work.Asymptotics.Compact.R24_p4 ℓ τ)
        + (Work.Residues.Ept z) ^ 6
          * (Work.Asymptotics.Compact.Xc ℓ z * Work.Asymptotics.Compact.R24_q5 ℓ τ
              + Work.Asymptotics.Compact.R24_p5 ℓ τ) := by
    rw [Work.Asymptotics.Compact.R24]
    simp only [Work.Asymptotics.Compact.R24_q0]
    ring
  -- the weight
  set W : ℝ := (Cc + Real.pi * 100000000000 + 1) * shape with hW
  have hW0 : (0 : ℝ) ≤ W := by
    rw [hW]
    refine mul_nonneg ?_ hshape0
    have : (0 : ℝ) ≤ Real.pi * 100000000000 := by positivity
    linarith [hCc.le]
  have hE1 : ‖Work.Residues.Ept z‖ ≤ 1 := by
    rw [Work.Residues.norm_Ept, Real.exp_le_one_iff]
    nlinarith [Real.pi_pos, ht3]
  have hE20 : (0 : ℝ) ≤ ‖Work.Residues.Ept z‖ ^ 2 := by positivity
  have hE : ∀ k : ℕ, 2 ≤ k → ‖(Work.Residues.Ept z) ^ k‖ ≤ ‖Work.Residues.Ept z‖ ^ 2 := by
    intro k hk
    rw [norm_pow]
    exact pow_le_pow_of_le_one (norm_nonneg _) hE1 hk
  have hterm : ∀ (k : ℕ) (hk : 2 ≤ k) (A : ℂ) (hA : ‖A‖ ≤ W),
      ‖(Work.Residues.Ept z) ^ k * A‖ ≤ W * ‖Work.Residues.Ept z‖ ^ 2 := by
    intro k hk A hA
    rw [norm_mul]
    calc ‖(Work.Residues.Ept z) ^ k‖ * ‖A‖ ≤ ‖Work.Residues.Ept z‖ ^ 2 * W :=
          mul_le_mul (hE k hk) hA (norm_nonneg _) hE20
      _ = W * ‖Work.Residues.Ept z‖ ^ 2 := by ring
  have ht1' := hterm 2 (by norm_num) _ (by rw [hW]; exact hB1)
  have ht2' := hterm 3 (by norm_num) _ (by rw [hW]; exact hB2)
  have ht3'' := hterm 4 (by norm_num) _ (by rw [hW]; exact hB3)
  have ht4' := hterm 5 (by norm_num) _ (by rw [hW]; exact hB4)
  have ht5' := hterm 6 (by norm_num) _ (by rw [hW]; exact hB5)
  rw [hexp]
  refine le_trans (Work.Asymptotics.Funnel24Tail.norm_five_sum_le ht1' ht2' ht3'' ht4' ht5') ?_
  -- final conversion
  have hE2 : ‖Work.Residues.Ept z‖ ^ 2 = Real.exp (-(2 * Real.pi * t)) := by
    rw [Work.Residues.norm_Ept, sq, ← Real.exp_add, hzim]
    congr 1; ring
  have hqinv : (‖Work.Kernels.qParamFun τ‖)⁻¹ = Real.exp (2 * Real.pi * τ.im) := by
    rw [Work.Asymptotics.norm_qParamFun, Real.exp_neg, inv_inv]
  set A : ℝ := Cc + Real.pi * 100000000000 + 1 with hA
  have hA0 : (0 : ℝ) ≤ A := by
    rw [hA]
    have hpi : (0 : ℝ) ≤ Real.pi * 100000000000 := by positivity
    linarith [hCc.le]
  have hEexp1 : (1 : ℝ) ≤ Real.exp (2 * Real.pi * τ.im) := by
    rw [Real.one_le_exp_iff]; nlinarith [Real.pi_pos, τ.im_pos]
  have hexpsum : (1 : ℝ) + Real.exp (2 * Real.pi * τ.im)
      ≤ 2 * Real.exp (2 * Real.pi * τ.im) := by linarith
  have hsN0 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ Nc :=
    Real.rpow_nonneg (Work.Kernels.scale_pos τ).le Nc
  have hWle : W ≤ 2 * A * (Work.Kernels.scale τ) ^ Nc * (1 + t)
      * Real.exp (2 * Real.pi * τ.im) := by
    rw [hW, hA, hshape]
    calc A * ((Work.Kernels.scale τ) ^ Nc
            * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t))
        = A * (Work.Kernels.scale τ) ^ Nc
            * (1 + Real.exp (2 * Real.pi * τ.im)) * (1 + t) := by ring
      _ ≤ A * (Work.Kernels.scale τ) ^ Nc
            * (2 * Real.exp (2 * Real.pi * τ.im)) * (1 + t) := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hexpsum (mul_nonneg hA0 hsN0)) (by linarith)
      _ = 2 * A * (Work.Kernels.scale τ) ^ Nc * (1 + t)
            * Real.exp (2 * Real.pi * τ.im) := by ring
  have hgoal5 : W * ‖Work.Residues.Ept z‖ ^ 2 + W * ‖Work.Residues.Ept z‖ ^ 2
        + W * ‖Work.Residues.Ept z‖ ^ 2 + W * ‖Work.Residues.Ept z‖ ^ 2
        + W * ‖Work.Residues.Ept z‖ ^ 2 = 5 * (W * ‖Work.Residues.Ept z‖ ^ 2) := by ring
  have hstep1 : W * ‖Work.Residues.Ept z‖ ^ 2
      ≤ 2 * A * (‖Work.Kernels.qParamFun τ‖)⁻¹ * (Work.Kernels.scale τ) ^ Nc
          * (1 + t) ^ (1 : ℝ) * Real.exp (-(2 * Real.pi * t)) := by
    have h := mul_le_mul_of_nonneg_right hWle hE20
    rw [hE2, ← hqinv] at h
    rw [hE2, Real.rpow_one]
    linarith [h]
  have hstep2 : 5 * (W * ‖Work.Residues.Ept z‖ ^ 2)
      ≤ 10 * A * (‖Work.Kernels.qParamFun τ‖)⁻¹ * (Work.Kernels.scale τ) ^ Nc
          * (1 + t) ^ (1 : ℝ) * Real.exp (-(2 * Real.pi * t)) := by
    have h := mul_le_mul_of_nonneg_left hstep1 (by norm_num : (0:ℝ) ≤ 5)
    linarith [h]
  have hbase : (0 : ℝ) ≤ (‖Work.Kernels.qParamFun τ‖)⁻¹ * (Work.Kernels.scale τ) ^ Nc
      * (1 + t) ^ (1 : ℝ) * Real.exp (-(2 * Real.pi * t)) := by
    have h1 : (0 : ℝ) ≤ (‖Work.Kernels.qParamFun τ‖)⁻¹ := inv_nonneg.mpr (norm_nonneg _)
    have h3 : (0 : ℝ) ≤ (1 + t) ^ (1 : ℝ) := Real.rpow_nonneg (by linarith) 1
    have h4 : (0 : ℝ) ≤ Real.exp (-(2 * Real.pi * t)) := (Real.exp_pos _).le
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 hsN0) h3) h4
  have hA_le : 10 * A ≤ 5 * A * 2 + 1 := by linarith
  have hfinal : 10 * A * (‖Work.Kernels.qParamFun τ‖)⁻¹ * (Work.Kernels.scale τ) ^ Nc
        * (1 + t) ^ (1 : ℝ) * Real.exp (-(2 * Real.pi * t))
      ≤ (5 * A * 2 + 1) * (‖Work.Kernels.qParamFun τ‖)⁻¹ * (Work.Kernels.scale τ) ^ Nc
        * (1 + t) ^ (1 : ℝ) * Real.exp (-(2 * Real.pi * t)) := by
    rw [show 10 * A * (‖Work.Kernels.qParamFun τ‖)⁻¹ * (Work.Kernels.scale τ) ^ Nc
            * (1 + t) ^ (1 : ℝ) * Real.exp (-(2 * Real.pi * t))
          = (10 * A) * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * (Work.Kernels.scale τ) ^ Nc
              * (1 + t) ^ (1 : ℝ) * Real.exp (-(2 * Real.pi * t))) by ring,
      show (5 * A * 2 + 1) * (‖Work.Kernels.qParamFun τ‖)⁻¹ * (Work.Kernels.scale τ) ^ Nc
            * (1 + t) ^ (1 : ℝ) * Real.exp (-(2 * Real.pi * t))
          = (5 * A * 2 + 1) * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * (Work.Kernels.scale τ) ^ Nc
              * (1 + t) ^ (1 : ℝ) * Real.exp (-(2 * Real.pi * t))) by ring]
    exact mul_le_mul_of_nonneg_right hA_le hbase
  rw [hgoal5]
  refine le_trans hstep2 ?_
  rw [hA]
  exact hfinal

end

end Work.Asymptotics.KhatE1
