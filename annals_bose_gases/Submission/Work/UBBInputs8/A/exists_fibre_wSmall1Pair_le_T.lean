import ChallengeDeps
import Submission.Work.UBBInputs8.A.abs_integral_wSmall1Pair_le
import Submission.Work.UBBInputs8.A.abs_wSmallPair_chiB_le
import Submission.Work.UBBInputs8.A.integral_abs_g0_shift_mul_chiSmallB_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs8.A

open MeasureTheory

/-- **The one-body fibre bound with the cutoff mass as the `u`-dependent factor.**

`wSmall1Pair h M L d u z y = χ_{B(u)}(z)·(g₀(z−y)/(χ_M⋆χ_M)((z−y)/(Ld)))·χ_{B(u)}(y)`, so

    `|∫_{acube L} wSmall1Pair h M L d u z y dy| ≤ K · (∫ χ_{B(u)}) · χ_{B(u)}(z)`

with `K = Bv/smallConvLower M` independent of `u` and `z`.  The point is that the
`y`-integral of the *numerator* is bounded by `Bv·∫χ_{B(u)}`, using that
`|g₀| = |v(1−w₀)| ≤ |v| ≤ Bv` almost everywhere — which the non-negativity, radiality and
compact support of `v` provide via `Submission.BoseGases.chosen_w0_bounds_ae`
(`0 ≤ w₀ ≤ 1` a.e.).  The absolute value of the cutoff factors is the cutoff (nonnegative) and
the renormalisation denominator is `≥ smallConvLower M` on the support
(`Submission.Work.SmallBoxSliding.abs_wSmallScaled_le`, or the sharpened
`Work.UBBInputs8.A.abs_wSmall1Pair_chiB_le`). -/
theorem exists_fibre_wSmall1Pair_le_T {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R0 Bv : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : BoseGases.IsRadial v)
    (hvb : ∀ y : EuclideanSpace ℝ (Fin 3), |v y| ≤ Bv)
    {M : ℕ} (hM : 1 ≤ M) {d : ℕ} (hd : (0 : ℝ) < (d : ℝ))
    (hdR : ∀ L : ℝ, 1 ≤ L → R0 ≤ (L * (d : ℝ)) / 16)
    (hdRχ : ∀ L : ℝ, 1 ≤ L → R0 ≤ L * Submission.BoseGases.chiR0)
    {L : ℝ} (hL : 1 ≤ L) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (u z : EuclideanSpace ℝ (Fin 3)),
      |∫ y in Submission.BoseGases.acube L,
          Submission.BoseGases.wSmall1Pair h M L (d : ℝ) u z y| ≤
        K * (∫ x : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.chiSmallB M L (d : ℝ) u x)
          * Submission.BoseGases.chiSmallB M L (d : ℝ) u z := by
  have hc₁ : 0 ≤ (Work.SmallBoxSliding.smallConvLower M)⁻¹ :=
    inv_nonneg.mpr (Work.SmallBoxSliding.smallConvLower_nonneg M)
  have hBv : 0 ≤ Bv := le_trans (abs_nonneg (v 0)) (hvb 0)
  refine ⟨2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ * Bv,
    mul_nonneg (mul_nonneg (by norm_num) hc₁) hBv, ?_⟩
  intro u z
  have hA : 0 ≤ Submission.BoseGases.chiSmallB M L (d : ℝ) u z :=
    Submission.BoseGases.chiSmallB_nonneg M L (d : ℝ) u z
  -- the `u`-free step: `|∫ f| ≤ ∫ |f|`
  have hstep1 : |∫ y in Submission.BoseGases.acube L,
        Submission.BoseGases.wSmall1Pair h M L (d : ℝ) u z y| ≤
      ∫ y in Submission.BoseGases.acube L,
        |Submission.BoseGases.wSmall1Pair h M L (d : ℝ) u z y| := by
    have hh := norm_integral_le_integral_norm
      (μ := volume.restrict (Submission.BoseGases.acube L))
      (f := fun y : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wSmall1Pair h M L (d : ℝ) u z y)
    simpa only [Real.norm_eq_abs] using hh
  -- integrate the pointwise domination over the analysis cube
  have hAint := abs_integral_wSmall1Pair_le (v := v) (h := h)
    hv_supp hR0 hM hd hdR hdRχ hL u z
  -- bound the remaining numerator-integral by `Bv·∫χ_{B(u)}`
  have hBint := integral_abs_g0_shift_mul_chiSmallB_le (v := v) (h := h)
    hv_supp hR0 hv hvrad hvb hM hd hL u z
  calc |∫ y in Submission.BoseGases.acube L,
        Submission.BoseGases.wSmall1Pair h M L (d : ℝ) u z y|
      ≤ ∫ y in Submission.BoseGases.acube L,
          |Submission.BoseGases.wSmall1Pair h M L (d : ℝ) u z y| := hstep1
    _ ≤ (2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹) * Submission.BoseGases.chiSmallB M L (d : ℝ) u z *
          (∫ y in Submission.BoseGases.acube L,
            |Submission.BoseGases.g0 v h (z - y)| *
              Submission.BoseGases.chiSmallB M L (d : ℝ) u y) := hAint
    _ ≤ (2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹) * Submission.BoseGases.chiSmallB M L (d : ℝ) u z *
          (Bv * ∫ y : EuclideanSpace ℝ (Fin 3),
            Submission.BoseGases.chiSmallB M L (d : ℝ) u y) :=
        mul_le_mul_of_nonneg_left hBint (mul_nonneg (mul_nonneg (by norm_num) hc₁) hA)
    _ = (2 * (Work.SmallBoxSliding.smallConvLower M)⁻¹ * Bv) *
          (∫ x : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.chiSmallB M L (d : ℝ) u x) *
          Submission.BoseGases.chiSmallB M L (d : ℝ) u z := by ring

end Work.UBBInputs8.A
