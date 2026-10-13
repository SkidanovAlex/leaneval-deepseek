import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces.integral_mul_le_sqrt_mul_sqrt
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces.integrable_mul_of_sq_integrable
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces2.weight_diff_integral_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

/-! **`shift_pair_bound`** — Cauchy–Schwarz for the two-sided shift pairing.

With `Δ y := G₂ (y+p) − G₂ (y−p)`, the difference of the two pairings is `∫ Q G₁ Δ`
(`integral_sub`, using `hJp`/`hJm`), which is bounded by `√(∫ Q G₁²) √(∫ Q Δ²)`:
`abs_integral_le_integral_abs`, `Q y = √(Q y)²`, then
`Work...JepsTransfer.Pieces.integral_mul_le_sqrt_mul_sqrt` (or
`...JepsTransfer.Pieces.abs_integral_mul_le_sqrt_mul_sqrt` in
`...JepsTransfer.Pieces2.weight_diff_integral_le`) applied to `√Q |G₁|` and `√Q |Δ|`. -/
theorem shift_pair_bound {Q G₁ G₂ : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hQ0 : ∀ y : ℝ × ℝ, 0 ≤ Q y) (hQm : Measurable Q) (hG1m : Measurable G₁)
    (hG2m : Measurable G₂)
    (hI1 : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₁ y ^ 2))
    (hInt : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2))
    (hJp : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₁ y * G₂ (y + p)))
    (hJm : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₁ y * G₂ (y - p))) :
    |(∫ y : ℝ × ℝ, Q y * G₁ y * G₂ (y + p)) - (∫ y : ℝ × ℝ, Q y * G₁ y * G₂ (y - p))|
      ≤ Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
          * Real.sqrt (∫ y : ℝ × ℝ, Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2) := by
  -- The difference of the two pairings is the pairing of `Q G₁` with `Δ = G₂(·+p) − G₂(·−p)`.
  have hdiff : (∫ y : ℝ × ℝ, Q y * G₁ y * (G₂ (y + p) - G₂ (y - p)))
      = (∫ y : ℝ × ℝ, Q y * G₁ y * G₂ (y + p))
        - (∫ y : ℝ × ℝ, Q y * G₁ y * G₂ (y - p)) := by
    rw [← MeasureTheory.integral_sub hJp hJm]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => by ring))
  -- `Q y = √(Q y)²`, so the integrand is a product of two square-roots-of-`Q` factors.
  have hpt : ∀ y : ℝ × ℝ, |Q y * G₁ y * (G₂ (y + p) - G₂ (y - p))|
      = |Real.sqrt (Q y) * G₁ y| * |Real.sqrt (Q y) * (G₂ (y + p) - G₂ (y - p))| := by
    intro y
    have h1 : (Real.sqrt (Q y) * G₁ y) * (Real.sqrt (Q y) * (G₂ (y + p) - G₂ (y - p)))
        = Real.sqrt (Q y) ^ 2 * (G₁ y * (G₂ (y + p) - G₂ (y - p))) := by ring
    calc |Q y * G₁ y * (G₂ (y + p) - G₂ (y - p))|
        = |(Real.sqrt (Q y) * G₁ y) * (Real.sqrt (Q y) * (G₂ (y + p) - G₂ (y - p)))| := by
          rw [h1, Real.sq_sqrt (hQ0 y)]
          congr 1
          ring
      _ = |Real.sqrt (Q y) * G₁ y| * |Real.sqrt (Q y) * (G₂ (y + p) - G₂ (y - p))| :=
          abs_mul _ _
  -- The two square-integrable factors.
  have hA2 : MeasureTheory.Integrable (fun y : ℝ × ℝ => (Real.sqrt (Q y) * G₁ y) ^ 2) := by
    refine hI1.congr (Filter.Eventually.of_forall (fun y => ?_))
    show Q y * G₁ y ^ 2 = (Real.sqrt (Q y) * G₁ y) ^ 2
    rw [mul_pow, Real.sq_sqrt (hQ0 y)]
  have hB2 : MeasureTheory.Integrable
      (fun y : ℝ × ℝ => (Real.sqrt (Q y) * (G₂ (y + p) - G₂ (y - p))) ^ 2) := by
    refine hInt.congr (Filter.Eventually.of_forall (fun y => ?_))
    show Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2
        = (Real.sqrt (Q y) * (G₂ (y + p) - G₂ (y - p))) ^ 2
    rw [mul_pow, Real.sq_sqrt (hQ0 y)]
  have eA : (∫ y : ℝ × ℝ, (Real.sqrt (Q y) * G₁ y) ^ 2) = ∫ y : ℝ × ℝ, Q y * G₁ y ^ 2 :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => by
      show (Real.sqrt (Q y) * G₁ y) ^ 2 = Q y * G₁ y ^ 2
      rw [mul_pow, Real.sq_sqrt (hQ0 y)]))
  have eB : (∫ y : ℝ × ℝ, (Real.sqrt (Q y) * (G₂ (y + p) - G₂ (y - p))) ^ 2)
      = ∫ y : ℝ × ℝ, Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2 :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => by
      show (Real.sqrt (Q y) * (G₂ (y + p) - G₂ (y - p))) ^ 2
          = Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2
      rw [mul_pow, Real.sq_sqrt (hQ0 y)]))
  have hAm : Measurable (fun y : ℝ × ℝ => Real.sqrt (Q y) * G₁ y) := hQm.sqrt.mul hG1m
  have hBm : Measurable (fun y : ℝ × ℝ =>
      Real.sqrt (Q y) * (G₂ (y + p) - G₂ (y - p))) :=
    hQm.sqrt.mul ((hG2m.comp (measurable_id.add measurable_const)).sub
      (hG2m.comp (measurable_id.sub measurable_const)))
  -- Cauchy–Schwarz for the two `√Q`-weighted factors.
  have hCS := Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces2.abs_integral_mul_le_sqrt_mul_sqrt
    (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) hAm hBm hA2 hB2
  calc |(∫ y : ℝ × ℝ, Q y * G₁ y * G₂ (y + p)) - (∫ y : ℝ × ℝ, Q y * G₁ y * G₂ (y - p))|
      = |∫ y : ℝ × ℝ, Q y * G₁ y * (G₂ (y + p) - G₂ (y - p))| := by rw [hdiff]
    _ ≤ ∫ y : ℝ × ℝ, |Q y * G₁ y * (G₂ (y + p) - G₂ (y - p))| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ = ∫ y : ℝ × ℝ, |Real.sqrt (Q y) * G₁ y| * |Real.sqrt (Q y) * (G₂ (y + p) - G₂ (y - p))| :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ ≤ Real.sqrt (∫ y : ℝ × ℝ, (Real.sqrt (Q y) * G₁ y) ^ 2)
        * Real.sqrt (∫ y : ℝ × ℝ, (Real.sqrt (Q y) * (G₂ (y + p) - G₂ (y - p))) ^ 2) := hCS
    _ = Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
        * Real.sqrt (∫ y : ℝ × ℝ, Q y * (G₂ (y + p) - G₂ (y - p)) ^ 2) := by rw [eA, eB]

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
