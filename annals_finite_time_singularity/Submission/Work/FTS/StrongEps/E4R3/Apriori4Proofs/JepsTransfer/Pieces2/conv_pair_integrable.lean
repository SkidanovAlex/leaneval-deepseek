import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces.integrable_conv_pair

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of the two mollifier–convolution pairings

The kernel `k` is nonnegative, integrable and supported in the box `|p.1| + |p.2| ≤ 2 ε`, and the
weight `Q ≥ 0` is only *shift bounded*, `Q (y + p) ≤ exp (Cw * (|p.1| + |p.2|)) * Q y`.  For such
data the *joint* (in `(y,p)`) integrability of `Q y * k p * G₁ (y - p) * G₂ y` is the content of
`Pieces.integrable_shifted_pair` (an AM–GM together with the convolution lemma
`MeasureTheory.Integrable.convolution_integrand`, with the support of `k` converting the shift
bound into the *constant* `Real.exp (2 * Cw * ε)`).

Here we deduce from it the *marginal* statement: the pairing in which the `p`-integral is carried
out first is again integrable in `y`.  Concretely, since the joint integrand is integrable, its
`s`-fibre integral `y ↦ ∫ p, Q y * k p * G₁ (y - p) * G₂ y` is integrable by Fubini
(`MeasureTheory.Integrable.integral_prod_left`); the constants `Q y` and `G₂ y` may be pulled out
of that fibre integral, turning it into `Q y * (∫ p, k p * G₁ (y - p)) * G₂ y`, and the two
functions are equal everywhere, hence a.e.
-/

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces2

open MeasureTheory

-- the two convolution-integrability hypotheses are not needed for the *marginal* statement
set_option linter.unusedVariables false in
theorem conv_pair_integrable {k Q G₁ G₂ : ℝ × ℝ → ℝ} {Cw ε : ℝ} (hCw : 0 ≤ Cw)
    (hk : MeasureTheory.Integrable k) (hk0 : ∀ p : ℝ × ℝ, 0 ≤ k p)
    (hksupp : ∀ p : ℝ × ℝ, k p ≠ 0 → |p.1| + |p.2| ≤ 2 * ε)
    (hQ0 : ∀ y : ℝ × ℝ, 0 ≤ Q y) (hQm : Measurable Q)
    (hQsh : ∀ y p : ℝ × ℝ, Q (y + p) ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q y)
    (hG1m : Measurable G₁) (hG2m : Measurable G₂)
    (hconv1 : ∀ y : ℝ × ℝ, MeasureTheory.Integrable (fun p : ℝ × ℝ => k p * G₁ (y - p)))
    (hconv2 : ∀ y : ℝ × ℝ, MeasureTheory.Integrable (fun p : ℝ × ℝ => k p * G₂ (y - p)))
    (hI1 : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₁ y ^ 2))
    (hI2 : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₂ y ^ 2)) :
    MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * (∫ p : ℝ × ℝ, k p * G₁ (y - p)) * G₂ y)
      ∧ MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₁ y * (∫ p : ℝ × ℝ, k p * G₂ (y - p))) := by
  -- The common shape: for measurable `A`, `B` with the weighted `L²` bounds `Q A²`, `Q B²`, the
  -- pairing `Q y * B y * (∫ p, k p * A (y - p))` is integrable.
  have key : ∀ (A B : ℝ × ℝ → ℝ), Measurable A → Measurable B →
      MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * A y ^ 2) →
      MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * B y ^ 2) →
      MeasureTheory.Integrable
        (fun y : ℝ × ℝ => Q y * B y * (∫ p : ℝ × ℝ, k p * A (y - p))) := by
    intro A B hAm hBm hIA hIB
    -- joint integrability of `(y, p) ↦ Q y * k p * A (y - p) * B y`
    have hJ : MeasureTheory.Integrable
        (fun z : (ℝ × ℝ) × (ℝ × ℝ) => Q z.1 * k z.2 * A (z.1 - z.2) * B z.1) volume :=
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces.integrable_shifted_pair
        hCw hk hk0 hksupp hQ0 hQm hQsh hAm hBm hIA hIB
    -- Fubini: the fibre integral over `p` is integrable in `y`
    have hI := MeasureTheory.Integrable.integral_prod_left (μ := volume) (ν := volume) hJ
    refine hI.congr ?_
    filter_upwards with y
    -- pull the `p`-independent constants out of the fibre integral
    have hfun : (fun p : ℝ × ℝ => Q y * k p * A (y - p) * B y)
        = fun p => (Q y * B y) * (k p * A (y - p)) := by
      funext p
      ring
    rw [hfun, MeasureTheory.integral_const_mul]
  exact ⟨(key G₁ G₂ hG1m hG2m hI1 hI2).congr (by filter_upwards with y; ring),
    key G₂ G₁ hG2m hG1m hI2 hI1⟩

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces2
