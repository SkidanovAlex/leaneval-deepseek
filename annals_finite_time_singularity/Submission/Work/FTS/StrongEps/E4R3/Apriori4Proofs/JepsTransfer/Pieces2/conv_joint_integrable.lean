import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces.integrable_conv_pair

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `conv_joint_integrable` — joint integrability of the two mollifier-convolution pairings

In the log coordinates `(s, ζ) = (log z, log tan θ)` of `JepsTransfer/Defs.lean` the level-`k`
pairing of the `IP6`-transfer estimate becomes an integral over `(y, p) ∈ (ℝ × ℝ)²` of one of

  `k p * Q y * G₁ (y - p) * G₂ y`   resp.   `k p * Q y * G₁ y * G₂ (y + p)`,

where `k` is the (nonnegative, integrable) mollifier kernel, supported in the box
`|p.1| + |p.2| ≤ 2 ε`, and `Q` is the pulled-back weight, which is only *shift bounded*,
`Q (y + p) ≤ exp (Cw * (|p.1| + |p.2|)) * Q y`.  The two profiles are merely measurable with
`Q G₁²`, `Q G₂²` integrable.

The `(y - p)` pairing is `Pieces.integrable_shifted_pair`, the dominating-function form of the
AM–GM argument: pointwise,

  `|k p Q y G₁ (y-p) G₂ y| ≤ (c/2) k p (Q (y-p) G₁ (y-p)²) + (c/2) k p (Q y G₂ y²)`,

with `c = exp (2 Cw ε)`, and the two summands are integrable by the convolution integrand lemma
and by `Integrable.mul_prod` respectively.

The `(y + p)` pairing is *not* of that shape; it is reduced to it by negating the kernel
(`p ↦ -p`, which preserves integrability, nonnegativity and the support condition) and then
flipping the sign of the `p`-variable in the joint integral.  The flip
`z ↦ (z.1, -z.2)` preserves Lebesgue measure on `(ℝ × ℝ)²` because it is the product of the
identity with `Measure.measurePreserving_neg`, and `MeasurePreserving.integrable_comp` transfers
integrability along it (`integrable_flip_snd` below).

The statement is used as given by the requester; nothing else in the development is affected.
-/

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces2

open MeasureTheory

/-- Flipping the sign of the second coordinate is a measure-preserving map of
`(ℝ × ℝ) × (ℝ × ℝ)` with Lebesgue measure: it is the product of the identity with the negation
of `ℝ × ℝ`. -/
lemma measurePreserving_snd_neg :
    MeasurePreserving (fun z : (ℝ × ℝ) × (ℝ × ℝ) => (z.1, -z.2)) volume volume := by
  rw [MeasureTheory.Measure.volume_eq_prod]
  exact MeasurePreserving.prod (MeasurePreserving.id _) (Measure.measurePreserving_neg _)

/-- Integrability of a joint integrand is invariant under flipping the sign of the second
variable. -/
lemma integrable_flip_snd {F : ℝ × ℝ → ℝ × ℝ → ℝ}
    (h : Integrable (Function.uncurry F) volume) :
    Integrable (Function.uncurry fun y p => F y (-p)) volume := by
  convert measurePreserving_snd_neg.integrable_comp_of_integrable h using 1
  ext z
  rfl

theorem conv_joint_integrable {k Q G₁ G₂ : ℝ × ℝ → ℝ} {Cw ε : ℝ} (hCw : 0 ≤ Cw)
    (hk : MeasureTheory.Integrable k) (hk0 : ∀ p : ℝ × ℝ, 0 ≤ k p)
    (hksupp : ∀ p : ℝ × ℝ, k p ≠ 0 → |p.1| + |p.2| ≤ 2 * ε)
    (hQ0 : ∀ y : ℝ × ℝ, 0 ≤ Q y) (hQm : Measurable Q)
    (hQsh : ∀ y p : ℝ × ℝ, Q (y + p) ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q y)
    (hG1m : Measurable G₁) (hG2m : Measurable G₂)
    (hI1 : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₁ y ^ 2))
    (hI2 : MeasureTheory.Integrable (fun y : ℝ × ℝ => Q y * G₂ y ^ 2)) :
    MeasureTheory.Integrable (Function.uncurry fun (y p : ℝ × ℝ) => k p * Q y * G₁ (y - p) * G₂ y)
      ∧ MeasureTheory.Integrable (Function.uncurry fun (y p : ℝ × ℝ) => k p * Q y * G₁ y * G₂ (y + p)) := by
  -- the `(y - p)` pairing: the AM–GM domination of the sibling module `Pieces`
  have key := Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces.integrable_shifted_pair
    (k := k) (Q := Q) (G := G₁) (H := G₂) hCw hk hk0 hksupp hQ0 hQm hQsh hG1m hG2m hI1 hI2
  constructor
  · -- only the order of the factors differs
    refine key.congr ?_
    filter_upwards with z
    simp only [Function.uncurry]
    ring
  · -- the `(y + p)` pairing: negate the kernel, exchange the two profiles, flip `p ↦ -p`
    have hk' : MeasureTheory.Integrable (fun p : ℝ × ℝ => k (-p)) := hk.comp_neg
    have hk0' : ∀ p : ℝ × ℝ, 0 ≤ k (-p) := fun p => hk0 (-p)
    have hksupp' : ∀ p : ℝ × ℝ, k (-p) ≠ 0 → |p.1| + |p.2| ≤ 2 * ε := by
      intro p hp
      have h := hksupp (-p) hp
      simpa using h
    have key2 := Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces.integrable_shifted_pair
      (k := fun p : ℝ × ℝ => k (-p)) (Q := Q) (G := G₂) (H := G₁)
      hCw hk' hk0' hksupp' hQ0 hQm hQsh hG2m hG1m hI2 hI1
    refine (integrable_flip_snd key2).congr ?_
    filter_upwards with z
    simp only [Function.uncurry, neg_neg, sub_neg_eq_add]
    ring

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Pieces2
