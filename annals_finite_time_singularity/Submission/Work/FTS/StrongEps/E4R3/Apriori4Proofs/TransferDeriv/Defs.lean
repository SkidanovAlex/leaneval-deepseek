import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.EllipticEst.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `TransferDeriv/Defs.lean` — the derivative-priced plane transfer estimate

The `JepsTransfer` chapter isolates, as the predicate `JT.LogPlaneTransfer`, the analytic core of
the *even*-kernel transfer estimate: for an even kernel `k` supported in the `ℓ¹`-ball of radius
`2ε` and a log-Lipschitz weight `Q`,

  `|∫ Q (k * G₁) G₂ − ∫ Q G₁ (k * G₂)| ≤ C ε √(∫ Q G₁²) √(∫ Q G₂²)`.

That estimate is **false** without the evenness of `k` (take `k` a point mass at `p₀` with
`|p₀| = ε`, `G₁ = 1_{[−ε,0]}`, `G₂ = 1_{[0,ε]}`: the defect is `≍ ε` while `ε‖G₁‖‖G₂‖ ≍ ε²`).
What *is* true for an arbitrary kernel is the same estimate **at the price of one derivative on
the second argument**:

  `|∫ Q (k * G₁) G₂ − ∫ Q G₁ (k * G₂)| ≤ C ε √(∫ Q G₁²) (√(∫ Q G₂²) + √(∫ Q ‖fderiv G₂‖²))`.

The mechanism: writing `D` for the defect and substituting `y ↦ y + p` in the first half,

  `D = ∫∫ k p · G₁ y · [Q (y+p) G₂ (y+p) − Q y G₂ (y−p)] dy dp`,

splits into the *weight difference* `∫∫ k p G₁ y (Q (y+p) − Q y) G₂ (y+p)` — which is `O(ε)`
because `Q` is log-Lipschitz (`Pieces2.weight_diff_integral_le`, proved) — and the *shift
difference* `∫∫ k p G₁ y Q y (G₂ (y+p) − G₂ (y−p))`.  For even `k` the shift-difference term
cancels under `p ↦ −p`; for odd `k` it does not, but it is a *difference operator*:
`∫ k p (G₂ (y+p) − G₂ (y−p)) dp` is controlled by `2|p| · sup|∇G₂|` on the segment, so its
`L²_Q`-norm is `O(ε) ‖∇G₂‖_{L²_Q}`.

This is the interface consumed by the level-four (and level-six) transfer lemmas of the
`Apriori4` chapter.  The predicate is stated for an arbitrary measurable kernel `k` with
`∫ |k| ≤ 1`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

/-- **The derivative-priced plane transfer estimate.**  For every measurable kernel `k` with
`∫ |k| ≤ 1` supported in the `ℓ¹`-ball of radius `2ε`, every nonnegative log-Lipschitz weight `Q`
and all `C¹` profiles `G₁`, `G₂` with finite weighted `L²`-norms, the transfer defect of the
convolution `k * ·` is `O(ε)`, with one derivative charged on the second argument.

The constant is `100 (Cw+1) e^{4Cw}`; the hypotheses `hI1`, `hI2`, `hIg`, `hconv1`, `hconv2` are
the integrability certificates (they are discharged in the applications from the weighted
membership of the slots). -/
def PlaneTransferDeriv : Prop :=
  ∀ {k Q : ℝ × ℝ → ℝ} {ε Cw : ℝ},
    0 < ε → ε ≤ 1 → 0 ≤ Cw →
    Measurable k → Integrable k → (∫ p : ℝ × ℝ, |k p| ≤ 1) →
    (∀ p : ℝ × ℝ, k p ≠ 0 → |p.1| + |p.2| ≤ 2 * ε) →
    (∀ y : ℝ × ℝ, 0 ≤ Q y) → Measurable Q →
    (∀ y p : ℝ × ℝ, Q (y + p) ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q y) →
    (∀ y p : ℝ × ℝ, Q y ≤ Real.exp (Cw * (|p.1| + |p.2|)) * Q (y + p)) →
    ∀ {G₁ G₂ : ℝ × ℝ → ℝ}, Measurable G₁ → Measurable G₂ → ContDiff ℝ 1 G₂ →
      (∀ y : ℝ × ℝ, Integrable (fun p : ℝ × ℝ => k p * G₁ (y - p))) →
      (∀ y : ℝ × ℝ, Integrable (fun p : ℝ × ℝ => k p * G₂ (y - p))) →
      Integrable (fun y : ℝ × ℝ => Q y * G₁ y ^ 2) →
      Integrable (fun y : ℝ × ℝ => Q y * G₂ y ^ 2) →
      Integrable (fun y : ℝ × ℝ => Q y * ‖fderiv ℝ G₂ y‖ ^ 2) →
      |(∫ y : ℝ × ℝ, Q y * (∫ p : ℝ × ℝ, k p * G₁ (y - p)) * G₂ y)
        - (∫ y : ℝ × ℝ, Q y * G₁ y * (∫ p : ℝ × ℝ, k p * G₂ (y - p)))| ≤
        100 * (Cw + 1) * Real.exp (4 * Cw) * ε * Real.sqrt (∫ y : ℝ × ℝ, Q y * G₁ y ^ 2)
          * (Real.sqrt (∫ y : ℝ × ℝ, Q y * G₂ y ^ 2)
              + Real.sqrt (∫ y : ℝ × ℝ, Q y * ‖fderiv ℝ G₂ y‖ ^ 2))

/-- **The integrability certificates of the derivative-priced slot transfer**, for one specific
slot pair `(u, v)`.  The single-slot transfer estimate is applied to the pairing
`wip w (mixed b a ·) (mixed b a ·)`; the plane estimate consumes the finiteness of the two slots,
of the *mollified* second slot, of the mixed product, and of the two first-order slots of the
second argument (the derivative price).  In the applications these six conditions are discharged
from `HkMem α 4 f` (for `u`) and `HkMem α 5 h` (for `v`). -/
def SlotIntegrableDeriv (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (w : ℝ → ℝ → ℝ) (a b : ℕ)
    (u v : Work.FTS.Galerkin.Fn) : Prop :=
  Integrable (Function.uncurry (fun z θ => w z θ * (Work.Spaces.mixed b a u z θ) ^ 2))
    ∧ Integrable (Function.uncurry (fun z θ => w z θ * (Work.Spaces.mixed b a v z θ) ^ 2))
    ∧ Integrable (Function.uncurry (fun z θ => w z θ
        * (Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε v) z θ) ^ 2))
    ∧ Integrable (Function.uncurry (fun z θ => w z θ * Work.Spaces.mixed b a u z θ
        * Work.Spaces.mixed b a (Work.FTS.StrongEps.Jeps ρ ε v) z θ))
    ∧ Integrable (Function.uncurry (fun z θ => w z θ
        * (Work.Spaces.mixed (b + 1) a v z θ) ^ 2))
    ∧ Integrable (Function.uncurry (fun z θ => w z θ
        * (Work.Spaces.mixed b (a + 1) v z θ) ^ 2))

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
