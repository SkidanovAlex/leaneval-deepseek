/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The one-sided disc-extension property, as a predicate

`DiscExt α c` packages the one-variable input used to extend a `C^k` function with finite
`C^{k,α}` norm across the boundary of a disc: over an arbitrary open parameter region `U` in an
arbitrary real normed space `X`, a function `g : X × ℂ → ℂ` of class `C^k` on `U × ball(0,1)`
with finite `C^{k,α}` norm there extends to a `C^k` function on `U × ball(0,c)`, agreeing with
`g` on `U × ball(0,1)`, with a `C^{k,α}` norm bound.

Its content is proved (as a separate lemma) in
`Work.NN.Final.one_sided_disc_extension`; this file only records the predicate so that the
coordinate-by-coordinate assembly of `Work.NN.Final.one_sided_extension_le` can be stated in
terms of it.
-/
import Mathlib
import Submission.Work.CR.Flat.Holder

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set Metric

namespace Work.NN.Final

open Work.CR.Flat

/-- The one-sided disc-extension property in the `C^{k,α}` scale, uniformly in the parameter
region and in the function. -/
def DiscExt (α : ℝ) (c : ℝ) : Prop :=
  ∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X],
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      ∀ (k : ℕ) (U : Set X) (g : X × ℂ → ℂ), IsOpen U →
        (∀ m : ℕ, m ≤ k → ContDiffOn ℝ (m : WithTop ENat) g (U ×ˢ Metric.ball (0 : ℂ) 1)) →
        Work.CR.Flat.holderNorm k α g (U ×ˢ Metric.ball (0 : ℂ) 1) ≠ ⊤ →
        ∃ G : X × ℂ → ℂ,
          ContDiffOn ℝ (k : WithTop ENat) G (U ×ˢ Metric.ball (0 : ℂ) c) ∧
          (∀ p : X × ℂ, p.1 ∈ U → ‖p.2‖ < 1 → G p = g p) ∧
          Work.CR.Flat.holderNorm k α G (U ×ˢ Metric.ball (0 : ℂ) c)
            ≤ ENNReal.ofReal (C k) * Work.CR.Flat.holderNorm k α g (U ×ˢ Metric.ball (0 : ℂ) 1)

end Work.NN.Final
