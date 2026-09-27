import Mathlib
import Submission.Work.Whitney.CancelSigned

/-!
# The signed insertion interface

The endgame's signed cancellation (`Work.Whitney.HasCancelSigned`) needs the framing hypothesis
`Work.Whitney.OppositeType f γ₁ γ₂ p₁ p₂ q₁ q₂` for the two arcs of its clean region.  The
insertion step must therefore produce not just *a* partner double point (`HasInsertionNF` does that,
sign-free) but a partner that is of the *opposite type* along whatever arcs the endgame will use.

The right shape is the one the proved `Work.Whitney.exists_oppositeType_of_insertion` supports: the
insertion produces **both** candidates `fp`, `fm` (same inserted pair `(p', q')`, same compatible
gluing, opposite determinant signs at the inserted point, as supplied by the proved
`Work.Whitney.exists_addDoublePoint_both_signs_located` family of results), and then, *for every*
pair of arcs joining `p₁, p₂` to `p', q'`, **one of the two** is of opposite type along those arcs.

That is `Work.Whitney.HasInsertionSigned` below.  It carries the framing data out of the insertion
step, so that the signed reduction (`exists_reduce_double_points_NFT` with `HasCancelSigned` in
place of `HasCancelNFT`) can pick the right candidate and cancel.
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Topology

set_option linter.unusedVariables false

/-- **The signed insertion interface.**  Two candidate modifications `fp`, `fm` of `f` inserting a
partner double point `(p', q')` with the full gluing structure (same inserted pair, both satisfying
`InsertedDP`, `SimpleDP`, `TransDP'`), such that for every pair of arcs from `p₁`, `p₂` to `p'`,
`q'` one of the two is of opposite type along those arcs. -/
def HasInsertionSigned (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M] : Prop :=
  ∀ (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ f)
    (himm : ∀ y, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) f y))
    (hfin : (doubleSet f).Finite)
    (hsimple : SimpleDP f) (htrans : TransDP' f)
    (p₁ p₂ : M) (hp₁p₂ : p₁ ≠ p₂) (hfp : f p₁ = f p₂),
    ∃ (fp fm : M → EuclideanSpace ℝ (Fin (2 * n))) (p' q' : M),
      InsertedDP f p₁ p₂ fp p' q' ∧ SimpleDP fp ∧ TransDP' fp ∧
      InsertedDP f p₁ p₂ fm p' q' ∧ SimpleDP fm ∧ TransDP' fm ∧
      (∀ (γ₁ γ₂ : ℝ → M), Continuous γ₁ → Continuous γ₂ →
        γ₁ 0 = p₁ → γ₁ 1 = p' → γ₂ 0 = p₂ → γ₂ 1 = q' →
        OppositeType fp γ₁ γ₂ p₁ p₂ p' q' ∨ OppositeType fm γ₁ γ₂ p₁ p₂ p' q')

end Work.Whitney
