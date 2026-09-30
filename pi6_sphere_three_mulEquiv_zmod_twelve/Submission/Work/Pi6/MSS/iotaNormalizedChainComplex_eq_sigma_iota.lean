import Mathlib
import Submission.Work.SSSR.serreE1CoefIso
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.MSS

open CategoryTheory

/- The normalized-chain-complex generator attached to a nondegenerate `n`-simplex `x` is the
coproduct inclusion of `R` at the index `⟨x, hx⟩`.

This is the public form of Mathlib's private lemma `SSet.ιNormalizedChainComplex_eq_ι`
(`Mathlib/AlgebraicTopology/SimplicialSet/Homology/Nondegenerate.lean`), where the proof needs
`respectTransparency false` in order to unfold the `[no_expose]` definition of
`ιNormalizedChainComplex` and the (semireducible) identification
`(X.normalizedChainComplex R).X n = ∐ (fun _ : X.nonDegenerate n => R)`. -/
set_option backward.isDefEq.respectTransparency false in
theorem iotaNormalizedChainComplex_eq_sigma_iota {C : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Limits.HasCoproducts C] [CategoryTheory.Preadditive C] (X : SSet) {R : C}
    {n : ℕ} (x : X.obj (Opposite.op (SimplexCategory.mk n))) (hx : x ∈ X.nonDegenerate n) :
    X.ιNormalizedChainComplex (R := R) x =
      CategoryTheory.Limits.Sigma.ι (fun _ : X.nonDegenerate n => R) ⟨x, hx⟩ := by
  dsimp [SSet.ιNormalizedChainComplex, SSet.ιChainComplex]
  rw [← cancel_mono ((X.fromNormalizedChainComplex R).f n), Category.assoc,
    SSet.toNormalizedChainComplex_f_fromNormalizedChainComplex_f]
  simp [SSet.fromNormalizedChainComplex, SimplicialObject.Splitting.fromNondegComplex_f]

end Work.Pi6.MSS
