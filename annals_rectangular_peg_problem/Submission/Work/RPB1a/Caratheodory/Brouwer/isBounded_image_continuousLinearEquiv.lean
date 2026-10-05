import Mathlib

namespace Work.RPB1a.Caratheodory.Brouwer

/-- **Boundedness is preserved by a continuous linear equivalence.**  For a continuous linear
equivalence `e : E ≃L[𝕜] F` between normed spaces over a nontrivially normed field (using the metric
bornology), the image `e '' s` of a set is bounded if and only if `s` is: both `e` and `e.symm` are
Lipschitz (with constants `‖e‖₊` and `‖e.symm‖₊`), so each maps bounded sets to bounded sets. -/
theorem isBounded_image_continuousLinearEquiv
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    (e : E ≃L[𝕜] F) (s : Set E) :
    Bornology.IsBounded (e '' s) ↔ Bornology.IsBounded s := by
  constructor
  · intro h
    have hs := (ContinuousLinearEquiv.lipschitzWith e.symm).isBounded_image h
    simpa [Set.image_image] using hs
  · intro h
    exact (ContinuousLinearEquiv.lipschitzWith e).isBounded_image h

end Work.RPB1a.Caratheodory.Brouwer
