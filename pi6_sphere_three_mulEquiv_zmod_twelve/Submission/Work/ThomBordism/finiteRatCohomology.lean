import Mathlib
import Submission.Work.ThomBordism.goodUnivCharted
import Submission.Work.Cohomology.pd_middleDegree_of_good
import Submission.Work.SignatureBordism.Rationalisation

set_option synthInstance.maxHeartbeats 400000

/-!
# Finiteness of the middle rational cohomology of a compact charted space with Poincaré duality

`Work.Cohomology.pd_middleDegree_of_good` gives, from `Good (n+n) c Set.univ` for a compact `T2`
space charted in dimension `n+n`, the **bijectivity** of the middle cap product
`y ↦ y ⌢ c : H^n(M;ℤ) → H_n(M;ℤ)`.  In particular the middle *cohomology* is finitely generated
whenever the middle *homology* is (which is the case for a compact `C^∞` manifold, by
`Work.ThomBordism.compactHomologyFinite`), and hence `H^n(M;ℚ)` is finite dimensional.

This is the finiteness input that the additivity statements of `σ` need
(`Work.ThomBordism.sigmaSigmaTypeSum`, `Work.Bordism.sigma_disj`): their hypotheses are
`FiniteDimensional ℚ (H^k(·;ℚ))`, which is *not* available in general but *is* available for the
compact closed pieces of this chapter.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory
open scoped TensorProduct

namespace Work.ThomBordism

noncomputable section

/-- **The middle rational cohomology of a compact charted space with `Good` is finite
dimensional**, from finite generation of its middle integral homology. -/
theorem finiteDimensional_ratCohomology_of_good {n : ℕ} {M : TopCat} [CompactSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + n))) M]
    {c : (Work.Cohomology.singularChains ℤ M).homology (n + n)}
    (h : Work.Cohomology.Good (n + n) c Set.univ isOpen_univ)
    (hfg : Module.Finite ℤ ((Work.Cohomology.singularChains ℤ M).homology n)) :
    FiniteDimensional ℚ (Work.SignatureBordism.ratCohomology n (TopCat.toSSet.obj M)) := by
  have hb := Work.Cohomology.pd_middleDegree_of_good n M c h
  let f : (Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj M)).homology n →ₗ[ℤ]
      (Work.Cohomology.chainC ℤ (TopCat.toSSet.obj M)).homology n :=
    (LinearMap.applyₗ c).comp (Work.Cohomology.capPair ℤ (TopCat.toSSet.obj M) n n)
  have hfb : Function.Bijective f := hb
  haveI hfg' : Module.Finite ℤ ((Work.Cohomology.chainC ℤ (TopCat.toSSet.obj M)).homology n) := hfg
  haveI : Module.Finite ℤ ((Work.Cohomology.cochainC ℤ (TopCat.toSSet.obj M)).homology n) :=
    Module.Finite.equiv (LinearEquiv.ofBijective f hfb).symm
  exact Module.Finite.base_change ℤ ℚ _

end

end Work.ThomBordism
