import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouParabolic.Core

/-- A complex differentiable map `F : ℂ → ℂ` whose derivative does not vanish on `s` is a local
homeomorphism around every point of `s`.

Since `F` is holomorphic it is analytic at every point (`Differentiable.analyticAt`), hence
strictly differentiable there (`AnalyticAt.hasStrictDerivAt`); a non-zero complex derivative makes
the differential an invertible (complex) linear map, and Mathlib's inverse function theorem
(`HasStrictFDerivAt.toOpenPartialHomeomorph`) turns this into the required chart. -/
theorem isLocalHomeomorphOn_of_deriv_ne_zero {F : ℂ → ℂ} {s : Set ℂ}
    (hF : Differentiable ℂ F) (h : ∀ x ∈ s, deriv F x ≠ 0) :
    IsLocalHomeomorphOn F s := by
  intro z hz
  have hzan : AnalyticAt ℂ F z := hF.analyticAt z
  have hsd : HasStrictDerivAt F (deriv F z) z := hzan.hasStrictDerivAt
  have hne : deriv F z ≠ 0 := h z hz
  have hfd : HasStrictFDerivAt F
      ((ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 (deriv F z) hne)) : ℂ →L[ℂ] ℂ) z :=
    hsd.hasStrictFDerivAt_equiv hne
  refine ⟨hfd.toOpenPartialHomeomorph F, ?_, ?_⟩
  · exact hfd.mem_toOpenPartialHomeomorph_source
  · exact (HasStrictFDerivAt.toOpenPartialHomeomorph_coe hfd).symm

end Work.FatouParabolic.Core
