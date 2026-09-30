import Mathlib
import Submission.Work.CurveFacts.KrullDim.ringKrullDim_le_of_isLocalization
import Submission.Work.CurveBasics.BaseChange.ringKrullDim_le_of_isIntegral

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CurveFacts.KrullDim

universe u

/-- **A standard étale algebra does not increase the Krull dimension.**
If `S` is standard étale over `R` then `ringKrullDim S ≤ ringKrullDim R`.

Indeed `Algebra.IsStandardEtale R S` says that `S` is `R`-isomorphic to
`R[X][Y]/⟨f, Yg-1⟩` for a monic `f ∈ R[X]`, which in turn is `R`-isomorphic to
`(AdjoinRoot f)[1/g]` (`StandardEtalePair.equivAwayAdjoinRoot`).  Since `f` is monic,
`AdjoinRoot f` is integral over `R` (`AdjoinRoot.isIntegral_of_monic`), so
`ringKrullDim (AdjoinRoot f) ≤ ringKrullDim R` by
`Work.CurveBasics.BaseChange.ringKrullDim_le_of_isIntegral` (module
`Submission.Work.CurveBasics.BaseChange.ringKrullDim_le_of_isIntegral`); localization away from
`g` does not increase the dimension further, which is the sibling lemma
`Work.CurveFacts.KrullDim.ringKrullDim_le_of_isLocalization` (module
`Submission.Work.CurveFacts.KrullDim.ringKrullDim_le_of_isLocalization`, proved in parallel in
this directory -- import it).  Transport along the `AlgEquiv` with
`ringKrullDim_eq_of_ringEquiv`. -/
theorem ringKrullDim_le_of_isStandardEtale {R : Type u} [CommRing R] {S : Type u} [CommRing S]
    [Algebra R S] [Algebra.IsStandardEtale R S] :
    ringKrullDim S ≤ ringKrullDim R := by
  obtain ⟨P⟩ := Algebra.IsStandardEtale.nonempty_standardEtalePresentation (R := R) (S := S)
  -- `S ≃ₐ[R] P.Ring ≃ₐ[R] (AdjoinRoot P.f)[1/(AdjoinRoot.mk P.f P.g)]`.
  have h1 : ringKrullDim S = ringKrullDim P.Ring :=
    ringKrullDim_eq_of_ringEquiv P.equivRing.toRingEquiv
  have h2 : ringKrullDim P.Ring
      = ringKrullDim (Localization.Away (AdjoinRoot.mk P.f P.g)) :=
    ringKrullDim_eq_of_ringEquiv P.P.equivAwayAdjoinRoot.toRingEquiv
  have h3 : ringKrullDim (Localization.Away (AdjoinRoot.mk P.f P.g))
      ≤ ringKrullDim (AdjoinRoot P.f) :=
    ringKrullDim_le_of_isLocalization (Submonoid.powers (AdjoinRoot.mk P.f P.g))
  have h4 : ringKrullDim (AdjoinRoot P.f) ≤ ringKrullDim R :=
    @Work.CurveBasics.BaseChange.ringKrullDim_le_of_isIntegral R (AdjoinRoot P.f) _ _ _
      (AdjoinRoot.isIntegral_of_monic P.monic_f)
  calc ringKrullDim S = ringKrullDim P.Ring := h1
    _ = ringKrullDim (Localization.Away (AdjoinRoot.mk P.f P.g)) := h2
    _ ≤ ringKrullDim (AdjoinRoot P.f) := h3
    _ ≤ ringKrullDim R := h4

end Work.CurveFacts.KrullDim
