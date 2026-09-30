import Mathlib
import Submission.Work.CurveFacts.KrullDim.ringKrullDimLE_one_of_etale_mvPolynomial_fin_one
import Submission.Work.CurveFacts.KrullDim.ringKrullDim_le_of_isLocalization

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CurveFacts.KrullDim

universe u

set_option linter.style.haveILetI false in
/-- **An algebra standard smooth of relative dimension one over a field has local rings of Krull
dimension at most one at every prime.**  This is the commutative-algebra core of item A2
(`Work.CurveFacts.krullDimLE_stalk_of_smoothOfRelativeDimension_one`): the scheme-level statement
reduces to it by taking an affine chart.

Route.  By Mathlib's `Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`
(`Mathlib/RingTheory/RingHom/StandardSmooth.lean`) the relative dimension is *exactly* the size of
the polynomial ring one lands in: there is `g : MvPolynomial (Fin 1) K →ₐ[K] A` with `g.Etale`
(in the tower `K → MvPolynomial (Fin 1) K → A`).  Then `Ring.KrullDimLE 1 A` follows from
`Work.CurveFacts.KrullDim.ringKrullDimLE_one_of_etale_mvPolynomial_fin_one` (module
`Submission.Work.CurveFacts.KrullDim.ringKrullDimLE_one_of_etale_mvPolynomial_fin_one`, proved in
this directory), and `ringKrullDim (Localization.AtPrime p) ≤ ringKrullDim A` is
`Work.CurveFacts.KrullDim.ringKrullDim_le_of_isLocalization` (module
`Submission.Work.CurveFacts.KrullDim.ringKrullDim_le_of_isLocalization`); combine with
`Ring.krullDimLE_iff`.  (Equivalently, use `IsLocalization.AtPrime.ringKrullDim_eq_height` together
with `Ideal.height_le_ringKrullDim_of_ne_top`.) -/
theorem krullDimLE_localizationAtPrime_of_isStandardSmoothOfRelativeDimension_one
    {K : Type u} [Field K] {A : Type u} [CommRing A] [Algebra K A]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 K A] (p : Ideal A) [p.IsPrime] :
    Ring.KrullDimLE 1 (Localization.AtPrime p) := by
  -- Step 1: `A` itself has Krull dimension at most one.
  have hA : Ring.KrullDimLE 1 A := by
    obtain ⟨g, hg⟩ :=
      Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial
        (n := 1) (R := K) (S := A)
    letI : Algebra (MvPolynomial (Fin 1) K) A := g.toRingHom.toAlgebra
    haveI : IsScalarTower K (MvPolynomial (Fin 1) K) A :=
      IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
    haveI : Algebra.Etale (MvPolynomial (Fin 1) K) A := hg
    exact ringKrullDimLE_one_of_etale_mvPolynomial_fin_one (K := K) (A := A)
  -- Step 2: localization does not increase the Krull dimension.
  rw [Ring.krullDimLE_iff]
  calc ringKrullDim (Localization.AtPrime p)
      ≤ ringKrullDim A :=
        ringKrullDim_le_of_isLocalization (R := A) (S := Localization.AtPrime p) p.primeCompl
    _ ≤ 1 := Ring.krullDimLE_iff.mp hA

end Work.CurveFacts.KrullDim
