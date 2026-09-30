import Mathlib
import Submission.Work.CurveFacts.KrullDim.ringKrullDim_le_of_isStandardEtale

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CurveFacts.KrullDim

universe u

set_option linter.style.haveILetI false in
/-- **An algebra étale over the polynomial ring in one variable over a field has Krull dimension
at most one.**

Route.  `Ring.krullDimLE_of_isLocalization_maximal` (`Mathlib/RingTheory/Ideal/Height.lean`)
reduces the claim to `Ring.KrullDimLE 1 (Localization.AtPrime P)` for maximal ideals `P`.  For such
a `P`, the local structure result for étale algebras
(`Algebra.IsEtaleAt.exists_isStandardEtale`, `Mathlib/RingTheory/Unramified/LocalStructure.lean`,
applicable since `Algebra.Etale` supplies `FinitePresentation` and `IsEtaleAt` at every prime)
gives `f ∉ P` with `IsStandardEtale (MvPolynomial (Fin 1) K) (Localization.Away f)`.

`Localization.AtPrime P` is the localization of `Localization.Away f` at the prime
`P' := P · Localization.Away f` (a localization of a localization, since `f ∉ P` is a unit in
`Localization.AtPrime P`), so by `IsLocalization.AtPrime.ringKrullDim_eq_height` and
`Ideal.height_le_ringKrullDim_of_ne_top`

  `ringKrullDim (Localization.AtPrime P) = height P' ≤ ringKrullDim (Localization.Away f)`,

and the latter is at most `ringKrullDim (MvPolynomial (Fin 1) K) = 1` by
`Work.CurveFacts.KrullDim.ringKrullDim_le_of_isStandardEtale` (module
`Submission.Work.CurveFacts.KrullDim.ringKrullDim_le_of_isStandardEtale`, already proved in this
directory) together with `MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite`.

An alternative, possibly shorter, route: the fibres of an étale (indeed of any unramified and
finitely presented) map are finite, so a strictly increasing chain of primes of `A` contracts to a
strictly increasing chain in `K[X₁]`, giving `ringKrullDim A ≤ ringKrullDim (MvPolynomial (Fin 1)
K) = 1` directly. -/
theorem ringKrullDimLE_one_of_etale_mvPolynomial_fin_one {K : Type u} [Field K] {A : Type u}
    [CommRing A] [Algebra K A] [Algebra (MvPolynomial (Fin 1) K) A]
    [IsScalarTower K (MvPolynomial (Fin 1) K) A] [Algebra.Etale (MvPolynomial (Fin 1) K) A] :
    Ring.KrullDimLE 1 A := by
  -- `A` is of finite presentation over `K[X]`, and étale at every prime.
  haveI : Algebra.FinitePresentation (MvPolynomial (Fin 1) K) A := inferInstance
  -- The polynomial ring in one variable over a field has Krull dimension one.
  have hmv : ringKrullDim (MvPolynomial (Fin 1) K) ≤ 1 := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite (R := K) (ι := Fin 1),
      ringKrullDim_eq_zero_of_field]
    norm_num [Nat.card_eq_fintype_card]
  -- It suffices to bound the dimension of the localizations at maximal ideals.
  refine Ring.krullDimLE_of_isLocalization_maximal
    (Rₚ := fun (P : Ideal A) (_ : P.IsMaximal) => Localization.AtPrime P) ?_
  intro P hP
  rw [Ring.krullDimLE_iff]
  -- Local structure: `A` is standard étale away from some `f ∉ P`.
  obtain ⟨f, hfP, hstd⟩ :=
    Algebra.IsEtaleAt.exists_isStandardEtale (R := MvPolynomial (Fin 1) K) (S := A) P
  haveI : Algebra.IsStandardEtale (MvPolynomial (Fin 1) K) (Localization.Away f) := hstd
  -- `f ∉ P`, so the powers of `f` are disjoint from the prime `P`.
  have hdisj : Disjoint (↑(Submonoid.powers f) : Set A) (↑P : Set A) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime (I := P) f).mpr hfP
  have hprime : (Ideal.map (algebraMap A (Localization.Away f)) P).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) (Localization.Away f) P
      inferInstance hdisj
  -- `A_P = (A_f)_{P'}` where `P' = P·A_f`, so `ringKrullDim A_P = height P' ≤ ringKrullDim A_f`.
  calc ringKrullDim (Localization.AtPrime P)
      = ↑P.height := IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P)
    _ = ↑(Ideal.map (algebraMap A (Localization.Away f)) P).height := by
        rw [IsLocalization.height_map_of_disjoint (Submonoid.powers f) P hdisj]
    _ ≤ ringKrullDim (Localization.Away f) :=
        Ideal.height_le_ringKrullDim_of_ne_top hprime.ne_top'
    _ ≤ ringKrullDim (MvPolynomial (Fin 1) K) :=
        ringKrullDim_le_of_isStandardEtale
    _ ≤ 1 := hmv

end Work.CurveFacts.KrullDim
