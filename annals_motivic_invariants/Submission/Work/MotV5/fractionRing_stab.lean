import Mathlib
import Submission.Work.MotA.quotient_map_rename
import Submission.Work.CrauderKatz.BlowUp.fractionRing_algEquiv_of_algEquiv

set_option linter.unusedVariables false -- v435-speed

set_option linter.style.haveILetI false

namespace Work.MotV5

/-- **Fraction fields of `MvPolynomial` do not see the base change to the fraction field.**

For a domain `R` that is a `𝕜`-algebra and any index type `σ`, the fraction field of the polynomial
ring over `R` agrees with that of the polynomial ring over the fraction field of `R`:

`FractionRing R[σ] ≃ₐ[𝕜] FractionRing (MvPolynomial σ (FractionRing R))`.

Both sides are localizations of `MvPolynomial σ R`: the left one at `nonZeroDivisors R[σ]`, the
right one — because `MvPolynomial σ (FractionRing R)` is the localization of `MvPolynomial σ R` at
`(nonZeroDivisors R).map MvPolynomial.C`, a submonoid of `nonZeroDivisors R[σ]` — also at
`nonZeroDivisors R[σ]` (`IsFractionRing.isFractionRing_of_isLocalization`), and the comparison of
the two fraction rings goes through `IsFractionRing.algEquivOfAlgEquiv`.

This is the statement of the sibling file
`Submission/Work/MotV5/fractionRing_mvPoly_fractionRing.lean`, reproved here so as not to depend
on it (its `Algebra (MvPolynomial σ (FractionRing R)) (FractionRing (MvPolynomial σ R))` structure
is constructed explicitly, which is the technical content). -/
theorem fractionRing_mvPoly_base {𝕜 R : Type*} [Field 𝕜] [CommRing R] [IsDomain R] [Algebra 𝕜 R]
    (σ : Type*) :
    Nonempty (FractionRing (MvPolynomial σ (FractionRing R)) ≃ₐ[𝕜]
      FractionRing (MvPolynomial σ R)) := by
  classical
  -- `MvPolynomial σ (FractionRing R)` is the localization of `MvPolynomial σ R` at
  -- `(nonZeroDivisors R).map MvPolynomial.C`.
  letI : Algebra (MvPolynomial σ R) (MvPolynomial σ (FractionRing R)) :=
    MvPolynomial.algebraMvPolynomial
  haveI hloc : IsLocalization ((nonZeroDivisors R).map (MvPolynomial.C (σ := σ)))
      (MvPolynomial σ (FractionRing R)) :=
    MvPolynomial.isLocalization (σ := σ) (nonZeroDivisors R) (FractionRing R)
  -- The localizing submonoid consists of nonzerodivisors (both rings are domains).
  have hM : (nonZeroDivisors R).map (MvPolynomial.C (σ := σ)) ≤
      nonZeroDivisors (MvPolynomial σ R) := by
    intro y hy
    rw [Submonoid.mem_map] at hy
    obtain ⟨r, hr, rfl⟩ := hy
    rw [mem_nonZeroDivisors_iff_ne_zero]
    exact MvPolynomial.C_eq_zero.not.mpr (mem_nonZeroDivisors_iff_ne_zero.mp hr)
  -- Its image in `FractionRing (MvPolynomial σ R)` consists of units.
  have hg : ∀ y : ((nonZeroDivisors R).map (MvPolynomial.C (σ := σ))),
      IsUnit (algebraMap (MvPolynomial σ R) (FractionRing (MvPolynomial σ R)) y) := by
    intro y
    rw [isUnit_iff_ne_zero]
    exact fun h => (mem_nonZeroDivisors_iff_ne_zero.mp (hM y.property))
      (IsFractionRing.injective (MvPolynomial σ R) (FractionRing (MvPolynomial σ R))
        (by simpa using h))
  -- The `MvPolynomial σ (FractionRing R)`-algebra structure on `FractionRing (MvPolynomial σ R)`.
  letI : Algebra (MvPolynomial σ (FractionRing R)) (FractionRing (MvPolynomial σ R)) :=
    (IsLocalization.lift (M := (nonZeroDivisors R).map (MvPolynomial.C (σ := σ))) (g :=
      algebraMap (MvPolynomial σ R) (FractionRing (MvPolynomial σ R))) hg).toAlgebra
  haveI hST : IsScalarTower (MvPolynomial σ R) (MvPolynomial σ (FractionRing R))
      (FractionRing (MvPolynomial σ R)) :=
    IsScalarTower.of_algebraMap_eq (fun x =>
      (IsLocalization.lift_eq (M := (nonZeroDivisors R).map (MvPolynomial.C (σ := σ))) hg x).symm)
  -- Compatibility with the `𝕜`-algebra structures.
  haveI hSTkAB : IsScalarTower 𝕜 (MvPolynomial σ R) (MvPolynomial σ (FractionRing R)) := by
    apply IsScalarTower.of_algebraMap_eq
    intro c
    rw [MvPolynomial.algebraMap_def,
        IsScalarTower.algebraMap_apply 𝕜 R (MvPolynomial σ R) c,
        MvPolynomial.algebraMap_eq R σ,
        MvPolynomial.map_C,
        ← IsScalarTower.algebraMap_apply 𝕜 R (FractionRing R) c,
        IsScalarTower.algebraMap_apply 𝕜 (FractionRing R) (MvPolynomial σ (FractionRing R)) c,
        MvPolynomial.algebraMap_eq (FractionRing R) σ]
  haveI hSTkBK : IsScalarTower 𝕜 (MvPolynomial σ (FractionRing R))
      (FractionRing (MvPolynomial σ R)) := by
    apply IsScalarTower.of_algebraMap_eq
    intro c
    rw [IsScalarTower.algebraMap_apply 𝕜 (MvPolynomial σ R) (MvPolynomial σ (FractionRing R)) c,
      ← IsScalarTower.algebraMap_apply (MvPolynomial σ R) (MvPolynomial σ (FractionRing R))
        (FractionRing (MvPolynomial σ R)),
      IsScalarTower.algebraMap_apply 𝕜 (MvPolynomial σ R) (FractionRing (MvPolynomial σ R)) c]
  -- Hence `FractionRing (MvPolynomial σ R)` is also a fraction ring of `MvPolynomial σ (FractionRing R)`.
  haveI hfr : IsFractionRing (MvPolynomial σ (FractionRing R))
      (FractionRing (MvPolynomial σ R)) :=
    IsFractionRing.isFractionRing_of_isLocalization ((nonZeroDivisors R).map (MvPolynomial.C (σ := σ)))
      (MvPolynomial σ (FractionRing R)) (FractionRing (MvPolynomial σ R)) hM
  exact ⟨IsFractionRing.algEquivOfAlgEquiv
    (AlgEquiv.refl : MvPolynomial σ (FractionRing R) ≃ₐ[𝕜] MvPolynomial σ (FractionRing R))⟩

/-- **Residue field under stabilisation.**  Let `p` be a prime ideal of `𝕜[x₀,…,x₃]` (`Fin 4`), and
let `p.map (Fin.castAdd k)` be its extension to `𝕜[x₀,…,x_{3+k}]`.  Then the fraction field of the
quotient by the extension is the fraction field of the polynomial ring in the `k` new variables over
the *fraction field* of `𝕜[Fin 4] ⧸ p`.  This is the residue-field half of the stabilisation census
`Work.MotA.divCount_rename` (node `A3`): the class of a stabilised point is the class of the original
point with `k` extra rational variables adjoined.

Route.  `Work.MotA.quotient_map_rename 𝕜 4 k p` gives
`𝕜[Fin (4+k)] ⧸ p.map (Fin.castAdd k) ≃ₐ[𝕜] MvPolynomial (Fin k) (𝕜[Fin 4] ⧸ p)`; transport along it
with `Work.CrauderKatz.BlowUp.fractionRing_algEquiv_of_algEquiv` (or
`IsFractionRing.algEquivOfAlgEquiv` and `MvPolynomial.mapAlgEquiv`), and then use the statement of
`Submission/Work/MotV5/fractionRing_mvPoly_fractionRing.lean` to replace
`FractionRing (MvPolynomial (Fin k) (𝕜[Fin 4] ⧸ p))` by
`FractionRing (MvPolynomial (Fin k) (FractionRing (𝕜[Fin 4] ⧸ p)))`; reprove that special case
locally if you prefer not to depend on it. -/
theorem fractionRing_stab (𝕜 : Type) [Field 𝕜] (k : ℕ)
    (p : Ideal (MvPolynomial (Fin 4) 𝕜)) [p.IsPrime] :
    Nonempty (FractionRing (MvPolynomial (Fin (4 + k)) 𝕜 ⧸
        p.map (MvPolynomial.rename (Fin.castAdd k))) ≃ₐ[𝕜]
      FractionRing (MvPolynomial (Fin k) (FractionRing (MvPolynomial (Fin 4) 𝕜 ⧸ p)))) := by
  -- The quotient by the extended ideal is the polynomial ring in `k` variables over `𝕜[Fin 4] ⧸ p`.
  obtain ⟨e⟩ := Work.MotA.quotient_map_rename 𝕜 4 k p
  -- Replace the base by its fraction field.
  obtain ⟨e2⟩ := fractionRing_mvPoly_base (𝕜 := 𝕜)
    (R := MvPolynomial (Fin 4) 𝕜 ⧸ p) (Fin k)
  -- Transport along the quotient identification, then along the base change to the fraction field.
  exact ⟨(IsFractionRing.algEquivOfAlgEquiv (R := 𝕜)
      (A := MvPolynomial (Fin (4 + k)) 𝕜 ⧸ p.map (MvPolynomial.rename (Fin.castAdd k)))
      (B := MvPolynomial (Fin k) (MvPolynomial (Fin 4) 𝕜 ⧸ p)) e).trans e2.symm⟩

end Work.MotV5
