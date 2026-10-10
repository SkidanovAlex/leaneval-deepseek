/-
This module is a local copy of the residue-field computation used by
`Submission/Work/MotA/resEquiv_iff_fractionRing.lean`, so that the `MotA` area does not depend on
the (dead-listed) `Work.CKLink` directories.  The statement and proof are unchanged: the residue
field of the point `⟨p⟩` of `Spec R` is the fraction field of `R ⧸ p`, compatibly with the
structure maps.
-/
import Mathlib
import Submission.Work.Motivic.Defs
import Submission.Work.CrauderKatz.BlowUp.lineResE

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false

namespace Work.MotA

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

/-- **The residue field of a prime of `Spec R` is the fraction field of the quotient.**
`κ(⟨p⟩) ≅ Frac (R ⧸ p)`, compatibly with the structure maps. -/
theorem residueField_fracEquiv (𝕜 : Type) [Field 𝕜] (R : Type) [CommRing R] [Algebra 𝕜 R]
    (p : Ideal R) (hp : p.IsPrime) :
    ∃ e : (Spec (CommRingCat.of R)).residueField (⟨p, hp⟩ : PrimeSpectrum R) ≃+*
        FractionRing (R ⧸ p),
      e.toRingHom.comp (resMap 𝕜 (Spec (CommRingCat.of R)) ⟨p, hp⟩) =
        (algebraMap R (FractionRing (R ⧸ p))).comp (algebraMap 𝕜 R) := by
  letI : p.IsPrime := hp
  let P : PrimeSpectrum R := ⟨p, hp⟩
  -- `κ(⟨p⟩) = p.ResidueField` is a fraction ring of `R ⧸ p`; the canonical map
  -- `R ⧸ p → κ(⟨p⟩)` is `algebraMap`.
  let eK : p.ResidueField ≃+* FractionRing (R ⧸ p) :=
    ((FractionRing.algEquiv (R ⧸ p) p.ResidueField).symm).toRingEquiv
  -- `Spec.residueFieldIso` identifies the residue field of the point of `Spec R` with
  -- the residue field of the underlying prime ideal.
  let iso := Scheme.Spec.residueFieldIso (CommRingCat.of R) P
  refine ⟨iso.commRingCatIsoToRingEquiv.trans eK, ?_⟩
  -- `iso.commRingCatIsoToRingEquiv` is inverse to `iso.inv.hom`.
  have h1 : ∀ x : P.asIdeal.ResidueField,
      iso.commRingCatIsoToRingEquiv (iso.inv.hom x) = x := by
    intro x
    show iso.hom.hom (iso.inv.hom x) = x
    exact Iso.inv_hom_id_apply iso x
  -- `eK` is the inverse of the `(R ⧸ p)`-algebra isomorphism `FractionRing.algEquiv`.
  have h2 : ∀ x : R ⧸ p,
      eK (algebraMap (R ⧸ p) p.ResidueField x) =
        algebraMap (R ⧸ p) (FractionRing (R ⧸ p)) x := by
    intro x
    exact AlgEquiv.commutes (FractionRing.algEquiv (R ⧸ p) p.ResidueField).symm x
  -- Chasing `𝕜 → R → R ⧸ p → κ(p) → Frac (R ⧸ p)` through the tower.
  have key : ∀ a : 𝕜, eK (algebraMap R p.ResidueField (algebraMap 𝕜 R a))
      = algebraMap 𝕜 (FractionRing (R ⧸ p)) a := by
    intro a
    rw [IsScalarTower.algebraMap_apply R (R ⧸ p) p.ResidueField (algebraMap 𝕜 R a)]
    rw [h2]
    rw [← IsScalarTower.algebraMap_apply 𝕜 R (R ⧸ p) a]
    exact (IsScalarTower.algebraMap_apply 𝕜 (R ⧸ p) (FractionRing (R ⧸ p)) a).symm
  -- Evaluate the compatibility identity on an element of `𝕜`.
  ext a
  rw [Work.CrauderKatz.BlowUp.resMap_spec_eq]
  simp only [RingHom.comp_apply]
  show eK (iso.commRingCatIsoToRingEquiv
    (iso.inv.hom (algebraMap R P.asIdeal.ResidueField (algebraMap 𝕜 R a)))) = _
  rw [h1, key]
  rw [IsScalarTower.algebraMap_apply 𝕜 R (FractionRing (R ⧸ p)) a]

end Work.MotA
