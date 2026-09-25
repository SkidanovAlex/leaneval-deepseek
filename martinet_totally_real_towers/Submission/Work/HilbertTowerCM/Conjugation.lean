import Mathlib
import Submission.Work.HilbertTowerCM.Defs
import Submission.Work.HilbertTowerCM.exists_isConj_of_isGalois
import Submission.Work.HilbertTowerCM.isCMField_of_isConj_of_central
import Submission.Work.HilbertTowerCM.isCMField_iff_exists_central_isConj

/-!
# `Work.HilbertTowerCM.Conjugation` -- the CM criterion for a Galois level

This module records the **correct form** of the classical fact "the Hilbert class field of a CM
field is CM", i.e. the criterion by which a level `L` of the unramified tower over the
imaginary quadratic field `Kc = ℚ(√-30030)` is proved to be CM.

## The criterion

Let `L/ℚ` be a Galois number field (the levels produced by
`Work.ClassFieldTower.MaximalUnramifiedProP.exists_unramifiedNumberField_rootDiscr_eq` are Galois
over the base `Kc`; for the CM criterion we need them Galois over `ℚ`, which holds e.g. for the
canonical Galois levels of `Kc_∅`).

* `isCMField_of_forall_isConj` (Mathlib, `NumberField.IsCMField.of_forall_isConj`): if a single
  `σ ∈ Gal(L/ℚ)` is the complex conjugation **at every** embedding, then `L` is CM.
* `isCMField_of_isAbelianGalois` (Mathlib): if `L/ℚ` is abelian and totally complex, then `L` is CM.
* `Work.HilbertTowerCM.isCMField_of_isConj_of_central` (delegated): if `σ ∈ Gal(L/ℚ)` is
  **central** and is the conjugation at **one** embedding, then it is the conjugation at every
  embedding, hence `L` is CM.  This is the generalisation of the abelian case that is actually
  used for towers: it says that the obstruction to `L` being CM is precisely the non-centrality
  of the lift of complex conjugation.
* `Work.HilbertTowerCM.exists_isConj_of_isGalois` (delegated): conversely, every embedding of a
  Galois `L/ℚ` has a conjugation element in `Gal(L/ℚ)`; so the hypothesis of centrality is the
  only extra input needed.

## What is *not* true (and why the endgame is conditional)

The naive statement "`L/Kc` abelian of `2`-power degree, unramified, `L/ℚ` Galois, `Kc` CM
⟹ `L` CM" is **false**.  A counterexample is `K = ℚ(√-39)`, `L =` its Hilbert class field: `L/K`
is unramified abelian of degree `4` (class group `ℤ/4`), `L/ℚ` is Galois (group `D₄`), `L` is
totally imaginary of degree `8` with maximal real subfield `ℚ(√13)` of degree `2`, so
`[L : L⁺] = 4 ≠ 2` and `L` is not CM.  In the same way the second level of the `2`-class field
tower of `ℚ(√-30)` has `[L : L⁺] = 4`, and the maximal real subfields of the levels of the tower
are the *real genus fields*, of degree `2^{rank₂ Cl(K)}`; see
`Work/HilbertTowerCM/Obstruction` and `Work/HilbertTowerCM/README.md`.
-/

open scoped NumberField
open NumberField

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

noncomputable section

namespace Work.HilbertTowerCM

/-! ## 1. The Mathlib criteria, in the form used for levels -/

/-- **A totally complex Galois field with a single global conjugation is CM**
(Mathlib's `NumberField.IsCMField.of_forall_isConj`). -/
theorem isCMField_of_forall_isConj (L : Type*) [Field L] [NumberField L]
    [NumberField.IsTotallyComplex L] [IsGalois ℚ L] (σ : L ≃ₐ[ℚ] L)
    (hσ : ∀ φ : L →+* ℂ, NumberField.ComplexEmbedding.IsConj φ σ) :
    NumberField.IsCMField L :=
  NumberField.IsCMField.of_forall_isConj L hσ

/-- **A totally complex abelian Galois field is CM**
(Mathlib's `NumberField.IsCMField.of_isAbelianGalois`). -/
theorem isCMField_of_isAbelianGalois (L : Type*) [Field L] [NumberField L]
    [NumberField.IsTotallyComplex L] [IsAbelianGalois ℚ L] : NumberField.IsCMField L :=
  NumberField.IsCMField.of_isAbelianGalois L

/-! ## 2. The criterion used for the levels over `Kc` -/

/-- **The centre of `Gal(L/ℚ)` decides CM-ness**: a central element which is the conjugation at
one embedding is the conjugation at every embedding, so `L` is CM.  For a level of the tower over
`Kc`, the candidate is the lift `τ` of the complex conjugation of `Kc`; the criterion says the
level is CM exactly when that lift can be chosen central. -/
theorem isCMField_of_central_lift (L : Type*) [Field L] [NumberField L]
    [NumberField.IsTotallyComplex L] [IsGalois ℚ L] (σ : L ≃ₐ[ℚ] L)
    (hc : ∀ ρ : L ≃ₐ[ℚ] L, σ * ρ = ρ * σ) (hσ : ∃ φ : L →+* ℂ, NumberField.ComplexEmbedding.IsConj φ σ) :
    NumberField.IsCMField L := by
  obtain ⟨φ, hφ⟩ := hσ
  exact isCMField_of_isConj_of_central L σ hc φ hφ

/-- **The conjugation element exists.**  For a Galois number field `L/ℚ`, every complex embedding
`φ` has its conjugate `star ∘ φ` induced by an element of `Gal(L/ℚ)`. -/
theorem exists_conj_of_isGalois (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]
    (φ : L →+* ℂ) : ∃ σ : L ≃ₐ[ℚ] L, NumberField.ComplexEmbedding.IsConj φ σ :=
  exists_isConj_of_isGalois L φ

/-- **The CM criterion is an equivalence**: a totally complex Galois number field is CM if and
only if some element which is central in `Gal(L/ℚ)` is the complex conjugation at some embedding.
(One direction is `Work.HilbertTowerCM.isCMField_of_isConj_of_central`; the other is the classical
fact that the complex conjugation of a Galois CM field is central in its Galois group.) -/
theorem isCMField_iff_central_isConj (L : Type*) [Field L] [NumberField L]
    [NumberField.IsTotallyComplex L] [IsGalois ℚ L] :
    NumberField.IsCMField L ↔
      ∃ σ : L ≃ₐ[ℚ] L, (∀ ρ : L ≃ₐ[ℚ] L, σ * ρ = ρ * σ) ∧
        ∃ φ : L →+* ℂ, NumberField.ComplexEmbedding.IsConj φ σ :=
  isCMField_iff_exists_central_isConj L

/-- **The CM criterion for a level of the tower over `Kc`.**  If a level `L` of the unramified
tower over `Kc` is Galois over `ℚ` (e.g. it is the compositum of its `ℚ`-conjugates inside
`Kc_∅`), then a **central** element of `Gal(L/ℚ)` which is the complex conjugation at one
embedding makes `L` CM, hence a witness for `Work.CMRealSubfield.CMWall` through
`Work.HilbertTowerCM.cmWall_of_cmLevelWall`.

Note the hypothesis: centrality, i.e. the lift of the conjugation of `Kc` is *central* in
`Gal(L/ℚ)`.  This is the extra structural input the endgame needs; it holds for the levels
abelian over `Kc` of exponent `2` (where complex conjugation inverts classes, hence acts
trivially), and fails for the levels whose Galois group over `Kc` is not of exponent `2`. -/
theorem isCMField_of_central_lift_level (L : UnramifiedLevel ClassFieldTower.Kc)
    [IsGalois ℚ L.L] (σ : L.L ≃ₐ[ℚ] L.L)
    (hc : ∀ ρ : L.L ≃ₐ[ℚ] L.L, σ * ρ = ρ * σ)
    (hσ : ∃ φ : L.L →+* ℂ, NumberField.ComplexEmbedding.IsConj φ σ) :
    IsCMField L.L := by
  haveI : IsTotallyComplex ClassFieldTower.Kc := ClassFieldTower.isTotallyComplex
  haveI : IsTotallyComplex L.L := L.isTotallyComplex
  exact isCMField_of_central_lift L.L σ hc hσ

/-- **The abelian levels are CM.**  A level of the tower over `Kc` which is abelian over `ℚ` is
CM.  These are the levels inside the genus field of `Kc` (of degree `2^6 = 64` over `ℚ`), so this
supplies only *bounded* CM levels: the deeper levels are not abelian over `ℚ`. -/
theorem isCMField_of_isAbelianGalois_level (L : UnramifiedLevel ClassFieldTower.Kc)
    [IsAbelianGalois ℚ L.L] : IsCMField L.L := by
  haveI : IsTotallyComplex ClassFieldTower.Kc := ClassFieldTower.isTotallyComplex
  haveI : IsTotallyComplex L.L := L.isTotallyComplex
  exact NumberField.IsCMField.of_isAbelianGalois L.L

end Work.HilbertTowerCM
