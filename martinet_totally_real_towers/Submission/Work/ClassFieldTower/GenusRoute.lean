import Mathlib
import Submission.Work.ClassFieldTower.Defs
import Submission.Work.ClassFieldTower.Objects
import Submission.Work.ClassFieldTower.Main
import Submission.Work.ClassFieldTower.exists_fiveUnramifiedQuadratics_of_unramified_exponentTwo

/-!
# `Work.ClassFieldTower.GenusRoute` -- the genus-theory interface of the Golod--Shafarevich route

The arithmetic input of the unramified `2`-class-tower route splits into

* **genus theory** (elementary number theory, CFT-free): the existence of a finite unramified
  Galois extension `L/F` of degree `2^5` whose Galois group has exponent `2` (for an imaginary
  quadratic `F = ℚ(√D)`, `D` a product of six prime discriminants, one takes
  `L = ℚ(√d₁, …, √d₆)`, whose Galois group over `F` is `(ℤ/2)^5`), and
* **the Shafarevich--Koch deficiency bound** (class field theory): `G_∅` has a minimal
  presentation with `d` generators, `r` relators and `r ≤ d + 1`.

This module combines them into a single criterion.  The genus-theory half is entirely CFT-free:
`exists_fiveUnramifiedQuadratics_of_unramified_exponentTwo` turns such an `L` into a surjection
`G_∅ ↠ (𝔽₂)^5` (via the universal property of `F_∅` and Galois theory), and
`five_le_of_surjective_zmodTwo_five` turns that into `d ≥ 5`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ClassFieldTower

/-- **THE CFT-FREE GENUS-THEORY CRITERION.**

Let `F` be a number field, `M = F_∅` its maximal unramified pro-`2` extension, and suppose

* `hpres`/`hdef`: `G_∅` has a minimal presentation with `d` generators and `r` relators with
  `r ≤ d + 1` (the Shafarevich--Koch deficiency bound);
* `L`: a finite unramified Galois extension of `F` of degree `2^5` with `Gal(L/F)` of exponent
  `2` (the genus field of an imaginary quadratic field with six prime discriminant factors).

Then `G_∅` is infinite, i.e. `F` has an infinite Hilbert `2`-class field tower. -/
@[deprecated "SUPERSEDED: its hypothesis is unsatisfiable -- see Work.ClassFieldTower.not_infiniteHilbertTwoClassFieldTower in Vacuity.lean; use Work.ClassFieldTower.ProTwoTowerInput / ProTwoShafarevichKochInput and ProTwo.lean / ProTwoGenus.lean instead" (since := "2026-09-17")]
theorem infinite_galoisGroup_of_presentation_and_genusField {F : Type} [Field F] [NumberField F]
    (M : MaximalUnramifiedProP.{0} F 2) {d r : ℕ}
    (hpres : HasMinimalPresentation (galoisGroup M) d r) (hdef : r ≤ d + 1)
    (L : Type) [Field L] [NumberField L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (hunr : differentIdeal (𝓞 F) (𝓞 L) = ⊤)
    (hexp : ∀ σ : L ≃ₐ[F] L, σ ^ 2 = 1)
    (hcard : Nat.card (L ≃ₐ[F] L) = 2 ^ 5) : Infinite (galoisGroup M) :=
  infinite_galoisGroup_of_presentation_and_fiveQuadratics M hpres hdef
    (exists_fiveUnramifiedQuadratics_of_unramified_exponentTwo M L hunr hexp hcard)

/-- **THE CFT-FREE GENUS-THEORY CRITERION, imaginary quadratic form.**

For an imaginary quadratic field `F`, a genus field `L` as above and the Shafarevich--Koch
deficiency bound give an infinite Hilbert `2`-class field tower over `F`. -/
@[deprecated "SUPERSEDED: its hypothesis is unsatisfiable -- see Work.ClassFieldTower.not_infiniteHilbertTwoClassFieldTower in Vacuity.lean; use Work.ClassFieldTower.ProTwoTowerInput / ProTwoShafarevichKochInput and ProTwo.lean / ProTwoGenus.lean instead" (since := "2026-09-17")]
theorem infinite_galoisGroup_of_imaginaryQuadratic_and_genusField {F : Type} [Field F]
    [NumberField F] [NumberField.IsTotallyComplex F] (h2 : Module.finrank ℚ F = 2)
    (M : MaximalUnramifiedProP.{0} F 2) {d r : ℕ}
    (hpres : HasMinimalPresentation (galoisGroup M) d r) (hdef : r ≤ d + 1)
    (L : Type) [Field L] [NumberField L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (hunr : differentIdeal (𝓞 F) (𝓞 L) = ⊤)
    (hexp : ∀ σ : L ≃ₐ[F] L, σ ^ 2 = 1)
    (hcard : Nat.card (L ≃ₐ[F] L) = 2 ^ 5) : Infinite (galoisGroup M) :=
  infinite_galoisGroup_of_presentation_and_genusField M hpres hdef L hunr hexp hcard

/-- **The Shafarevich--Koch deficiency input, isolated.**

`G_∅` has a minimal presentation with `r ≤ d + 1` relators -- equivalently, its deficiency
`df = r - d` is at least `-1`, which for an imaginary quadratic `F` is the Shafarevich--Koch
bound `df ≤ d₂(O_F^×) = 1` read in reverse (`Work.ClassFieldTower.DeficiencyBoundInput` states
it against `d = rank₂ Cl(F)` specifically).  This is the ONLY class-field-theoretic input the
chapter needs beyond the existence of `F_∅`. -/
def HasMinimalPresentationWithFewRelators {F : Type} [Field F] [NumberField F]
    (M : MaximalUnramifiedProP.{0} F 2) : Prop :=
  ∃ (d r : ℕ), HasMinimalPresentation (galoisGroup M) d r ∧ r ≤ d + 1

/-- **THE CRUX OF THE CHAPTER, cleanly split.**

If the Shafarevich--Koch deficiency input holds for `G_∅` (`HasMinimalPresentationWithFewRelators`)
and `F` has a finite unramified Galois extension `L/F` of degree `2^5` with `Gal(L/F)` of exponent
`2` (the genus field), then `G_∅` is infinite: `F` has an infinite Hilbert `2`-class field tower.

The second hypothesis is pure genus theory (no class field theory); the first is the
Shafarevich--Koch relation bound. -/
@[deprecated "SUPERSEDED: its hypothesis is unsatisfiable -- see Work.ClassFieldTower.not_infiniteHilbertTwoClassFieldTower in Vacuity.lean; use Work.ClassFieldTower.ProTwoTowerInput / ProTwoShafarevichKochInput and ProTwo.lean / ProTwoGenus.lean instead" (since := "2026-09-17")]
theorem infinite_galoisGroup_of_fewRelators_and_genusField {F : Type} [Field F] [NumberField F]
    (M : MaximalUnramifiedProP.{0} F 2) (h : HasMinimalPresentationWithFewRelators M)
    (L : Type) [Field L] [NumberField L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (hunr : differentIdeal (𝓞 F) (𝓞 L) = ⊤)
    (hexp : ∀ σ : L ≃ₐ[F] L, σ ^ 2 = 1)
    (hcard : Nat.card (L ≃ₐ[F] L) = 2 ^ 5) : Infinite (galoisGroup M) := by
  obtain ⟨d, r, hpres, hdef⟩ := h
  exact infinite_galoisGroup_of_presentation_and_genusField M hpres hdef L hunr hexp hcard

end Work.ClassFieldTower
