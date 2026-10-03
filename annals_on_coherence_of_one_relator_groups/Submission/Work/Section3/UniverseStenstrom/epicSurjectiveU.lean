/-
# Epimorphisms out of a von Neumann regular ring are surjective (universe-general)

The classical theorem of Stenström (*Rings of quotients*, XI.1.4) and Gardner
(*Epimorphisms of regular rings*, Comment. Math. Univ. Carolinae **16** (1975), Theorem 1.6):
an epic ring homomorphism `f : R →+* S` whose source `R` is von Neumann regular is surjective.

The existing files `Submission.Work.ORHughesFree.Section3.surjective_of_isEpic_vnRegular` and
`Submission.Work.ORHughesFree.Epic.surjective_of_isEpic_of_vonNeumannRegular` prove this at
universe `0`.  The `Section3` development needs it for rings in an arbitrary fixed universe `u`
(the diagonal `∗`-regular closure of the uniqueness theorem lives in `U₁ × U₂` with `Uᵢ : Type u`),
so here we assemble the universe-general version from the three ingredients, all of which are
proved at `Type u` in the sibling files of this directory:

* `Work.Section3.UniverseStenstrom.tmul_eq_of_isEpic` — Silver's step applied to `1 ⊗ 1` in the
  balanced tensor product `S ⊗[R] S` (`silverStepU.lean`);
* `Work.Section3.UniverseStenstrom.mazetPresentationU` — Mazet's presentation of an arbitrary
  element of `S` (`mazetPresentationU.lean`);
* `Work.Section3.UniverseStenstrom.exists_preimage_of_matrix_eq` — the von Neumann regular step
  (`matrixStepU.lean`).
-/
import Mathlib
import Submission.Work.Section3.UniverseStenstrom.mazetPresentationU
import Submission.Work.Section3.UniverseStenstrom.silverStepU
import Submission.Work.Section3.UniverseStenstrom.matrixStepU

set_option autoImplicit false

universe u

namespace Work.Section3.UniverseStenstrom

open Work.ORHughesFree

/-- **Stenström XI.1.4 / Gardner, universe-general form.**  An epic ring homomorphism out of a
von Neumann regular ring is surjective. -/
theorem surjective_of_isEpic_vnRegularU {R S : Type u} [Ring R] [Ring S]
    [VonNeumannRegularRing R] (f : R →+* S) (hf : IsEpic f) : Function.Surjective f := by
  intro d
  obtain ⟨n, X, P, Y, hX, hY, hd⟩ := mazetPresentationU f (tmul_eq_of_isEpic f hf) d
  obtain ⟨r, hr⟩ := exists_preimage_of_matrix_eq f X P Y hX hY
  exact ⟨r, hr.trans hd.symm⟩

end Work.Section3.UniverseStenstrom
