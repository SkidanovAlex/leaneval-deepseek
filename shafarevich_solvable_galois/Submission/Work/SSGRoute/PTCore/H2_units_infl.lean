import Mathlib
import Submission.Work.SSGRoute.PTCore.H2_level_defs
import Submission.Work.SSGRoute.PTCore.H2_level_pieces
import Submission.Work.SSGRoute.PTCore.H2_level_mono
import Submission.Work.SSGRoute.PTCore.H2_level_cover_alt
import Submission.Work.SSGRoute.cocycles_iso_Z2
import Submission.Work.SSGRoute.groupCohomology_two_iso_cocycles
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level structure of `H²(G_F, F̄ˣ)`: the three properties of the inflation, assembled

The node `Work.SSGRoute.PTCore.H2_units_level_structure`
(`Submission/Work/SSGRoute/PTCore/H2_units_level_structure.lean`) is the statement that the level
inflations `psiTilde L : H²(Gal(L/F), Lˣ) → H²(G_F, F̄ˣ)` of the finite Galois levels `L` of `F`
are injective, nested, and cover `H²(G_F, F̄ˣ)`.  It is the missing ingredient of
`Work.SSGRoute.Nakayama.h2_muAdd_card` / `br_pTorsion`, the arithmetic core of the cyclotomic base
case of local Tate duality (Milne, *ADT*, I.1.8/I.2.3 at `r = 0`).

This file records the three properties, each with the name used by the consumers
(`psiTilde_injective`, `psiTilde_range_mono`, `psiTilde_range_cover`), and derives them from the
fleet's proofs of the same statements:

* `H2_level_injective` (in `H2_level_pieces.lean`, from Hilbert 90 at `Gal(F̄/L)` via
  `H2_level_hilbert90` and `psiTilde_eq_zero_iff`);
* `H2_level_mono` (in `H2_level_mono.lean`, via the tower of coefficient inclusions
  `inclLL`/`inclL_eq_inclLL` and `resL_eq_resLL_comp`);
* `H2_level_cover` / `H2_level_cover_alt` (in `H2_level_cover.lean`/`H2_level_cover_alt.lean`,
  from `AbsoluteKummer.Factorisation` and `exists_level_of_locallyConstant_isGalois`).

The assembly `H2_units_level_structure_of_pieces` below is the version of the node phrased with the
cocycle model `LevelH2 L` in place of Mathlib's `groupCohomology _ 2` (the two being identified by
`Work.SSGRoute.groupCohomology_two_iso_cocycles`).
-/

noncomputable section

open scoped Classical
open Work.AbsoluteKummer

namespace Work.SSGRoute.PTCore

variable {F : Type} [Field F] [IsGalois F (AlgebraicClosure F)]

/-- **Injectivity of the level inflation** `H²(Gal(L/F), Lˣ) → H²(G_F, F̄ˣ)`. -/
theorem psiTilde_injective (L : FiniteGaloisIntermediateField F (AlgebraicClosure F)) :
    Function.Injective (psiTilde L) :=
  H2_level_injective L (H2_level_hilbert90 L)

/-- **Nesting of the level inflations**: for `L ≤ L'` every class living on `L` also lives on
`L'`. -/
theorem psiTilde_range_mono
    (L L' : FiniteGaloisIntermediateField F (AlgebraicClosure F))
    (h : (L : IntermediateField F (AlgebraicClosure F)) ≤ L') :
    Set.range (psiTilde L) ⊆ Set.range (psiTilde L') :=
  H2_level_mono L L' h

/-- **Covering of `H²(G_F, F̄ˣ)` by its finite levels**: every class is the inflation of a class of
a finite Galois level. -/
theorem psiTilde_range_cover (x : Work.AbsoluteKummer.H2 (AbsGal F) (UnitsK F)) :
    ∃ L : FiniteGaloisIntermediateField F (AlgebraicClosure F), x ∈ Set.range (psiTilde L) := by
  obtain ⟨L, hL⟩ := H2_level_cover_alt x
  exact ⟨L, hL⟩

/-- **The node assembled from its three pieces.** -/
theorem H2_units_level_structure_of_pieces :
    ∃ φ : ∀ L : FiniteGaloisIntermediateField F (AlgebraicClosure F),
        LevelH2 L →+ Work.AbsoluteKummer.H2 (AbsGal F) (UnitsK F),
      (∀ L : FiniteGaloisIntermediateField F (AlgebraicClosure F), Function.Injective (φ L)) ∧
      (∀ (L L' : FiniteGaloisIntermediateField F (AlgebraicClosure F))
        (h : (L : IntermediateField F (AlgebraicClosure F)) ≤ L'),
        Set.range (φ L) ⊆ Set.range (φ L')) ∧
      (∀ x : Work.AbsoluteKummer.H2 (AbsGal F) (UnitsK F),
        ∃ L : FiniteGaloisIntermediateField F (AlgebraicClosure F), x ∈ Set.range (φ L)) :=
  ⟨psiTilde, psiTilde_injective, psiTilde_range_mono, psiTilde_range_cover⟩

end Work.SSGRoute.PTCore
