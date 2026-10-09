import Mathlib
import Submission.Work.SSGRoute.PTCore.H2_level_defs
import Submission.Work.SSGRoute.PTCore.H2_units_level_structure
import Submission.NK.NUV2.LC.natCard_groupCohomology_two_units_local_eq_finrank
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Finiteness and cardinality of the level cohomology of a `p`-adic field

The first hypothesis of `Work.SSGRoute.Nakayama.natCard_ptorsion_H2_units_eq_p` (the colimit
assembly for the `p`-torsion of `H²(G_F, F̄ˣ)`) is the *finiteness of the level cohomology*
`Finite (LevelH2 L)` for the finite Galois levels `L` of the base field.  Here it is discharged for
the workspace's local fields: `F = Q.adicCompletion K` the `Q`-adic completion of a number field
`K` at a finite prime `Q`, where the level cardinality is the classical `H²(Gal(L/F), Lˣ) ≅
ℤ/[L:F]` (`NK.NUV2.LC.natCard_groupCohomology_two_units_local_eq_finrank`, local reciprocity),
transported from Mathlib's `groupCohomology` to the cocycle model `LevelH2` by
`Work.SSGRoute.PTCore.h2LevelEquiv`.
-/

noncomputable section

open scoped Classical
open Work.AbsoluteKummer

namespace Work.SSGRoute.PTCore

/-- **The level cohomology of a `p`-adic level has the cardinality of the degree.**

For a number field `K`, a finite prime `Q`, and a finite Galois level
`L` of the `Q`-adic completion `F = Q.adicCompletion K`, `Nat.card (LevelH2 L) = [L : F]`. -/
theorem natCard_levelH2_eq_finrank {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (L : FiniteGaloisIntermediateField (Q.adicCompletion K)
      (AlgebraicClosure (Q.adicCompletion K))) :
    Nat.card (LevelH2 L) = Module.finrank (Q.adicCompletion K) ↥L := by
  have h1 : Nat.card (LevelH2 L)
      = Nat.card (↥(groupCohomology (Rep.ofAlgebraAutOnUnits (Q.adicCompletion K) ↥L) 2)) :=
    (Nat.card_congr (h2LevelEquiv (F := Q.adicCompletion K) L).toEquiv).symm
  rw [h1]
  exact NK.NUV2.LC.natCard_groupCohomology_two_units_local_eq_finrank (K := K) Q
    (F := Q.adicCompletion K) (E := ↥L)

/-- **Finiteness of the level cohomology of a `p`-adic level** — the first hypothesis of
`Work.SSGRoute.Nakayama.natCard_ptorsion_H2_units_eq_p` in the local setting. -/
theorem finite_levelH2 {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (L : FiniteGaloisIntermediateField (Q.adicCompletion K)
      (AlgebraicClosure (Q.adicCompletion K))) :
    Finite (LevelH2 L) :=
  Nat.finite_of_card_ne_zero (by
    rw [natCard_levelH2_eq_finrank Q L]
    exact (Module.finrank_pos (R := Q.adicCompletion K) (M := ↥L)).ne')

end Work.SSGRoute.PTCore
