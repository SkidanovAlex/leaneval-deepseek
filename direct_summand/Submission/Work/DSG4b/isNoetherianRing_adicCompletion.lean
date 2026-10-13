import Mathlib
import Submission.Work.DSG4b.Defs
import Submission.Work.DSG4b.AdicNoetherianGraded
import Submission.Work.DSG4b.isNoetherianRing_reesAlgebra_quotient_adicCompletion

namespace Work.DSG4b

universe u

/-- The adic completion of a Noetherian ring at a finitely generated ideal is Noetherian
(Stacks 05GH, EGA 0_I 7.3.6): the associated graded ring of the completion is a quotient of the
finitely generated `R/I`-algebra `gr_I R`, hence Noetherian, and a complete filtered ring with
Noetherian associated graded and finitely generated first piece is Noetherian (Nakayama/Artin–Rees
descent).

This is a gap in Mathlib (`Mathlib/RingTheory/AdicCompletion/` has flatness, locality, the residue
field and `spanFinrank` of the completion, but not Noetherianness), and it is needed in
`Work.DSG4b` to know that `IsRegularLocalRing` transfers to `m`-adic completions. -/
theorem isNoetherianRing_adicCompletion {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (hI : I.FG) : IsNoetherianRing (AdicCompletion I R) :=
  -- `R^ = AdicCompletion I R` is complete and separated for the `I R^`-adic topology, and its
  -- associated graded ring `gr_{I R^}(R^) = reesAlgebra (I R^) / I R^ · reesAlgebra (I R^)` is
  -- Noetherian; then the abstract graded descent applies.
  isNoetherianRing_of_isAdicComplete_graded (A := AdicCompletion I R)
    (Ideal.map (algebraMap R (AdicCompletion I R)) I)
    (AdicCompletion.isAdicComplete_self I hI)
    (isNoetherianRing_reesAlgebra_quotient_adicCompletion I hI)

end Work.DSG4b
