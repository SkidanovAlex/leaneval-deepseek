import Mathlib
import Submission.Work.RatHurewicz.Excision
import Submission.Work.RatHurewicz.ExcisionSetup
import Submission.Work.RatHurewicz.pair_les
import Submission.Work.RatHurewicz.homotopyFibreMap_exists
import Submission.Work.RatHurewicz.excisionRelPiVanishing

namespace Work.RatHurewicz

noncomputable section

open scoped Topology unitInterval

variable {X : Type} [TopologicalSpace X] {B C : Set X}

/-!
## The three ingredients of the proof

The proof of `Work.RatHurewicz.HomotopyExcision` carried out below is the classical one (Puppe's
elementary proof of the Blakers–Massey excision theorem, tom Dieck, *Algebraic Topology*, §6.7 and
§6.9).  It is split into two statements, the first of which is delegated:

1. `excisionRelPiVanishing` — the crux, delegated below: given the hypotheses of the theorem at
   `x₀`, the comparison map
   `excisionComparison B C x₀ : F_B → F` of `Submission/Work/RatHurewicz/ExcisionSetup.lean`
   induces an isomorphism on `π_k` for `k ≤ p+q`.  This is Puppe's argument: subdivision of the
   cube, the preparation theorem (tom Dieck 6.9.2, using 6.9.1), the dimension count of (6.9.3) and
   the transfer to the fibres (6.7.7).
2. The final step — the composition with the basepoint transport `homotopyGroupCast`, which is a
   `MulEquiv` and hence bijective — is done here.

The crux `excisionRelPiVanishing` is proved in the module
`Submission/Work/RatHurewicz/excisionRelPiVanishing.lean` (imported here).
-/

/-- **Homotopy excision (Blakers–Massey) for open triads.**  The proposition
`Work.RatHurewicz.HomotopyExcision` (`Submission/Work/RatHurewicz/Excision.lean`) states: for an
open cover `X = B ∪ C` (`hBC`, `hB`, `hC`) with `x₀ ∈ B ∩ C`, if the relative groups of `(B, B∩C)`
vanish up to `p` and those of `(C, B∩C)` up to `q` in the `RelHomotopyGroup` indexing
(`RelHomotopyGroup i a₀ n` is the classical relative group `π_{n+1}` of the pair, realised as `π_n`
of the homotopy fibre of the inclusion), then the *comparison map*
`Work.RatHurewicz.excisionMap B C x₀ n` — the map induced on homotopy groups by the canonical map of
homotopy fibres of the square of inclusions (`Work.RatHurewicz.homotopyFibreMap`, transported by
`Work.StemsB.πmap`) — is bijective for `n + 1 ≤ p + q`, i.e. in the classical degrees
`j ≤ p + q + 1 = m_B + m_C - 1`.  This is the Blakers–Massey result for a triad (tom Dieck,
*Algebraic Topology*, §6.9; Hatcher 4.23 for CW triads), stated with open subsets.

Note the two traps, both avoided by the statement and documented in the file together with
counterexamples: the cover hypothesis `B ∪ C = X` is essential, and the range is `n + 1 ≤ p + q`
and *not* `p + q + 1` (the isomorphism only holds up to `m_B + m_C - 1` in classical degrees; there
is no vanishing consequence in the last degree). -/
theorem homotopyExcision : Work.RatHurewicz.HomotopyExcision := by
  intro X _ B C hBC hB hC x₀ p q hBvan hCvan n hn
  have hcrux := excisionRelPiVanishing hB hC hBC x₀ p q hBvan hCvan n (by omega)
  exact (Work.StemsB.homotopyGroupCast
      (homotopyFibreMap_basepoint (interInclLeft B C) (setIncl C) (setIncl B)
        (interInclRight B C) (excision_square B C) x₀) n).bijective.comp hcrux

end

end Work.RatHurewicz
