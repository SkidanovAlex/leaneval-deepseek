import Mathlib
import Submission.Work.Stems.RankOneClauses
import Submission.Work.Stems.rankOne_hurewicz_rank
import Submission.Work.Stems.rankOne_hurewicz_torsion
import Submission.Work.Stems.rankOne_bottomCell
import Submission.Work.Stems.rankOne_coverAcyclic
import Submission.Work.Stems.wangLowDegree
import Submission.Work.Stems.mappingTheoremOfHomotopyFibreAcyclic
import Submission.Work.StemsB.sphRatHomology
import Submission.Work.Serre.serreE3a

/-!
# The odd step of the rank-one `C2` interface, level by level

`Work.Stems.rankOne_oddStep` is the rank-one analogue of `Work.Stems.oddStepLocal`: the even clause
at level `j` (a rank-one range model of `K(A,2j)` has the rational homology of `ℂP^∞` rescaled by
`2j`, hence its loop space — a rank-one range model of `K(A,2j-1)`, `2j-1` odd — is a rational
sphere) gives the odd clause at level `2j+1`.

The proof is the `C2` odd step's: the cover `E = hofib(f)` of the bottom cell
`f : S^{2j+1} → X` is rationally acyclic up to `M - 2j` (`Work.Stems.rankOne_coverAcyclic`, proved
from the Wang sequence with the fibre `ΩX` supplied by the even clause, together with the low-degree
Wang degree `b = 2j+1` handled by `Work.Stems.wangLowDegree`), and the mapping theorem
(`Work.Stems.mappingTheoremOfHomotopyFibreAcyclic`) then identifies `H_i(S^{2j+1};ℚ)` with
`H_i(X;ℚ)` for `i < M - 2j`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Stems

noncomputable section

/-- **The odd step of the rank-one interface, level-local.**  The even clause at level `j` (at
every top) gives the odd clause at level `2j+1` (at every top). -/
theorem rankOne_oddStep (j : ℕ) (hj : 1 ≤ j)
    (heven : ∀ N' : ℕ, EvenClauseR j N') :
    ∀ N : ℕ, OddClauseR (2 * j + 1) N := by
  intro N X tX x₀ hab hvan hgen j' hj'1 hj'2
  by_cases hsmall : N ≤ 2 * (2 * j + 1)
  · exfalso; omega
  · have hN1 : 2 * j + 1 + 1 ≤ N := by omega
    letI : TopologicalSpace X := tX
    haveI : PathConnectedSpace X :=
      Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero x₀
        (hvan 0 (by omega) (by omega))
    haveI : Nonempty (Fin (2 * j + 1)) := ⟨⟨0, by omega⟩⟩
    haveI : Nonempty (Fin (2 * j)) := ⟨⟨0, by omega⟩⟩
    haveI : Nonempty (Fin (2 * j + 1 - 1)) := ⟨⟨0, by omega⟩⟩
    obtain ⟨s₀, f, hfib_conn, hfib_tors, hfib_conn_n⟩ :=
      rankOne_bottomCell (n := 2 * j + 1) (by omega) hN1 (X := X) (x₀ := x₀) hvan hgen
    have hacyc : Work.Serre.RatAcyclicBelow (Work.RatHurewicz.homotopyFibre f s₀) (N - 2 * j) :=
      rankOne_coverAcyclic (M := N) (X := X) j hj (x₀ := x₀) hvan hgen heven s₀ f
        hfib_conn hfib_tors hfib_conn_n
    have hmap := mappingTheoremOfHomotopyFibreAcyclic Work.Serre.serreE3a f s₀ (N - 2 * j) hacyc
    have hj'lt : j' < N - 2 * j := by omega
    obtain ⟨e⟩ := hmap j' hj'lt
    have hzero : IsZero (Work.Serre.ratH (TopCat.of (Work.Serre.Sph (2 * j + 1))) j') :=
      (Work.StemsB.sphRatHomology (2 * j + 1) (by omega)).2 j' (by omega) (by omega)
    exact IsZero.of_iso hzero e.symm

end

end Work.Stems
