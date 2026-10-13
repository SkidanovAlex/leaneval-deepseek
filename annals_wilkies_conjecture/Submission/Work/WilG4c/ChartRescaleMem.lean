/-
  WilG4c / ChartRescaleMem — BNZ's affine rescaling of the *value* of a family member.

  The statement: if the graph of `ψ` is an `Ω`-set of format `a` and degree `Dg`, then so is
  the graph of `(l,t) ↦ c + ψ l t / K`, with format `a + K₀` (`K₀` depending only on `p`, `n`)
  and degree `Dg + 2`.

  Construction (`m := p + (n+1)`, `N := m+1`; a point of `ℝ^N` is `(arguments, value)`):

  * `crSet m K c A` puts a fresh copy `u` of the *old* point in the trailing block of
    `ℝ^{N+N}` (it is `liftLast N A` intersected with the zero set of `crQ`), and
  * `crQ = 0` says, in one degree-`2` sum of squares, that the `m` argument coordinates of `u`
    and of the new point agree (`∀ i : Fin m, u i.castSucc = z i.castSucc`) and that the new
    value is affinely rescaled: `z (last m) = c + u (last m) / K`.

  The degree cost is exactly `+2` because the whole relation is a *single* `hyp` atom of degree
  `2` (`CrQ_totalDegree_le`), not an intersection of a degree-`2` and a degree-`1` hypersurface.
  The construction and its polynomial facts live in `Submission/Work/WilG4c/ChartRescaleDefs.lean`;
  the two halves of the argument were proved as standalone lemmas in parallel:

  * `Work.WilG4c.CrProjEq` (`CrProjEq.lean`) — the projection of `crSet` of a graph is the graph
    of the rescaled function (set theory / `Fin` bookkeeping),
  * `Work.WilG4c.CrSetMem` (`CrSetMem.lean`) — `Ω`-membership of that projection, via
    `liftLast_mem`, `SOMin.hyp`, an intersection and `projN_mem`.

  The proof below is the assembly: specialise `A` to the graph of
  `u ↦ ψ (params u) (vars u)` — which is *definitionally* `CG.famGraph ψ` — and replace the
  projection by the rescaled graph via `CrProjEq`.
-/
import Mathlib
import Submission.Work.WilG4c.Defs
import Submission.Work.WilG4c.ChartRescaleDefs
import Submission.Work.WilG4c.CrSetMem
import Submission.Work.WilG4c.CrProjEq

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign

theorem ChartRescaleMem (S : WilkiesDesign.SOMin) (p n : ℕ) :
    ∃ K₀ : ℕ, ∀ (K : ℕ) (c : ℝ) (a Dg : ℕ)
      (ψ : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ),
      WilkiesDesign.CG.famGraph ψ ∈ S.Ω a Dg (p + (n + 1) + 1) →
      WilkiesDesign.CG.famGraph (fun l t => c + ψ l t / (K : ℝ))
        ∈ S.Ω (a + K₀) (Dg + 2) (p + (n + 1) + 1) := by
  obtain ⟨K₀, hK⟩ := CrSetMem S (p + (n + 1))
  refine ⟨K₀, ?_⟩
  intro K c a Dg ψ h
  -- `CG.famGraph ψ` is `graphOf` of the family read as a function of the whole argument tuple.
  have hmem := hK K c a Dg
    (WilkiesDesign.graphOf (fun u : (Fin (p + (n + 1)) → ℝ) =>
      ψ (fun i : Fin p => u (Fin.castAdd (n + 1) i))
        (fun j : Fin (n + 1) => u (Fin.natAdd p j)))) h
  rw [CrProjEq (p + (n + 1)) K c (fun u : (Fin (p + (n + 1)) → ℝ) =>
      ψ (fun i : Fin p => u (Fin.castAdd (n + 1) i))
        (fun j : Fin (n + 1) => u (Fin.natAdd p j)))] at hmem
  exact hmem

end Work.WilG4c
