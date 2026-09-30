import Mathlib
import Submission.Work.RatHurewicz.AttachCells
import Submission.Work.RatHurewicz.RelHomotopy
import Submission.Work.RatHurewicz.attachCells_extension
import Submission.Work.RatHurewicz.attachCells_kill
import Submission.Work.RatHurewicz.homotopyExcision
import Submission.Work.RatHurewicz.compressRel_attachCells_range
import Submission.Work.RatHurewicz.subsingleton_relPi_of_compressRel_range

namespace Work.RatHurewicz

/-- **Attaching cells of dimension `n+2` does not change the homotopy groups in degrees `≤ n`.**

For a space `Y`, a family of attaching maps `f : ι → C(S^{n+1}, Y)` and a base point `y₀ : Y`, the
inclusion `attachIncl n Y ι f : Y → attachCells n Y ι f` induces an isomorphism on `π_j` for
`j ≤ n` (and a surjection at `j = n+1`; `π_{n+2}` of the pair is free on the cells and is genuinely
non-zero).  Equivalently the pair is `(n+1)`-connected: in this area's indexing
(`RelHomotopyGroup i a₀ j` is the classical `π_{j+1}` of the pair) this reads
`Subsingleton (RelHomotopyGroup (attachIncl n Y ι f) y₀ j)` for `j ≤ n`.

This is the "compression" fact of the Serre blueprint (`Submission/Work/Drive/SERRE_BLUEPRINT.md`
§2 C0 and ADDENDUM 1 (E), ADDENDUM 2 K1): it is the reason why the model `Y_{i+1}` obtained by
attaching `(i+2)`-cells to `Y_i` keeps `π_j` for `j ≤ i+1`, so that the Postnikov and
Eilenberg–MacLane models can be built by iterating the attachment.  The reason is dimensional: a
cube `(I^{j+1}, ∂I^{j+1}) → (Y', Y)` with `j + 1 ≤ n+1 < n+2` can be pushed off the interiors of
the `(n+2)`-cells, cell by cell, using the homotopy extension property together with the geometric
fact that a map of a cube of dimension `< n+2` into `D^{n+2}` whose boundary lies in `S^{n+1}` can
be homotoped, relative to the boundary, into `S^{n+1}`.  Tools available in this directory:
`Work.RatHurewicz.attachCells_extension` (the universal property, needed to extend maps out of the
attachment), `Work.RatHurewicz.attachIncl_comp_nullhomotopic` (which handles the `π_{n+1}` input)
and `Work.RatHurewicz.homotopyExcision` (Blakers–Massey, which gives the same conclusion through
the triad `(Y'; Y, cells)`: the relative groups of a cell attachment are those of the cells,
`π_j(Y', Y) ≅ ⊕ π_j(D^{n+2}, S^{n+1}) = 0` for `j ≤ n+1`, the vanishing for the disc pair
following from the long exact sequence of `(D^{n+2}, S^{n+1})`,
`Work.RatHurewicz.pair_les` and `Work.Stems.sphereConnectivity`). -/
theorem attachCells_relPi_subsingleton (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphere n, Y)) (y₀ : Y) :
    ∀ j : ℕ, j ≤ n →
      Subsingleton (RelHomotopyGroup (attachIncl n Y ι f) y₀ j) :=
  subsingleton_relPi_of_compressRel_range n Y ι f y₀
    (compressRel_attachCells_range n Y ι f)

end Work.RatHurewicz
