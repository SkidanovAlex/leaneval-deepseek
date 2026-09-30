import Mathlib
import Submission.Work.RatHurewicz.AttachCells
import Submission.Work.RatHurewicz.attachCells_relPi_subsingleton
import Submission.Work.RatHurewicz.LESConsequences

/-!
# Attaching cells does not change `π_≤ n`

Area **RATHUREWICZ**, C0/K1 of the Serre blueprint.  `attachCells n Y ι f` attaches `(n+2)`-cells to
`Y` along the maps `f i : S^{n+1} → Y`.  This module records the consequence of the compression fact
`Work.RatHurewicz.attachCells_relPi_subsingleton` that the Serre tower needs: the map induced by the
inclusion on `π_{≤ n}` is a bijection (on `π_{n+1}` it is only onto — `π_{n+2}` of the pair is free
on the cells), so the models `Y_{i+1}` of the blueprint have the same homotopy groups as `Y_i`
below the dimension of the attached cells.
-/

open scoped Topology

namespace Work.RatHurewicz

noncomputable section

/-- **Attaching cells of dimension `n+2` is an isomorphism on `π_{j+1}` for `j + 1 ≤ n`.**

`Work.StemsB.πmap f j` is the map induced by `f` on the `(j+1)`-st homotopy group, so the claim is
that `attachIncl n Y ι f` induces a bijection on `π_{j+1}` for `2 ≤ j` and `j + 1 ≤ n`.  Both halves come from
the exactness of the pair sequence (`Work.RatHurewicz.pair_les`) together with the vanishing of the
relative groups `RelHomotopyGroup (attachIncl n Y ι f) y₀ m` for `m ≤ n`
(`Work.RatHurewicz.attachCells_relPi_subsingleton`):
surjectivity of `πmap` needs the relative group at `j`, injectivity the one at `j + 1`
(`Work.RatHurewicz.piMap_surjective_of_relPi_subsingleton`,
`Work.RatHurewicz.piMap_injective_of_relPi_subsingleton`).  The hypotheses `2 ≤ j` and
`j + 1 ≤ n` keep the argument inside the range in which `pair_les` is stated (its bottom, `π_1` and
`π_2`, is a sequence of pointed sets); the applications of the tower start at `π_3`. -/
theorem attachCells_piMap_bijective (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphere n, Y)) (y₀ : Y) (j : ℕ) (hj2 : 2 ≤ j) (hj : j + 1 ≤ n) :
    Function.Bijective (Work.StemsB.πmap (attachIncl n Y ι f) j y₀) := by
  have hsub := attachCells_relPi_subsingleton n Y ι f y₀
  have hk : 1 ≤ j - 1 := by omega
  constructor
  · have h := piMap_injective_of_relPi_subsingleton (attachIncl n Y ι f) y₀ (j - 1)
      hk (by rw [show j - 1 + 2 = j + 1 from by omega]; exact hsub (j + 1) (by omega))
    rw [show j - 1 + 1 = j from by omega] at h
    exact h
  · have h := piMap_surjective_of_relPi_subsingleton (attachIncl n Y ι f) y₀ (j - 1)
      hk (by rw [show j - 1 + 1 = j from by omega]; exact hsub j (by omega))
    rw [show j - 1 + 1 = j from by omega] at h
    exact h

end

end Work.RatHurewicz
