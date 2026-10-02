import Mathlib
import Submission.Work.Stems.Hur2b.NetGeo

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The six readings of the T-net, extended to the whole square

The `k`-th reading `netRead k : I² → ∂I³` of `NetLayout.lean` is affine on the cell
`cellRead k : I² → I²`; here we extend it to a map on the whole square by *clamping the cell
coordinates*, which is the natural continuous extension (`readExt`).

The cell coordinates of a point `y` relative to the `k`-th net cell are
`(clamp (8 y₀ - i), clamp (8 y₁ - j))` where `(i,j) = netCellIdx k`; on the cell itself this
recovers the inverse of `cellRead`, and off the cell it is the (clamped) projection onto the cell.
Consequently `readExt k` agrees with `netRead k` on the cell, and — the key point for the pinched
model — the six maps `readExt k` agree with each other on every point of `∂D`, so that they glue
to a single continuous map `∂D → ∂I³`.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2b

open Work.Stems.Cubical Work.Stems.Hur2

noncomputable section

/-- The cell coordinates of a point relative to the `k`-th net cell (clamped). -/
def cellCoord (k : Fin 6) (y : IC 2) : IC 2 :=
  pair2 (clamp (8 * (y 0 : ℝ) - ((netCellIdx k).1 : ℝ)))
        (clamp (8 * (y 1 : ℝ) - ((netCellIdx k).2 : ℝ)))

/-- The `k`-th reading, extended to the whole square by clamping the cell coordinates. -/
def readExt (k : Fin 6) (y : IC 2) : Bdy3 := netRead k (cellCoord k y)

theorem continuous_cellCoord (k : Fin 6) : Continuous (cellCoord k) := by
  refine continuous_pair2 ?_ ?_
  · exact continuous_clamp.comp (by fun_prop)
  · exact continuous_clamp.comp (by fun_prop)

theorem continuous_readExt (k : Fin 6) : Continuous (readExt k) :=
  (netRead k).continuous.comp (continuous_cellCoord k)

@[simp] theorem cellCoord_coe (k : Fin 6) (y : IC 2) (i : Fin 2) :
    ((cellCoord k y i : unitInterval) : ℝ) =
      clamp (8 * (y i : ℝ) - (((if i = 0 then (netCellIdx k).1 else (netCellIdx k).2) : ℕ) : ℝ)) := by
  fin_cases i <;> simp [cellCoord, pair2_zero, pair2_one]

/-- The walk value at a point of the net region: the reading of any cell containing it. -/
noncomputable def walkVal (y : IC 2) (hy : y ∈ NetRegion) : Bdy3 :=
  readExt (Classical.choose (Set.mem_iUnion.mp hy)) y

theorem walkVal_eq (y : IC 2) (hy : y ∈ NetRegion) {k : Fin 6} (hk : y ∈ netCell k)
    (hagree : ∀ y : IC 2, ∀ k l : Fin 6, y ∈ netCell k → y ∈ netCell l →
      readExt k y = readExt l y) :
    walkVal y hy = readExt k y := by
  unfold walkVal
  exact hagree y _ k (Classical.choose_spec (Set.mem_iUnion.mp hy)) hk

end

end Work.Stems.Hur2b
