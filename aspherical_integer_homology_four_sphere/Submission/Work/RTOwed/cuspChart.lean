/-
# The cusp chart `mbarLow` of the hyperbolic piece (definition layer)

This file defines the UHS chart of the cusp neighbourhood of `M̄ = Work.FoldInst.Mbar` — the
*lower* branch of the collar chart of the cusp chapter, i.e. the point of `M̄` with given upper half
space coordinates `q` (below the ceiling `s = β(x)`).

## Conventions

The cube data are those of `Work.Cusp.Data` (`cubeCusp`, `cubeVertex`, `cubeCopy`, `cubeCorner`,
`cubeOfMod`, `cubeXToKlein`), used through the development `Submission/Work/RTOwed/cuspDev.lean`
(the ceiling map `mbarPt` of the area's `CuspCeilingData`).  The UHS *cube* coordinates of the data
are related to the UHS coordinates of the cusp chapter (`Work.Cusp`, whose ceiling is
`beta x = sqrt (9/4 - sum (off (x i))^2)`, centred at the nearest *integer*) by the translation
`h = (1/2, 1/2, 1/2)`: `x_cube = x_cusp + h`.

For the cube `a : Fin 48`, `chartMat a` (generated in `cuspChartData.lean`) is a positive integer
multiple of the inverse of the JSON matrix `mu_a`, so that

  `chartKlein a q = kleinOfHyp (chartMat a * hypOfUHS q)`

is the Möbius chart of the cube: its restriction to the ceiling is the affine map `cubeXToKlein a`,
and it maps the points of the cube below the ceiling into `Q̄`.

The map `mbarLow v` is then the chart of the cube `cubeOf v (x + h)` evaluated at the *reduced*
coordinate `redV v (x + h)` (whose fibre is the cusp lattice `Λ_v`), with the copy bit of the cube.
The definition is total, with a junk branch when the chart value is not in `Q̄` (the certificates
show that the branch is never taken on the region of interest).
-/
import Mathlib
import Submission.Work.RTOwed.cuspChartData
import Submission.Work.RTOwed.cuspDev
import Submission.Work.RTOwed.cuspChartWalls

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open scoped Matrix
open Set Topology Function

namespace Work.RTOwed

/-- The translation `h = (1/2, 1/2, 1/2)` between the cusp UHS coordinates (`Work.Cusp`) and the
cube UHS coordinates of `Work.Cusp.Data`. -/
def cuspH : CuspE3 := WithLp.toLp 2 fun _ : Fin 3 => (1 / 2 : ℝ)

/-- The horizontal part of a point of `E4`. -/
def xOf4 (q : CuspE4) : CuspE3 := WithLp.toLp 2 ![q 0, q 1, q 2]

/-- The cube coordinates of a point of `E4`: the first three coordinates shifted by `h`. -/
def uhsXj (q : CuspE4) : CuspE3 := xOf4 q + cuspH

/-- The point of `E4` with horizontal part `x` and height `s`. -/
def mkE4 (x : CuspE3) (s : ℝ) : CuspE4 := WithLp.toLp 2 ![x 0, x 1, x 2, s]

/-- **The Möbius chart of the cube `a`**: the Klein coordinates of the point of the hyperbolic
piece with cube coordinates `q`. -/
def chartKlein (a : Fin 48) (q : CuspE4) : CuspE4 :=
  Work.HypModel.kleinOfHyp
    ((chartMat a).map (Int.castRingHom ℝ) *ᵥ Work.HypModel.hypOfUHS q)

/-- **The reduced cube chart of the cube `a`**: evaluate the chart of `a` at the reduced
coordinate of `q` (with respect to the cube of `cubeOf v`). -/
def redChart (v : Fin 5) (a : Fin 48) (q : CuspE4) : CuspE4 :=
  chartKlein a (mkE4 (redV v (uhsXj q)) (q 3))

/-- **The point of `X̄` over the UHS coordinate `q`**: the copy bit of the cube containing `q` and
the Klein point of the reduced chart.  The conditional branch (junk point `(0, 0)`) is never taken
on the region of the collar charts (certificates). -/
def cuspLowPt (v : Fin 5) (q : CuspE4) : CuspXbar := by
  classical
  exact
    if h : redChart v (cubeOf v (uhsXj q)) q ∈ Work.FoldInst.Qbar then
      (cubeBit (cubeOf v (uhsXj q)),
        ⟨redChart v (cubeOf v (uhsXj q)) q, h⟩)
    else (0, ⟨0, zero_mem_Qbar⟩)

/-- **The cusp chart of the hyperbolic piece**: the point of `M̄` with UHS coordinates `q` (below
the ceiling `s = β (xOf q)`), in the `v`-th cusp. -/
def mbarLow (v : Fin 5) (q : CuspE4) : Work.FoldInst.Mbar :=
  Work.FoldInst.mk (cuspLowPt v q)

/-- The chart of the cube containing `q` (the cube of the reduced cube coordinate). -/
def chartCube (v : Fin 5) (q : CuspE4) : Fin 48 := cubeOf v (uhsXj q)

/-- The reduced cube coordinate of `q`. -/
def chartRed (v : Fin 5) (q : CuspE4) : CuspE3 := redV v (uhsXj q)

/-! ### The ceiling of a cube -/

/-- **The ceiling of the cube `a`**: the height of the truncation facet of the cube, i.e. the
hemisphere of radius `3/2` centred at the centre `cubeCorner a + (1/2,1/2,1/2)` of the cube (the
data of `rtdata/data/uhs_cusp_data.json`: `trunc_hemisphere`). -/
def ceilH (a : Fin 48) (x : CuspE3) : ℝ :=
  Real.sqrt (9 / 4 - ∑ i : Fin 3, (x i - ((Work.Cusp.cubeCorner a i : ℝ) + 1 / 2)) ^ 2)

/-- The lattice shift of the far side of a wall, as a vector of `CuspE3`. -/
def wallLamV (a : Fin 48) (i : Fin 3) (side : Fin 2) : CuspE3 :=
  WithLp.toLp 2 fun j : Fin 3 => (wallLam a i side j : ℝ)

/-- The group element of the identification of a wall, as an element of `Gg`. -/
def wallGam (a : Fin 48) (i : Fin 3) (side : Fin 2) : Work.FoldInst.Gg :=
  (wallGamK a i side, wallGamFlip a i side)

/- The ceiling of the cube in the cusp coordinates of `Work.Cusp`: `ceilH a (y + h)` is the
hemisphere centred at the nearest integer, i.e. `Work.Cusp.beta y`.  (Delegated as
`Submission/Work/RTOwed/ceilH_eq_beta`.) -/

end Work.RTOwed
