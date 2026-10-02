import Mathlib
import Submission.Work.Stems.Hur2b.NetData
import Submission.Work.Stems.Hur2b.NetLayout

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The geometry of the T-net: the radial exit point and the direction parameter

This file fixes the *geometric* vocabulary used to build the pinched model `ψ : I² → ∂I³` of
`Work.Stems.Hur2b.net_model`.

The centre `c = (7/16, 7/16)` of the middle cell `(3,3)` of the T-net lies in the interior of both
rectangles
* the belt `[1/4,3/4] × [3/8,1/2]` and the column `[3/8,1/2] × [1/4,5/8]`
whose union is the net region `D = ⋃ k, netCell k`.  Hence `D` is star-shaped with respect to `c`,
and for every direction `z ≠ 0` the ray `t ↦ c + t z` meets `D` in a segment `[0, s*]`; the *exit
point* `c + s* • z` lies on `∂D`.

Everything is written with *offsets* from the centre (the vector `z = y - c`), and all the formulas
use the *reciprocal* parameter `nu`: for a coordinate with interval `[l,u]` and `l < c < u`,
`nu l u c z = z / (u - c)` if `z ≥ 0` and `= z / (l - c)` if `z ≤ 0`,
so that `1 / nu` is the scale at which the coordinate `c + t z` reaches the bound, and no division
by zero ever occurs (the denominators are nonzero because `c` is interior to the interval).

The geometric facts (the ray really does exit at `rayOff`, `radialPoint` lands on `∂D`, etc.) are
stated in `NetExit.lean`.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2b

open Work.Stems.Cubical Work.Stems.Hur2

noncomputable section

/-! ## The centre, the two rectangles, and the net region -/

/-- The centre `(7/16, 7/16)` of the middle cell `(3,3)` of the T-net.  It lies in the interior of
both the belt `[1/4,3/4] × [3/8,1/2]` and the column `[3/8,1/2] × [1/4,5/8]`. -/
def netCentre : IC 2 := pair2 ⟨(7:ℝ)/16, by norm_num⟩ ⟨(7:ℝ)/16, by norm_num⟩

theorem netCentre_coe (i : Fin 2) : ((netCentre i : unitInterval) : ℝ) = 7/16 := by
  fin_cases i <;> simp [netCentre, pair2_zero, pair2_one]

/-- The offset of a point of the square from the centre. -/
def offOf (y : IC 2) : Fin 2 → ℝ := fun i => (y i : ℝ) - 7/16

/-- The point of the square with coordinates `clamp (7/16 + z i)`. -/
def ptOf (z : Fin 2 → ℝ) : IC 2 := pair2 (clamp (7/16 + z 0)) (clamp (7/16 + z 1))

@[simp] theorem ptOf_zero (z : Fin 2 → ℝ) : ptOf z 0 = clamp (7/16 + z 0) := by
  rw [ptOf, pair2_zero]

@[simp] theorem ptOf_one (z : Fin 2 → ℝ) : ptOf z 1 = clamp (7/16 + z 1) := by
  rw [ptOf, pair2_one]

theorem ptOf_coe (z : Fin 2 → ℝ) (i : Fin 2) :
    ((ptOf z i : unitInterval) : ℝ) = clamp (7/16 + z i) := by
  fin_cases i <;> simp

/-- The belt `[1/4,3/4] × [3/8,1/2]`, as a set of offsets from the centre. -/
def beltOff : Set (Fin 2 → ℝ) := {z | -3/16 ≤ z 0 ∧ z 0 ≤ 5/16 ∧ -1/16 ≤ z 1 ∧ z 1 ≤ 1/16}

/-- The column `[3/8,1/2] × [1/4,5/8]`, as a set of offsets from the centre. -/
def colOff : Set (Fin 2 → ℝ) := {z | -1/16 ≤ z 0 ∧ z 0 ≤ 1/16 ∧ -3/16 ≤ z 1 ∧ z 1 ≤ 3/16}

/-- The union of the two rectangles, as a set of offsets. -/
def netOff : Set (Fin 2 → ℝ) := beltOff ∪ colOff

/-- The net region `D = ⋃ k, netCell k` of the square. -/
def NetRegion : Set (IC 2) := ⋃ k : Fin 6, netCell k

/-- The inner boundary `∂D` of the net region. -/
def NetBdy : Set (IC 2) := NetRegion \ interior NetRegion

/-! ## The reciprocal ray parameter -/

/-- The reciprocal ray parameter.  For an interval `[l,u]` with `l < c < u`, `nu l u c z` is the
reciprocal of the scale at which the ray `t ↦ c + t z` reaches the bound (`u` if `z ≥ 0`, `l` if
`z ≤ 0`); it vanishes exactly when `z = 0` (vacuous constraint). -/
def nu (l u c z : ℝ) : ℝ := if 0 ≤ z then z / (u - c) else z / (l - c)

/-- The belt's first coordinate interval. -/
def nuB0 (z : ℝ) : ℝ := nu (1/4) (3/4) (7/16) z

/-- The belt's second coordinate interval. -/
def nuB1 (z : ℝ) : ℝ := nu (3/8) (1/2) (7/16) z

/-- The column's first coordinate interval. -/
def nuC0 (z : ℝ) : ℝ := nu (3/8) (1/2) (7/16) z

/-- The column's second coordinate interval. -/
def nuC1 (z : ℝ) : ℝ := nu (1/4) (5/8) (7/16) z

/-- The reciprocal exit scale of the belt. -/
def MBelt (z : Fin 2 → ℝ) : ℝ := max (nuB0 (z 0)) (nuB1 (z 1))

/-- The reciprocal exit scale of the column. -/
def MCol (z : Fin 2 → ℝ) : ℝ := max (nuC0 (z 0)) (nuC1 (z 1))

/-- The reciprocal exit scale of the net region. -/
def Mmin (z : Fin 2 → ℝ) : ℝ := min (MBelt z) (MCol z)

/-- The scale at which the ray `t ↦ c + t z` leaves the net region. -/
def exitScale (z : Fin 2 → ℝ) : ℝ := 1 / Mmin z

/-- The offset of the exit point of the ray `t ↦ c + t z` from the net region. -/
def rayOff (z : Fin 2 → ℝ) : Fin 2 → ℝ := fun i => exitScale z * z i

/-- The exit point of the ray in direction `z`, as a point of the square. -/
def radialPoint (z : Fin 2 → ℝ) : IC 2 := ptOf (rayOff z)

/-- The `ℓ∞` norm of a vector. -/
def sNorm (z : Fin 2 → ℝ) : ℝ := max |z 0| |z 1|

/-- The `ℓ∞` distance from the centre to the exit point. -/
def exitDist (z : Fin 2 → ℝ) : ℝ := sNorm (rayOff z)

/-! ## The direction parameter on the square circle `∂[-1,1]²` -/

/-- The parameter of a direction on the square circle `∂[-1,1]²`, starting at `(1,-1)` and running
counterclockwise (so `0 ↦ (1,-1)`, `1/4 ↦ (1,1)`, `1/2 ↦ (-1,1)`, `3/4 ↦ (-1,-1)`). -/
def dirPar (z : Fin 2 → ℝ) : ℝ :=
  if z 0 / sNorm z = 1 then (z 1 / sNorm z + 1) / 8
  else if z 1 / sNorm z = 1 then 1/4 + (1 - z 0 / sNorm z) / 8
  else if z 0 / sNorm z = -1 then 1/2 + (1 - z 1 / sNorm z) / 8
  else 3/4 + (z 0 / sNorm z + 1) / 8

/-- The inverse of `dirPar`: the point of the square circle with a given parameter. -/
def delta (t : ℝ) : Fin 2 → ℝ :=
  if t ≤ 1/4 then ![1, -1 + 8 * t]
  else if t ≤ 1/2 then ![3 - 8 * t, 1]
  else if t ≤ 3/4 then ![-1, 5 - 8 * t]
  else ![8 * t - 7, -1]

/-- The direction parameter, as an element of `I`. -/
def dirParU (z : Fin 2 → ℝ) : unitInterval := clamp (dirPar z)

/-- The radial parameter of the collar: `0` on `∂D` and `1` on `∂I²`. -/
def tau (y : IC 2) : ℝ := clamp (8 * (sNorm (offOf y) - exitDist (offOf y)))

/-- The radial parameter, as an element of `I`. -/
def tauU (y : IC 2) : unitInterval := clamp (tau y)

end

end Work.Stems.Hur2b
