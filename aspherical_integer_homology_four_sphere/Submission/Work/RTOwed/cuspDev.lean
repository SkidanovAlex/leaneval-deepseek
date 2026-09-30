/-
# The cusp development of `M̄`: definitions

This file fixes the *definitions* of the cusp development of the concrete truncated 24-cell
`Work.FoldInst.Mbar`, i.e. the data of the ceiling maps `mbarPt v : E3 → M̄` whose range is the
`v`-th truncation torus (`cuspCeilingData_exists`).

Conventions (all read off the validated data `rtdata/data/uhs_cusp_data.json`, generated into
`Work.Cusp.Data`):

* `Work.Cusp.cubeCusp a` is the cusp (`Fin 5`) of the cube `a : Fin 48`;
* `Work.Cusp.cubeCopy a` is the copy of `Q̄` (`true` = `Q̄₀`), `Work.Cusp.cubeVertex a` the truncated
  ideal vertex (RT's 1-based numbering), `Work.Cusp.cubeCorner a` the lower corner of the unit cube
  in UHS coordinates;
* `Work.Cusp.cubeXToKlein a` / `Work.Cusp.cubeXToKleinb a`: the affine map
  `x ↦ y = A x + b` from the cube coordinates to the Klein coordinates of the truncation facet;
* `Work.Cusp.latMod v` are the elementary divisors of the cusp lattice `Λ_v`, so that
  `Λ_v = diag(latMod v) · ℤ³` in cube coordinates;
* `Work.Cusp.cubeOfMod v p` is the lookup table of the cube of cusp `v` whose corner is congruent
  to `p` modulo `latMod v`.

The cusp development is then

  `mbarPt v x = mk ⟨copy, kleinPt a (redV v x)⟩`,  `a = cubeOf v x`,

where `cubeOf v x = cubeOfMod v ⌊x⌋` (only the *residue class* of `⌊x⌋` matters) and
`redV v x = x − ⌊x⌋ + cubeCorner a` is the representative of `x` in the unit cube of `a`.  This is
`Λ_v`-periodic by construction.
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.FoldInst.Quotient

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function
open scoped BigOperators

namespace Work.RTOwed

/-- The UHS cube coordinate space. -/
abbrev CuspE3 := Work.Cusp.E3

/-- The Klein coordinate space. -/
abbrev CuspE4 := Work.Cusp.E4

/-- The two copies of `Q̄`. -/
abbrev CuspXbar := Work.FoldInst.Xbar

/-- The floor vector of a point of `E3`. -/
def floorV (x : CuspE3) : Fin 3 → ℤ := fun i => ⌊x i⌋

/-- The cube of cusp `v` carrying the residue class of `⌊x⌋`. -/
def cubeOf (v : Fin 5) (x : CuspE3) : Fin 48 := Work.Cusp.cubeOfMod v (floorV x)

/-- **The representative of `x` in the unit cube of its cube**: `x − ⌊x⌋ + cubeCorner a`. -/
def redV (v : Fin 5) (x : CuspE3) : CuspE3 :=
  WithLp.toLp 2 fun i : Fin 3 =>
    x i - (⌊x i⌋ : ℝ) + (Work.Cusp.cubeCorner (cubeOf v x) i : ℝ)

/-- **The affine map of the cube `a`**: the Klein coordinates of the point of the truncation facet
with cube coordinates `x`. -/
def kleinPt (a : Fin 48) (x : CuspE3) : CuspE4 :=
  WithLp.toLp 2 fun i : Fin 4 =>
    (∑ j : Fin 3, ((Work.Cusp.cubeXToKlein a) i j : ℝ) * x j) +
      ((Work.Cusp.cubeXToKleinb a i) : ℝ)

/-- The inverse affine map: the cube coordinates of the Klein point `y`. -/
def kleinToX (a : Fin 48) (y : CuspE4) : CuspE3 :=
  WithLp.toLp 2 fun i : Fin 3 =>
    (∑ j : Fin 4, ((Work.Cusp.cubeKleinToX a) i j : ℝ) * y j) +
      ((Work.Cusp.cubeKleinToXb a i) : ℝ)

/-- The closed unit cube of the cube `a`. -/
def cubeBox (a : Fin 48) : Set CuspE3 :=
  {x | ∀ i : Fin 3, (Work.Cusp.cubeCorner a i : ℝ) ≤ x i ∧ x i ≤ (Work.Cusp.cubeCorner a i : ℝ) + 1}

/-- The copy bit of a cube as an element of `ZMod 2` (`true` = copy `Q̄₀`). -/
def cubeBit (a : Fin 48) : ZMod 2 := if Work.Cusp.cubeCopy a then 0 else 1

/-- `0` is a point of `Q̄`. -/
theorem zero_mem_Qbar : (0 : CuspE4) ∈ Work.FoldInst.Qbar := by
  refine ⟨fun S => ?_, fun w => ?_⟩
  · rw [Work.FoldInst.sideSlack]
    simp only [PiLp.zero_apply, mul_zero, Finset.sum_const_zero, sub_zero]
    norm_num
  · rw [Work.FoldInst.truncSlack]
    simp only [PiLp.zero_apply, mul_zero, Finset.sum_const_zero, sub_zero]
    norm_num

/-- **The point of `X̄` over the cube coordinate `x`**, for the cube `a = cubeOf v x`: the copy of the
cube together with the Klein coordinates of the facet point.  (The definition uses a conditional
only so that this file does not depend on the certificate that the facet points lie in `Q̄`.) -/
def cuspPtX (v : Fin 5) (x : CuspE3) : CuspXbar := by
  classical
  exact
    if h : kleinPt (cubeOf v x) (redV v x) ∈ Work.FoldInst.Qbar then
      (cubeBit (cubeOf v x), ⟨kleinPt (cubeOf v x) (redV v x), h⟩)
    else (0, ⟨0, zero_mem_Qbar⟩)

/-- **The ceiling map of the `v`-th cusp**: the point of the `v`-th truncation torus whose UHS cube
coordinate is `x`. -/
def mbarPt (v : Fin 5) (x : CuspE3) : Work.FoldInst.Mbar :=
  Work.FoldInst.mk (cuspPtX v x)


/-! ### The wall table of the cubes -/

/-- The wall side of the *lower* face `{x i = cubeCorner a i}` of the cube `a`. -/
def wallLo : Fin 48 → Fin 3 → Fin 24 := ![
  ![0, 4, 12],
  ![3, 5, 13],
  ![3, 7, 13],
  ![0, 6, 12],
  ![0, 8, 16],
  ![3, 9, 19],
  ![2, 9, 19],
  ![1, 8, 16],
  ![4, 8, 20],
  ![7, 10, 21],
  ![7, 10, 23],
  ![4, 8, 22],
  ![12, 16, 20],
  ![14, 19, 23],
  ![14, 18, 23],
  ![12, 17, 20],
  ![3, 7, 11],
  ![23, 6, 11],
  ![3, 19, 9],
  ![0, 4, 12],
  ![1, 18, 10],
  ![21, 7, 11],
  ![22, 19, 9],
  ![20, 5, 13],
  ![23, 18, 10],
  ![2, 6, 11],
  ![0, 16, 12],
  ![1, 5, 8],
  ![20, 17, 9],
  ![2, 17, 12],
  ![22, 4, 14],
  ![21, 16, 10],
  ![21, 16, 13],
  ![22, 4, 8],
  ![2, 17, 9],
  ![20, 17, 13],
  ![1, 5, 15],
  ![0, 16, 10],
  ![2, 6, 12],
  ![23, 18, 14],
  ![20, 5, 8],
  ![22, 19, 14],
  ![21, 7, 13],
  ![1, 18, 15],
  ![0, 4, 8],
  ![3, 19, 15],
  ![23, 6, 14],
  ![3, 7, 15]
]

/-- The wall side of the *upper* face `{x i = cubeCorner a i + 1}` of the cube `a`. -/
def wallHi : Fin 48 → Fin 3 → Fin 24 := ![
  ![2, 6, 14],
  ![1, 7, 15],
  ![1, 5, 15],
  ![2, 4, 14],
  ![1, 10, 18],
  ![2, 11, 17],
  ![3, 11, 17],
  ![0, 10, 18],
  ![5, 9, 22],
  ![6, 11, 23],
  ![6, 11, 21],
  ![5, 9, 20],
  ![13, 17, 21],
  ![15, 18, 22],
  ![15, 19, 22],
  ![13, 16, 21],
  ![23, 19, 15],
  ![2, 19, 14],
  ![22, 5, 15],
  ![20, 16, 8],
  ![23, 7, 15],
  ![3, 17, 13],
  ![2, 4, 14],
  ![1, 16, 8],
  ![0, 6, 14],
  ![21, 17, 12],
  ![21, 6, 10],
  ![22, 18, 15],
  ![3, 5, 13],
  ![20, 4, 9],
  ![0, 18, 8],
  ![1, 7, 13],
  ![1, 7, 10],
  ![0, 18, 14],
  ![20, 4, 12],
  ![3, 5, 9],
  ![22, 18, 8],
  ![21, 6, 12],
  ![21, 17, 11],
  ![0, 6, 10],
  ![1, 16, 13],
  ![2, 4, 9],
  ![3, 17, 11],
  ![23, 7, 10],
  ![20, 16, 12],
  ![22, 5, 9],
  ![2, 19, 11],
  ![23, 19, 11]
]

/-- The truncated ideal vertex of the cube `a`, as an element of `Fin 24` (RT's numbering is 1-based). -/
def cubeVert : Fin 48 → Fin 24 := ![
  (16 : Fin 24), (17 : Fin 24), (17 : Fin 24), (16 : Fin 24), (18 : Fin 24), (19 : Fin 24), (19 : Fin 24), (18 : Fin 24),
  (20 : Fin 24), (21 : Fin 24), (21 : Fin 24), (20 : Fin 24), (22 : Fin 24), (23 : Fin 24), (23 : Fin 24), (22 : Fin 24),
  (0 : Fin 24), (8 : Fin 24), (2 : Fin 24), (15 : Fin 24), (4 : Fin 24), (1 : Fin 24), (10 : Fin 24), (7 : Fin 24),
  (12 : Fin 24), (9 : Fin 24), (13 : Fin 24), (6 : Fin 24), (3 : Fin 24), (11 : Fin 24), (14 : Fin 24), (5 : Fin 24),
  (5 : Fin 24), (14 : Fin 24), (11 : Fin 24), (3 : Fin 24), (6 : Fin 24), (13 : Fin 24), (9 : Fin 24), (12 : Fin 24),
  (7 : Fin 24), (10 : Fin 24), (1 : Fin 24), (4 : Fin 24), (15 : Fin 24), (2 : Fin 24), (8 : Fin 24), (0 : Fin 24)
]

/-- The point of `X̄` with copy `a` and position `y` (the membership in `Q̄` is an explicit
argument). -/
def xbarOf (a : Fin 48) (y : CuspE4) (hy : y ∈ Work.FoldInst.Qbar) : CuspXbar :=
  (cubeBit a, ⟨y, hy⟩)

/-- The cusp lattice in cube coordinates: `Λ_v = diag(latMod v) · ℤ³`. -/
def latVec (v : Fin 5) (z : CuspE3) : Prop :=
  ∀ i : Fin 3, ∃ k : ℤ, z i = (Work.Cusp.latMod v i : ℝ) * k

/-- A cube of cusp `v`. -/
def IsCuspCube (v : Fin 5) (a : Fin 48) : Prop := Work.Cusp.cubeCusp a = v

/-- `cuspPtX` unfolds once the membership in `Q̄` is known. -/
theorem cuspPtX_of_mem (v : Fin 5) (x : CuspE3)
    (h : kleinPt (cubeOf v x) (redV v x) ∈ Work.FoldInst.Qbar) :
    cuspPtX v x = xbarOf (cubeOf v x) (kleinPt (cubeOf v x) (redV v x)) h := by
  simp only [cuspPtX, dif_pos h, xbarOf]

/-- `redV` lies in the box of its cube (the fractional part is in `[0,1)`). -/
theorem redV_mem_cubeBox (v : Fin 5) (x : CuspE3) : redV v x ∈ cubeBox (cubeOf v x) := by
  intro i
  have h1 : (⌊x i⌋ : ℝ) ≤ x i := Int.floor_le _
  have h2 : x i < (⌊x i⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  simp only [redV, PiLp.toLp_apply]
  constructor <;> linarith

/-- The floor of the `i`-th coordinate of `redV v x`. -/
theorem floorV_redV (v : Fin 5) (x : CuspE3) (i : Fin 3) :
    ⌊redV v x i⌋ = Work.Cusp.cubeCorner (cubeOf v x) i := by
  have h1 : (⌊x i⌋ : ℝ) ≤ x i := Int.floor_le _
  have h2 : x i < (⌊x i⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hx : redV v x i = x i - (⌊x i⌋ : ℝ) + (Work.Cusp.cubeCorner (cubeOf v x) i : ℝ) := by
    simp only [redV, PiLp.toLp_apply]
  rw [hx]
  have h3 : (0 : ℝ) ≤ x i - (⌊x i⌋ : ℝ) := by linarith
  have h4 : x i - (⌊x i⌋ : ℝ) < 1 := by linarith
  rw [Int.floor_eq_iff]
  constructor <;> push_cast <;> linarith

/-- The integer shift taking `x` into the cube of `cubeOf v x`. -/
def cuspShift (v : Fin 5) (x : CuspE3) : Fin 3 → ℤ :=
  fun i => ⌊x i⌋ - Work.Cusp.cubeCorner (cubeOf v x) i

/-- `redV` agrees with `x` modulo the lattice: the shift is a lattice vector (its coordinates are
multiples of `latMod`). -/
theorem redV_sub_eq (v : Fin 5) (x : CuspE3) :
    (fun i => x i - redV v x i) = fun i => (cuspShift v x i : ℝ) := by
  funext i
  simp only [redV, cuspShift, PiLp.toLp_apply]
  push_cast
  ring

end Work.RTOwed
