/-
# Auxiliary vocabulary for the finite junction-collar cover `Work.RTOwed.jCollar_cover_fin`

The junction charts of `M̂` (`Submission/Work/RTOwed/FillBigDefs.lean`) are indexed by the pinning
data `Work.RTOwed.JPin`:

* `cU : ℝ`, `k : Fin 4` — the pinning of the *perimeter* coordinate `uqOf v q` (the lift of the
  perimeter direction);
* `W : Set E2` — the section box of the `w`-coordinates (with the injectivity condition `hsec`);
* `kx : E3`, `δ : ℝ` — the horizontal box of the collar branch.

The cover theorem `Work.RTOwed.jCollar_cover_fin` needs a *finite* family of such data.  This file
fixes the two finite families that make this possible.

* **The `w`-section family** `jWSet v c`, indexed by a centre `c : E2`: the preimage under the
  linear isomorphism `invY v` of the box `jWBox c = {y | ∀ j, |y j − c j| < 1/4}`.  On such a box
  the `w`-coordinates determine the cusp coordinate modulo `ℤ²` (`jWSet_hsec`), and every lift
  whose coordinates lie in the unit square lies in one of finitely many such boxes
  (`Work.RTOwed.exists_jW_cover`).  The box radius `1/4` is what makes `hsec` true: two points of
  the box differ by less than `1/2` in every coordinate, while `ℤ²` is `1`-separated.

* **The perimeter-pinning family** `jPin : Fin 8 → ℝ × Fin 4`: the eight pairs
  `(0,k), (−1/8,k)`, `k : Fin 4`.  For every `u ∈ [0,1)` some pair `(cU,k)` satisfies
  `u − cU ∈ [0,1)` and `fract (u − cU) ∈ (k/4, (k+1)/4)` (`Work.RTOwed.jPin_cover`): the four
  wedges of the cut `cU = 0` cover all of `(0,1)` except the four quarter points, which are covered
  by the shifted cut `cU = −1/8` (the shift of `Work.Cusp.polarLayer_subset_range_polarCoordM`).
-/
import Mathlib
import Submission.Work.RTOwed.FillBigDefs
import Submission.Work.Cusp.exists_section_box

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function

namespace Work.RTOwed

open Work.Cusp

/-! ### The `w`-section boxes -/

/-- **The box of `w`-coordinates** of side `1/2` around the centre `c` (in the `y`-coordinates of
the cusp, i.e. in the coordinates in which the section condition is read). -/
def jWBox (c : E2) : Set E2 := {y | ∀ j, |y j - c j| < 1 / 4}

/-- **The section box of a junction chart**, indexed by the centre `c` of the box in the
`y`-coordinates of the cusp: the set of `w`-coordinates `wOf v y` of the points `y` of the box
`jWBox c`.  Equivalently (and definitionally) it is the preimage of `jWBox c` under the linear
isomorphism `invY v`. -/
def jWSet (v : Work.Space.Cusp) (c : E2) : Set E2 := {w | invY v w ∈ jWBox c}

theorem jWBox_isOpen (c : E2) : IsOpen (jWBox c) := by
  have hset : jWBox c = ⋂ j, {y : E2 | |y j - c j| < 1 / 4} := by
    ext y; simp [jWBox, Set.mem_iInter]
  rw [hset]
  exact isOpen_iInter_of_finite fun j => isOpen_lt (by fun_prop) continuous_const

/-- `invY v` is continuous: it is the explicit inverse matrix `Work.Cusp.invYLin v`. -/
theorem continuous_invY (v : Work.Space.Cusp) : Continuous (invY v) :=
  (invYLin v).continuous_of_finiteDimensional

/-- **The section box of a junction chart is open.** -/
theorem jWSet_isOpen (v : Work.Space.Cusp) (c : E2) : IsOpen (jWSet v c) :=
  (continuous_invY v).isOpen_preimage _ (jWBox_isOpen c)

/-- **The section condition of the junction charts.**  On `jWSet v c` the `w`-coordinates determine
the cusp coordinate modulo `ℤ²`: two points whose `w`-images lie in the box and which agree in
`(ℝ/ℤ)²` are equal.  This is exactly the field `Work.RTOwed.JPin.hsec`. -/
theorem jWSet_hsec (v : Work.Space.Cusp) (c : E2) :
    ∀ y y' : E2, wOf v y ∈ jWSet v c → wOf v y' ∈ jWSet v c →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y' := by
  intro y y' hy hy' hmod
  have h1 : ∀ j, |y j - y' j| < 1 / 2 := by
    intro j
    have ha' : |y j - c j| < 1 / 4 := by
      have h := hy j
      rw [invY_wOf] at h
      exact h
    have hb' : |y' j - c j| < 1 / 4 := by
      have h := hy' j
      rw [invY_wOf] at h
      exact h
    have htri : |y j - y' j| ≤ |y j - c j| + |c j - y' j| := abs_sub_le _ _ _
    rw [abs_sub_comm (c j) (y' j)] at htri
    linarith
  ext j
  obtain ⟨n, hn⟩ := sub_eq_intCast_of_addCircle_eq (hmod j)
  have hlt : |(n : ℝ)| < 1 := by rw [← hn]; exact lt_trans (h1 j) (by norm_num)
  have hn0 : n = 0 := by
    have h3 : (n : ℝ) < 1 := (abs_lt.mp hlt).2
    have h4 : -(1 : ℝ) < (n : ℝ) := (abs_lt.mp hlt).1
    have h5 : n < 1 := by exact_mod_cast h3
    have h6 : -1 < n := by exact_mod_cast h4
    omega
  have : y j - y' j = 0 := by rw [hn, hn0]; norm_num
  exact sub_eq_zero.mp this

/-! ### Coordinate identities of the polar and outer charts -/

/-- The horizontal part of the outer chart is the cusp coordinate `cuspX v (u p) y`. -/
theorem xOf_thetaOuter (v : Work.Space.Cusp) (p y : E2) :
    xOf (ThetaOuter v p y) = cuspX v (u p) y := by
  ext i
  fin_cases i <;> simp [ThetaOuter, xOf]

/-- The radial coordinate of the polar chart. -/
theorem thetaPolar_zero (v : Work.Space.Cusp) (p y : E2) :
    (ThetaPolar v p y) 0 = radial v p y := by
  simp [ThetaPolar]

/-- The `w`-coordinates of the polar chart are `wOf v y`. -/
theorem thetaPolar_two_three (v : Work.Space.Cusp) (p y : E2) :
    (!₂[(ThetaPolar v p y) 2, (ThetaPolar v p y) 3] : E2) = wOf v y := by
  ext i
  fin_cases i <;> simp [ThetaPolar]

/-- **The perimeter coordinate recovered from a point of the polar chart is the perimeter
parameter `u p`**: `uqOf v q` recovers `u` from the angle coordinate
`q 1 = 2π u p + 2π⟪y,σ_v⟫/‖σ_v‖²` and from the `w`-coordinates `(q 2, q 3) = wOf v y` (inverted by
`invY_wOf`); the phase correction cancels.  (The same statement as
`Work.Cusp.polarChart_uqOf_ThetaPolar`, proved here so that this file depends only on the
definition layer.) -/
theorem uqOf_thetaPolar (v : Work.Space.Cusp) (p y : E2) :
    uqOf v (ThetaPolar v p y) = u p := by
  have hy : invY v !₂[(ThetaPolar v p y) 2, (ThetaPolar v p y) 3] = y := by
    rw [thetaPolar_two_three v p y, invY_wOf]
  rw [uqOf, hy]
  rw [show (ThetaPolar v p y) 1
      = 2 * Real.pi * u p + 2 * Real.pi * (inner ℝ (cuspY v y) (slope v) / ‖slope v‖ ^ 2) from by
    simp [ThetaPolar, thetaAng]]
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  field_simp
  ring

/-! ### The perimeter pinning family -/

/-- **The eight pinning data of the perimeter coordinate**: indices `0..3` carry the cut `cU = 0`
and the wedge index `k = i`, indices `4..7` carry the shifted cut `cU = −1/8` and the wedge index
`k = i − 4`. -/
def jPin (i : Fin 8) : ℝ × Fin 4 :=
  if h : (i : ℕ) < 4 then (0, ⟨(i : ℕ), h⟩) else (-1 / 8, ⟨(i : ℕ) - 4, by omega⟩)

end Work.RTOwed
