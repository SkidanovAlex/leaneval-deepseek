/-
# Injectivity of `p ↦ (‖p‖∞, u(p))` on the filling square

The filling disk of the Dehn filling is the square `Sq = [-1,1]² ⊂ ℝ²`, written in the layer
parameter `‖p‖∞ = nrm p = max |p 0| |p 1|` and the perimeter parameter `u p = uPerim (bnd p)`
of the ray through `p`.  This file proves that these two coordinates *determine* the point:

`Set.InjOn (fun p : E2 => (nrm p, u p)) Sq`.

The mathematical content is entirely in two facts.

* **Radial projection.**  For `p ≠ 0` the point `bnd p = (nrm p)⁻¹ • p` lies on the boundary
  `∂Sq = {q | nrm q = 1}` (`nrm_bnd`), and `p = nrm p • bnd p` (`smul_bnd`).  Hence, for
  `nrm p = nrm q ≠ 0`, the points agree iff their radial projections do.  At `nrm p = 0` the
  point is `0`, and there is nothing left to prove.

* **The perimeter parameter is a coordinate on the boundary.**  `uPerim` traverses the four edges
  of `∂Sq` counterclockwise from `(1,1)`, each edge carrying an interval of length `1/4`:
  on `q 0 = 1` it is `(1 - q 1)/8 ∈ [0,1/4]`, on `q 1 = -1` it is `(3 - q 0)/8 ∈ [1/4,1/2]`, on
  `q 0 = -1` it is `(5 + q 1)/8 ∈ [1/2,3/4]`, and otherwise (with `nrm q = 1` this forces `q 1 = 1`)
  it is `(7 + q 0)/8 ∈ (3/4,1)`.  Since the four intervals are listed in increasing order and meet
  only at the corners, `uPerim` is injective on `∂Sq`; equivalently `bndOfU` inverts it there, which
  is what we prove (`nrmu_bndOfU_uPerim`), reducing the injectivity to a computation in each of the
  four branches.
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.nrm_bnd
import Submission.Work.Cusp.smul_bnd
import Submission.Work.Cusp.uPerim_mem

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- `nrm p = 0` forces `p = 0`: the sup norm dominates both coordinates. -/
theorem nrmu_nrm_eq_zero {p : E2} (h : nrm p = 0) : p = 0 := by
  have h0 : p 0 = 0 := by
    have : |p 0| = 0 := le_antisymm (by rw [← h]; exact le_max_left _ _) (abs_nonneg _)
    exact abs_eq_zero.mp this
  have h1 : p 1 = 0 := by
    have : |p 1| = 0 := le_antisymm (by rw [← h]; exact le_max_right _ _) (abs_nonneg _)
    exact abs_eq_zero.mp this
  ext i
  fin_cases i <;> simp [h0, h1]

/-- **`bndOfU` inverts `uPerim` on the boundary `∂Sq = {q | nrm q = 1}`.**  Since `uPerim q ∈ [0,1)`
on `∂Sq` (`uPerim_mem`), `Int.fract (uPerim q) = uPerim q`, and the branch of `uPerim` taken by `q`
is the branch of `bndOfU` taken by `uPerim q`: each branch of `uPerim` has its values in the range
of the corresponding branch of `bndOfU`, the ranges meeting only at the corners, where the two
consecutive formulas agree. -/
theorem nrmu_bndOfU_uPerim {q : E2} (hq : nrm q = 1) : bndOfU (uPerim q) = q := by
  have hmax : max |q 0| |q 1| = 1 := hq
  have hq0le : q 0 ≤ 1 := (abs_le.mp (hmax ▸ le_max_left |q 0| |q 1|)).2
  have hq0ge : -1 ≤ q 0 := (abs_le.mp (hmax ▸ le_max_left |q 0| |q 1|)).1
  have hq1le : q 1 ≤ 1 := (abs_le.mp (hmax ▸ le_max_right |q 0| |q 1|)).2
  have hq1ge : -1 ≤ q 1 := (abs_le.mp (hmax ▸ le_max_right |q 0| |q 1|)).1
  by_cases hA : q 0 = 1
  · -- the right edge: `uPerim q = (1 - q 1)/8 ∈ [0, 1/4]`
    have hU : uPerim q = (1 - q 1) / 8 := by unfold uPerim; rw [ite_eq_left hA]
    rw [hU]
    have hfr : Int.fract ((1 - q 1) / 8) = (1 - q 1) / 8 := by
      rw [Int.fract_eq_self]; exact ⟨by nlinarith, by nlinarith⟩
    simp only [bndOfU]
    rw [hfr]
    split_ifs with h1 h2 h3
    · ext i; fin_cases i <;> simp_all <;> ring_nf
    · rw [not_lt] at h1
      have hq1 : q 1 = -1 := by nlinarith
      ext i; fin_cases i <;> simp_all <;> norm_num
    · rw [not_lt] at h1
      exfalso; nlinarith
    · rw [not_lt] at h2
      exfalso; nlinarith
  · by_cases hB : q 1 = -1
    · -- the bottom edge: `uPerim q = (3 - q 0)/8 ∈ [1/4, 1/2]`
      have hU : uPerim q = (3 - q 0) / 8 := by unfold uPerim; rw [ite_eq_right hA, ite_eq_left hB]
      rw [hU]
      have hfr : Int.fract ((3 - q 0) / 8) = (3 - q 0) / 8 := by
        rw [Int.fract_eq_self]; exact ⟨by nlinarith, by nlinarith⟩
      simp only [bndOfU]
      rw [hfr]
      split_ifs with h1 h2 h3
      · exfalso; nlinarith
      · ext i; fin_cases i <;> simp_all <;> ring_nf
      · rw [not_lt] at h2
        have hq0 : q 0 = -1 := by nlinarith
        ext i; fin_cases i <;> simp_all <;> ring_nf
      · rw [not_lt] at h3
        exfalso; nlinarith
    · by_cases hC : q 0 = -1
      · -- the left edge: `uPerim q = (5 + q 1)/8 ∈ [1/2, 3/4]`
        have hU : uPerim q = (5 + q 1) / 8 := by
          unfold uPerim; rw [ite_eq_right hA, ite_eq_right hB, ite_eq_left hC]
        rw [hU]
        have hfr : Int.fract ((5 + q 1) / 8) = (5 + q 1) / 8 := by
          rw [Int.fract_eq_self]; exact ⟨by nlinarith, by nlinarith⟩
        simp only [bndOfU]
        rw [hfr]
        split_ifs with h1 h2 h3
        · exfalso; nlinarith
        · rw [not_lt] at h1
          exfalso; nlinarith
        · rw [not_lt] at h2
          ext i; fin_cases i <;> simp_all <;> ring_nf
        · rw [not_lt] at h3
          have hq1 : q 1 = 1 := by nlinarith
          ext i; fin_cases i <;> simp_all <;> ring_nf
      · -- the top edge, reached with `q 1 = 1`: `uPerim q = (7 + q 0)/8 ∈ (3/4, 1)`
        have hq0ne : |q 0| ≠ 1 := by
          intro h
          rcases (abs_eq_abs.mp (h.trans abs_one.symm)) with h' | h'
          · exact hA h'
          · exact hC h'
        have hcase : |q 0| = 1 ∨ |q 1| = 1 := by
          have h1le : 1 ≤ max |q 0| |q 1| := hmax.symm.le
          rcases le_max_iff.mp h1le with h | h
          · exact Or.inl (le_antisymm (hmax ▸ le_max_left |q 0| |q 1|) h)
          · exact Or.inr (le_antisymm (hmax ▸ le_max_right |q 0| |q 1|) h)
        have hq1abs : |q 1| = 1 := by
          rcases hcase with h | h
          · exact absurd h hq0ne
          · exact h
        have hq1 : q 1 = 1 := by
          rcases (abs_eq_abs.mp (hq1abs.trans abs_one.symm)) with h' | h'
          · exact h'
          · exact absurd h' hB
        have hq0lt : q 0 < 1 := lt_of_le_of_ne hq0le hA
        have hU : uPerim q = (7 + q 0) / 8 := by
          unfold uPerim; rw [ite_eq_right hA, ite_eq_right hB, ite_eq_right hC]
        rw [hU]
        have hfr : Int.fract ((7 + q 0) / 8) = (7 + q 0) / 8 := by
          rw [Int.fract_eq_self]; exact ⟨by nlinarith, by nlinarith⟩
        simp only [bndOfU]
        rw [hfr]
        split_ifs with h1 h2 h3
        · exfalso; nlinarith
        · exfalso; nlinarith
        · rw [not_lt] at h1 h2
          exfalso; nlinarith
        · rw [not_lt] at h3
          ext i; fin_cases i <;> simp_all <;> ring_nf

/-- **The perimeter parameter `uPerim` is injective on the boundary `∂Sq`**: it is the inverse of
the bijection `t ↦ bndOfU t` of `[0,1)` onto `∂Sq`. -/
theorem nrmu_uPerim_injOn : Set.InjOn uPerim {q : E2 | nrm q = 1} := by
  intro r hr s hs hrs
  rw [← nrmu_bndOfU_uPerim hr, ← nrmu_bndOfU_uPerim hs, hrs]

/-- **The layer parameter and the perimeter parameter determine a point of the filling square.**
This is the injectivity of the chart `p ↦ (‖p‖∞, u(p))` of the filling disk, needed to see the
filling piece `W_v = Sq × (ℝ/ℤ)²` as a square of polar coordinates around the core. -/
theorem nrm_u_injOn : Set.InjOn (fun p : E2 => (nrm p, u p)) Sq := by
  intro p hp q hq hpq
  have hn : nrm p = nrm q := congrArg Prod.fst hpq
  have hu : u p = u q := congrArg Prod.snd hpq
  rcases eq_or_ne (nrm p) 0 with h0 | h0
  · -- the core point: both points are `0`
    have hq0' : nrm q = 0 := by rw [← hn]; exact h0
    rw [nrmu_nrm_eq_zero h0, nrmu_nrm_eq_zero hq0']
  · -- otherwise radial projection to `∂Sq`, where `uPerim` is a coordinate
    have hpne : p ≠ 0 := fun h => h0 (by rw [h]; simp [nrm])
    have hqne : q ≠ 0 := by
      intro h
      exact h0 (by rw [hn, h]; simp [nrm])
    have hb : bnd p = bnd q :=
      nrmu_uPerim_injOn (nrm_bnd hpne) (nrm_bnd hqne)
        (show uPerim (bnd p) = uPerim (bnd q) from hu)
    calc p = nrm p • bnd p := (smul_bnd p).symm
      _ = nrm q • bnd q := by rw [hn, hb]
      _ = q := smul_bnd q

end Work.Cusp
