/-
# Two collar coordinates of `M̂` that agree differ by an integer vector

`Work.Cusp.cuspCoordMTop a v D c δ` (`Work.Cusp.Assembly`) is the coordinate inclusion of the
*unslabbed* collar chart of the `v`-th cusp on the assembled space `M̂`: an element of the box
`cuspBoxTop v c δ` (side `2δ` in the UHS coordinate `x`, height window `(s₁, sTop)`, and **no**
meridian slab) is sent below the ceiling to the point of the hyperbolic piece with those UHS
coordinates, and on/above the ceiling to the filling point recovered by the outer chart
`cuspInvOuter v`.

This file proves the *comparison* statement between the collar coordinates of two **different**
boxes `cuspBoxTop v c δ` and `cuspBoxTop v c' δ'`, in the filling branch of both: two points `x, y`
on or above the ceiling with the same image in `M̂` differ by an element of the cusp lattice
`Λ_v = ⟨σ_v, λ₂, λ₃⟩`, i.e. by a vector with integer coordinates:

  `∃ m : Fin 3 → ℤ, x = y + (m 0, m 1, m 2, 0)`.

The mixed (below/above ceiling) case cannot occur here, because both hypotheses `β(xOf x) ≤ x 3`
and `β(xOf y) ≤ y 3` put both points in the upper branch.

## The argument

Putting `q = ⟨x, hx⟩` and `q' = ⟨y, hy⟩`, the two values are the filling branches
`cuspCoordMTopUp` (`Work.Cusp.cuspCoordMTop_continuous`), so `a.incW v` is injective and gives

1. `(cuspInvOuter v x).1 = (cuspInvOuter v y).1`, i.e. the recovered layer points of the filling
   square agree; writing them as `‖·‖∞ • bndOfU (outerU v (xOf ·))`
   (`Work.Cusp.cuspInvOuter_fst_eq_smulTop`) and cancelling the (positive) layer parameter gives
   `bndOfU (outerU v (xOf x)) = bndOfU (outerU v (xOf y))`, hence
   `Int.fract (outerU v (xOf x)) = Int.fract (outerU v (xOf y))`
   (`Work.Cusp.uPerim_bndOfU`): the **meridian** coordinates differ by an integer `k`;
2. `outerY v (xOf x) = outerY v (xOf y) + ofInt2 m` for some `m : Fin 2 → ℤ`, from the equality of
   the torus coordinates in `ℝ/ℤ` (`Work.Cusp.addCircle_one_coe_eq_iff`).

The heights then agree: the height round trip `Work.Cusp.cuspInvOuter_heightTop` expresses `x 3`
(resp. `y 3`) through `collarS v`, the first components agree, and the second ones agree up to the
translation `ofInt2 m`, under which `collarS` is invariant (`Work.Cusp.collarS_add_int`).

Finally `xOf` of a cusp coordinate is recovered from its `(outerU, outerY)` coordinates
(`Work.Cusp.cuspX_outerU_outerY`), so, using the equivariance of `cuspX` under an integer
translation of the meridian coordinate (`cuspX_add_int_slope`) and of the torus coordinates
(`Work.Cusp.cuspX_add_int_ofInt3`), the difference `xOf x - xOf y` is

  `k • σ_v + m₀ λ₂ + m₁ λ₃`,

an integer combination of the integer lattice vectors `σ_v, λ₂, λ₃` (`cuspX_intCast_smul_slope`).
-/
import Mathlib
import Submission.Work.Space.Assembly
import Submission.Work.Cusp.Assembly
import Submission.Work.Cusp.cuspCoordMTop_continuous
import Submission.Work.Cusp.cuspTopUp_eq
import Submission.Work.Cusp.cuspInvOuter_mem_SqTop
import Submission.Work.Cusp.cuspInvOuter_heightTop
import Submission.Work.Cusp.cuspX_outerU_outerY
import Submission.Work.Cusp.ThetaOuter_add_int
import Submission.Work.Cusp.uPerim_bndOfU
import Submission.Work.Cusp.nrm_smul
import Submission.Work.Cusp.cuspCoordM_injective
import Submission.Work.Cusp.CuspCollarAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.RTOWed

/-! ### The cusp lattice: an integer multiple of the slope has integer coordinates -/

/-- **The integer multiple of the slope is an integer vector.**  The coordinates of `σ_v` in the
standard basis are the integers `(κ_{v,1})_i + b_v (κ_{v,2})_i + c_v (κ_{v,3})_i`. -/
private lemma cuspX_intCast_smul_slope (v : Fin 5) (k : ℤ) :
    (k : ℝ) • Work.Cusp.slope v =
      Work.Cusp.ofInt3 (fun j => k * (Work.Cusp.kappa v 0 j + Work.Cusp.slopeB v * Work.Cusp.kappa v 1 j
        + Work.Cusp.slopeC v * Work.Cusp.kappa v 2 j)) := by
  ext j
  fin_cases j <;>
    simp [Work.Cusp.slope, Work.Cusp.kv, Work.Cusp.ofInt3, PiLp.add_apply, PiLp.smul_apply] <;>
    ring

/-- **Equivariance of `cuspX` under an integer translation of the meridian coordinate**:
`cuspX v (u + k) y = cuspX v u y + k σ_v`. -/
private lemma cuspX_add_int_slope (v : Fin 5) (u : ℝ) (y : Work.Cusp.E2) (k : ℤ) :
    Work.Cusp.cuspX v (u + (k : ℝ)) y
      = Work.Cusp.cuspX v u y + (k : ℝ) • Work.Cusp.slope v := by
  simp only [Work.Cusp.cuspX, add_smul]
  abel

/-- `ofInt3` is additive. -/
private lemma ofInt3_add_int (A B : Fin 3 → ℤ) :
    Work.Cusp.ofInt3 A + Work.Cusp.ofInt3 B = Work.Cusp.ofInt3 (A + B) := by
  ext j
  fin_cases j <;> simp [Work.Cusp.ofInt3, PiLp.add_apply]

/-! ### From the coordinate data to the statement of the theorem -/

/-- **Assembly of the conclusion.**  If two points of `E4` have the same height and their horizontal
parts differ by an integer vector, then the points differ by the corresponding lattice vector of the
cusp (with vanishing last coordinate). -/
private lemma eq_add_ofInt4_of {x y : Work.Cusp.E4} {n : Fin 3 → ℤ} (h3 : x 3 = y 3)
    (hn : Work.Cusp.xOf x - Work.Cusp.xOf y = Work.Cusp.ofInt3 n) :
    x = y + !₂[(n 0 : ℝ), (n 1 : ℝ), (n 2 : ℝ), 0] := by
  have hadd : Work.Cusp.mkE4 (Work.Cusp.xOf y + Work.Cusp.ofInt3 n) (y 3 + 0)
      = Work.Cusp.mkE4 (Work.Cusp.xOf y) (y 3) + Work.Cusp.mkE4 (Work.Cusp.ofInt3 n) 0 := by
    ext i
    fin_cases i <;> simp [Work.Cusp.mkE4, Work.Cusp.xOf, PiLp.add_apply]
  have hxy : Work.Cusp.xOf x = Work.Cusp.xOf y + Work.Cusp.ofInt3 n := by rw [← hn]; abel
  calc x = Work.Cusp.mkE4 (Work.Cusp.xOf x) (x 3) := (Work.Cusp.mkE4_xOf_three x).symm
    _ = Work.Cusp.mkE4 (Work.Cusp.xOf y + Work.Cusp.ofInt3 n) (y 3 + 0) := by rw [hxy, h3]; simp
    _ = Work.Cusp.mkE4 (Work.Cusp.xOf y) (y 3) + Work.Cusp.mkE4 (Work.Cusp.ofInt3 n) 0 := hadd
    _ = y + Work.Cusp.mkE4 (Work.Cusp.ofInt3 n) 0 := by rw [Work.Cusp.mkE4_xOf_three]
    _ = y + !₂[(n 0 : ℝ), (n 1 : ℝ), (n 2 : ℝ), 0] := rfl

/-! ### The comparison of two collar coordinates -/

theorem cuspCoordMTop_high_diff (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : Work.Cusp.CuspGlueData a v) {c c' : Work.Cusp.E3} {δ δ' : ℝ}
    {x y : Work.Cusp.E4} (hx : x ∈ Work.Cusp.cuspBoxTop v c δ)
    (hy : y ∈ Work.Cusp.cuspBoxTop v c' δ')
    (hxge : Work.Cusp.beta (Work.Cusp.xOf x) ≤ x 3)
    (hyge : Work.Cusp.beta (Work.Cusp.xOf y) ≤ y 3)
    (h : Work.Cusp.cuspCoordMTop a v D c δ ⟨x, hx⟩ =
         Work.Cusp.cuspCoordMTop a v D c' δ' ⟨y, hy⟩) :
    ∃ m : Fin 3 → ℤ, x = y + !₂[(m 0 : ℝ), (m 1 : ℝ), (m 2 : ℝ), 0] := by
  have hsrcx : x ∈ Work.Cusp.cuspSourceTop v c δ := ⟨hx, hxge⟩
  have hsSrcy : y ∈ Work.Cusp.cuspSourceTop v c' δ' := ⟨hy, hyge⟩
  -- ### Step 1: both points are in the filling branch, so the two recovered points agree
  have hup : Work.Cusp.cuspCoordMTopUp a v D c δ ⟨x, hsrcx⟩ =
      Work.Cusp.cuspCoordMTopUp a v D c' δ' ⟨y, hsSrcy⟩ := by
    rw [← Work.Cusp.cuspCoordMTop_eq_ge a v D c δ ⟨x, hx⟩ hxge,
        ← Work.Cusp.cuspCoordMTop_eq_ge a v D c' δ' ⟨y, hy⟩ hyge]
    exact h
  simp only [Work.Cusp.cuspCoordMTopUp] at hup
  have hpair := a.incW_injective v hup
  have hfst : (Work.Cusp.cuspInvOuter v x).1 = (Work.Cusp.cuspInvOuter v y).1 := by
    have h1 := congrArg (fun z : Work.Space.SquarePt × a.Torus v => (z.1 : Work.Cusp.E2)) hpair
    simpa using h1
  have hsnd : ∀ i : Fin 2, (((Work.Cusp.cuspInvOuter v x).2 i : ℝ) : AddCircle (1 : ℝ)) =
      (((Work.Cusp.cuspInvOuter v y).2 i : ℝ) : AddCircle (1 : ℝ)) := by
    have h2 := congrArg (fun z : Work.Space.SquarePt × a.Torus v => z.2) hpair
    have h2' := (Homeomorph.injective D.tor.symm) h2
    intro i
    exact congrFun h2' i
  -- ### Step 2: the torus coordinates differ by an integer pair `m`
  have hm : ∀ i : Fin 2, ∃ m : ℤ,
      (Work.Cusp.cuspInvOuter v x).2 i = (Work.Cusp.cuspInvOuter v y).2 i + (m : ℝ) :=
    fun i => (Work.Cusp.addCircle_one_coe_eq_iff _ _).mp (hsnd i)
  choose m hm using hm
  have hyx : (Work.Cusp.cuspInvOuter v x).2
      = (Work.Cusp.cuspInvOuter v y).2 + Work.Cusp.ofInt2 m := by
    ext i
    fin_cases i
    · simpa [Work.Cusp.ofInt2, PiLp.add_apply] using hm 0
    · simpa [Work.Cusp.ofInt2, PiLp.add_apply] using hm 1
  have hyxO : Work.Cusp.outerY v (Work.Cusp.xOf x)
      = Work.Cusp.outerY v (Work.Cusp.xOf y) + Work.Cusp.ofInt2 m := hyx
  -- ### Step 3: the meridian coordinates differ by an integer `k`
  have hfx := Work.Cusp.cuspInvOuter_fst_eq_smulTop v c δ x hsrcx
  have hfy := Work.Cusp.cuspInvOuter_fst_eq_smulTop v c' δ' y hsSrcy
  have hnrm : Work.Cusp.nrm (Work.Cusp.cuspInvOuter v x).1
      = Work.Cusp.nrm (Work.Cusp.cuspInvOuter v y).1 := congrArg Work.Cusp.nrm hfst
  have hposx : 0 < Work.Cusp.nrm (Work.Cusp.cuspInvOuter v x).1 :=
    lt_trans (by norm_num [Work.Cusp.layerLo])
      (Work.Cusp.cuspInvOuter_nrm_Top v c δ x hsrcx).1
  have hposy : 0 < Work.Cusp.nrm (Work.Cusp.cuspInvOuter v y).1 := by
    rw [← hnrm]; exact hposx
  have hbnd : Work.Cusp.bndOfU (Work.Cusp.outerU v (Work.Cusp.xOf x))
      = Work.Cusp.bndOfU (Work.Cusp.outerU v (Work.Cusp.xOf y)) := by
    have hh := hfst
    rw [hfx, hfy, hnrm] at hh
    exact (smul_right_inj (ne_of_gt hposy)).mp hh
  have hfract : Int.fract (Work.Cusp.outerU v (Work.Cusp.xOf x))
      = Int.fract (Work.Cusp.outerU v (Work.Cusp.xOf y)) := by
    have hh := congrArg Work.Cusp.uPerim hbnd
    rwa [Work.Cusp.uPerim_bndOfU, Work.Cusp.uPerim_bndOfU] at hh
  obtain ⟨k, hk⟩ : ∃ k : ℤ, Work.Cusp.outerU v (Work.Cusp.xOf x)
      - Work.Cusp.outerU v (Work.Cusp.xOf y) = (k : ℝ) := Int.fract_eq_fract.mp hfract
  have hux : Work.Cusp.outerU v (Work.Cusp.xOf x)
      = Work.Cusp.outerU v (Work.Cusp.xOf y) + (k : ℝ) := by linarith
  -- ### Step 4: the heights agree
  have h3 : x 3 = y 3 := by
    have hx3 : x 3 = Work.Cusp.collarS v (Work.Cusp.cuspInvOuter v x).1
        (Work.Cusp.cuspInvOuter v x).2 :=
      (Work.Cusp.cuspInvOuter_heightTop v c δ x hsrcx).symm
    have hy3 : Work.Cusp.collarS v (Work.Cusp.cuspInvOuter v y).1
        (Work.Cusp.cuspInvOuter v y).2 = y 3 :=
      Work.Cusp.cuspInvOuter_heightTop v c' δ' y hsSrcy
    rw [hx3, ← hy3, hfst]
    have hshift := Work.Cusp.collarS_add_int v (Work.Cusp.cuspInvOuter v y).1
      (Work.Cusp.cuspInvOuter v y).2 m
    rw [← hyx] at hshift
    exact hshift
  -- ### Step 5: the cusp coordinates differ by the lattice vector `k σ_v + m₀ λ₂ + m₁ λ₃`
  have hkey : Work.Cusp.xOf x = Work.Cusp.xOf y +
      (Work.Cusp.ofInt3 (fun i => m 0 * Work.Cusp.kappa v 1 i + m 1 * Work.Cusp.kappa v 2 i)
       + Work.Cusp.ofInt3 (fun i => k * (Work.Cusp.kappa v 0 i + Work.Cusp.slopeB v * Work.Cusp.kappa v 1 i
          + Work.Cusp.slopeC v * Work.Cusp.kappa v 2 i))) := by
    calc Work.Cusp.xOf x
        = Work.Cusp.cuspX v (Work.Cusp.outerU v (Work.Cusp.xOf x))
            (Work.Cusp.outerY v (Work.Cusp.xOf x)) :=
          (Work.Cusp.cuspX_outerU_outerY v (Work.Cusp.xOf x)).symm
      _ = Work.Cusp.cuspX v (Work.Cusp.outerU v (Work.Cusp.xOf y) + (k : ℝ))
            (Work.Cusp.outerY v (Work.Cusp.xOf y) + Work.Cusp.ofInt2 m) := by rw [hux, hyxO]
      _ = Work.Cusp.cuspX v (Work.Cusp.outerU v (Work.Cusp.xOf y))
            (Work.Cusp.outerY v (Work.Cusp.xOf y) + Work.Cusp.ofInt2 m)
          + (k : ℝ) • Work.Cusp.slope v :=
          cuspX_add_int_slope v (Work.Cusp.outerU v (Work.Cusp.xOf y))
            (Work.Cusp.outerY v (Work.Cusp.xOf y) + Work.Cusp.ofInt2 m) k
      _ = (Work.Cusp.cuspX v (Work.Cusp.outerU v (Work.Cusp.xOf y)) (Work.Cusp.outerY v (Work.Cusp.xOf y))
            + Work.Cusp.ofInt3 (fun i => m 0 * Work.Cusp.kappa v 1 i
                + m 1 * Work.Cusp.kappa v 2 i))
          + (k : ℝ) • Work.Cusp.slope v := by
          rw [Work.Cusp.cuspX_add_int_ofInt3]
      _ = Work.Cusp.xOf y + (Work.Cusp.ofInt3 (fun i => m 0 * Work.Cusp.kappa v 1 i
              + m 1 * Work.Cusp.kappa v 2 i) + (k : ℝ) • Work.Cusp.slope v) := by
          rw [Work.Cusp.cuspX_outerU_outerY]; abel
      _ = Work.Cusp.xOf y +
          (Work.Cusp.ofInt3 (fun i => m 0 * Work.Cusp.kappa v 1 i + m 1 * Work.Cusp.kappa v 2 i)
           + Work.Cusp.ofInt3 (fun i => k * (Work.Cusp.kappa v 0 i
              + Work.Cusp.slopeB v * Work.Cusp.kappa v 1 i
              + Work.Cusp.slopeC v * Work.Cusp.kappa v 2 i))) := by
          rw [cuspX_intCast_smul_slope v k]
  let n : Fin 3 → ℤ := fun i => (m 0 * Work.Cusp.kappa v 1 i + m 1 * Work.Cusp.kappa v 2 i)
      + k * (Work.Cusp.kappa v 0 i + Work.Cusp.slopeB v * Work.Cusp.kappa v 1 i
        + Work.Cusp.slopeC v * Work.Cusp.kappa v 2 i)
  have hdiff : Work.Cusp.xOf x - Work.Cusp.xOf y = Work.Cusp.ofInt3 n := by
    rw [hkey, ofInt3_add_int, add_sub_cancel_left]
    rfl
  exact ⟨n, eq_add_ofInt4_of h3 hdiff⟩

end Work.RTOWed
