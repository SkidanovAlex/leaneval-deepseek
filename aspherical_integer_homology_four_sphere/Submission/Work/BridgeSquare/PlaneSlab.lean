/-
# `BridgeSquare/PlaneSlab.lean` — the sheared slab of the `planeIdentT` comparison

This module sets up the *domain-side* calculus of the slab used by `Work.BridgeSquare.planeIdentT`.

**Geometry.**  Fix `v : Fin 5`, let `m = dirKappa v 0` be the cube-coordinate axis of the meridian
`κ_{v,1}`, and put `cuspHm v = ½ e_m`.  The slab is the `3`-parameter family

  `Φ(y₀,y₁,t) = mbarPt v (cuspY v (y₀,y₁) + cuspH - t • cuspHm v)`

  `= mbarPtC v (cuspY v (y₀,y₁) - t • cuspHm v)`.

At `t = 0` it is the section (`Fn v y = mbarPtC v (cuspY v y)`, `Fn_apply`); at `t = 1` it is the
*wall* `z_m = 0`.  Because the shift is only in the meridian direction, the cube-coordinate
components `z_i = (cuspY v y)_i + ½` (`i ≠ m`) are **independent of `t`**: the slab is a union of
vertical prisms, one per shifted-grid cell, and `mbarPt v` is affine on each of them.

**Formalisation.**  Rather than pushing a chain of the slab space forward along the continuous map
`Φ` (`PlanePush.lean`/`planeToSingD.lean`), we work directly with the *chart chains*
`cChain v p = singGen (cSimp v p)` of `ChartAlgA.lean`, transported through the affine vertex map

  `slabL v z = z₀ • κ_{v,2} + z₁ • κ_{v,3} - z₂ • cuspHm v`,   `slabV v p = p ∘ slabL`,

and the linear map

  `slabChain v k : AffC k →ₗ[ℤ] C_k(M̄)`,  `slabChain v k (single p a) = a • cChain v (slabV v p)`.

The point of doing it this way is that the boundary formula

  `∂ (slabChain v (k+1) c) = slabChain v k (dLC k c)`

is an immediate consequence of the *face formula* `cChain_d` of `ChartAlgA` — no affineness, no
`esimp`, no `toSing` bookkeeping.  Every chain identity of the construction therefore reduces to a
finite identity of `Finsupp`s on the *domain* (which is generated data), and the only geometric
inputs left are the identifications of the specific faces (`bot` below, the wall, the sides).
-/
import Mathlib
import Submission.Work.BridgeSquare.PlaneAff
import Submission.Work.BridgeSquare.ChartAlgA

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped Topology Simplicial
open Convexity

namespace Work.BridgeSquare

noncomputable section

/-! ## §1  The slab coordinates -/

/-- The vector of the slab coordinate space with the three given coordinates. -/
def slabPt (a b c : ℝ) : CuspE3 := WithLp.toLp 2 ![a, b, c]

@[simp] theorem slabPt_zero_apply (a b c : ℝ) : slabPt a b c 0 = a := rfl
@[simp] theorem slabPt_one_apply (a b c : ℝ) : slabPt a b c 1 = b := rfl
@[simp] theorem slabPt_two_apply (a b c : ℝ) : slabPt a b c 2 = c := rfl

/-- **The meridian half shift**: the cube-coordinate vector `½ e_m`, `m = dirKappa v 0` the axis of
the meridian `κ_{v,1}`. -/
def cuspHm (v : Fin 5) : CuspE3 :=
  WithLp.toLp 2 fun i : Fin 3 => if i = dirKappa v 0 then (1 / 2 : ℝ) else 0

@[simp] theorem cuspHm_apply (v : Fin 5) (i : Fin 3) :
    cuspHm v i = if i = dirKappa v 0 then (1 / 2 : ℝ) else 0 := rfl

/-- **The slab-coordinate map**: from the slab coordinates `(y₀,y₁,t)` to the cusp cube
coordinates `cuspY v y - t • cuspHm v`. -/
def slabL (v : Fin 5) (z : CuspE3) : CuspE3 :=
  z 0 • Work.Cusp.lam2 v + z 1 • Work.Cusp.lam3 v - z 2 • cuspHm v

theorem slabL_eq_cuspY (v : Fin 5) (z : CuspE3) :
    slabL v z = Work.Cusp.cuspY v !₂[z 0, z 1] - z 2 • cuspHm v := by
  simp only [slabL, Work.Cusp.cuspY, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem slabL_add (v : Fin 5) (z w : CuspE3) : slabL v (z + w) = slabL v z + slabL v w := by
  simp only [slabL, PiLp.add_apply, add_smul]
  abel

theorem slabL_smul (v : Fin 5) (c : ℝ) (z : CuspE3) : slabL v (c • z) = c • slabL v z := by
  simp only [slabL, PiLp.smul_apply, smul_assoc, smul_sub, smul_add]

/-- The vertex-family transport along `slabL`. -/
def slabV (v : Fin 5) {k : ℕ} (p : Fin (k + 1) → CuspE3) : Fin (k + 1) → CuspE3 :=
  fun i => slabL v (p i)

theorem slabV_apply (v : Fin 5) {k : ℕ} (p : Fin (k + 1) → CuspE3) (i : Fin (k + 1)) :
    slabV v p i = slabL v (p i) := rfl

/-- Face compatibility: the `i`-th face family of the transported family is the transport of the
`i`-th face family. -/
theorem slabV_vface (v : Fin 5) {k : ℕ} (p : Fin (k + 2) → CuspE3) (i : Fin (k + 2)) :
    slabV v (vface i p) = vface i (slabV v p) := rfl

/-! ## §2  The slab chains and their boundary formula -/

/-- **The pushforward of affine chains of the slab space into the singular chains of `M̄`**:
the `ℤ`-linear extension of `p ↦ cChain v (slabV v p)`. -/
def slabChain (v : Fin 5) (k : ℕ) : AffC k →ₗ[ℤ] (singCxFun.obj cMtop).X k :=
  Finsupp.linearCombination ℤ fun p => cChain v (slabV v p)

theorem slabChain_add (v : Fin 5) (k : ℕ) (c d : AffC k) :
    slabChain v k (c + d) = slabChain v k c + slabChain v k d := map_add _ _ _

theorem slabChain_single (v : Fin 5) (k : ℕ) (p : Fin (k + 1) → CuspE3) (a : ℤ) :
    slabChain v k (Finsupp.single p a) = a • cChain v (slabV v p) := by
  rw [slabChain, Finsupp.linearCombination_single]
  exact int_smul_eq_zsmul _ a _

theorem slabChain_single_one (v : Fin 5) (k : ℕ) (p : Fin (k + 1) → CuspE3) :
    slabChain v k (Finsupp.single p (1 : ℤ)) = cChain v (slabV v p) := by
  rw [slabChain, Finsupp.linearCombination_single]
  exact (int_smul_eq_zsmul _ (1 : ℤ) _).trans (one_smul ℤ _)

/-- The differential of the singular chain complex of `M̄` commutes with the `ℤ`-action. -/
theorem slabD_zsmul (k : ℕ) (a : ℤ) (x : (singCxFun.obj cMtop).X (k + 1)) :
    (singCxFun.obj cMtop).d (k + 1) k (a • x)
      = a • ((singCxFun.obj cMtop).d (k + 1) k x) :=
  map_zsmul (ConcreteCategory.hom ((singCxFun.obj cMtop).d (k + 1) k)) a x

private theorem slabChain_d_gen_one (v : Fin 5) (k : ℕ) (p : Fin (k + 2) → CuspE3) :
    (singCxFun.obj cMtop).d (k + 1) k (slabChain v (k + 1) (Finsupp.single p (1 : ℤ)))
      = slabChain v k (dLC k (Finsupp.single p (1 : ℤ))) := by
  have hL : slabChain v (k + 1) (Finsupp.single p (1 : ℤ)) = cChain v (slabV v p) :=
    slabChain_single_one v (k + 1) p
  have hR : slabChain v k (dLC k (Finsupp.single p (1 : ℤ)))
      = ∑ i : Fin (k + 2), ((-1 : ℤ) ^ (i : ℕ)) • cChain v (slabV v (vface i p)) := by
    rw [dLC_single, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, slabChain_single_one]
  rw [hL, cChain_d, hR]
  refine Finset.sum_congr rfl fun i _ => ?_
  rfl

theorem slabChain_d_single (v : Fin 5) (k : ℕ) (p : Fin (k + 2) → CuspE3) (a : ℤ) :
    (singCxFun.obj cMtop).d (k + 1) k (slabChain v (k + 1) (Finsupp.single p a))
      = slabChain v k (dLC k (Finsupp.single p a)) := by
  have hs : (Finsupp.single p a : AffC (k + 1)) = a • Finsupp.single p (1 : ℤ) := by
    rw [Finsupp.smul_single_one]
  rw [hs, map_zsmul, slabD_zsmul, slabChain_d_gen_one,
    map_zsmul (dLC k) a, ← map_zsmul (slabChain v k) a]

theorem slabChain_d (v : Fin 5) (k : ℕ) (c : AffC (k + 1)) :
    (singCxFun.obj cMtop).d (k + 1) k (slabChain v (k + 1) c)
      = slabChain v k (dLC k c) := by
  refine Finsupp.induction c ?_ ?_
  · simp
  · intro p a f hp ha hf
    simp only [map_add]
    rw [hf, slabChain_d_single]

/-! ## §3  Periodicity of the chart chains under the cusp lattice -/

/-- **Translating a vertex family by a cusp lattice vector does not change the chart chain.** -/
theorem cChain_add_lattice (v : Fin 5) {k : ℕ} (p : Fin (k + 1) → CuspE3) (l : CuspE3)
    (hl : l ∈ Work.Cusp.lattice v) :
    cChain v (fun i => p i + l) = cChain v p := by
  rw [cChain, cChain]
  congr 1
  ext z
  rw [cSimp_apply, cSimp_apply]
  have hpt : cPt (fun i => p i + l) z = cPt p z + l := by
    rw [cPt_eq_sum, cPt_eq_sum]
    have hsum : (∑ i, z.weights i • (p i + l)) = (∑ i, z.weights i • p i) + l := by
      simp only [smul_add, Finset.sum_add_distrib]
      rw [← Finset.sum_smul, StdSimplex.total_of_fintype, one_smul]
    exact hsum
  rw [hpt]
  exact Work.RTOwed.mbarPtC_periodic v (by rw [add_sub_cancel_left]; exact hl)


/-! ## §4  Reduction of the target to a slab cycle -/

/-- **A 2-cycle of the slab space whose `slabChain`-image is `singT v - s • Ψ_M(planeCycleVec v 0)`
produces the chain of `planeIdentT`** (by coning it over any point of the slab space). -/
theorem slabChain_cone (v : Fin 5) (q : CuspE3) (c : AffC 2) (hc : dLC 1 c = 0) :
    (singCxFun.obj cMtop).d 3 2 (slabChain v 3 (coneLC 2 q c)) = slabChain v 2 c := by
  rw [slabChain_d v 2 (coneLC 2 q c), dLC_coneLC_of_dLC_eq_zero 1 q c hc]

/-- **The reduction step.**  If some `2`-cycle `c` of the slab space is carried by `slabChain v` to
`singT v - s • Ψ_M(planeCycleVec v 0)`, then the chain of `planeIdentT` exists (with the same sign
`s`). -/
theorem exists_of_slabCycle (v : Fin 5) (s : ℤ) (hs : s = 1 ∨ s = -1) (c : AffC 2)
    (q : CuspE3) (hc : dLC 1 c = 0)
    (himg : slabChain v 2 c = Work.BridgeSquare.singT v
      - s • ((Work.BridgeSquare.PsiM.f 2) (Work.BridgeSquare.planeCycleVec v 0))) :
    ∃ (s' : ℤ) (y : ↑((Work.BridgeSquare.singCxFun.obj (TopCat.of Work.FoldInst.Mbar)).X 3)),
      (s' = 1 ∨ s' = -1) ∧
      ((Work.BridgeSquare.singCxFun.obj (TopCat.of Work.FoldInst.Mbar)).d 3 2) y
        = Work.BridgeSquare.singT v
          - s' • (Work.BridgeSquare.PsiM.f 2) (Work.BridgeSquare.planeCycleVec v 0) := by
  refine ⟨s, slabChain v 3 (coneLC 2 q c), hs, ?_⟩
  rw [slabChain_cone v q c hc, himg]

end

end Work.BridgeSquare
