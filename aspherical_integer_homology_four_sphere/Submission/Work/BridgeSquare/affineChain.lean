/-
# `BridgeSquare/affineChain.lean` — affine chains of the cusp coordinate space `E3`

The cusp coordinate space `E3 = ℝ³` is convex, so an affine simplex of `E3` with prescribed vertices
is an honest continuous map `Δ^k → E3`; these are the pieces out of which the chains of the fibre
identities are built, before pushing them into `M̄` by the ceiling map `mbarPt v`.

Contents.

* `CuspE3` — the cusp coordinate space;
* `esimp`, `esimp_apply`, `esimp_map`, `esimp_face`, `esimp_boundary` — affine simplices of `E3` and
  the boundary formula;
* `loopC` — the `κ_{v,3}`-loop (the line through the centres of the cusp cubes);
* `cornerC` — the corner line of the same longitude (the line through the cube corners);
* `unitStep`, `corPt`, `piece` — the unit cube edges of the corner line, and
  `lam3_eq_smul_unitStep`, the data identity `κ_{v,3} = (fibreLen v 1) • u` behind the subdivision
  of the corner line into `fibreLen v 1` unit edges.
-/
import Mathlib
import Submission.Work.BridgeSquare.FibreData
import Submission.Work.BridgeSquare.PsiM_truncCell_mem_range
import Submission.Work.BridgeSquare.Fn_apply

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option maxHeartbeats 4000000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped Topology Simplicial
open Convexity

namespace Work.BridgeSquare

noncomputable section

/-- The cusp coordinate space. -/
abbrev CuspE3 := Work.Cusp.E3

/-! ## Affine simplices of the cusp coordinate space -/

/-- **The affine simplex of `E3` with the given vertices**: `w ↦ ∑ i, w_i • p_i`. -/
def esimp {k : ℕ} (p : Fin (k + 1) → CuspE3) :
    C(StdSimplex ℝ (Fin (k + 1)), TopCat.of CuspE3) where
  toFun w := ∑ i, w.weights i • p i
  continuous_toFun := by
    apply continuous_finsetSum
    intro i _
    exact ((by fun_prop : Continuous fun w : StdSimplex ℝ (Fin (k + 1)) =>
      w.weights i)).smul continuous_const

@[simp] theorem esimp_apply {k : ℕ} (p : Fin (k + 1) → CuspE3)
    (w : StdSimplex ℝ (Fin (k + 1))) :
    esimp p w = ∑ i, w.weights i • p i := rfl

/-- The affine simplex commutes with reindexing the standard simplex. -/
theorem esimp_map {k l : ℕ} (p : Fin (k + 1) → CuspE3) (f : Fin (l + 1) → Fin (k + 1))
    (z : StdSimplex ℝ (Fin (l + 1))) :
    esimp p (StdSimplex.map f z) = esimp (fun j => p (f j)) z := by
  show (∑ i, (StdSimplex.map f z).weights i • p i) = (∑ i, z.weights i • p (f i))
  rw [Convexity.StdSimplex.weights_map,
    ← Finsupp.sum_fintype _ (fun j c => c • p j) (by intro i; simp),
    ← Finsupp.sum_fintype _ (fun i c => c • p (f i)) (by intro i; simp)]
  exact Finsupp.sum_mapDomain_index (fun b => by simp) (fun b m₁ m₂ => by simp [add_smul])

/-- The `i`-th face of the affine simplex `esimp p` is the affine simplex on the face of the
vertex family. -/
theorem esimp_face {k : ℕ} (p : Fin (k + 2) → CuspE3) (i : Fin (k + 2)) :
    (TopCat.toSSetObjEquiv (TopCat.of CuspE3)
        (Opposite.op (SimplexCategory.mk k)))
      ((TopCat.toSSet.obj (TopCat.of CuspE3)).δ i
        ((TopCat.toSSetObjEquiv (TopCat.of CuspE3)
          (Opposite.op (SimplexCategory.mk (k + 1)))).symm (esimp p)))
      = esimp (fun j => p (i.succAbove j)) := by
  apply ContinuousMap.ext
  intro z
  rw [TopCat.toSSetObjEquiv_δ_apply, Equiv.apply_symm_apply]
  exact esimp_map p i.succAbove z

/-- **The boundary of an affine simplex of `E3`**: the alternating sum of its faces. -/
theorem esimp_boundary {k : ℕ} (p : Fin (k + 2) → CuspE3) :
    (singCxFun.obj (TopCat.of CuspE3)).d (k + 1) k (singGen (esimp p)) =
      ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
        singGen (esimp (fun j => p (i.succAbove j))) := by
  have h := Work.Cohomology.chainComplex_d_ι_apply (R := ℤ)
    (X := TopCat.toSSet.obj (TopCat.of CuspE3)) (n := k)
    ((TopCat.toSSetObjEquiv (TopCat.of CuspE3)
      (Opposite.op (SimplexCategory.mk (k + 1)))).symm (esimp p))
  refine h.trans (Finset.sum_congr rfl fun i _ => ?_)
  congr 1
  show ((TopCat.toSSet.obj (TopCat.of CuspE3)).ιChainComplex (R := Work.Homology.ZMod)
      (((TopCat.toSSet.obj (TopCat.of CuspE3)).δ i)
        ((TopCat.toSSetObjEquiv (TopCat.of CuspE3)
          (Opposite.op (SimplexCategory.mk (k + 1)))).symm (esimp p)))) (1 : ℤ)
    = ((TopCat.toSSet.obj (TopCat.of CuspE3)).ιChainComplex (R := Work.Homology.ZMod)
      ((TopCat.toSSetObjEquiv (TopCat.of CuspE3)
        (Opposite.op (SimplexCategory.mk k))).symm
          (esimp (fun j => p (i.succAbove j))))) (1 : ℤ)
  have hface : ((TopCat.toSSet.obj (TopCat.of CuspE3)).δ i)
        ((TopCat.toSSetObjEquiv (TopCat.of CuspE3)
          (Opposite.op (SimplexCategory.mk (k + 1)))).symm (esimp p))
      = (TopCat.toSSetObjEquiv (TopCat.of CuspE3)
          (Opposite.op (SimplexCategory.mk k))).symm
          (esimp (fun j => p (i.succAbove j))) := by
    rw [Equiv.eq_symm_apply]
    exact esimp_face p i
  rw [hface]

/-! ## The `κ_{v,3}`-loop and its corner line -/

/-- The `κ_{v,3}`-loop in the cube coordinates: the line through the **centres** of the cubes. -/
def loopC (v : Fin 5) : (singCxFun.obj (TopCat.of CuspE3)).X 1 :=
  singGen (esimp ![Work.RTOwed.cuspH, Work.RTOwed.cuspH + Work.Cusp.lam3 v])

/-- The **corner line** of the same longitude: the line through the cube corners. -/
def cornerC (v : Fin 5) : (singCxFun.obj (TopCat.of CuspE3)).X 1 :=
  singGen (esimp ![0, Work.Cusp.lam3 v])

/-! ## The unit cube edges of the corner line -/

/-- The unit step along the `κ_{v,3}` direction. -/
def unitStep (v : Fin 5) : CuspE3 :=
  Work.Cusp.ofInt3 (fun i => if i = Work.BridgeSquare.fibreDir v 1 then
    (if 0 < Work.Cusp.kappa v 2 i then 1 else -1) else 0)

/-- The `k`-th lattice point of the corner line: `k • u`. -/
def corPt (v : Fin 5) (k : ℕ) : CuspE3 := (k : ℝ) • unitStep v

/-- The `k`-th unit cube edge of the corner line. -/
def piece (v : Fin 5) (k : Fin (Work.BridgeSquare.fibreLen v 1)) :
    (singCxFun.obj (TopCat.of CuspE3)).X 1 :=
  singGen (esimp ![corPt v k, corPt v (k + 1)])

/-- `κ_{v,3} = (fibreLen v 1) • u`: the data identity behind the subdivision. -/
theorem lam3_eq_smul_unitStep (v : Fin 5) :
    Work.Cusp.lam3 v = (Work.BridgeSquare.fibreLen v 1 : ℝ) • unitStep v := by
  rw [show Work.Cusp.lam3 v = Work.Cusp.kv v 2 from rfl]
  ext i
  simp only [Work.Cusp.kv, Work.Cusp.ofInt3, Work.BridgeSquare.unitStep]
  fin_cases v <;> fin_cases i <;>
    simp [Work.BridgeSquare.fibreLen, Work.BridgeSquare.fibreDir, Work.BridgeSquare.dirKappa,
      Work.Cusp.latMod, Work.Cusp.kappa]

end

end Work.BridgeSquare
